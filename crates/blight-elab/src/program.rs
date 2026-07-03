//! The multi-form program/prelude driver (spec §8.2, Stage 2). UNTRUSTED.
//!
//! M0's REPL processes one form at a time and can only attach a type to a recursive definition
//! through an out-of-band table (see the test helpers in [`crate::elab`]). M3 needs to *load*
//! real Blight programs — a prelude, then a tower written in Blight — so this module owns:
//!
//! - a [`Program`] driver that threads a single [`ElabEnv`] over many top-level forms;
//! - a `(load "path")` form that splices another file's forms in place;
//! - a *typed* recursive-definition surface form, `(define-rec name T body)` /
//!   `(deftotal name T body)` (and the optional `(define name T body)`), since the kernel reads a
//!   recursive definition's motive off its declared type (`elab.rs`, `Decl::DefineRec`) and there
//!   is otherwise no surface way to attach that type.
//!
//! None of this is trusted: every definition still bottoms out in [`ElabEnv::declare`], whose core
//! term the spore re-checks.

use crate::diagnostic::Diagnostic;
use crate::elab::{elaborate, parse_decl, ElabEnv, ElabError};
use crate::macros::MacroEnv;
use crate::scope::narrow_span;
use crate::sexpr::{read_all, read_all_spanned, Sexpr};
use crate::spores::PackageManifest;
use crate::surface::Decl;
use blight_kernel::{check_top_with, Proof, Term};
use std::collections::HashSet;

/// What processing one top-level form produced.
#[derive(Debug, Clone)]
pub enum Outcome {
    /// A declaration updated the environment (no checking result to report).
    Declared,
    /// An ascribed term `(the T e)` was checked by the kernel, yielding a proof.
    Checked(Proof),
}

/// Resolves a `(load "name")` form to source text (filesystem, in-memory, or embedded prelude).
type Resolver<'a> = Box<dyn Fn(&str) -> Result<String, ElabError> + 'a>;

/// A driver that loads and processes many forms against one shared [`ElabEnv`].
pub struct Program<'a> {
    env: &'a mut ElabEnv,
    /// Resolves a `(load "name")` form to source text. The default resolver reads the filesystem;
    /// tests inject an in-memory resolver so they need no on-disk fixtures.
    resolver: Resolver<'a>,
    /// The hygienic macro table; `(define-macro …)` forms register here and every other form is
    /// macro-expanded before parsing/elaboration.
    macros: MacroEnv,
    /// An optional package manifest. When present, `(import "pkg/mod")` resolves module identifiers
    /// against it (independently of the `(load …)` resolver).
    package: Option<PackageManifest>,
    /// Module identifiers already fully imported — `(import …)` of one of these is a no-op
    /// (idempotent re-import).
    imported: HashSet<String>,
    /// Module identifiers whose import is in progress (the import stack), used to detect cycles.
    importing: Vec<String>,
}

impl<'a> Program<'a> {
    /// A driver whose `(load …)` reads from the filesystem.
    pub fn new(env: &'a mut ElabEnv) -> Self {
        Program {
            env,
            resolver: Box::new(|path: &str| {
                std::fs::read_to_string(path)
                    .map_err(|e| ElabError::BadForm(format!("cannot load {path:?}: {e}")))
            }),
            macros: MacroEnv::new(),
            package: None,
            imported: HashSet::new(),
            importing: Vec::new(),
        }
    }

    /// A driver whose `(load …)` is resolved by `resolver` (used in tests and for the embedded
    /// prelude).
    pub fn with_resolver(
        env: &'a mut ElabEnv,
        resolver: impl Fn(&str) -> Result<String, ElabError> + 'a,
    ) -> Self {
        Program {
            env,
            resolver: Box::new(resolver),
            macros: MacroEnv::new(),
            package: None,
            imported: HashSet::new(),
            importing: Vec::new(),
        }
    }

    /// A driver backed by a [`PackageManifest`]: `(import "pkg/mod")` resolves module identifiers
    /// against the manifest, and `(load …)` falls back to the manifest's module resolver too (so a
    /// package's modules may use either form). Imports are deduplicated and cycle-checked.
    pub fn with_package(env: &'a mut ElabEnv, manifest: PackageManifest) -> Self {
        // The `load` resolver shares the manifest's module resolution, so legacy `(load "pkg/mod")`
        // inside package sources still works. We clone the manifest into the boxed resolver.
        let resolver_manifest = manifest.clone();
        Program {
            env,
            resolver: Box::new(move |module: &str| resolver_manifest.resolve(module)),
            macros: MacroEnv::new(),
            package: Some(manifest),
            imported: HashSet::new(),
            importing: Vec::new(),
        }
    }

    /// A driver backed by a [`PackageManifest`] *and* a fallback resolver for `(load …)`: the
    /// manifest is tried first (so a pinned dependency always wins over anything else of the same
    /// name — the manifest is the source of truth once a project opts into one), and only a path
    /// the manifest doesn't know about falls through to `fallback`. This is what
    /// [`Self::with_package`] is missing: that constructor's `(load …)` resolver is
    /// manifest-*only*, so e.g. the CLI's embedded-prelude fallback (`(load "std/nat.bl")` with no
    /// source checkout) silently stops working the moment a project adds a `spore.toml` — this
    /// constructor is how the CLI keeps both working together.
    ///
    /// `(import "pkg/mod")` is unaffected by `fallback`: it always resolves strictly against the
    /// manifest (see `run_import`), since an import is inherently "one of my declared
    /// dependencies", not an arbitrary loadable path.
    pub fn with_package_and_fallback(
        env: &'a mut ElabEnv,
        manifest: PackageManifest,
        fallback: impl Fn(&str) -> Result<String, ElabError> + 'a,
    ) -> Self {
        let resolver_manifest = manifest.clone();
        Program {
            env,
            resolver: Box::new(move |path: &str| match resolver_manifest.resolve(path) {
                Ok(src) => Ok(src),
                Err(manifest_err) => fallback(path).map_err(|fallback_err| {
                    ElabError::BadForm(format!(
                        "cannot load {path:?}: not found via the package manifest ({manifest_err}) \
                         or the fallback resolver ({fallback_err})"
                    ))
                }),
            }),
            macros: MacroEnv::new(),
            package: Some(manifest),
            imported: HashSet::new(),
            importing: Vec::new(),
        }
    }

    /// Process every form in `src`, returning the outcome of each. Stops at the first error.
    pub fn run(&mut self, src: &str) -> Result<Vec<Outcome>, ElabError> {
        let forms = read_all(src).map_err(|e| ElabError::BadForm(e.msg))?;
        let mut outcomes = Vec::new();
        for form in &forms {
            let mut produced = self.run_form(form)?;
            outcomes.append(&mut produced);
        }
        Ok(outcomes)
    }

    /// Span-aware sibling of [`run`](Self::run): parse with the span-aware reader and, on the first
    /// error, return a [`Diagnostic`] carrying a source span so the caller can render a
    /// caret-underlined message — the *offending sub-expression*'s span when one can be
    /// recovered (currently: an unbound name, via [`narrow_span`]), else the whole top-level
    /// form's span. A reader error carries its own (finer) span.
    pub fn run_with_diagnostics(&mut self, src: &str) -> Result<Vec<Outcome>, Diagnostic> {
        let forms = read_all_spanned(src).map_err(|e| Diagnostic {
            message: e.msg,
            span: e.span,
        })?;
        let mut outcomes = Vec::new();
        for form in &forms {
            let plain = form.strip();
            let mut produced = self
                .run_form(&plain)
                .map_err(|e| Diagnostic::at(e.to_string(), narrow_span(form, &e)))?;
            outcomes.append(&mut produced);
        }
        Ok(outcomes)
    }

    /// Process every form in `src`, collecting a [`Diagnostic`] for **every** failing top-level
    /// form rather than stopping at the first (unlike [`run`](Self::run) and
    /// [`run_with_diagnostics`](Self::run_with_diagnostics)). This is the API an editor/LSP needs:
    /// a buffer with three unrelated typos should report three errors in one pass.
    ///
    /// Forms are not independent: several declaration forms mutate `ElabEnv` incrementally *before*
    /// they are known to succeed (e.g. `(defdata …)` registers each constructor as it elaborates
    /// that constructor's fields, but only declares the datatype itself in the signature at the
    /// very end — see `declare_effect`/`declare_data` in `elab.rs`). So "catch the error and keep
    /// going" would be unsound on its own: a form that fails partway through could leave behind a
    /// constructor registered for a datatype that was never declared, corrupting what later,
    /// unrelated forms observe. To stay sound, every form's mutable state (`ElabEnv`, the macro
    /// table, and the import bookkeeping) is snapshotted before it runs and is restored verbatim if
    /// the form fails, so a rolled-back form leaves *no* trace.
    pub fn check_all_diagnostics(&mut self, src: &str) -> Vec<Diagnostic> {
        let forms = match read_all_spanned(src) {
            Ok(forms) => forms,
            Err(e) => {
                return vec![Diagnostic {
                    message: e.msg,
                    span: e.span,
                }]
            }
        };
        let mut diagnostics = Vec::new();
        for form in &forms {
            let plain = form.strip();
            let env_snapshot = self.env.clone();
            let macros_snapshot = self.macros.clone();
            let imported_snapshot = self.imported.clone();
            let importing_snapshot = self.importing.clone();
            if let Err(e) = self.run_form(&plain) {
                diagnostics.push(Diagnostic::at(e.to_string(), narrow_span(form, &e)));
                *self.env = env_snapshot;
                self.macros = macros_snapshot;
                self.imported = imported_snapshot;
                self.importing = importing_snapshot;
            }
        }
        diagnostics
    }

    /// Process a single top-level form. A `(load …)` expands to the outcomes of the loaded file;
    /// `(define-macro …)` registers a macro; every other form is macro-expanded before processing.
    pub fn run_form(&mut self, form: &Sexpr) -> Result<Vec<Outcome>, ElabError> {
        if let Sexpr::List(items) = form {
            if let Some(Sexpr::Atom(kw)) = items.first() {
                // `(load "path")` — splice another file's forms in place.
                if kw == "load" {
                    if items.len() != 2 {
                        return Err(ElabError::BadForm("(load \"path\")".into()));
                    }
                    let path = string_literal(&items[1]).ok_or_else(|| {
                        ElabError::BadForm("(load \"path\"): path must be a string".into())
                    })?;
                    let src = (self.resolver)(&path)?;
                    return self.run(&src);
                }
                // `(import "pkg/mod")` — resolve a module identifier against the package manifest
                // and splice it *once* (idempotent), guarding against import cycles. Unlike `load`,
                // a repeated import of an already-loaded module is a no-op rather than a re-splice
                // (so instance registrations and datatype declarations are not duplicated).
                if kw == "import" {
                    if items.len() != 2 {
                        return Err(ElabError::BadForm("(import \"pkg/mod\")".into()));
                    }
                    let module = string_literal(&items[1]).ok_or_else(|| {
                        ElabError::BadForm("(import \"pkg/mod\"): module must be a string".into())
                    })?;
                    return self.run_import(&module);
                }
                // `(define-macro name (syntax-rules …))` — register and produce no core output.
                if kw == "define-macro" {
                    self.macros.define(form).map_err(ElabError::BadForm)?;
                    return Ok(vec![Outcome::Declared]);
                }
                // `(mutual …)` / `(define-recs …)` / `(deftotals …)` — mutual recursion. Desugar to a
                // generated tag datatype + one merged recursive function + per-member projections
                // (crate::mutual), then process each emitted form in place. Zero kernel growth.
                if kw == "mutual" || kw == "define-recs" || kw == "deftotals" {
                    let forms = if kw == "mutual" {
                        crate::mutual::desugar_mutual(items)?
                    } else {
                        crate::mutual::desugar_block(kw, items)?
                    };
                    let mut outcomes = Vec::new();
                    for f in &forms {
                        let mut produced = self.run_form(f)?;
                        outcomes.append(&mut produced);
                    }
                    return Ok(outcomes);
                }
                // `(defn name T [pats body] …)` — equation-style definition sugar (E5). Desugar to a
                // `(define-rec name T (lam … (matchx …)))` and process it in place. Zero kernel
                // growth; first-match/exhaustiveness come from the existing `matchx` path.
                if kw == "defn" {
                    let forms = crate::defn::desugar_defn(items)?;
                    let mut outcomes = Vec::new();
                    for f in &forms {
                        let mut produced = self.run_form(f)?;
                        outcomes.append(&mut produced);
                    }
                    return Ok(outcomes);
                }
                // Measured total definition (E6): `(deftotal name T (measure e) (default e) (lam …))`.
                // Desugar to a fueled helper (structural on the prepended fuel) + a seeding wrapper,
                // and process both in place. The kernel certifies totality; measure adequacy is the
                // documented, unchecked contract. Zero kernel growth.
                if crate::measure::is_measured(items) {
                    let forms = crate::measure::desugar_measured(items)?;
                    let mut outcomes = Vec::new();
                    for f in &forms {
                        let mut produced = self.run_form(f)?;
                        outcomes.append(&mut produced);
                    }
                    return Ok(outcomes);
                }
            }
        }
        // Macro-expand before parsing: a macro call rewrites to ordinary surface syntax.
        let expanded = self.macros.expand(form).map_err(ElabError::BadForm)?;
        Ok(vec![self.process_one(&expanded)?])
    }

    /// Resolve and splice a module by identifier (the `(import …)` machinery): idempotent (a
    /// re-import of an already-loaded module produces no forms) and cycle-checked (a module that
    /// transitively imports itself is a clear error rather than an infinite loop). Resolution uses
    /// the package manifest if present, else the `(load …)` resolver.
    fn run_import(&mut self, module: &str) -> Result<Vec<Outcome>, ElabError> {
        // Already fully imported: no-op (idempotent).
        if self.imported.contains(module) {
            return Ok(Vec::new());
        }
        // On the current import stack: a cycle.
        if self.importing.iter().any(|m| m == module) {
            let mut chain = self.importing.clone();
            chain.push(module.to_string());
            return Err(ElabError::BadForm(format!(
                "import cycle detected: {}",
                chain.join(" -> ")
            )));
        }
        let src = match &self.package {
            Some(manifest) => manifest.resolve(module)?,
            None => (self.resolver)(module)?,
        };
        self.importing.push(module.to_string());
        let result = self.run(&src);
        self.importing.pop();
        let outcomes = result?;
        self.imported.insert(module.to_string());
        Ok(outcomes)
    }

    /// Process exactly one (non-`load`) top-level form.
    fn process_one(&mut self, form: &Sexpr) -> Result<Outcome, ElabError> {
        if let Sexpr::List(items) = form {
            if let Some(Sexpr::Atom(kw)) = items.first() {
                match kw.as_str() {
                    // Typed recursive definitions: `(define-rec name T body)` / `(deftotal …)`.
                    // The 3-element form (no type) is rejected here with a clear message, matching
                    // the kernel's requirement that a recursive definition declare its type.
                    "define-rec" | "deftotal" => {
                        return self
                            .process_typed_rec(kw, items)
                            .map(|()| Outcome::Declared);
                    }
                    // `(define name body)` or `(define name T body)`.
                    "define" => {
                        return self.process_define(items).map(|()| Outcome::Declared);
                    }
                    // `(define-by name T <tactic>)` — prove goal `T` by running the tactic script;
                    // the resulting term is re-checked by the spore (LCF) and bound as a global.
                    "define-by" => {
                        return self.process_define_by(items);
                    }
                    // `(class C)` — register a type-class head symbol for instance search.
                    "class" => {
                        if items.len() != 2 {
                            return Err(ElabError::BadForm("(class C)".into()));
                        }
                        let c = crate::elab::sym_pub(&items[1])?;
                        self.env.register_class(&c);
                        return Ok(Outcome::Declared);
                    }
                    // `(instance (C H) dict)` — elaborate `dict` against `(C H)` and register it
                    // keyed by the class `C` and the head type symbol `H`.
                    "instance" => {
                        return self.process_instance(items).map(|()| Outcome::Declared);
                    }
                    _ => {}
                }
            }
        }

        // `defdata` / `effect` go through the ordinary parser, with no external type needed.
        if is_decl_head(form) {
            let decl = parse_decl(form)?;
            self.env.declare(&decl, None)?;
            return Ok(Outcome::Declared);
        }

        // Otherwise it is a term; an ascribed `(the T e)` is checked by the spore.
        let surface = crate::elab::parse_surface(form)?;
        let core = elaborate(self.env, &surface)?;
        match core {
            Term::Ann(e, t) => {
                let proof = check_top_with(self.env.signature().clone(), *e, *t)
                    .map_err(|err| ElabError::BadForm(err.to_string()))?;
                Ok(Outcome::Checked(proof))
            }
            _ => Err(ElabError::BadForm(
                "a bare term must be ascribed `(the T e)` to be checked".into(),
            )),
        }
    }

    /// `(define-rec name T body)` / `(deftotal name T body)`: elaborate `T`, then declare.
    fn process_typed_rec(&mut self, kw: &str, items: &[Sexpr]) -> Result<(), ElabError> {
        if items.len() != 4 {
            return Err(ElabError::BadForm(format!(
                "({kw} name T body): a recursive definition must declare its type"
            )));
        }
        let name = crate::elab::sym_pub(&items[1])?;
        let ty_surface = crate::elab::parse_surface(&items[2])?;
        let body = crate::elab::parse_surface(&items[3])?;
        let ty_core = elaborate(self.env, &ty_surface)?;
        let specs = crate::elab::surface_implicit_specs(self.env, &ty_surface);
        let decl = if kw == "deftotal" {
            Decl::DefTotal {
                name: name.clone(),
                body,
            }
        } else {
            Decl::DefineRec {
                name: name.clone(),
                body,
            }
        };
        self.env.declare(&decl, Some(&ty_core))?;
        self.env.set_implicit_specs(&name, specs);
        Ok(())
    }

    /// `(define name body)` or `(define name T body)`.
    fn process_define(&mut self, items: &[Sexpr]) -> Result<(), ElabError> {
        match items.len() {
            3 => {
                let decl = parse_decl(&Sexpr::List(items.to_vec()))?;
                self.env.declare(&decl, None)
            }
            4 => {
                let name = crate::elab::sym_pub(&items[1])?;
                let ty_surface = crate::elab::parse_surface(&items[2])?;
                let body = crate::elab::parse_surface(&items[3])?;
                let ty_core = elaborate(self.env, &ty_surface)?;
                let specs = crate::elab::surface_implicit_specs(self.env, &ty_surface);
                let decl = Decl::Define {
                    name: name.clone(),
                    body,
                };
                self.env.declare(&decl, Some(&ty_core))?;
                self.env.set_implicit_specs(&name, specs);
                Ok(())
            }
            _ => Err(ElabError::BadForm(
                "(define name body) or (define name T body)".into(),
            )),
        }
    }

    /// `(define-by name T <tactic>)`: prove the goal type `T` by running the tactic script against
    /// it, then bind `name := <proof term>` (the term re-checked by the spore). Returns the kernel
    /// [`Proof`] as a [`Outcome::Checked`] — the proof-by-tactics acceptance path (spec §6.3, §9).
    fn process_define_by(&mut self, items: &[Sexpr]) -> Result<Outcome, ElabError> {
        if items.len() != 4 {
            return Err(ElabError::BadForm("(define-by name T <tactic>)".into()));
        }
        let name = crate::elab::sym_pub(&items[1])?;
        let goal_ty = crate::elab::parse_surface(&items[2])?;
        let tac = crate::tactic::parse_tactic(&items[3])
            .map_err(|e| ElabError::BadForm(format!("tactic script: {e:?}")))?;
        let goal = crate::tactic::Goal::new(goal_ty.clone());
        // Run the tactic to *propose* a surface proof term, then re-check via the kernel door.
        let proof_term = crate::tactic::run(self.env, &tac, &goal)
            .map_err(|e| ElabError::BadForm(format!("tactic failed: {e:?}")))?;
        let proof = crate::tactic::check_core(self.env, &goal_ty, &proof_term)
            .map_err(|m| ElabError::BadForm(format!("proof-by-tactics rejected: {m}")))?;
        // Bind the (now-verified) proof term as a global so later forms may refer to it.
        let ty_core = elaborate(self.env, &goal_ty)?;
        let term_core = crate::elab::elaborate_against(self.env, &proof_term, &ty_core)?;
        let decl = Decl::Define {
            name: name.clone(),
            body: proof_term,
        };
        let _ = term_core; // the body is re-elaborated by `declare`; this confirms it elaborates.
        self.env.declare(&decl, Some(&ty_core))?;
        Ok(Outcome::Checked(proof))
    }

    /// `(instance (C H) dict)`: `C` is a (registered) class, `H` the head type symbol. The
    /// dictionary `dict` is elaborated and checked against the constraint type `(C H)`, then
    /// registered for instance search. Re-registering `(C H)` is an overlapping-instance error.
    fn process_instance(&mut self, items: &[Sexpr]) -> Result<(), ElabError> {
        if items.len() != 3 {
            return Err(ElabError::BadForm("(instance (C H) dict)".into()));
        }
        let head_form = match &items[1] {
            Sexpr::List(parts) if parts.len() == 2 => parts,
            _ => return Err(ElabError::BadForm("instance head must be (C H)".into())),
        };
        let class = crate::elab::sym_pub(&head_form[0])?;
        let head = crate::elab::sym_pub(&head_form[1])?;
        if !self.env.is_class(&class) {
            return Err(ElabError::BadForm(format!(
                "`{class}` is not a registered class (declare `(class {class})` first)"
            )));
        }
        // Elaborate the constraint type `(C H)` and the dictionary value against it.
        let cty_surface = crate::elab::parse_surface(&items[1])?;
        let cty = elaborate(self.env, &cty_surface)?;
        let dict_surface = crate::elab::parse_surface(&items[2])?;
        let dict = crate::elab::elaborate_against(self.env, &dict_surface, &cty)?;
        // Re-check the dictionary through the spore so a bogus instance is rejected at registration.
        check_top_with(self.env.signature().clone(), dict.clone(), cty)
            .map_err(|err| ElabError::BadForm(format!("instance dictionary ill-typed: {err}")))?;
        self.env.register_instance(&class, &head, dict)
    }
}

/// Whether a form's head is a declaration keyword the ordinary parser handles directly.
fn is_decl_head(form: &Sexpr) -> bool {
    matches!(form, Sexpr::List(items)
        if matches!(items.first(), Some(Sexpr::Atom(kw)) if kw == "defdata" || kw == "effect" || kw == "foreign"))
}

/// Extract the contents of a string-literal atom `"…"`, if `s` is one.
fn string_literal(s: &Sexpr) -> Option<String> {
    match s {
        Sexpr::Atom(a) if a.starts_with('"') && a.ends_with('"') && a.len() >= 2 => {
            Some(a[1..a.len() - 1].to_string())
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A `define-macro` registers a hygienic macro; a later call expands and the result is
    /// checked by the spore — proving the macro phase runs *before* elaboration in the driver.
    #[test]
    fn do_notation_macro() {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define-macro two (syntax-rules () ((two x) (Succ (Succ x)))))\n\
                 (the Nat (two Zero))",
            )
            .expect("macro expands and checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// A program of several declarations threads one environment: later forms see earlier ones.
    #[test]
    fn program_loads_multiple_decls() {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define one (the Nat (Succ Zero)))\n\
                 (the Nat (Succ (Succ Zero)))",
            )
            .expect("program runs")
        };
        assert_eq!(outcomes.len(), 3);
        assert!(
            matches!(outcomes[2], Outcome::Checked(_)),
            "the last form is kernel-checked"
        );
        assert!(
            env.global_term("one").is_some(),
            "the definition is recorded"
        );
    }

    /// `with_package_and_fallback`: a `(load …)` path the manifest doesn't know about still
    /// resolves via the fallback resolver — the CLI's embedded-prelude-under-a-manifest-project
    /// regression this constructor exists to fix.
    #[test]
    fn with_package_and_fallback_falls_through_for_unknown_paths() {
        let manifest = PackageManifest::parse(
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
            std::path::Path::new("/proj"),
        )
        .expect("manifest parses");
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_package_and_fallback(&mut env, manifest, |path| {
                if path == "std/nat.bl" {
                    Ok("(defdata Nat () (Zero) (Succ (n Nat)))".into())
                } else {
                    Err(ElabError::BadForm(format!(
                        "no such fallback file {path:?}"
                    )))
                }
            });
            prog.run("(load \"std/nat.bl\")\n(the Nat Zero)")
                .expect("falls back and checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// `with_package_and_fallback`: when *both* the manifest and the fallback could resolve a
    /// path, the manifest wins — a pinned dependency is never silently shadowed by whatever the
    /// fallback would have produced.
    #[test]
    fn with_package_and_fallback_prefers_the_manifest() {
        let dir = std::env::temp_dir().join(format!(
            "blight_program_manifest_precedence_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("main.bl"),
            "(defdata FromManifest () (FromManifestCtor))",
        )
        .unwrap();
        let manifest =
            PackageManifest::parse("[package]\nname = \"demo\"\nversion = \"0.1.0\"\n", &dir)
                .expect("manifest parses");
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_package_and_fallback(&mut env, manifest, |_path| {
                Ok("(defdata FromFallback () (FromFallbackCtor))".into())
            });
            prog.run("(load \"demo/main\")").expect("manifest resolves");
        }
        assert!(
            env.data_constructors("FromManifest").is_some(),
            "the manifest's source won, not the fallback's"
        );
        assert!(env.data_constructors("FromFallback").is_none());
        std::fs::remove_dir_all(&dir).ok();
    }

    /// When neither the manifest nor the fallback can resolve a path, the error mentions both
    /// attempts (so a user isn't left guessing which resolution path was supposed to work).
    #[test]
    fn with_package_and_fallback_reports_both_failures() {
        let manifest = PackageManifest::parse(
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
            std::path::Path::new("/proj"),
        )
        .expect("manifest parses");
        let mut env = ElabEnv::new();
        let mut prog = Program::with_package_and_fallback(&mut env, manifest, |path| {
            Err(ElabError::BadForm(format!("fallback also has no {path:?}")))
        });
        let r = prog.run("(load \"nope.bl\")");
        match r {
            Err(ElabError::BadForm(msg)) => {
                assert!(msg.contains("package manifest"), "{msg}");
                assert!(msg.contains("fallback"), "{msg}");
            }
            other => panic!("expected a BadForm error, got {other:?}"),
        }
    }

    /// `(load "name")` splices another file's forms; the resolver supplies the source.
    #[test]
    fn load_form_pulls_in_file() {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, |path| {
                if path == "nat.bl" {
                    Ok("(defdata Nat () (Zero) (Succ (n Nat)))".into())
                } else {
                    Err(ElabError::BadForm(format!("no such file {path:?}")))
                }
            });
            prog.run("(load \"nat.bl\")\n(the Nat Zero)")
                .expect("loads and checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// The typed recursive form `(define-rec name T body)` elaborates with the type supplied
    /// inline — no out-of-band table needed.
    #[test]
    fn typed_define_rec_form_elaborates() {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define-rec double (Pi ((n Nat)) Nat) \
                    (lam (n) (match n [(Zero) Zero] [(Succ k) (Succ (Succ (double k)))])))",
            )
            .expect("typed define-rec elaborates");
        }
        assert!(env.global_term("double").is_some());
    }

    /// A bare `(define-rec name body)` (no type) is a clear error, not a silent acceptance.
    #[test]
    fn untyped_define_rec_rejected() {
        let mut env = ElabEnv::new();
        let mut prog = Program::new(&mut env);
        let r = prog.run("(define-rec loop (lam (n) (loop n)))");
        assert!(matches!(r, Err(ElabError::BadForm(_))));
    }

    /// A `Sigma` type with a `pair` value round-trips through the spore (records are sound sugar).
    #[test]
    fn sigma_pair_checks_through_spore() {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (the (Sigma ((x Nat)) Nat) (pair Zero (Succ Zero)))",
            )
            .expect("sigma/pair checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    // ---- implicit arguments + unification (spec §6.4) ----------------------------------------

    /// Set up a polymorphic identity `id : {A : Type 0} → A → A` and return the env.
    fn env_with_id() -> ElabEnv {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define id (Pi ({A (Type 0) 0} (x A)) A) (lam (A x) x))",
            )
            .expect("id defines");
        }
        env
    }

    /// `(id Zero)` inserts the implicit type argument `A := Nat`, producing `((id Nat) Zero)` that
    /// re-checks through the spore at `Nat`.
    #[test]
    fn implicit_arg_inserted() {
        let mut env = env_with_id();
        assert_eq!(env.implicit_arity("id"), 1, "id has one leading implicit");
        let outcomes = {
            let mut prog = Program::new(&mut env);
            prog.run("(the Nat (id Zero))")
                .expect("implicit inserted and checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// The implicit can be solved from the *expected* result type: `(the Nat (id Zero))` unifies
    /// the result `A` against `Nat`. (Here it is also solvable from the argument; the point is the
    /// pipeline accepts result-driven solving.)
    #[test]
    fn meta_solved_from_result() {
        let mut env = env_with_id();
        // `(id (Succ Zero))` against expected `Nat`.
        let outcomes = {
            let mut prog = Program::new(&mut env);
            prog.run("(the Nat (id (Succ Zero)))").expect("solved")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// The implicit binder is *grade 0* (erasable): its declared type is `(Pi ((A …0)) …)`, so the
    /// stored core type begins with a grade-`Zero` `Pi`.
    #[test]
    fn implicit_grade_zero_erased() {
        let env = env_with_id();
        let ty = env
            .global_type("id")
            .expect("id has a declared type")
            .clone();
        match ty {
            Term::Pi(g, _, _) => {
                assert_eq!(g, blight_kernel::Grade::Zero, "implicit binder is erased")
            }
            other => panic!("expected leading Pi, got {other:?}"),
        }
    }

    /// An ambiguous implicit — one that neither the arguments nor the expected type pin down — is a
    /// clear elaboration error, never a silently-wrong term.
    #[test]
    fn ambiguous_meta_errors() {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::new(&mut env);
            // `mkpair : {A:Type0} → Nat → Nat` — the implicit `A` appears *nowhere* in the
            // explicit signature, so nothing can determine it.
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define mkpair (Pi ({A (Type 0) 0} (x Nat)) Nat) (lam (A x) x))",
            )
            .expect("mkpair defines");
        }
        let mut prog = Program::new(&mut env);
        let r = prog.run("(the Nat (mkpair Zero))");
        assert!(
            matches!(r, Err(ElabError::BadForm(_))),
            "ambiguous implicit is rejected: {r:?}"
        );
    }

    // ---- instance / dictionary search (spec §6.4) --------------------------------------------

    /// Build an env with a `Show` class (`Show a := a → Nat`), a constrained `showit`, and a
    /// `Show Nat` instance. `extra` is appended after the standard preamble.
    fn env_with_show(extra: &str) -> Result<ElabEnv, ElabError> {
        let mut env = ElabEnv::new();
        let src = format!(
            "(defdata Nat () (Zero) (Succ (n Nat)))\n\
             (class Show)\n\
             (define Show (Pi ((a (Type 0))) (Type 0)) (lam (a) (Pi ((x a)) Nat)))\n\
             (define showit (Pi ({{A (Type 0) 0}} {{d (Show A)}} (x A)) Nat) \
                (lam (A d x) (d x)))\n\
             {extra}"
        );
        let mut prog = Program::new(&mut env);
        prog.run(&src)?;
        drop(prog);
        Ok(env)
    }

    /// `(showit Zero)` resolves the `Show Nat` dictionary and applies it, checking at `Nat`.
    #[test]
    fn instance_resolved_for_show_nat() {
        let mut env = env_with_show("(instance (Show Nat) (lam (x) x))").expect("setup");
        let outcomes = {
            let mut prog = Program::new(&mut env);
            prog.run("(the Nat (showit Zero))")
                .expect("instance resolved and checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// With no `Show Nat` instance registered, the constraint cannot be discharged.
    #[test]
    fn missing_instance_errors() {
        let mut env = env_with_show("").expect("setup");
        let mut prog = Program::new(&mut env);
        let r = prog.run("(the Nat (showit Zero))");
        assert!(
            matches!(r, Err(ElabError::BadForm(ref m)) if m.contains("instance")),
            "missing instance is an error: {r:?}"
        );
    }

    /// Registering two instances for the same `(class, head)` is rejected (coherence: no overlap).
    #[test]
    fn overlapping_instance_rejected() {
        let r = env_with_show(
            "(instance (Show Nat) (lam (x) x))\n\
             (instance (Show Nat) (lam (x) Zero))",
        );
        assert!(
            matches!(r, Err(ElabError::BadForm(ref m)) if m.contains("overlapping")),
            "overlapping instance is rejected: {r:?}"
        );
    }

    // ---- `check_all_diagnostics` (Wave 1 / A1a: LSP-oriented multi-error collection) ----------

    /// Two independent bad top-level forms in one buffer both surface as diagnostics — an editor
    /// wants every error in the buffer, not just the first (unlike `run`/`run_with_diagnostics`,
    /// which stop at the first failure).
    #[test]
    fn collects_a_diagnostic_per_failing_form() {
        let mut env = ElabEnv::new();
        let diags = {
            let mut prog = Program::new(&mut env);
            prog.check_all_diagnostics(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (the Nat undefined-one)\n\
                 (the Nat undefined-two)",
            )
        };
        assert_eq!(
            diags.len(),
            2,
            "both independent bad forms are reported: {diags:?}"
        );
        assert!(diags[0].span.is_some(), "each diagnostic carries a span");
        assert!(diags[1].span.is_some(), "each diagnostic carries a span");
    }

    /// A valid form standing between two bad forms still elaborates and is visible afterwards —
    /// `check_all_diagnostics` does not abandon the rest of the buffer after an error.
    #[test]
    fn valid_form_between_errors_still_commits() {
        let mut env = ElabEnv::new();
        let diags = {
            let mut prog = Program::new(&mut env);
            prog.check_all_diagnostics(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (the Nat undefined-one)\n\
                 (define one (the Nat (Succ Zero)))\n\
                 (the Nat undefined-two)",
            )
        };
        assert_eq!(diags.len(), 2, "the two bad forms are reported: {diags:?}");
        assert!(
            env.global_term("one").is_some(),
            "the good form in between still committed"
        );
    }

    /// The core rollback gotcha: `(defdata ...)` registers constructors into `ElabEnv` one at a
    /// time as it elaborates each field (elab.rs ~340-390), *before* the datatype itself is
    /// declared in the signature. A `defdata` whose second constructor is ill-typed must not leave
    /// the first constructor's registration behind — otherwise a later, unrelated form could
    /// observe a constructor that belongs to no declared datatype.
    #[test]
    fn failed_defdata_does_not_leak_partial_constructor_state() {
        let mut env = ElabEnv::new();
        let diags = {
            let mut prog = Program::new(&mut env);
            prog.check_all_diagnostics(
                "(defdata Bad () (Ok1) (Bad2 (x NoSuchType)))\n\
                 (the Bad (Ok1))",
            )
        };
        // Both the bad `defdata` and the now-meaningless reference to `Bad`/`Ok1` are errors.
        assert_eq!(diags.len(), 2, "{diags:?}");
        assert!(
            env.constructor_rec_flags("Ok1").is_none(),
            "the first constructor of the failed defdata must not remain registered"
        );
        assert!(
            env.data_constructors("Bad").is_none(),
            "the datatype itself must not be registered either"
        );
    }

    /// A whole-buffer reader (parse) error is reported as a single diagnostic, matching
    /// `run_with_diagnostics`'s existing behavior for malformed s-expressions.
    #[test]
    fn unbalanced_parens_is_a_single_reader_diagnostic() {
        let mut env = ElabEnv::new();
        let diags = {
            let mut prog = Program::new(&mut env);
            prog.check_all_diagnostics("(defdata Nat () (Zero)")
        };
        assert_eq!(diags.len(), 1, "{diags:?}");
    }

    /// Wave 9 / T1 (LSP v2): an unbound name deep inside a top-level form is underlined at the
    /// *sub-expression* itself, not the whole enclosing form — the deferred "inline sub-expression
    /// diagnostics" half of the A1 plan's Gotcha 3, delivered via [`crate::scope::narrow_span`]
    /// rather than a full `Surface`/`ElabError` span-threading refactor.
    #[test]
    fn diagnostic_points_at_subexpression_span() {
        let mut env = ElabEnv::new();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (the Nat (lam (x) (Succ undefined-thing)))";
        let diags = {
            let mut prog = Program::new(&mut env);
            prog.check_all_diagnostics(src)
        };
        assert_eq!(diags.len(), 1, "{diags:?}");
        let span = diags[0].span.expect("carries a span");
        assert_eq!(
            &src[span.start..span.end],
            "undefined-thing",
            "the span underlines the offending identifier, not the whole `(the ...)` form"
        );
    }

    /// `run_with_diagnostics` gets the same sub-expression narrowing as `check_all_diagnostics`.
    #[test]
    fn run_with_diagnostics_also_narrows_the_span() {
        let mut env = ElabEnv::new();
        let src = "(defdata Nat () (Zero))\n(the Nat undefined-thing)";
        let mut prog = Program::new(&mut env);
        let err = prog.run_with_diagnostics(src).unwrap_err();
        let span = err.span.expect("carries a span");
        assert_eq!(&src[span.start..span.end], "undefined-thing");
    }

    /// No errors at all yields no diagnostics, and every form commits normally.
    #[test]
    fn clean_buffer_yields_no_diagnostics() {
        let mut env = ElabEnv::new();
        let diags = {
            let mut prog = Program::new(&mut env);
            prog.check_all_diagnostics(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define one (the Nat (Succ Zero)))",
            )
        };
        assert!(diags.is_empty(), "{diags:?}");
        assert!(env.global_term("one").is_some());
    }
}
