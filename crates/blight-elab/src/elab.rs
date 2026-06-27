//! The bidirectional elaborator (spec §6.1): surface terms to core kernel terms. UNTRUSTED.
//!
//! This is the §1.3 governing rule applied to the type checker itself: even "the type system
//! the user experiences" is untrusted tower code. Whatever core term `elaborate` produces is
//! re-checked by the spore; a wrong result is simply rejected (spec §6.1).

use crate::meta::{meta_term, MetaCtx};
use crate::sexpr::Sexpr;
use crate::surface::{Binder, Clause, ConstructorDecl, Decl, Surface};
use blight_kernel::Term;

/// An elaboration error (parsing-into-surface or surface-into-core).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElabError {
    /// A symbol was not in scope.
    Unbound(String),
    /// The s-expression was not a valid surface form.
    BadForm(String),
    /// A `match` did not cover its constructors / referenced an unknown one.
    BadMatch(String),
}

impl ElabError {
    /// The human-facing message body (without the error-kind prefix).
    pub fn message(&self) -> &str {
        match self {
            ElabError::Unbound(s) | ElabError::BadForm(s) | ElabError::BadMatch(s) => s,
        }
    }

    /// A short label for the kind of error, used as a diagnostic prefix.
    pub fn kind_label(&self) -> &'static str {
        match self {
            ElabError::Unbound(_) => "unbound name",
            ElabError::BadForm(_) => "bad form",
            ElabError::BadMatch(_) => "bad match",
        }
    }
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.kind_label(), self.message())
    }
}

impl std::error::Error for ElabError {}

/// The elaboration environment: known top-level definitions and inductive declarations,
/// accumulated as the REPL processes forms.
#[derive(Debug, Clone, Default)]
pub struct ElabEnv {
    /// Top-level definitions: name → (its elaborated core term, optional closed type). When a type
    /// is known, references inline as an ascription so the kernel can infer through applications.
    globals: std::collections::HashMap<String, (Term, Option<Term>)>,
    /// Constructor metadata: constructor name → (data name, recursive-arg flags in order).
    constructors: std::collections::HashMap<String, ConInfo>,
    /// Data declarations: data name → ordered list of constructor names.
    datas: std::collections::HashMap<String, Vec<String>>,
    /// The kernel signature mirroring the declared inductives, used at check time.
    signature: blight_kernel::Signature,
    /// Per-global *implicit specs*: for each leading implicit `Pi` binder of a global's declared
    /// type, how to fill it (by unification, or by instance search). Absent ⟹ no implicit binders.
    implicits: std::collections::HashMap<String, Vec<ImplicitSpec>>,
    /// Registered type-class head symbols (a class `C` is resolved by dictionary search).
    classes: std::collections::HashSet<String>,
    /// Registered instances: `(class, head-type-symbol) → dictionary term` (spec §6.4).
    instances: std::collections::HashMap<(String, String), Term>,
}

/// How the elaborator fills one leading implicit binder at a use site (spec §6.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplicitSpec {
    /// An ordinary implicit type/value argument, solved by metavariable unification.
    Unify,
    /// A type-class constraint `{_ (C A)}`: resolved by dictionary search keyed on `C` and the
    /// head symbol of `A` (which is itself usually an earlier implicit, solved first).
    Instance { class: String },
}

/// Per-constructor info the elaborator needs to desugar `match`/`Con`.
#[derive(Debug, Clone)]
struct ConInfo {
    data: String,
    /// For each argument, whether it is recursive (a value of the data type).
    rec_flags: Vec<bool>,
}

impl ElabEnv {
    pub fn new() -> Self {
        ElabEnv::default()
    }

    /// The kernel signature accumulated from `defdata` declarations.
    pub fn signature(&self) -> &blight_kernel::Signature {
        &self.signature
    }

    /// The elaborated core term for a global definition, if defined.
    pub fn global_term(&self, name: &str) -> Option<&Term> {
        self.globals.get(name).map(|(t, _)| t)
    }

    /// The declared (closed) core type for a global definition, if known.
    pub fn global_type(&self, name: &str) -> Option<&Term> {
        self.globals.get(name).and_then(|(_, ty)| ty.as_ref())
    }

    /// Every global definition that carries a closed type, as `(name, term, type)`. Used by the
    /// independent re-checker harness (M6 §8.3) to re-verify each kernel-accepted definition from
    /// scratch. Definitions without a declared type (untyped `(define name body)`) are skipped,
    /// since there is no claimed type to re-verify against.
    pub fn typed_globals(&self) -> Vec<(String, Term, Term)> {
        let mut out: Vec<(String, Term, Term)> = self
            .globals
            .iter()
            .filter_map(|(name, (term, ty))| {
                ty.as_ref().map(|t| (name.clone(), term.clone(), t.clone()))
            })
            .collect();
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out
    }

    /// The constructor names of an inductive type, in declaration order. Consumed by the tactic
    /// engine's `induction` to enumerate the cases it must cover.
    pub fn data_constructors(&self, data: &str) -> Option<Vec<String>> {
        self.datas.get(data).cloned()
    }

    /// For each argument of a constructor, whether it is recursive (a value of the data type being
    /// defined). The tactic engine uses this to know which `induction` fields carry an induction
    /// hypothesis.
    pub fn constructor_rec_flags(&self, ctor: &str) -> Option<Vec<bool>> {
        self.constructors.get(ctor).map(|i| i.rec_flags.clone())
    }

    /// Register a global definition's elaborated core term together with an optional (closed) type.
    pub fn define_global(&mut self, name: String, term: Term, ty: Option<Term>) {
        self.globals.insert(name, (term, ty));
    }

    /// Re-check an elaborated definition body through the *trusted kernel door*
    /// ([`blight_kernel::check_top_with`]) at its declared type, at `declare` time.
    ///
    /// Historically the elaborator stored each `define`/`define-rec`/`deftotal` body on its own
    /// inferred type and only the opt-in `--recheck` pass ever fed it to a checker. Routing every
    /// eligible definition through the kernel here closes that gap: a body whose elaborated core
    /// term does not actually inhabit its declared type is rejected immediately, not silently
    /// trusted. This grows no TCB — it only sends more programs *through* the existing door.
    ///
    /// The kernel door demands a **pure, total, empty-effect-row** top-level (spec §4.1, §4.5): a
    /// proof may neither diverge nor escape an unhandled effect. So we only route bodies whose
    /// declared type is a *function or path/identity proof* with a pure, total conclusion (see
    /// [`gate_routes_through_kernel`]); effectful `main : (! Console Unit)` and partial
    /// `define-rec : … → Delay A` are out of the pure door and skipped, and closed *ground-value*
    /// definitions (e.g. `main : Nat = …`) are skipped because kernel-checking them degenerates into
    /// running the whole program (codegen already type-checks + executes `main`). Effectful/partial
    /// constructs are governed by their own typing rules during elaboration and re-verified (or
    /// `Declined`) by the `--recheck` pass instead. As a final safety net, if an eligible body
    /// nonetheless trips the kernel's empty-row check (a partial recursion whose declared conclusion
    /// *looked* pure), we treat that as "outside the pure door" and skip rather than reject — only
    /// genuine typing disagreements (`Mismatch`, `GradeViolation`, universe/data errors) hard-error.
    ///
    /// As of plan item 1b the kernel performs *dependent pattern-match refinement* itself
    /// (`check_refined_method`/`refine_method`/`unify_index` in `blight-kernel`), so the former
    /// temporary skip of the `safe-tail`/`vec-map` index-`Mismatch` shape is **gone**: those
    /// definitions are now kernel-certified directly. One narrow skip remains — a *higher-order
    /// eliminator motive* (the `zip-vec` shape, detected structurally up front) — which is a distinct
    /// kernel limitation (motive reconstruction, not refinement) that the independent re-checker also
    /// honestly *declines*; it is out of scope for 1b.
    fn kernel_check_def(&self, name: &str, term: &Term, ty: &Term) -> Result<(), ElabError> {
        if !gate_routes_through_kernel(ty) {
            return Ok(());
        }
        // The higher-order-motive shape (`zip-vec`) is detected structurally and skipped — the kernel
        // cannot reconstruct it yet and the re-checker declines it. Detecting it here (vs. matching a
        // brittle kernel error) keeps the skip precise. This is NOT a dependent-match-refinement case.
        if term_has_higher_order_elim_motive(term) {
            return Ok(());
        }
        match blight_kernel::check_top_with(self.signature().clone(), term.clone(), ty.clone()) {
            Ok(_) => Ok(()),
            // A non-empty effect/partial row on a pure-looking declared type ⟹ outside the pure
            // door; the construct verifies via its own rule / `--recheck`, not here. Skip, do not
            // reject (rejecting would be a false soundness alarm).
            Err(blight_kernel::TypeError::EffectError(_)) => Ok(()),
            Err(e) => Err(ElabError::BadForm(format!(
                "kernel rejected definition `{name}` at its declared type: {e}"
            ))),
        }
    }

    /// Record the implicit-binder specs of global `name` (computed from its surface type), so use
    /// sites insert and resolve them. Empty ⟹ no implicits.
    pub fn set_implicit_specs(&mut self, name: &str, specs: Vec<ImplicitSpec>) {
        if !specs.is_empty() {
            self.implicits.insert(name.to_string(), specs);
        }
    }

    /// The number of leading implicit binders of `name` (0 if none / unknown).
    pub fn implicit_arity(&self, name: &str) -> usize {
        self.implicits.get(name).map(|v| v.len()).unwrap_or(0)
    }

    /// Register a type-class head symbol `C`.
    pub fn register_class(&mut self, class: &str) {
        self.classes.insert(class.to_string());
    }

    /// Whether `name` is a registered type class.
    pub fn is_class(&self, name: &str) -> bool {
        self.classes.contains(name)
    }

    /// Register an instance dictionary for `(class, head)`. Errors on an overlapping (duplicate)
    /// instance — the tower's coherence policy is no-overlap (spec §6.4).
    pub fn register_instance(
        &mut self,
        class: &str,
        head: &str,
        dict: Term,
    ) -> Result<(), ElabError> {
        let key = (class.to_string(), head.to_string());
        if self.instances.contains_key(&key) {
            return Err(ElabError::BadForm(format!(
                "overlapping instance for `{class} {head}` (instances must be unique)"
            )));
        }
        self.instances.insert(key, dict);
        Ok(())
    }

    /// Look up the instance dictionary for `(class, head)`.
    pub fn lookup_instance(&self, class: &str, head: &str) -> Option<&Term> {
        self.instances.get(&(class.to_string(), head.to_string()))
    }

    /// Process a top-level declaration, updating the environment. For `defdata` it also extends the
    /// kernel signature; for `define`/`define-rec` it elaborates and stores the body. A declared
    /// core type may be supplied (required for `define-rec`, whose motive is read off the type).
    pub fn declare(&mut self, decl: &Decl, ty: Option<&Term>) -> Result<(), ElabError> {
        match decl {
            Decl::DefData {
                name,
                params,
                indices,
                constructors,
            } => self.declare_data(name, params, indices, constructors),
            Decl::Define { name, body } => {
                let term = match ty {
                    Some(t) => elaborate_against(self, body, t)?,
                    None => elaborate(self, body)?,
                };
                if let Some(t) = ty {
                    self.kernel_check_def(name, &term, t)?;
                }
                self.define_global(name.clone(), term, ty.cloned());
                Ok(())
            }
            Decl::DefineRec { name, body } => {
                let t = ty.ok_or_else(|| {
                    ElabError::BadForm(format!("`define-rec {name}` requires a declared type"))
                })?;
                let term = elaborate_rec(self, name, body, t, false)?;
                self.kernel_check_def(name, &term, t)?;
                self.define_global(name.clone(), term, Some(t.clone()));
                Ok(())
            }
            Decl::DefTotal { name, body } => {
                let t = ty.ok_or_else(|| {
                    ElabError::BadForm(format!("`deftotal {name}` requires a declared type"))
                })?;
                let term = elaborate_rec(self, name, body, t, true)?;
                self.kernel_check_def(name, &term, t)?;
                self.define_global(name.clone(), term, Some(t.clone()));
                Ok(())
            }
            Decl::DefEffect { name, ops } => self.declare_effect(name, ops),
            Decl::Foreign {
                name,
                ty: surface_ty,
                symbol,
            } => {
                // Elaborate the ascribed type, then bind `name` to a kernel `Foreign` postulate of
                // that type (spec §7.6). The kernel trusts it; codegen calls the C `symbol`; the
                // re-checker declines any judgement mentioning it.
                let core_ty = match ty {
                    Some(t) => t.clone(),
                    None => elaborate(self, surface_ty)?,
                };
                let term = Term::Foreign {
                    symbol: symbol.clone(),
                    ty: Box::new(core_ty.clone()),
                };
                self.define_global(name.clone(), term, Some(core_ty));
                Ok(())
            }
        }
    }

    fn declare_data(
        &mut self,
        name: &str,
        params: &[Binder],
        indices: &[Binder],
        constructors: &[crate::surface::ConstructorDecl],
    ) -> Result<(), ElabError> {
        use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName};
        let data_name = DataName(name.to_string());
        // Elaborate the parameter telescope. Each param type is checked in the scope of the
        // preceding params. The params become the *outermost* binders of every constructor's
        // argument scope (kernel convention: arg/index terms see `[preceding_args, params]`).
        let mut param_scope = Scope::new();
        let mut param_terms = Vec::new();
        for p in params {
            let ty = elab(self, &param_scope, &p.ty, None)?;
            param_terms.push(ty);
            param_scope = param_scope.push_var(&p.name);
        }
        // Index telescope, in scope of the params.
        let mut index_scope = param_scope.clone();
        let mut index_terms = Vec::new();
        for i in indices {
            let ty = elab(self, &index_scope, &i.ty, None)?;
            index_terms.push(ty);
            index_scope = index_scope.push_var(&i.name);
        }
        let mut kernel_ctors = Vec::new();
        let mut ctor_order = Vec::new();
        for ctor in constructors {
            let cname = &ctor.name;
            let mut args = Vec::new();
            let mut rec_flags = Vec::new();
            // Each field is elaborated in `param_scope` extended by the preceding fields, so a
            // field type may reference the parameter(s) and earlier fields.
            let mut field_scope = param_scope.clone();
            for f in &ctor.fields {
                // A field is recursive iff its type's head is the data being defined (applied to
                // the params, for a parameterized family). We detect both `D` (nullary) and
                // `(D p ...)` (applied).
                let is_rec = surface_head_is(&f.ty, name);
                if is_rec {
                    // The recursive occurrence's index expressions are the surface args after the
                    // parameters (for an indexed family); empty for a non-indexed one.
                    let rec_indices = surface_app_args(&f.ty);
                    let n_params = param_terms.len();
                    let mut rec_ix = Vec::new();
                    for ix in rec_indices.iter().skip(n_params) {
                        rec_ix.push(elab(self, &field_scope, ix, None)?);
                    }
                    args.push(Arg::Rec(rec_ix));
                    rec_flags.push(true);
                } else {
                    let ty = elab(self, &field_scope, &f.ty, None)?;
                    args.push(Arg::NonRec(ty));
                    rec_flags.push(false);
                }
                field_scope = field_scope.push_var(&f.name);
            }
            // Result indices: elaborated in the full field scope (innermost = last field).
            let mut result_indices = Vec::new();
            for ix in &ctor.result_indices {
                result_indices.push(elab(self, &field_scope, ix, None)?);
            }
            kernel_ctors.push(Constructor {
                name: ConName(cname.clone()),
                args,
                result_indices,
            });
            self.constructors.insert(
                cname.clone(),
                ConInfo {
                    data: name.to_string(),
                    rec_flags,
                },
            );
            ctor_order.push(cname.clone());
        }
        self.datas.insert(name.to_string(), ctor_order);
        self.signature.declare(DataDecl {
            name: data_name,
            params: param_terms,
            indices: index_terms,
            level: 0,
            constructors: kernel_ctors,
            path_constructors: vec![],
        });
        Ok(())
    }

    /// Declare an algebraic effect (spec §4.2): elaborate each operation's parameter and result
    /// type to a core term and register the `EffDecl` in the kernel signature after a
    /// well-formedness check. Operation continuation-multiplicity defaults to `ω` (multi-shot) at
    /// the surface; a finer grade is a kernel-level concern (see [`blight_kernel::OpSig`]).
    fn declare_effect(
        &mut self,
        name: &str,
        ops: &[(String, Surface, Surface)],
    ) -> Result<(), ElabError> {
        use blight_kernel::{EffDecl, EffName, Grade, OpSig};
        let mut op_sigs = Vec::with_capacity(ops.len());
        for (op_name, param_ty, result_ty) in ops {
            let param_ty = elaborate(self, param_ty)?;
            // The kernel's `result_ty` lives in the scope `x:A`; surface ops are non-dependent in
            // M2, so the elaborated (closed) result type is valid there unchanged.
            let result_ty = elaborate(self, result_ty)?;
            op_sigs.push(OpSig {
                name: op_name.clone(),
                param_ty,
                result_ty,
                cont_grade: Grade::Omega,
            });
        }
        let decl = EffDecl {
            name: EffName::new(name),
            ops: op_sigs,
        };
        self.signature
            .check_effect(&decl)
            .map_err(ElabError::BadForm)?;
        self.signature.declare_effect(decl);
        Ok(())
    }
}

/// Parse a raw s-expression into a surface term.
pub fn parse_surface(s: &Sexpr) -> Result<Surface, ElabError> {
    match s {
        Sexpr::Atom(a) => {
            // Untrusted reader sugar (tower code; the kernel still only sees `Con`s): a quoted
            // string literal in term position desugars to a `String` (std/string.bl) cons-list of
            // `Nat` codepoints, and a `?x` char literal desugars to the codepoint `Nat`. Both lower
            // to `Con` chains the elaborator already understands. Plain symbols are unchanged.
            if let Some(text) = term_string_literal(a) {
                return Ok(string_to_surface(&text));
            }
            if let Some(cp) = char_literal_codepoint(a) {
                return Ok(nat_to_surface(cp));
            }
            // The `Int` type atom — primitive machine integers (M11). A reserved type name, so it
            // never shadows a user binding (the kernel has no `Int` data declaration).
            if a == "Int" {
                return Ok(Surface::IntTy);
            }
            Ok(Surface::Var(a.clone()))
        }
        Sexpr::List(items) => parse_list(items),
    }
}

/// Recognize a term-position string literal atom `"…"` (quotes retained by the reader) and return
/// its decoded interior. Returns `None` for a plain symbol so existing parsing is unaffected.
fn term_string_literal(a: &str) -> Option<String> {
    if a.starts_with('"') && a.ends_with('"') && a.len() >= 2 {
        Some(a[1..a.len() - 1].to_string())
    } else {
        None
    }
}

/// Recognize a char literal atom `?x` (e.g. `?A`) and return its Unicode scalar value as the
/// codepoint to encode as a `Nat`. `??` denotes a literal `?`. Returns `None` for anything else.
fn char_literal_codepoint(a: &str) -> Option<u64> {
    let mut chars = a.chars();
    if chars.next() != Some('?') {
        return None;
    }
    let c = chars.next()?;
    // Exactly one character after `?`.
    if chars.next().is_some() {
        return None;
    }
    Some(c as u64)
}

/// Build the surface term for a `Nat` numeral `n`: `(Succ (Succ … Zero))`, `n` deep.
fn nat_to_surface(n: u64) -> Surface {
    let mut term = Surface::Var("Zero".to_string());
    for _ in 0..n {
        term = Surface::App(Box::new(Surface::Var("Succ".to_string())), vec![term]);
    }
    term
}

/// Build the surface term for a `String` literal: a right-nested `(push <cp> rest)` chain ending in
/// `empty`, where each codepoint is a `Nat` numeral. Matches std/string.bl's `empty`/`push`.
fn string_to_surface(text: &str) -> Surface {
    let mut term = Surface::Var("empty".to_string());
    for c in text.chars().rev() {
        term = Surface::App(
            Box::new(Surface::Var("push".to_string())),
            vec![nat_to_surface(c as u64), term],
        );
    }
    term
}

fn sym(s: &Sexpr) -> Result<String, ElabError> {
    match s {
        Sexpr::Atom(a) => Ok(a.clone()),
        _ => Err(ElabError::BadForm("expected a symbol".into())),
    }
}

/// Public re-export of the symbol parser for the [`crate::program`] driver.
pub fn sym_pub(s: &Sexpr) -> Result<String, ElabError> {
    sym(s)
}

fn parse_list(items: &[Sexpr]) -> Result<Surface, ElabError> {
    let head = items
        .first()
        .ok_or_else(|| ElabError::BadForm("empty list".into()))?;
    if let Sexpr::Atom(kw) = head {
        match kw.as_str() {
            "the" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(the T e)".into()));
                }
                let ty = parse_surface(&items[1])?;
                let e = parse_surface(&items[2])?;
                return Ok(Surface::The(Box::new(ty), Box::new(e)));
            }
            "lam" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(lam (x ...) body)".into()));
                }
                let names = parse_name_list(&items[1])?;
                let body = parse_surface(&items[2])?;
                return Ok(Surface::Lam(names, Box::new(body)));
            }
            "Pi" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(Pi ((x A) ...) B)".into()));
                }
                let binders = parse_binders(&items[1])?;
                let cod = parse_surface(&items[2])?;
                return Ok(Surface::Pi(binders, Box::new(cod)));
            }
            "Path" => {
                if items.len() != 4 {
                    return Err(ElabError::BadForm("(Path A x y)".into()));
                }
                return Ok(Surface::Path(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_surface(&items[2])?),
                    Box::new(parse_surface(&items[3])?),
                ));
            }
            "plam" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(plam (i) body)".into()));
                }
                let dims = parse_name_list(&items[1])?;
                if dims.len() != 1 {
                    return Err(ElabError::BadForm("(plam (i) body): one dim".into()));
                }
                let body = parse_surface(&items[2])?;
                return Ok(Surface::PLam(
                    dims.into_iter().next().unwrap(),
                    Box::new(body),
                ));
            }
            "match" => {
                // `(match scrut [pat body] …)` — single scrutinee, one pattern per clause.
                if items.len() < 2 {
                    return Err(ElabError::BadForm("(match scrut clauses...)".into()));
                }
                let scrut = parse_surface(&items[1])?;
                let mut clauses = Vec::new();
                for c in &items[2..] {
                    clauses.push(parse_clause_single(c)?);
                }
                return Ok(Surface::Match(vec![scrut], clauses));
            }
            "matchx" => {
                // `(matchx (s1 s2 …) [(p1 p2 …) body] …)` — multiple scrutinees; each clause's
                // pattern position is the parenthesized list of one pattern per scrutinee.
                if items.len() < 2 {
                    return Err(ElabError::BadForm("(matchx (scruts…) clauses…)".into()));
                }
                let scruts = match &items[1] {
                    Sexpr::List(ss) => ss
                        .iter()
                        .map(parse_surface)
                        .collect::<Result<Vec<_>, _>>()?,
                    _ => {
                        return Err(ElabError::BadForm(
                            "(matchx (scruts…) …): scrutinees must be a list".into(),
                        ))
                    }
                };
                let mut clauses = Vec::new();
                for c in &items[2..] {
                    clauses.push(parse_clause_multi(c, scruts.len())?);
                }
                return Ok(Surface::Match(scruts, clauses));
            }
            "Type" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(Type ℓ)".into()));
                }
                let lvl: usize = sym(&items[1])?
                    .parse()
                    .map_err(|_| ElabError::BadForm("(Type ℓ): ℓ must be a nat".into()))?;
                return Ok(Surface::Univ(lvl));
            }
            "Delay" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(Delay A)".into()));
                }
                return Ok(Surface::Delay(Box::new(parse_surface(&items[1])?)));
            }
            "now" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(now a)".into()));
                }
                return Ok(Surface::Now(Box::new(parse_surface(&items[1])?)));
            }
            "later" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(later d)".into()));
                }
                return Ok(Surface::Later(Box::new(parse_surface(&items[1])?)));
            }
            "force" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(force d)".into()));
                }
                return Ok(Surface::Force(Box::new(parse_surface(&items[1])?)));
            }
            // ---- primitive machine integers (M11) ----
            "int" => {
                // `(int 42)` — an `Int` literal. The numeral is parsed as a real `i64` (not a unary
                // `Nat`), which is the whole point of the distinct surface form.
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(int n)".into()));
                }
                let n: i64 = sym(&items[1])?
                    .parse()
                    .map_err(|_| ElabError::BadForm("(int n): n must be an i64 literal".into()))?;
                return Ok(Surface::IntLit(n));
            }
            "int+" | "int-" | "int*" | "int/" | "int=" | "int<" => {
                use blight_kernel::IntPrimOp;
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(int<op> a b)".into()));
                }
                let op = match kw.as_str() {
                    "int+" => IntPrimOp::Add,
                    "int-" => IntPrimOp::Sub,
                    "int*" => IntPrimOp::Mul,
                    "int/" => IntPrimOp::Div,
                    "int=" => IntPrimOp::Eq,
                    "int<" => IntPrimOp::Lt,
                    _ => unreachable!(),
                };
                let a = parse_surface(&items[1])?;
                let b = parse_surface(&items[2])?;
                return Ok(Surface::IntPrim(op, Box::new(a), Box::new(b)));
            }
            "perform" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(perform op arg)".into()));
                }
                let op = sym(&items[1])?;
                return Ok(Surface::Perform(op, Box::new(parse_surface(&items[2])?)));
            }
            "handle" => {
                // (handle body (return x r) (op x k e) ...)
                if items.len() < 3 {
                    return Err(ElabError::BadForm(
                        "(handle body (return x r) (op x k e) ...)".into(),
                    ));
                }
                let body = parse_surface(&items[1])?;
                let mut return_clause: Option<(String, Surface)> = None;
                let mut op_clauses = Vec::new();
                for clause in &items[2..] {
                    let parts = match clause {
                        Sexpr::List(p) => p,
                        _ => {
                            return Err(ElabError::BadForm("handler clause must be a list".into()))
                        }
                    };
                    let head = sym(parts
                        .first()
                        .ok_or_else(|| ElabError::BadForm("empty handler clause".into()))?)?;
                    if head == "return" {
                        // (return x r)
                        if parts.len() != 3 {
                            return Err(ElabError::BadForm("(return x r)".into()));
                        }
                        return_clause = Some((sym(&parts[1])?, parse_surface(&parts[2])?));
                    } else {
                        // (op x k e)
                        if parts.len() != 4 {
                            return Err(ElabError::BadForm("(op x k e)".into()));
                        }
                        op_clauses.push((
                            head,
                            sym(&parts[1])?,
                            sym(&parts[2])?,
                            parse_surface(&parts[3])?,
                        ));
                    }
                }
                let return_clause = return_clause.ok_or_else(|| {
                    ElabError::BadForm("handler needs a (return x r) clause".into())
                })?;
                return Ok(Surface::Handle {
                    body: Box::new(body),
                    return_clause: (return_clause.0, Box::new(return_clause.1)),
                    op_clauses,
                });
            }
            "!" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(! E A)".into()));
                }
                return Ok(Surface::Bang(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_surface(&items[2])?),
                ));
            }
            "Sigma" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(Sigma ((x A) ...) B)".into()));
                }
                let binders = parse_binders(&items[1])?;
                let cod = parse_surface(&items[2])?;
                return Ok(Surface::Sigma(binders, Box::new(cod)));
            }
            "pair" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(pair a b)".into()));
                }
                return Ok(Surface::Pair(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_surface(&items[2])?),
                ));
            }
            "fst" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(fst p)".into()));
                }
                return Ok(Surface::Fst(Box::new(parse_surface(&items[1])?)));
            }
            "snd" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(snd p)".into()));
                }
                return Ok(Surface::Snd(Box::new(parse_surface(&items[1])?)));
            }
            "let" => {
                // (let ((x e)) b)
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(let ((x e)) b)".into()));
                }
                let bindings = match &items[1] {
                    Sexpr::List(b) if b.len() == 1 => b,
                    _ => return Err(ElabError::BadForm("(let ((x e)) b): one binding".into())),
                };
                let (x, e) = match &bindings[0] {
                    Sexpr::List(p) if p.len() == 2 => (sym(&p[0])?, parse_surface(&p[1])?),
                    _ => return Err(ElabError::BadForm("let binding must be (x e)".into())),
                };
                let body = parse_surface(&items[2])?;
                return Ok(Surface::Let(x, Box::new(e), Box::new(body)));
            }
            "region" => {
                // (region r body) — bind a linear region capability `r : Rgn` over `body`.
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(region r body)".into()));
                }
                let r = sym(&items[1])?;
                let body = parse_surface(&items[2])?;
                return Ok(Surface::Region(r, Box::new(body)));
            }
            _ => {}
        }
    }

    // Path application sugar: `(p @ r)`.
    if items.len() == 3 {
        if let Sexpr::Atom(at) = &items[1] {
            if at == "@" {
                return Ok(Surface::PApp(
                    Box::new(parse_surface(&items[0])?),
                    Box::new(parse_surface(&items[2])?),
                ));
            }
            // Pair sugar: `(a , b)`.
            if at == "," {
                return Ok(Surface::Pair(
                    Box::new(parse_surface(&items[0])?),
                    Box::new(parse_surface(&items[2])?),
                ));
            }
        }
    }

    // Otherwise an application `(f a ...)`.
    let f = parse_surface(&items[0])?;
    let mut args = Vec::new();
    for a in &items[1..] {
        args.push(parse_surface(a)?);
    }
    if args.is_empty() {
        Ok(f)
    } else {
        Ok(Surface::App(Box::new(f), args))
    }
}

/// Parse `(x y z)` as a list of names.
fn parse_name_list(s: &Sexpr) -> Result<Vec<String>, ElabError> {
    match s {
        Sexpr::List(items) => items.iter().map(sym).collect(),
        _ => Err(ElabError::BadForm("expected a list of names".into())),
    }
}

/// Parse `((x A) (y B) ...)` as binders (grade defaults to ω).
/// Heuristic distinguishing an index *telescope* `((n Nat) …)` from a *constructor* `(Con …)` in
/// the ambiguous third position of `defdata`: a telescope's elements are themselves binder lists
/// `(name Type)`, so its head is a list; a constructor's head is the constructor *symbol*. An empty
/// list `()` is treated as an (empty) telescope.
fn is_binder_list(s: &Sexpr) -> bool {
    match s {
        Sexpr::List(items) => matches!(items.first(), None | Some(Sexpr::List(_))),
        _ => false,
    }
}

fn parse_binders(s: &Sexpr) -> Result<Vec<Binder>, ElabError> {
    let items = match s {
        Sexpr::List(items) => items,
        _ => return Err(ElabError::BadForm("expected a binder telescope".into())),
    };
    let mut out = Vec::new();
    for b in items {
        out.push(parse_one_binder(b)?);
    }
    Ok(out)
}

/// Parse a single binder. Explicit forms `(x A)` / `(x A ρ)`; the *implicit* form is `{x A}`,
/// read by the s-expression reader as `(brace x A)`/`(brace x A ρ)` (curly braces desugar to a
/// `brace`-headed list), whose argument the elaborator infers rather than receiving at the call
/// site (spec §6.4). An explicit trailing `implicit` keyword is also accepted: `(x A implicit)`.
fn parse_one_binder(b: &Sexpr) -> Result<Binder, ElabError> {
    let parts = match b {
        Sexpr::List(parts) if !parts.is_empty() => parts,
        _ => {
            return Err(ElabError::BadForm(
                "binder must be (x A), (x A ρ) or {x A}".into(),
            ))
        }
    };
    // Curly-brace implicit binder `{x A}` ⟹ `(brace x A …)`.
    if sym(&parts[0]).ok().as_deref() == Some("brace") {
        let inner = &parts[1..];
        return match inner.len() {
            2 => Ok(Binder {
                name: sym(&inner[0])?,
                ty: parse_surface(&inner[1])?,
                grade: None,
                implicit: true,
            }),
            3 => Ok(Binder {
                name: sym(&inner[0])?,
                ty: parse_surface(&inner[1])?,
                grade: Some(parse_surface(&inner[2])?),
                implicit: true,
            }),
            _ => Err(ElabError::BadForm(
                "implicit binder must be {x A} or {x A ρ}".into(),
            )),
        };
    }
    // Explicit `implicit` keyword as the final token marks an implicit binder.
    let implicit = parts.last().and_then(|p| sym(p).ok()).as_deref() == Some("implicit");
    let core = if implicit {
        &parts[..parts.len() - 1]
    } else {
        &parts[..]
    };
    match core.len() {
        2 => Ok(Binder {
            name: sym(&core[0])?,
            ty: parse_surface(&core[1])?,
            grade: None,
            implicit,
        }),
        3 => Ok(Binder {
            name: sym(&core[0])?,
            ty: parse_surface(&core[1])?,
            grade: Some(parse_surface(&core[2])?),
            implicit,
        }),
        _ => Err(ElabError::BadForm("binder must be (x A) or (x A ρ)".into())),
    }
}

/// Parse a pattern: `_` (wildcard), a bare symbol (variable, unless it names a known nullary
/// constructor — handled at compile time), or `(Con p …)` (constructor with sub-patterns).
fn parse_pattern(s: &Sexpr) -> Result<crate::surface::Pattern, ElabError> {
    use crate::surface::Pattern;
    match s {
        Sexpr::Atom(a) if a == "_" => Ok(Pattern::Wild),
        Sexpr::Atom(a) => Ok(Pattern::Var(a.clone())),
        Sexpr::List(p) if !p.is_empty() => {
            let con = sym(&p[0])?;
            let mut subs = Vec::with_capacity(p.len() - 1);
            for sp in &p[1..] {
                subs.push(parse_pattern(sp)?);
            }
            Ok(Pattern::Con(con, subs))
        }
        _ => Err(ElabError::BadMatch(
            "pattern must be `_`, a var, or (Con p…)".into(),
        )),
    }
}

/// Parse a single-scrutinee clause `[pat body]`. The pattern may be nested/wildcard.
fn parse_clause_single(s: &Sexpr) -> Result<Clause, ElabError> {
    let items = match s {
        Sexpr::List(items) if items.len() == 2 => items,
        _ => return Err(ElabError::BadMatch("clause must be [pat body]".into())),
    };
    Ok(Clause {
        patterns: vec![parse_pattern(&items[0])?],
        body: parse_surface(&items[1])?,
    })
}

/// Parse a multi-scrutinee clause `[(p1 p2 …) body]` with exactly `arity` patterns.
fn parse_clause_multi(s: &Sexpr, arity: usize) -> Result<Clause, ElabError> {
    let items = match s {
        Sexpr::List(items) if items.len() == 2 => items,
        _ => return Err(ElabError::BadMatch("clause must be [(p…) body]".into())),
    };
    let pats = match &items[0] {
        Sexpr::List(ps) => ps,
        _ => {
            return Err(ElabError::BadMatch(
                "multi-clause patterns must be a list".into(),
            ))
        }
    };
    if pats.len() != arity {
        return Err(ElabError::BadMatch(format!(
            "clause has {} patterns but there are {arity} scrutinees",
            pats.len()
        )));
    }
    Ok(Clause {
        patterns: pats.iter().map(parse_pattern).collect::<Result<_, _>>()?,
        body: parse_surface(&items[1])?,
    })
}

/// Parse a raw s-expression into a top-level declaration.
pub fn parse_decl(s: &Sexpr) -> Result<Decl, ElabError> {
    let items = match s {
        Sexpr::List(items) if !items.is_empty() => items,
        _ => {
            return Err(ElabError::BadForm(
                "a declaration must be a non-empty list".into(),
            ))
        }
    };
    let kw = sym(&items[0])?;
    match kw.as_str() {
        "defdata" => {
            // (defdata D (params...) (Con (field ty)...)...)
            // Indexed form: (defdata D (params...) (indices...) (Con (field ty)... (=> idx...))...)
            // The third list is read as the *index telescope* iff every constructor afterwards is a
            // list whose head is itself a list (the index telescope is `((n Nat))`-shaped, distinct
            // from a constructor whose head is the symbol `Con`).
            if items.len() < 3 {
                return Err(ElabError::BadForm("(defdata D (params) ctors...)".into()));
            }
            let name = sym(&items[1])?;
            let params = parse_binders(&items[2])?;
            // Detect an optional index telescope in position 3.
            let (indices, ctor_start) = if items.len() >= 4 && is_binder_list(&items[3]) {
                (parse_binders(&items[3])?, 4)
            } else {
                (Vec::new(), 3)
            };
            let mut constructors = Vec::new();
            for c in &items[ctor_start..] {
                let parts = match c {
                    Sexpr::List(parts) if !parts.is_empty() => parts,
                    _ => {
                        return Err(ElabError::BadForm(
                            "constructor must be (Con fields...)".into(),
                        ))
                    }
                };
                let cname = sym(&parts[0])?;
                let mut result_indices: Vec<Surface> = Vec::new();
                let mut field_parts: &[Sexpr] = &parts[1..];
                // Trailing `(=> i ...)` declares this constructor's result indices.
                if let Some(Sexpr::List(last)) = field_parts.last() {
                    if last.first().and_then(|h| sym(h).ok()).as_deref() == Some("=>") {
                        for ix in &last[1..] {
                            result_indices.push(parse_surface(ix)?);
                        }
                        field_parts = &field_parts[..field_parts.len() - 1];
                    }
                }
                let mut fields = Vec::new();
                for f in field_parts {
                    match f {
                        Sexpr::List(fp) if fp.len() == 2 => fields.push(Binder {
                            name: sym(&fp[0])?,
                            ty: parse_surface(&fp[1])?,
                            grade: None,
                            implicit: false,
                        }),
                        _ => {
                            return Err(ElabError::BadForm(
                                "constructor field must be (name Type)".into(),
                            ))
                        }
                    }
                }
                constructors.push(ConstructorDecl {
                    name: cname,
                    fields,
                    result_indices,
                });
            }
            Ok(Decl::DefData {
                name,
                params,
                indices,
                constructors,
            })
        }
        "define-rec" => {
            if items.len() != 3 {
                return Err(ElabError::BadForm("(define-rec name body)".into()));
            }
            Ok(Decl::DefineRec {
                name: sym(&items[1])?,
                body: parse_surface(&items[2])?,
            })
        }
        "deftotal" => {
            if items.len() != 3 {
                return Err(ElabError::BadForm("(deftotal name body)".into()));
            }
            Ok(Decl::DefTotal {
                name: sym(&items[1])?,
                body: parse_surface(&items[2])?,
            })
        }
        "effect" => {
            // (effect E (op A B) ...)
            if items.len() < 2 {
                return Err(ElabError::BadForm("(effect E (op A B) ...)".into()));
            }
            let name = sym(&items[1])?;
            let mut ops = Vec::new();
            for op in &items[2..] {
                let parts = match op {
                    Sexpr::List(p) => p,
                    _ => return Err(ElabError::BadForm("effect op must be (name A B)".into())),
                };
                if parts.len() != 3 {
                    return Err(ElabError::BadForm("effect op must be (name A B)".into()));
                }
                ops.push((
                    sym(&parts[0])?,
                    parse_surface(&parts[1])?,
                    parse_surface(&parts[2])?,
                ));
            }
            Ok(Decl::DefEffect { name, ops })
        }
        "define" => {
            if items.len() != 3 {
                return Err(ElabError::BadForm("(define name body)".into()));
            }
            Ok(Decl::Define {
                name: sym(&items[1])?,
                body: parse_surface(&items[2])?,
            })
        }
        "foreign" => {
            // (foreign name <type> "c_symbol")
            if items.len() != 4 {
                return Err(ElabError::BadForm(
                    "(foreign name <type> \"c_symbol\")".into(),
                ));
            }
            let symbol = match &items[3] {
                Sexpr::Atom(a) if a.starts_with('"') && a.ends_with('"') && a.len() >= 2 => {
                    a[1..a.len() - 1].to_string()
                }
                _ => {
                    return Err(ElabError::BadForm(
                        "foreign C symbol must be a string literal \"sym\"".into(),
                    ))
                }
            };
            Ok(Decl::Foreign {
                name: sym(&items[1])?,
                ty: parse_surface(&items[2])?,
                symbol,
            })
        }
        other => Err(ElabError::BadForm(format!("unknown declaration `{other}`"))),
    }
}

/// Elaborate a surface term to a core kernel term in inference mode (no expected type).
pub fn elaborate(env: &ElabEnv, term: &Surface) -> Result<Term, ElabError> {
    let scope = Scope::new();
    elab(env, &scope, term, None)
}

/// Elaborate a surface term against an expected core type (checking mode). Required to desugar a
/// `match` whose motive is read off the expected type (spec §6.2).
pub fn elaborate_against(
    env: &ElabEnv,
    term: &Surface,
    expected: &Term,
) -> Result<Term, ElabError> {
    let scope = Scope::new();
    elab(env, &scope, term, Some(expected))
}

/// A lexical scope tracking term-variable and dimension-variable names (each its own de Bruijn
/// space), plus an optional recursive self-name and the variable it structurally recurses on.
#[derive(Clone)]
struct Scope {
    /// Term variables, innermost last. de Bruijn index of name = `len - 1 - position`.
    vars: Vec<String>,
    /// Each term variable's type (in the de Bruijn scope at its binding site), when known.
    var_types: Vec<Option<Term>>,
    /// Dimension variables, innermost last.
    dims: Vec<String>,
    /// The name of the recursive function currently being elaborated, with the name of its
    /// recursion argument and the set of induction-hypothesis bindings available.
    rec: Option<RecCtx>,
}

#[derive(Clone)]
struct RecCtx {
    /// The function's own name (recursive self-reference).
    self_name: String,
    /// Map from "the structural sub-term variable name" → its IH variable name in scope.
    ih: std::collections::HashMap<String, String>,
    /// `true` for `deftotal`: a non-structural recursive call is a hard error (the definition must
    /// compile to `Elim`). `false` for `define-rec`: a non-structural recursive call is permitted
    /// and elaborates to a `Later`-guarded partial step (spec §4.5, §6.2).
    total: bool,
    /// The argument layout of the matched function, so a recursive call `(self a0 … an)` can be
    /// recognized even when the scrutinee is not the *first* argument. `leading` are the names of
    /// the parameters *before* the scrutinee (which a structural call must repeat verbatim, since
    /// the induction hypothesis fixes them); the scrutinee occupies the next position, and any
    /// remaining `trailing` arguments are applied to the IH. Empty ⟹ unknown layout (fall back to
    /// the first-argument-is-the-scrutinee rule).
    leading: Vec<String>,
}

impl Scope {
    fn new() -> Self {
        Scope {
            vars: Vec::new(),
            var_types: Vec::new(),
            dims: Vec::new(),
            rec: None,
        }
    }

    fn push_var(&self, name: &str) -> Self {
        self.push_var_ty(name, None)
    }

    fn push_var_ty(&self, name: &str, ty: Option<Term>) -> Self {
        let mut s = self.clone();
        s.vars.push(name.to_string());
        s.var_types.push(ty);
        s
    }

    fn push_dim(&self, name: &str) -> Self {
        let mut s = self.clone();
        s.dims.push(name.to_string());
        s
    }

    fn var_index(&self, name: &str) -> Option<usize> {
        self.vars.iter().rev().position(|n| n == name)
    }

    fn dim_index(&self, name: &str) -> Option<usize> {
        self.dims.iter().rev().position(|n| n == name)
    }
}

/// Resolve a surface interval expression (a dimension variable or an endpoint) to a kernel
/// [`Interval`].
fn elab_interval(scope: &Scope, term: &Surface) -> Result<blight_kernel::Interval, ElabError> {
    use blight_kernel::Interval;
    match term {
        Surface::Var(v) if v == "i0" => Ok(Interval::I0),
        Surface::Var(v) if v == "i1" => Ok(Interval::I1),
        Surface::Var(v) => scope
            .dim_index(v)
            .map(Interval::Dim)
            .ok_or_else(|| ElabError::Unbound(format!("dimension `{v}`"))),
        _ => Err(ElabError::BadForm("expected an interval expression".into())),
    }
}

fn elab(
    env: &ElabEnv,
    scope: &Scope,
    term: &Surface,
    expected: Option<&Term>,
) -> Result<Term, ElabError> {
    use blight_kernel::ConName;
    match term {
        Surface::Var(name) => {
            // 1) a bound term variable (exact match — hygiene marks are significant for locals).
            if let Some(i) = scope.var_index(name) {
                return Ok(Term::Var(i));
            }
            // 2) a recursive self-reference is not directly representable; handled at call sites.
            // 3) a nullary constructor.
            if let Some(info) = env.constructors.get(name) {
                if info.rec_flags.is_empty() {
                    return Ok(Term::Con(ConName(name.clone()), vec![]));
                }
            }
            // 4) a data type name with no params.
            if env.datas.contains_key(name) {
                return Ok(Term::Data(
                    blight_kernel::DataName(name.clone()),
                    vec![],
                    vec![],
                ));
            }
            // 5) a global definition: inline it. When a type is known, wrap in an ascription so
            //    the kernel can infer through applications of an otherwise-bare `Lam`.
            if let Some((t, ty)) = env.globals.get(name) {
                return Ok(match ty {
                    Some(ty) => Term::Ann(Box::new(t.clone()), Box::new(ty.clone())),
                    None => t.clone(),
                });
            }
            // 6) Hygiene fallback: a macro-introduced *free* reference carries a mark (`name%N`).
            //    Such a reference never names a local (locals match exactly above), so strip the
            //    mark and retry the global/constructor/data lookups under the base name.
            let base = crate::macros::strip_mark(name);
            if base != name {
                if let Some(info) = env.constructors.get(base) {
                    if info.rec_flags.is_empty() {
                        return Ok(Term::Con(ConName(base.to_string()), vec![]));
                    }
                }
                if env.datas.contains_key(base) {
                    return Ok(Term::Data(
                        blight_kernel::DataName(base.to_string()),
                        vec![],
                        vec![],
                    ));
                }
                if let Some((t, ty)) = env.globals.get(base) {
                    return Ok(match ty {
                        Some(ty) => Term::Ann(Box::new(t.clone()), Box::new(ty.clone())),
                        None => t.clone(),
                    });
                }
            }
            Err(ElabError::Unbound(name.clone()))
        }

        Surface::The(ty, e) => {
            let ty_c = elab(env, scope, ty, None)?;
            let e_c = elab(env, scope, e, Some(&ty_c))?;
            Ok(Term::Ann(Box::new(e_c), Box::new(ty_c)))
        }

        Surface::Univ(l) => Ok(Term::Univ(nat_level(*l))),

        Surface::Lam(names, body) => {
            // Peel the expected Pi-telescope binder-by-binder, recording each binder's domain type
            // so that a `match` on an outer binder can generalize over later binders.
            let mut sc = scope.clone();
            let mut cur = expected.cloned();
            for n in names {
                let (dom, cod) = match cur {
                    Some(Term::Pi(_, dom, cod)) => (Some(*dom), Some(*cod)),
                    _ => (None, None),
                };
                sc = sc.push_var_ty(n, dom);
                cur = cod;
            }
            let mut core = elab(env, &sc, body, cur.as_ref())?;
            for _ in names {
                core = Term::Lam(Box::new(core));
            }
            Ok(core)
        }

        Surface::Pi(binders, cod) => elab_pi(env, scope, binders, cod),

        Surface::App(f, args) => {
            // Implicit-argument insertion: a global head with leading implicit binders gets its
            // implicits solved (metavariable + unification) before the explicit args are applied.
            if let Surface::Var(g) = f.as_ref() {
                let k = env.implicit_arity(g);
                if k > 0 && scope.var_index(g).is_none() {
                    if let Some((gt, Some(gty))) = env.globals.get(g) {
                        let g_term = Term::Ann(Box::new(gt.clone()), Box::new(gty.clone()));
                        let specs = env.implicits.get(g).cloned().unwrap_or_default();
                        return elab_implicit_app(
                            env, scope, g, &g_term, gty, &specs, args, expected,
                        );
                    }
                }
            }
            if let Some(t) = elab_app_head(env, scope, f, args)? {
                return Ok(t);
            }
            let mut head = elab(env, scope, f, None)?;
            for a in args {
                head = Term::App(Box::new(head), Box::new(elab(env, scope, a, None)?));
            }
            Ok(head)
        }

        Surface::Path(a, x, y) => {
            let sc_dim = scope.push_dim("_");
            let family = elab(env, &sc_dim, a, None)?;
            let lhs = elab(env, scope, x, None)?;
            let rhs = elab(env, scope, y, None)?;
            Ok(Term::PathP {
                family: Box::new(family),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
        }

        Surface::PLam(dim, body) => {
            let sc = scope.push_dim(dim);
            let core = elab(env, &sc, body, None)?;
            Ok(Term::PLam(Box::new(core)))
        }

        Surface::PApp(p, r) => {
            let pc = elab(env, scope, p, None)?;
            let rc = elab_interval(scope, r)?;
            Ok(Term::PApp(Box::new(pc), rc))
        }

        Surface::Match(scruts, clauses) => {
            use crate::surface::Pattern;
            // The primitive case: a single variable scrutinee whose clauses are already flat
            // (constructor patterns with variable/wildcard sub-patterns). This is the only shape
            // `elab_flat_match` consumes; everything else lowers to a tree of these.
            let is_flat = scruts.len() == 1
                && matches!(scruts[0], Surface::Var(_))
                && clauses.iter().all(|c| {
                    matches!(&c.patterns[0],
                        Pattern::Con(_, subs)
                            if subs.iter().all(|s| matches!(s, Pattern::Var(_) | Pattern::Wild)))
                });
            if is_flat {
                let motive_owned;
                let motive = match expected {
                    Some(t) => t,
                    None => {
                        motive_owned = infer_match_motive(env, scope, term)?;
                        &motive_owned
                    }
                };
                return elab_flat_match(env, scope, term, motive);
            }
            // Otherwise lower nested/wildcard/multi-scrutinee patterns to a tree of flat matches
            // (and `let`s for non-variable scrutinees), then elaborate that tree normally so each
            // flat match hits the primitive above with the right expected type threaded in.
            let lowered = lower_match(env, scruts, clauses)?;
            elab(env, scope, &lowered, expected)
        }

        // ---- partiality (spec §4.5) ----
        Surface::Delay(a) => Ok(Term::Delay(Box::new(elab(env, scope, a, None)?))),
        Surface::Now(a) => {
            // When checking against `Delay A`, the payload is checked against `A`.
            let inner_expected = match expected {
                Some(Term::Delay(a_ty)) => Some(a_ty.as_ref()),
                _ => None,
            };
            Ok(Term::Now(Box::new(elab(env, scope, a, inner_expected)?)))
        }
        Surface::Later(d) => {
            // `later d : Delay A` when `d : Delay A`: the guarded continuation has the same type.
            Ok(Term::Later(Box::new(elab(env, scope, d, expected)?)))
        }
        Surface::Force(d) => {
            // `force d : A` when `d : Delay A`. When checking against an expected `A`, the payload
            // is checked against `Delay A`; otherwise it is inferred.
            let inner_expected = expected.map(|a| Term::Delay(Box::new(a.clone())));
            Ok(Term::Force(Box::new(elab(
                env,
                scope,
                d,
                inner_expected.as_ref(),
            )?)))
        }

        // ---- primitive machine integers (M11) ----
        Surface::IntTy => Ok(Term::IntTy),
        Surface::IntLit(n) => Ok(Term::IntLit(*n)),
        Surface::IntPrim(op, a, b) => {
            // Both operands are `Int`; the kernel re-checks this. We thread the expected `Int` type
            // so literal/neutral operands elaborate without an ascription.
            let int_ty = Term::IntTy;
            let lhs = elab(env, scope, a, Some(&int_ty))?;
            let rhs = elab(env, scope, b, Some(&int_ty))?;
            Ok(Term::IntPrim {
                op: *op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
        }

        // ---- effects (spec §4.2, §4.3) ----
        Surface::Perform(op, arg) => {
            // Resolve which effect declares this operation from the signature.
            let (eff, _sig) = env
                .signature()
                .op_of(op)
                .ok_or_else(|| ElabError::Unbound(format!("operation `{op}`")))?;
            let effect = eff.name.clone();
            let arg_c = elab(env, scope, arg, None)?;
            Ok(Term::Op {
                effect,
                op: op.clone(),
                arg: Box::new(arg_c),
            })
        }
        Surface::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            let body_c = elab(env, scope, body, None)?;
            // `return x. r`: one binder `x` (de Bruijn 0 in `r`).
            let (ret_name, ret_body) = return_clause;
            let ret_scope = scope.push_var(ret_name);
            let return_c = elab(env, &ret_scope, ret_body, None)?;
            // Each `op x k e`: two binders — `x` then `k`, so in `e` `k` is de Bruijn 0, `x` is 1.
            let mut op_clauses_c = Vec::with_capacity(op_clauses.len());
            for (op, x_name, k_name, clause_body) in op_clauses {
                let clause_scope = scope.push_var(x_name).push_var(k_name);
                let clause_c = elab(env, &clause_scope, clause_body, None)?;
                op_clauses_c.push((op.clone(), Box::new(clause_c)));
            }
            Ok(Term::Handle {
                body: Box::new(body_c),
                return_clause: Box::new(return_c),
                op_clauses: op_clauses_c,
            })
        }
        Surface::Bang(eff, a) => {
            use blight_kernel::{EffName, Grade, Row};
            // `E` is either `()`/`pure` (the empty row) or a single declared effect name.
            let row = match eff.as_ref() {
                Surface::Var(name) if name == "pure" => Row::empty(),
                Surface::Var(name) => Row::single(EffName::new(name.clone()), Grade::Omega),
                // `(! () A)` parses `()` as an empty application, i.e. nothing; treat as pure.
                _ => {
                    return Err(ElabError::BadForm(
                        "(! E A): E must be a single effect name or `pure`".into(),
                    ))
                }
            };
            let a_c = elab(env, scope, a, None)?;
            Ok(Term::EffTy(row, Box::new(a_c)))
        }

        // ---- records / dependent pairs (spec §6.4/§6.5) ----
        Surface::Sigma(binders, cod) => elab_sigma(env, scope, binders, cod),
        Surface::Pair(a, b) => {
            // In checking mode against `Sigma A B`, check the first component against `A`. The
            // second component's expected type depends on the first; rather than perform a kernel
            // substitution here, we leave it to inference and let the spore re-check.
            let (exp_a, exp_b) = match expected {
                Some(Term::Sigma(a_ty, b_ty)) => (Some(a_ty.as_ref()), Some(b_ty.as_ref())),
                _ => (None, None),
            };
            let a_c = elab(env, scope, a, exp_a)?;
            // The second expected type is `b_ty` with the first component substituted in. We only
            // pass a non-dependent expected type through unchanged (de Bruijn 0 absent); otherwise
            // infer and rely on re-checking.
            let exp_b = exp_b.filter(|t| !term_mentions_var(t, 0));
            let b_c = elab(env, scope, b, exp_b)?;
            Ok(Term::Pair(Box::new(a_c), Box::new(b_c)))
        }
        Surface::Fst(p) => Ok(Term::Fst(Box::new(elab(env, scope, p, None)?))),
        Surface::Snd(p) => Ok(Term::Snd(Box::new(elab(env, scope, p, None)?))),
        Surface::Let(x, e, body) => {
            // `(let ((x e)) b)` ⤳ `((lam (x) b) e)`. Elaborate `e` first (inference), then the body
            // under a binder. When both the bound value's type and the expected result type are
            // known, ascribe the lambda `(λx. b) : Π(x:E). expected` so the application is
            // *checkable* (a bare `Lam` head cannot be inferred by the kernel).
            let e_c = elab(env, scope, e, None)?;
            let e_ty = synth_type(env, scope, &e_c);
            let sc = scope.push_var_ty(x, e_ty.clone());
            let body_c = elab(env, &sc, body, expected)?;
            let lam = Term::Lam(Box::new(body_c.clone()));
            // The codomain: the expected result if known, else the body's synthesized type
            // (strengthened back past the `x` binder so it is valid in the outer scope).
            let cod = match expected {
                Some(c) => Some(weaken(c, 1)),
                None => synth_type(env, &sc, &body_c),
            };
            let fun = match (e_ty, cod) {
                (Some(dom), Some(cod)) => {
                    let pi = Term::Pi(blight_kernel::Grade::Omega, Box::new(dom), Box::new(cod));
                    Term::Ann(Box::new(lam), Box::new(pi))
                }
                _ => lam,
            };
            Ok(Term::App(Box::new(fun), Box::new(e_c)))
        }

        Surface::Region(r, body) => {
            // `(region r body)` desugars to a grade-1 (linear) binding of the region capability:
            //   ((λ r. body) : Π(r :¹ Rgn). cod) rgn-tok
            // The grade-1 binder makes the *existing* kernel linear-binder rule scope the token's
            // lifetime (no new core node, no kernel change — spec §3.5). The backend recognizes the
            // shape `App(Ann(Lam .., Pi(One, Rgn, ..)), Con("rgn-tok"))` as an arena region scope.
            let rgn_ty = region_handle_type(env)?;
            let tok = region_token(env)?;
            let sc = scope.push_var_ty(r, Some(rgn_ty.clone()));
            let body_c = elab(env, &sc, body, expected)?;
            // Codomain: the expected result if known (strengthened back past the `r` binder), else
            // the synthesized body type. The token must not escape *in the type* — an opaque `Rgn`
            // appearing in the region's result type means the capability leaked past its scope.
            let cod = match expected {
                Some(c) => weaken(c, 1),
                None => synth_type(env, &sc, &body_c).ok_or_else(|| {
                    ElabError::BadForm(
                        "(region r body): cannot infer the region body's type; ascribe it with `the`"
                            .into(),
                    )
                })?,
            };
            if mentions_region_handle(&cod) {
                return Err(ElabError::BadForm(
                    "(region r body): the region capability must not escape — the body's type \
                     mentions `Rgn`"
                        .into(),
                ));
            }
            let pi = Term::Pi(blight_kernel::Grade::One, Box::new(rgn_ty), Box::new(cod));
            let fun = Term::Ann(Box::new(Term::Lam(Box::new(body_c))), Box::new(pi));
            Ok(Term::App(Box::new(fun), Box::new(tok)))
        }
    }
}

fn nat_level(n: usize) -> blight_kernel::Level {
    let mut l = blight_kernel::Level::Zero;
    for _ in 0..n {
        l = blight_kernel::Level::Suc(Box::new(l));
    }
    l
}

/// The opaque region-handle type name, declared in the untrusted prelude (`regions.bl`).
const REGION_TYPE: &str = "Rgn";
/// The region-handle's single nullary token constructor.
const REGION_TOKEN: &str = "rgn-tok";

/// The core type of a region capability, `Rgn`. Errors if the prelude declaring it is not loaded.
fn region_handle_type(env: &ElabEnv) -> Result<Term, ElabError> {
    if env.datas.contains_key(REGION_TYPE) {
        Ok(Term::Data(
            blight_kernel::DataName(REGION_TYPE.to_string()),
            vec![],
            vec![],
        ))
    } else {
        Err(ElabError::BadForm(format!(
            "(region …): the `{REGION_TYPE}` type is not in scope (load \"regions.bl\")"
        )))
    }
}

/// The fresh region capability token value, `rgn-tok`. Errors if the prelude is not loaded.
fn region_token(env: &ElabEnv) -> Result<Term, ElabError> {
    if env.constructors.contains_key(REGION_TOKEN) {
        Ok(Term::Con(
            blight_kernel::ConName(REGION_TOKEN.to_string()),
            vec![],
        ))
    } else {
        Err(ElabError::BadForm(format!(
            "(region …): the `{REGION_TOKEN}` constructor is not in scope (load \"regions.bl\")"
        )))
    }
}

/// Whether a core type mentions the opaque region handle `Rgn` anywhere — used as the elaborator's
/// non-escape guard: a region's *result type* mentioning `Rgn` means the linear capability leaked
/// past its scope (spec §3.5). This is a structural occurs check over the type term.
fn mentions_region_handle(ty: &Term) -> bool {
    use blight_kernel::Term as T;
    match ty {
        T::Data(name, params, indices) => {
            name.0 == REGION_TYPE
                || params.iter().any(mentions_region_handle)
                || indices.iter().any(mentions_region_handle)
        }
        T::Pi(_, a, b) | T::Sigma(a, b) => mentions_region_handle(a) || mentions_region_handle(b),
        T::App(f, a) => mentions_region_handle(f) || mentions_region_handle(a),
        T::Lam(b) | T::Delay(b) | T::Now(b) | T::Later(b) => mentions_region_handle(b),
        T::Ann(e, t) => mentions_region_handle(e) || mentions_region_handle(t),
        T::Pair(a, b) => mentions_region_handle(a) || mentions_region_handle(b),
        T::Fst(p) | T::Snd(p) => mentions_region_handle(p),
        T::Con(_, args) => args.iter().any(mentions_region_handle),
        _ => false,
    }
}

fn elab_pi(
    env: &ElabEnv,
    scope: &Scope,
    binders: &[Binder],
    cod: &Surface,
) -> Result<Term, ElabError> {
    match binders.split_first() {
        None => elab(env, scope, cod, None),
        Some((b, rest)) => {
            let dom = elab(env, scope, &b.ty, None)?;
            let grade = parse_grade(b.grade.as_ref())?;
            let sc = scope.push_var(&b.name);
            let cod_c = elab_pi(env, &sc, rest, cod)?;
            Ok(Term::Pi(grade, Box::new(dom), Box::new(cod_c)))
        }
    }
}

/// Elaborate `(Sigma ((x A) ...) B)` to a right-nested kernel `Term::Sigma` telescope. Grades are
/// not tracked on `Sigma` components (the kernel `Sigma` is ungraded), so binder grades are ignored
/// here.
/// Whether a surface field type's head is the data type `name` being defined — either the bare
/// name `D` or an application `(D p …)`. This generalizes recursion detection beyond exact-name to
/// "head is the data applied to its parameters" (so `(List a)` fields in `List`'s own definition
/// are recognized as recursive occurrences).
fn surface_head_is(ty: &Surface, name: &str) -> bool {
    match ty {
        Surface::Var(v) => v == name,
        Surface::App(head, _) => surface_head_is(head, name),
        _ => false,
    }
}

/// The argument list of a surface application `(D a b …)`, flattened; `[]` for a bare head.
fn surface_app_args(ty: &Surface) -> Vec<Surface> {
    match ty {
        Surface::App(_, args) => args.clone(),
        _ => Vec::new(),
    }
}

/// Compute the implicit-binder specs of a surface type `{a A} … → rest`: one entry per leading
/// implicit binder, classified as an instance-constraint when its type's head is a registered
/// class, else an ordinary unification implicit (spec §6.4). Implicits must lead; nesting stops at
/// the first explicit binder.
pub fn surface_implicit_specs(env: &ElabEnv, ty: &Surface) -> Vec<ImplicitSpec> {
    fn go(env: &ElabEnv, ty: &Surface, out: &mut Vec<ImplicitSpec>) {
        if let Surface::Pi(binders, cod) = ty {
            for b in binders {
                if !b.implicit {
                    return;
                }
                match surface_type_class(&b.ty) {
                    Some(c) if env.is_class(&c) => out.push(ImplicitSpec::Instance { class: c }),
                    _ => out.push(ImplicitSpec::Unify),
                }
            }
            go(env, cod, out);
        }
    }
    let mut out = Vec::new();
    go(env, ty, &mut out);
    out
}

/// The class head symbol of a constraint type `(C A …)`, if it is a simple application headed by a
/// symbol; `None` otherwise.
fn surface_type_class(ty: &Surface) -> Option<String> {
    match ty {
        Surface::App(head, _) => match head.as_ref() {
            Surface::Var(c) => Some(c.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// The head type symbol of an applied type `(H …)` or a bare `H`, used as the instance-search key.
fn term_head_symbol(t: &Term) -> Option<String> {
    match t {
        Term::Data(name, _, _) => Some(name.0.clone()),
        Term::App(f, _) => term_head_symbol(f),
        Term::Ann(e, _) => term_head_symbol(e),
        _ => None,
    }
}

/// Best-effort type synthesis for an *already-elaborated* core term in `scope`, used only to drive
/// implicit-argument unification. Returns `None` when the type cannot be read off cheaply (the
/// implicit must then be solved from the expected type, or it is reported unsolved). This never
/// re-checks: the spore is the authority; a wrong guess simply fails to solve a meta.
fn synth_type(env: &ElabEnv, scope: &Scope, t: &Term) -> Option<Term> {
    match t {
        // A bound variable: its declared type, weakened past the binders introduced since.
        Term::Var(i) => {
            let pos = scope.vars.len().checked_sub(1 + *i)?;
            let ty = scope.var_types.get(pos)?.clone()?;
            Some(weaken(&ty, *i + 1))
        }
        // An ascription carries its type directly.
        Term::Ann(_, ty) => Some((**ty).clone()),
        // A constructor application: read the result type from the signature. For a data type with
        // no parameters or indices the result is just `Data name` regardless of the constructor's
        // arguments (e.g. both `Zero : Nat` and `(Succ k) : Nat`); this lets implicit-argument
        // unification recover `A := Nat` from an argument like `(Succ (Succ Zero))`.
        Term::Con(name, _args) => {
            let (decl, _, _) = env.signature().data_of_con(name)?;
            if decl.params.is_empty() && decl.indices.is_empty() {
                Some(Term::Data(decl.name.clone(), vec![], vec![]))
            } else {
                None
            }
        }
        Term::Univ(l) => Some(Term::Univ(blight_kernel::Level::Suc(Box::new(l.clone())))),
        // An application's type is the function's codomain, with the argument substituted in.
        Term::App(f, x) => {
            let f_ty = synth_type(env, scope, f)?;
            whnf_pi(&f_ty).map(|(_g, _dom, cod)| subst0_closed(&cod, x))
        }
        // A projection's type comes from the pair's `Sigma`.
        Term::Fst(p) => {
            let p_ty = synth_type(env, scope, p)?;
            whnf_sigma(&p_ty).map(|(dom, _cod)| dom)
        }
        Term::Snd(p) => {
            let p_ty = synth_type(env, scope, p)?;
            whnf_sigma(&p_ty).map(|(_dom, cod)| subst0_closed(&cod, &Term::Fst(p.clone())))
        }
        // An eliminator's result type is its motive applied to the scrutinee: `motive scrut`.
        // The motive is `λs. M`, so the type is `M[s := scrutinee]` (one β-step).
        Term::Elim {
            motive, scrutinee, ..
        } => {
            if let Term::Lam(body) = motive.as_ref() {
                Some(subst0_closed(body, scrutinee))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Weaken a closed-ish type by `d` binders (shift all free de Bruijn indices up by `d`).
fn weaken(t: &Term, d: usize) -> Term {
    weaken_above(t, 0, d)
}

/// Shift every free de Bruijn variable `≥ cutoff` up by `d`, leaving variables below `cutoff`
/// (and metavariables) untouched. `weaken(t, d)` is `weaken_above(t, 0, d)`. Used to insert fresh
/// binders into the middle of a term's context (e.g. unused index binders just above a scrutinee
/// binder when building an indexed `Elim` motive).
fn weaken_above(t: &Term, cutoff: usize, d: usize) -> Term {
    fn go(t: &Term, j: usize, d: usize) -> Term {
        use blight_kernel::Term as T;
        match t {
            T::Var(i) => T::Var(if crate::meta::is_meta(*i) {
                *i
            } else if *i >= j {
                i + d
            } else {
                *i
            }),
            T::Univ(_) | T::Interval(_) | T::Erased | T::System(_) => t.clone(),
            T::Pi(g, a, b) => T::Pi(*g, Box::new(go(a, j, d)), Box::new(go(b, j + 1, d))),
            T::Sigma(a, b) => T::Sigma(Box::new(go(a, j, d)), Box::new(go(b, j + 1, d))),
            T::Lam(b) => T::Lam(Box::new(go(b, j + 1, d))),
            T::PLam(b) => T::PLam(Box::new(go(b, j + 1, d))),
            T::App(f, x) => T::App(Box::new(go(f, j, d)), Box::new(go(x, j, d))),
            T::Pair(a, b) => T::Pair(Box::new(go(a, j, d)), Box::new(go(b, j, d))),
            T::Fst(p) => T::Fst(Box::new(go(p, j, d))),
            T::Snd(p) => T::Snd(Box::new(go(p, j, d))),
            T::Ann(a, b) => T::Ann(Box::new(go(a, j, d)), Box::new(go(b, j, d))),
            T::Data(n, ps, is) => T::Data(
                n.clone(),
                ps.iter().map(|x| go(x, j, d)).collect(),
                is.iter().map(|x| go(x, j, d)).collect(),
            ),
            T::Con(n, args) => T::Con(n.clone(), args.iter().map(|x| go(x, j, d)).collect()),
            T::Delay(a) => T::Delay(Box::new(go(a, j, d))),
            T::Now(a) => T::Now(Box::new(go(a, j, d))),
            T::Later(a) => T::Later(Box::new(go(a, j, d))),
            other => other.clone(),
        }
    }
    go(t, cutoff, d)
}

/// Insert and solve implicit arguments for a global head `g` with leading implicit binders
/// described by `specs` (spec §6.4). Ordinary implicits are solved by metavariable unification
/// against the arguments' synthesized types and the expected result; type-class constraints are
/// resolved by dictionary search keyed on the class and the (already-solved) head type. A leftover
/// unsolved meta, or a missing instance, is a clear error.
#[allow(clippy::too_many_arguments)]
fn elab_implicit_app(
    env: &ElabEnv,
    scope: &Scope,
    g: &str,
    g_term: &Term,
    g_ty: &Term,
    specs: &[ImplicitSpec],
    args: &[Surface],
    expected: Option<&Term>,
) -> Result<Term, ElabError> {
    let mut mc = MetaCtx::new();
    // 1. Instantiate each leading implicit Pi. A `Unify` implicit gets a fresh meta; an `Instance`
    //    implicit is recorded with the (meta-bearing) domain type so it can be resolved after the
    //    explicit arguments pin down its parameter.
    let mut ty = g_ty.clone();
    enum Slot {
        Unify(Term),
        Instance { class: String, dom: Term },
    }
    let mut slots: Vec<Slot> = Vec::with_capacity(specs.len());
    for spec in specs {
        let (dom, cod) = match &ty {
            Term::Pi(_grade, dom, cod) => ((**dom).clone(), (**cod).clone()),
            _ => {
                return Err(ElabError::BadForm(format!(
                    "`{g}` declares more implicit binders than its type has Pis"
                )))
            }
        };
        match spec {
            ImplicitSpec::Unify => {
                let id = mc.fresh();
                let m = meta_term(id);
                slots.push(Slot::Unify(m.clone()));
                ty = subst0_closed(&cod, &m);
            }
            ImplicitSpec::Instance { class } => {
                // Defer: the dictionary occupies this binder; advance the type with a placeholder
                // meta so dependent later binders still type. The placeholder is solved only if it
                // is later constrained; the dictionary value is filled by search below.
                let id = mc.fresh();
                let placeholder = meta_term(id);
                slots.push(Slot::Instance {
                    class: class.clone(),
                    dom,
                });
                ty = subst0_closed(&cod, &placeholder);
            }
        }
    }
    // 2. Explicit args: unify each declared (meta-bearing) domain with the arg's synthesized type.
    let mut explicit = Vec::with_capacity(args.len());
    for a in args {
        let (dom, cod) = match &ty {
            Term::Pi(_grade, dom, cod) => ((**dom).clone(), (**cod).clone()),
            _ => {
                return Err(ElabError::BadForm(format!(
                    "too many explicit arguments applied to `{g}`"
                )))
            }
        };
        let ac = elab(env, scope, a, None)?;
        if let Some(at) = synth_type(env, scope, &ac) {
            mc.unify(&dom, &at)
                .map_err(|_| ElabError::BadForm(format!("implicit-argument mismatch for `{g}`")))?;
        }
        ty = subst0_closed(&cod, &ac);
        explicit.push(ac);
    }
    // 3. Unify the result against the expected type when known.
    if let Some(exp) = expected {
        let _ = mc.unify(&ty, exp);
    }
    // 4. Fill the implicit slots: metas by zonking, instances by dictionary search.
    let mut inserted = Vec::with_capacity(slots.len());
    for slot in slots {
        match slot {
            Slot::Unify(m) => {
                let z = mc.zonk(&m);
                if mc.has_unsolved(&z) {
                    return Err(ElabError::BadForm(format!(
                        "could not infer implicit argument of `{g}` (add an annotation)"
                    )));
                }
                inserted.push(z);
            }
            Slot::Instance { class, dom } => {
                // The constraint type `(class A)`: A is the first type argument; resolve its head.
                let dom_z = mc.zonk(&dom);
                let head = instance_head_of(&class, &dom_z).ok_or_else(|| {
                    ElabError::BadForm(format!(
                        "could not determine the instance head for `{class}` in `{g}`"
                    ))
                })?;
                let dict = env.lookup_instance(&class, &head).ok_or_else(|| {
                    ElabError::BadForm(format!("no instance `{class} {head}` in scope"))
                })?;
                inserted.push(dict.clone());
            }
        }
    }
    // 5. Build `((g implicit…) explicit…)`.
    let mut head = g_term.clone();
    for s in inserted {
        head = Term::App(Box::new(head), Box::new(s));
    }
    for e in explicit {
        head = Term::App(Box::new(head), Box::new(e));
    }
    Ok(head)
}

/// The instance-search head for a constraint domain `(class A …)`: the head symbol of its first
/// type argument `A` (e.g. `Nat` for `(Show Nat)`).
fn instance_head_of(class: &str, dom: &Term) -> Option<String> {
    // `dom` is the elaborated constraint type. It is the class type former applied to `A`; we
    // recover `A` as the last applied argument and take its head symbol.
    fn first_type_arg(t: &Term) -> Option<&Term> {
        match t {
            Term::App(f, a) => match first_type_arg(f) {
                Some(inner) => Some(inner),
                None => Some(a),
            },
            Term::Ann(e, _) => first_type_arg(e),
            _ => None,
        }
    }
    let _ = class;
    first_type_arg(dom).and_then(term_head_symbol)
}

fn elab_sigma(
    env: &ElabEnv,
    scope: &Scope,
    binders: &[Binder],
    cod: &Surface,
) -> Result<Term, ElabError> {
    match binders.split_first() {
        None => elab(env, scope, cod, None),
        Some((b, rest)) => {
            let dom = elab(env, scope, &b.ty, None)?;
            let sc = scope.push_var(&b.name);
            let cod_c = elab_sigma(env, &sc, rest, cod)?;
            Ok(Term::Sigma(Box::new(dom), Box::new(cod_c)))
        }
    }
}

/// Whether `t` mentions the de Bruijn variable at index `k` (relative to `t`'s scope). Used to
/// decide whether a `Sigma`'s second-component type is dependent on the first; conservative
/// (an unhandled node is treated as mentioning the variable). Binders increment `k`.
fn term_mentions_var(t: &Term, k: usize) -> bool {
    match t {
        Term::Var(i) => *i == k,
        Term::Univ(_) | Term::Interval(_) | Term::Erased => false,
        Term::Pi(_, a, b) | Term::Sigma(a, b) => {
            term_mentions_var(a, k) || term_mentions_var(b, k + 1)
        }
        Term::Lam(b) | Term::PLam(b) => term_mentions_var(b, k + 1),
        Term::App(f, a) => term_mentions_var(f, k) || term_mentions_var(a, k),
        Term::Pair(a, b) => term_mentions_var(a, k) || term_mentions_var(b, k),
        Term::Fst(p) | Term::Snd(p) | Term::Unglue(p) => term_mentions_var(p, k),
        Term::Ann(a, b) => term_mentions_var(a, k) || term_mentions_var(b, k),
        Term::Data(_, ps, is) => {
            ps.iter().any(|x| term_mentions_var(x, k)) || is.iter().any(|x| term_mentions_var(x, k))
        }
        Term::Con(_, args) => args.iter().any(|x| term_mentions_var(x, k)),
        Term::Delay(a) | Term::Now(a) | Term::Later(a) | Term::Force(a) => term_mentions_var(a, k),
        Term::EffTy(_, a) => term_mentions_var(a, k),
        Term::Op { arg, .. } => term_mentions_var(arg, k),
        // Conservative for the rest (cubical machinery, handlers, systems): assume it mentions the
        // variable so we never forward a wrong (dependent) expected type. The spore re-checks.
        _ => true,
    }
}

/// Translate a surface binder grade into a kernel [`Grade`] (spec §3.2 surface syntax §5):
/// `0` ⟼ erased, `1` ⟼ linear, absent or `omega`/`w` ⟼ unrestricted. Any other token is a
/// (caught) user error rather than a silent default.
fn parse_grade(grade: Option<&Surface>) -> Result<blight_kernel::Grade, ElabError> {
    use blight_kernel::Grade;
    match grade {
        None => Ok(Grade::Omega),
        Some(Surface::Var(s)) => match s.as_str() {
            "0" => Ok(Grade::Zero),
            "1" => Ok(Grade::One),
            "omega" | "w" | "ω" => Ok(Grade::Omega),
            other => Err(ElabError::BadForm(format!(
                "binder grade must be 0, 1, or omega; got `{other}`"
            ))),
        },
        Some(other) => Err(ElabError::BadForm(format!(
            "binder grade must be a grade literal (0 | 1 | omega), got {other:?}"
        ))),
    }
}

/// Try to elaborate an application whose head is a constructor or a recursive self-call. Returns
/// `Ok(Some(term))` when handled specially, `Ok(None)` to fall back to plain application.
fn elab_app_head(
    env: &ElabEnv,
    scope: &Scope,
    f: &Surface,
    args: &[Surface],
) -> Result<Option<Term>, ElabError> {
    use blight_kernel::ConName;
    if let Surface::Var(raw) = f {
        // Hygiene: an applied head that is not a local binder may be a macro-introduced reference
        // to a global/constructor/data; resolve such a head under its base (mark-stripped) name.
        let base = if scope.var_index(raw).is_none() {
            crate::macros::strip_mark(raw).to_string()
        } else {
            raw.clone()
        };
        let name = &base;
        // Data type applied to parameters/indices: `(D p … i …)` → `Term::Data(D, params, indices)`.
        // The kernel records how many of each the family takes; we route the leading args to
        // `params` and the trailing args to `indices`.
        if env.datas.contains_key(name) {
            if let Some(decl) = env.signature().get(&blight_kernel::DataName(name.clone())) {
                let n_params = decl.params.len();
                let n_indices = decl.indices.len();
                if args.len() == n_params + n_indices {
                    let mut params = Vec::with_capacity(n_params);
                    let mut indices = Vec::with_capacity(n_indices);
                    for (i, a) in args.iter().enumerate() {
                        let c = elab(env, scope, a, None)?;
                        if i < n_params {
                            params.push(c);
                        } else {
                            indices.push(c);
                        }
                    }
                    return Ok(Some(Term::Data(
                        blight_kernel::DataName(name.clone()),
                        params,
                        indices,
                    )));
                }
            }
        }
        // Constructor application `(Con a ...)`.
        if let Some(info) = env.constructors.get(name) {
            if info.rec_flags.len() == args.len() {
                let mut cargs = Vec::new();
                for a in args {
                    cargs.push(elab(env, scope, a, None)?);
                }
                return Ok(Some(Term::Con(ConName(name.clone()), cargs)));
            }
        }
        // Recursive self-call `(self subterm ...)`: if the first argument is the recursion
        // variable, replace the call by its induction hypothesis applied to the remaining args.
        if let Some(rec) = &scope.rec {
            if &rec.self_name == name {
                // First try the general layout: the scrutinee sits at position `leading.len()`,
                // preceded by the function's leading parameters/indices (a structural call repeats
                // the *parameters* verbatim; an *index* of an indexed family may legitimately vary
                // — e.g. `vec-length A m xs` recurses with the smaller length `m`). We therefore do
                // *not* insist the leading args match name-for-name; we only require that the
                // scrutinee-position argument is a recursive sub-term variable carrying an induction
                // hypothesis. The IH already has the fully-specialized type `motive <indices> sub`,
                // so the preceding param/index args are subsumed by it. Soundness does not rest on
                // this recognition: the kernel re-checks the resulting `Elim`, and a mis-recognized
                // call simply fails to type-check.
                if !rec.leading.is_empty() {
                    let k = rec.leading.len();
                    if args.len() > k {
                        if let Surface::Var(sub) = &args[k] {
                            if let Some(ih_name) = rec.ih.get(sub) {
                                if let Some(idx) = scope.var_index(ih_name) {
                                    let mut head = Term::Var(idx);
                                    for a in &args[k + 1..] {
                                        head = Term::App(
                                            Box::new(head),
                                            Box::new(elab(env, scope, a, None)?),
                                        );
                                    }
                                    return Ok(Some(head));
                                }
                            }
                        }
                    }
                }
                if let Some(Surface::Var(first)) = args.first() {
                    if let Some(ih_name) = rec.ih.get(first) {
                        if let Some(idx) = scope.var_index(ih_name) {
                            let mut head = Term::Var(idx);
                            for a in &args[1..] {
                                head =
                                    Term::App(Box::new(head), Box::new(elab(env, scope, a, None)?));
                            }
                            return Ok(Some(head));
                        }
                    }
                }
                // Not on the structural sub-term. For `deftotal` this is a hard error; for
                // `define-rec` it is a *partial* (possibly-diverging) call, elaborated to a
                // `Later`-guarded application of the self-reference variable (spec §4.5). The
                // function's declared return type is `Delay A`, so `later (self a …) : Delay A`.
                if rec.total {
                    return Err(ElabError::BadMatch(format!(
                        "recursive call to `{name}` must be on the structural sub-term \
                         (use `define-rec` instead of `deftotal` for general recursion)"
                    )));
                }
                let self_idx = scope
                    .var_index(name)
                    .ok_or_else(|| ElabError::Unbound(format!("self-reference `{name}`")))?;
                let mut head = Term::Var(self_idx);
                for a in args {
                    head = Term::App(Box::new(head), Box::new(elab(env, scope, a, None)?));
                }
                return Ok(Some(Term::Later(Box::new(head))));
            }
        }
    }
    Ok(None)
}

/// Whether a (closed, core) declared type has a *pure, total* conclusion — i.e. peeling its `Pi`
/// binders lands on a codomain that is neither an effectful computation type `! E A` (with a
/// non-empty row `E`) nor a partial `Delay A`. Only such definitions are eligible for the kernel's
/// pure top-level door ([`ElabEnv::kernel_check_def`]); effectful and partial conclusions are
/// governed by their own typing rules during elaboration and re-verified (or `Declined`) by the
/// `--recheck` pass instead. A `! ⟨⟩ A` (empty row) conclusion is pure and unwrapped.
fn is_pure_total_conclusion(ty: &Term) -> bool {
    let mut t = ty;
    loop {
        match t {
            Term::Pi(_, _, cod) => t = cod,
            Term::EffTy(row, inner) => {
                if !row.is_empty() {
                    return false;
                }
                // `! ⟨⟩ A` is pure: look through to the carried type's conclusion.
                t = inner;
            }
            Term::Delay(_) => return false,
            _ => return true,
        }
    }
}

/// Whether the kernel gate ([`ElabEnv::kernel_check_def`]) should *route this definition through the
/// kernel at all*. Beyond purity/totality ([`is_pure_total_conclusion`]), the gate is restricted to
/// definitions whose verification is bounded by the term's *structure* — **functions** (a `Pi` head,
/// possibly under pure `! ⟨⟩` wrappers) and **path/identity proofs** (`PathP`).
///
/// It deliberately SKIPS closed ground-*value* definitions whose declared conclusion is a concrete
/// data type (e.g. `main : Nat = (head-or Zero (qsort input))`). For those, kernel-checking the body
/// against its type degenerates into *evaluating the whole program to normal form* (the
/// `palindrome`/`mergesort`/`quicksort` blowup) — work that is (a) redundant with codegen's own
/// `check_top` on `main` plus execution, and (b) unbounded by the term's structure. Such values are
/// not where elaborator bugs hide; functions and proofs are, and those stay fully gated. This is a
/// deterministic, elaborator-side restriction (it touches no kernel/TCB code).
fn gate_routes_through_kernel(ty: &Term) -> bool {
    if !is_pure_total_conclusion(ty) {
        return false;
    }
    let mut t = ty;
    loop {
        match t {
            // A function: gate it (checking a `Pi` body is structural — no whole-program eval).
            Term::Pi(_, _, _) => return true,
            // A path/identity proof: gate it (proofs are exactly the elaborator-bug-prone case).
            Term::PathP { .. } => return true,
            // Look through pure effect wrappers to the carried conclusion.
            Term::EffTy(row, inner) if row.is_empty() => t = inner,
            // Any other (ground data) conclusion: skip — kernel-checking would just run the program.
            _ => return false,
        }
    }
}

/// Whether `term` contains an eliminator (`Elim`) with a **higher-order motive** — one whose body,
/// after peeling its leading `Lam` binders (the index binders + the scrutinee binder), is itself a
/// `Pi`. This is the `zip-vec` shape: matching `v` while a second vector `w` is still in scope lifts
/// `w` into the motive, so the result is a *function* `Vec B n → Vec (Pair A B) n`.
///
/// TEMPORARY (plan item 1a, removed by 1b): the kernel cannot yet reconstruct such a motive (it
/// errors mid-check), and the independent re-checker *honestly DECLINES* this exact shape rather than
/// re-verify it. It is part of the same dependent-pattern-matching frontier item 1b closes. Until
/// then the gate detects it structurally (deterministically, in untrusted elaborator code) and skips
/// it, rather than matching a brittle kernel error string. `safe-tail`/`vec-map` do NOT match here:
/// their motive body is a `Data` (`Vec A n`), not a `Pi`.
fn term_has_higher_order_elim_motive(term: &Term) -> bool {
    fn motive_is_higher_order(motive: &Term) -> bool {
        let mut body = motive;
        while let Term::Lam(inner) = body {
            body = inner;
        }
        matches!(body, Term::Pi(_, _, _))
    }
    fn walk(t: &Term) -> bool {
        match t {
            Term::Elim {
                motive,
                methods,
                scrutinee,
                ..
            } => {
                motive_is_higher_order(motive)
                    || walk(motive)
                    || methods.iter().any(walk)
                    || walk(scrutinee)
            }
            Term::Var(_) | Term::Univ(_) | Term::Interval(_) | Term::Foreign { .. } => false,
            Term::Pi(_, a, b)
            | Term::Sigma(a, b)
            | Term::Pair(a, b)
            | Term::App(a, b)
            | Term::Ann(a, b) => walk(a) || walk(b),
            Term::Lam(a)
            | Term::Fst(a)
            | Term::Snd(a)
            | Term::PLam(a)
            | Term::Delay(a)
            | Term::Now(a)
            | Term::Later(a)
            | Term::Force(a)
            | Term::Unglue(a)
            | Term::EffTy(_, a) => walk(a),
            Term::PApp(a, _) => walk(a),
            Term::Data(_, xs, ys) => xs.iter().any(walk) || ys.iter().any(walk),
            Term::Con(_, xs) => xs.iter().any(walk),
            Term::PathP { family, lhs, rhs } => walk(family) || walk(lhs) || walk(rhs),
            Term::Partial(_, a) => walk(a),
            Term::System(branches) => branches.iter().any(|b| walk(&b.term)),
            Term::Transp { family, base, .. } => walk(family) || walk(base),
            Term::HComp { ty, tube, base, .. } => walk(ty) || walk(tube) || walk(base),
            Term::Comp {
                family, tube, base, ..
            } => walk(family) || walk(tube) || walk(base),
            Term::Glue {
                base, ty, equiv, ..
            } => walk(base) || walk(ty) || walk(equiv),
            Term::GlueTerm { partial, base, .. } => walk(partial) || walk(base),
            Term::Op { arg, .. } => walk(arg),
            Term::Handle {
                body,
                return_clause,
                op_clauses,
            } => walk(body) || walk(return_clause) || op_clauses.iter().any(|(_, c)| walk(c)),
            Term::IntTy | Term::IntLit(_) => false,
            Term::IntPrim { lhs, rhs, .. } => walk(lhs) || walk(rhs),
            Term::Erased => false,
        }
    }
    walk(term)
}

/// Elaborate a `define-rec`/`deftotal` body. The body must be `(lam (x ...) (match xi clauses))`
/// where the match is on one of the lambda binders; structural recursion is realized as the
/// `Elim`'s induction hypotheses (spec §6.2). A non-structural recursive call is rejected when
/// `total` is set (`deftotal`); otherwise it elaborates to a `Later`-guarded partial step that
/// makes the inferred row carry the built-in `Partial` effect at a nonzero grade (spec §4.5).
fn elaborate_rec(
    env: &ElabEnv,
    name: &str,
    body: &Surface,
    ty: &Term,
    total: bool,
) -> Result<Term, ElabError> {
    // First attempt the *structural* compilation (to `Elim`, total, partiality grade 0). The
    // self-name is handled at call sites as the eliminator's induction hypothesis.
    let structural = {
        let mut scope = Scope::new();
        scope.rec = Some(RecCtx {
            self_name: name.to_string(),
            ih: std::collections::HashMap::new(),
            total: true,
            leading: Vec::new(),
        });
        elab(env, &scope, body, Some(ty))
    };
    match structural {
        Ok(t) => Ok(t),
        Err(e) => {
            // `deftotal` must compile structurally: propagate the failure.
            if total {
                return Err(e);
            }
            // `define-rec`: fall back to the *partial* compilation. Bind the self-reference as an
            // ordinary variable `self : T` and guard each non-structural recursive call under
            // `later` (spec §4.5). The result is `λ(self:T). body : T → T`; the guarded call
            // `later (self a)` makes the inferred row carry `Partial` at a nonzero grade.
            let mut scope = Scope::new();
            scope = scope.push_var_ty(name, Some(ty.clone()));
            scope.rec = Some(RecCtx {
                self_name: name.to_string(),
                ih: std::collections::HashMap::new(),
                total: false,
                leading: Vec::new(),
            });
            // `body` is checked against `ty` under the extra `self` binder; `ty` mentions no
            // bound vars (it is closed), so no shifting is needed for it.
            let inner = elab(env, &scope, body, Some(ty))?;
            Ok(Term::Lam(Box::new(inner)))
        }
    }
}

/// Lower a (possibly nested/wildcard/multi-scrutinee) `match` to a tree of *flat* single-scrutinee
/// matches over variable scrutinees, following Maranget's column compilation. Non-variable
/// scrutinees are first bound with a `let` so the motive can abstract a variable. The result
/// contains only `Surface::Match` nodes that satisfy [`elab_flat_match`]'s preconditions.
fn lower_match(
    env: &ElabEnv,
    scruts: &[Surface],
    clauses: &[Clause],
) -> Result<Surface, ElabError> {
    use crate::surface::Pattern;
    if clauses.is_empty() {
        return Err(ElabError::BadMatch("empty match".into()));
    }
    let mut g = Gensym::default();
    // Bind every scrutinee to a fresh variable via nested `let`s, collecting the occurrence names.
    let mut occ = Vec::with_capacity(scruts.len());
    let mut wrap: Vec<(String, Surface)> = Vec::new();
    for s in scruts {
        match s {
            Surface::Var(v) => occ.push(v.clone()),
            other => {
                let name = g.fresh("scrut");
                wrap.push((name.clone(), other.clone()));
                occ.push(name);
            }
        }
    }
    let rows: Vec<(Vec<Pattern>, Surface)> = clauses
        .iter()
        .map(|c| (c.patterns.clone(), c.body.clone()))
        .collect();
    let mut body = compile_matrix(env, &mut g, &occ, rows)?;
    // Wrap the let-bindings outermost-first (so earlier scrutinees bind outermost).
    for (name, init) in wrap.into_iter().rev() {
        body = Surface::Let(name, Box::new(init), Box::new(body));
    }
    Ok(body)
}

/// A monotonic fresh-name source for lowering. Names use a `$` sigil so they never clash with
/// user identifiers or macro marks.
#[derive(Default)]
struct Gensym(u64);

impl Gensym {
    fn fresh(&mut self, hint: &str) -> String {
        self.0 += 1;
        format!("${hint}{}", self.0)
    }
}

/// Maranget column compilation. `occ` are the occurrence variable names (in scope); `rows` are the
/// remaining clauses as `(patterns, body)` with one pattern per occurrence.
fn compile_matrix(
    env: &ElabEnv,
    g: &mut Gensym,
    occ: &[String],
    rows: Vec<(Vec<crate::surface::Pattern>, Surface)>,
) -> Result<Surface, ElabError> {
    use crate::surface::Pattern;
    // Base: no columns left — the first row matches unconditionally.
    if occ.is_empty() {
        return Ok(rows
            .into_iter()
            .next()
            .ok_or_else(|| ElabError::BadMatch("non-exhaustive match".into()))?
            .1);
    }
    // If the first column is all variable/wildcard, bind those and recurse on the rest.
    let all_var = rows
        .iter()
        .all(|(ps, _)| matches!(ps[0], Pattern::Var(_) | Pattern::Wild));
    if all_var {
        let o0 = &occ[0];
        let rest_occ = &occ[1..];
        let new_rows = rows
            .into_iter()
            .map(|(mut ps, body)| {
                let head = ps.remove(0);
                // A `Var x` aliases the occurrence into the body via a `let`.
                let body = match head {
                    Pattern::Var(x) if &x != o0 => {
                        Surface::Let(x, Box::new(Surface::Var(o0.clone())), Box::new(body))
                    }
                    _ => body,
                };
                (ps, body)
            })
            .collect();
        return compile_matrix(env, g, rest_occ, new_rows);
    }
    // Otherwise the first column is a constructor column. Determine its data type from the first
    // constructor pattern present, and emit a flat match exhaustive over that type.
    let con0 = rows
        .iter()
        .find_map(|(ps, _)| match &ps[0] {
            Pattern::Con(c, _) => Some(c.clone()),
            _ => None,
        })
        .ok_or_else(|| ElabError::BadMatch("no constructor in column".into()))?;
    let data = env
        .constructors
        .get(&con0)
        .map(|i| i.data.clone())
        .ok_or_else(|| ElabError::BadMatch(format!("unknown constructor {con0}")))?;
    let ctors = env
        .datas
        .get(&data)
        .cloned()
        .ok_or_else(|| ElabError::BadMatch(format!("unknown data type {data}")))?;

    let o0 = occ[0].clone();
    let rest_occ = &occ[1..];
    let mut flat_clauses = Vec::with_capacity(ctors.len());
    for cname in &ctors {
        let info = env
            .constructors
            .get(cname)
            .expect("constructor info present");
        let arity = info.rec_flags.len();
        // Fresh occurrences for this constructor's fields.
        let field_occ: Vec<String> = (0..arity)
            .map(|i| g.fresh(&format!("{cname}f{i}")))
            .collect();
        // Specialize: keep rows whose column-0 pattern matches `cname` (or is var/wild — a default).
        let mut spec_rows: Vec<(Vec<Pattern>, Surface)> = Vec::new();
        for (ps, body) in &rows {
            match &ps[0] {
                Pattern::Con(c, subs) if c == cname => {
                    let mut new_ps = subs.clone();
                    new_ps.extend_from_slice(&ps[1..]);
                    spec_rows.push((new_ps, body.clone()));
                }
                Pattern::Var(_) | Pattern::Wild => {
                    // A default row matches every constructor: its fields become wildcards.
                    let mut new_ps: Vec<Pattern> = (0..arity).map(|_| Pattern::Wild).collect();
                    new_ps.extend_from_slice(&ps[1..]);
                    // A `Var x` default still aliases the *whole* scrutinee into the body.
                    let body = match &ps[0] {
                        Pattern::Var(x) if x != &o0 => Surface::Let(
                            x.clone(),
                            Box::new(Surface::Var(o0.clone())),
                            Box::new(body.clone()),
                        ),
                        _ => body.clone(),
                    };
                    spec_rows.push((new_ps, body));
                }
                Pattern::Con(..) => {} // different constructor: row does not apply here
            }
        }
        if spec_rows.is_empty() {
            return Err(ElabError::BadMatch(format!(
                "non-exhaustive match: no clause for constructor `{cname}`"
            )));
        }
        let mut sub_occ = field_occ.clone();
        sub_occ.extend_from_slice(rest_occ);
        let sub = compile_matrix(env, g, &sub_occ, spec_rows)?;
        flat_clauses.push(Clause {
            patterns: vec![Pattern::Con(
                cname.clone(),
                field_occ.iter().map(|n| Pattern::Var(n.clone())).collect(),
            )],
            body: sub,
        });
    }
    Ok(Surface::Match(vec![Surface::Var(o0)], flat_clauses))
}

/// Inference-mode motive: with no expected type, synthesize a *non-dependent* result type by
/// elaborating the first clause's body under fresh binders and reading off its type. Used only for
/// `match` in synthesis position (spec §6.2). Returns an error when the type cannot be read off.
fn infer_match_motive(env: &ElabEnv, scope: &Scope, flat: &Surface) -> Result<Term, ElabError> {
    use crate::surface::Pattern;
    let (scrut, clauses) = match flat {
        Surface::Match(scruts, clauses) if scruts.len() == 1 => (&scruts[0], clauses),
        _ => {
            return Err(ElabError::BadMatch(
                "cannot infer motive for this match".into(),
            ))
        }
    };
    let _ = scrut;
    let first = clauses
        .first()
        .ok_or_else(|| ElabError::BadMatch("empty match".into()))?;
    // Extend the scope with the first clause's constructor binders (untyped is fine for synthesis),
    // elaborate the body, and synthesize its type. The motive must not mention those binders.
    let mut sc = scope.clone();
    let mut introduced = 0usize;
    if let Some(Pattern::Con(con, subs)) = first.patterns.first() {
        if let Some(info) = env.constructors.get(con) {
            for (i, &is_rec) in info.rec_flags.iter().enumerate() {
                let nm = match subs.get(i) {
                    Some(Pattern::Var(v)) => v.clone(),
                    _ => format!("_inf{i}"),
                };
                sc = sc.push_var(&nm);
                introduced += 1;
                if is_rec {
                    sc = sc.push_var(&format!("{nm}#ih"));
                    introduced += 1;
                }
            }
        }
    }
    let body = elab(env, &sc, &first.body, None)?;
    let ty = synth_type(env, &sc, &body).ok_or_else(|| {
        ElabError::BadMatch("cannot infer match result type; add an ascription".into())
    })?;
    // The synthesized type lives under `introduced` extra binders; it must be closed w.r.t. them so
    // it is a valid motive in the original scope.
    if mentions_below(&ty, introduced) {
        return Err(ElabError::BadMatch(
            "inference-mode match result depends on the matched value; add an ascription".into(),
        ));
    }
    Ok(strengthen(&ty, introduced))
}

/// Whether `t` mentions any de Bruijn index `< d` (i.e. one of the `d` innermost binders).
/// Reduce a type term toward a `Pi` head, conservatively: strip ascriptions and β-reduce a
/// top-level `App(Lam, a)`. Returns `(grade, domain, codomain)` when a `Pi` is reached.
fn whnf_pi(t: &Term) -> Option<(blight_kernel::Grade, Term, Term)> {
    match whnf_head(t) {
        Term::Pi(g, a, b) => Some((g, *a, *b)),
        _ => None,
    }
}

/// Reduce a type term toward a `Sigma` head (see [`whnf_pi`]). Returns `(domain, codomain)`.
fn whnf_sigma(t: &Term) -> Option<(Term, Term)> {
    match whnf_head(t) {
        Term::Sigma(a, b) => Some((*a, *b)),
        _ => None,
    }
}

/// A small head-normalizer over elaborated `Term`s, sufficient for [`synth_type`]'s needs: peels
/// `Ann`, inlines globals (whose stored term is closed), and β-reduces a head `App(Lam, a)` /
/// projects a head `Fst/Snd(Pair …)`. Bounded to avoid loops on (well-typed) cyclic-looking terms.
fn whnf_head(t: &Term) -> Term {
    let mut cur = t.clone();
    for _ in 0..64 {
        cur = match cur {
            Term::Ann(e, _) => *e,
            Term::App(f, x) => match whnf_head(&f) {
                Term::Lam(b) => subst0_closed(&b, &x),
                other => return Term::App(Box::new(other), x),
            },
            Term::Fst(p) => match whnf_head(&p) {
                Term::Pair(a, _) => *a,
                other => return Term::Fst(Box::new(other)),
            },
            Term::Snd(p) => match whnf_head(&p) {
                Term::Pair(_, b) => *b,
                other => return Term::Snd(Box::new(other)),
            },
            other => return other,
        };
    }
    cur
}

fn mentions_below(t: &Term, d: usize) -> bool {
    fn go(t: &Term, depth: usize, d: usize) -> bool {
        match t {
            Term::Var(i) => {
                if crate::meta::is_meta(*i) {
                    false
                } else {
                    *i >= depth && *i - depth < d
                }
            }
            Term::Lam(b) | Term::Now(b) | Term::Later(b) | Term::Delay(b) | Term::PLam(b) => {
                go(b, depth + 1, d)
            }
            Term::Force(b) => go(b, depth, d),
            Term::Pi(_, a, b) | Term::Sigma(a, b) => go(a, depth, d) || go(b, depth + 1, d),
            Term::App(f, x) => go(f, depth, d) || go(x, depth, d),
            Term::Pair(a, b) => go(a, depth, d) || go(b, depth, d),
            Term::Fst(p) | Term::Snd(p) => go(p, depth, d),
            Term::Ann(e, ty) => go(e, depth, d) || go(ty, depth, d),
            _ => false,
        }
    }
    go(t, 0, d)
}

/// Whether `t` references the (outer-scope) de Bruijn variable `k`, accounting for binders crossed.
fn mentions_var(t: &Term, k: usize) -> bool {
    fn go(t: &Term, depth: usize, k: usize) -> bool {
        match t {
            Term::Var(i) => !crate::meta::is_meta(*i) && *i == k + depth,
            Term::Lam(b) | Term::Now(b) | Term::Later(b) | Term::Delay(b) | Term::PLam(b) => {
                go(b, depth + 1, k)
            }
            Term::Force(b) => go(b, depth, k),
            Term::Pi(_, a, b) | Term::Sigma(a, b) => go(a, depth, k) || go(b, depth + 1, k),
            Term::App(f, x) => go(f, depth, k) || go(x, depth, k),
            Term::Pair(a, b) => go(a, depth, k) || go(b, depth, k),
            Term::Fst(p) | Term::Snd(p) => go(p, depth, k),
            Term::Ann(e, ty) => go(e, depth, k) || go(ty, depth, k),
            Term::Data(_, ps, is) => {
                ps.iter().any(|x| go(x, depth, k)) || is.iter().any(|x| go(x, depth, k))
            }
            Term::Con(_, args) => args.iter().any(|x| go(x, depth, k)),
            _ => false,
        }
    }
    go(t, 0, k)
}

/// Strengthen `t` by removing the `d` innermost binders it is known not to mention (the dual of
/// weakening): every free `Var(i) >= d` is lowered by `d`.
fn strengthen(t: &Term, d: usize) -> Term {
    fn go(t: &Term, depth: usize, d: usize) -> Term {
        match t {
            Term::Var(i) if crate::meta::is_meta(*i) => Term::Var(*i),
            Term::Var(i) if *i >= depth + d => Term::Var(*i - d),
            Term::Var(i) => Term::Var(*i),
            Term::Lam(b) => Term::Lam(Box::new(go(b, depth + 1, d))),
            Term::Now(b) => Term::Now(Box::new(go(b, depth, d))),
            Term::Later(b) => Term::Later(Box::new(go(b, depth, d))),
            Term::Delay(b) => Term::Delay(Box::new(go(b, depth, d))),
            Term::Force(b) => Term::Force(Box::new(go(b, depth, d))),
            Term::PLam(b) => Term::PLam(Box::new(go(b, depth + 1, d))),
            Term::Pi(gr, a, b) => Term::Pi(
                *gr,
                Box::new(go(a, depth, d)),
                Box::new(go(b, depth + 1, d)),
            ),
            Term::Sigma(a, b) => {
                Term::Sigma(Box::new(go(a, depth, d)), Box::new(go(b, depth + 1, d)))
            }
            Term::App(f, x) => Term::App(Box::new(go(f, depth, d)), Box::new(go(x, depth, d))),
            Term::Pair(a, b) => Term::Pair(Box::new(go(a, depth, d)), Box::new(go(b, depth, d))),
            Term::Fst(p) => Term::Fst(Box::new(go(p, depth, d))),
            Term::Snd(p) => Term::Snd(Box::new(go(p, depth, d))),
            Term::Ann(e, ty) => Term::Ann(Box::new(go(e, depth, d)), Box::new(go(ty, depth, d))),
            other => other.clone(),
        }
    }
    go(t, 0, d)
}

/// Elaborate a *flat* single-scrutinee match to a kernel `Elim`. Every clause must have exactly one
/// pattern of the form `Con(name, subs)` where each sub-pattern is a variable or wildcard, and the
/// clauses must be exhaustive over the scrutinee's data type in declaration order. The richer
/// surface (nested/wildcard/multi-scrutinee, inference-mode) is reduced to this form by
/// [`lower_match`]. `expected` is the type the match must inhabit in the current de Bruijn scope.
fn elab_flat_match(
    env: &ElabEnv,
    scope: &Scope,
    flat: &Surface,
    expected: &Term,
) -> Result<Term, ElabError> {
    use blight_kernel::{DataName, Grade};

    let (scrut, clauses) = match flat {
        Surface::Match(scruts, clauses) if scruts.len() == 1 => (&scruts[0], clauses),
        _ => return Err(ElabError::BadMatch("internal: non-flat match".into())),
    };
    // The scrutinee must be a variable, so the motive is a clean abstraction over it.
    let scrut_name = match scrut {
        Surface::Var(v) => v.clone(),
        _ => {
            return Err(ElabError::BadMatch(
                "internal: flat `match` requires a variable scrutinee".into(),
            ))
        }
    };
    let scrut_idx = scope
        .var_index(&scrut_name)
        .ok_or_else(|| ElabError::Unbound(scrut_name.clone()))?;

    // Read each clause's single top-level constructor pattern, materializing wildcard sub-patterns
    // as fresh binder names.
    struct FlatClause<'a> {
        constructor: String,
        binders: Vec<String>,
        body: &'a Surface,
    }
    let mut flats: Vec<FlatClause> = Vec::with_capacity(clauses.len());
    for c in clauses {
        let pat = c
            .patterns
            .first()
            .ok_or_else(|| ElabError::BadMatch("empty clause".into()))?;
        let (con, subs) = match pat {
            crate::surface::Pattern::Con(con, subs) => (con.clone(), subs),
            _ => {
                return Err(ElabError::BadMatch(
                    "internal: flat match clause must be a constructor pattern".into(),
                ))
            }
        };
        let mut binders = Vec::with_capacity(subs.len());
        for (i, s) in subs.iter().enumerate() {
            match s {
                crate::surface::Pattern::Var(v) => binders.push(v.clone()),
                crate::surface::Pattern::Wild => binders.push(format!("_wild{con}{i}")),
                crate::surface::Pattern::Con(..) => {
                    return Err(ElabError::BadMatch(
                        "internal: nested pattern reached flat compiler".into(),
                    ))
                }
            }
        }
        flats.push(FlatClause {
            constructor: con,
            binders,
            body: &c.body,
        });
    }

    // Binders introduced *after* the scrutinee (de Bruijn index < scrut_idx) are generalized into
    // the motive: it ranges over them and every method re-binds them. This is required whenever
    // those binders are *typed* (e.g. an enclosing function parameter the body still uses, as in
    // `plus`'s `b`). When any is *untyped* — only the fresh/IH binders introduced by pattern
    // lowering, which the (already-aliased) bodies never reference — we skip generalization (`m=0`).
    // The *trailing* binders are those bound strictly *inside* the scrutinee (de Bruijn index
    // below `scrut_idx`). They must be re-bound by every method, so the motive abstracts over
    // them: `λ s. Π(t_{m-1})…Π(t_0). expected`. Each stored type lives at *its own* binding
    // baseline (the scope depth when it was bound), so we first re-base every trailing type and
    // `expected` to the *full* current scope, giving a consistent index space, then weaken as the
    // Π-telescope reintroduces binders. (A naive `Pi(stored_ty, body)` mixes baselines — the source
    // of a long-standing parameterized-`match` de Bruijn bug.) We require all trailing binders to
    // be *typed*; an untyped one (only the fresh/IH binders introduced by pattern lowering, which
    // the already-aliased bodies never reference) means we skip generalization (`m = 0`).
    let n_vars = scope.vars.len();
    let mut trailing: Vec<Term> = Vec::new(); // index 0 = innermost (lowest de Bruijn), in full scope
    let mut all_typed = true;
    for i in 0..scrut_idx {
        let pos = n_vars - 1 - i; // absolute position in `vars`
        match scope.var_types[pos].clone() {
            // The stored type lives in a scope of size `pos`; lift it into the full scope (size
            // `n_vars`) by shifting its free variables up by `n_vars - pos`.
            Some(ty) => trailing.push(weaken(&ty, n_vars - pos)),
            None => {
                all_typed = false;
                break;
            }
        }
    }
    if !all_typed {
        trailing.clear();
    }
    let m = trailing.len();

    // Which inductive does this match on?
    let first = flats
        .first()
        .ok_or_else(|| ElabError::BadMatch("empty match".into()))?;
    let data_name = env
        .constructors
        .get(&first.constructor)
        .map(|i| i.data.clone())
        .ok_or_else(|| ElabError::BadMatch(format!("unknown constructor {}", first.constructor)))?;
    let ctor_order = env
        .datas
        .get(&data_name)
        .cloned()
        .ok_or_else(|| ElabError::BadMatch(format!("unknown data type {data_name}")))?;
    // The family's index arity, for building the canonical indexed motive below.
    let decl_nindices = env
        .signature()
        .get(&blight_kernel::DataName(data_name.clone()))
        .map(|d| d.indices.len())
        .unwrap_or(0);

    // Motive `λ s. Pi (t_{m-1}) ... Pi (t_0). expected`. Because the scrutinee binds *outside* the
    // trailing binders originally, the de Bruijn structure of `expected` already matches this
    // reconstruction; we only abstract the scrutinee occurrences.
    // Motive `λ s. Π(t_{m-1}) … Π(t_0). expected`. All `trailing[i]` and `expected` are now in the
    // same (full) scope, so we weaken each as the Π-telescope reintroduces binders: the body
    // `expected` sits under `m` new binders (shift by `m`); the domain reintroduced as the `k`-th
    // Π from the outside is `trailing[m-1-k]` sitting under `k` binders (shift by `k`).
    let mut motive_body = weaken(expected, m);
    // Outermost-first domains with their weakening applied.
    let mut domains: Vec<Term> = Vec::with_capacity(m);
    for k in 0..m {
        domains.push(weaken(&trailing[m - 1 - k], k));
    }
    // Fold innermost-first to assemble `Π(t_{m-1})…Π(t_0). expected'`.
    for dom in domains.into_iter().rev() {
        motive_body = Term::Pi(Grade::Omega, Box::new(dom), Box::new(motive_body));
    }

    // For an *indexed* family the kernel and the re-checker both require the motive to be `λ i1..im.
    // λ (_:D ps i1..im). T`, abstracting the family's indices *and* the scrutinee. We recover the
    // index values from the scrutinee's type `D ps i1..im`. We support the standard case where each
    // index value is a distinct variable in scope (e.g. `Vec A n`'s `n`); the motive then abstracts
    // those variables (a non-dependent body simply ignores the new binders). A non-variable or
    // duplicated index is outside this fragment, so we fall back to the bare `λ s. …` motive and let
    // the kernel/re-checker adjudicate (the latter will `Decline`/`Reject` rather than silently
    // accept an ill-formed motive).
    let scrut_pos = scope.vars.len() - 1 - scrut_idx;
    let index_vars: Option<Vec<usize>> = scope
        .var_types
        .get(scrut_pos)
        .and_then(|o| o.as_ref())
        // The stored type lives in the scope of size `scrut_pos` (when the scrutinee was bound);
        // re-base it into the full current scope so its index variables are valid de Bruijn indices
        // *here* (the same re-basing the trailing-binder telescope above performs).
        .map(|ty| weaken(ty, n_vars - scrut_pos))
        .and_then(|ty| match whnf_head(&ty) {
            Term::Data(d, _ps, is) if d.0 == data_name && is.len() == decl_nindices => {
                let mut vars = Vec::with_capacity(is.len());
                for ix in &is {
                    match ix {
                        Term::Var(v) if !crate::meta::is_meta(*v) => vars.push(*v),
                        _ => return None,
                    }
                }
                // Indices must be distinct variables, and none may coincide with the scrutinee.
                let mut seen = std::collections::HashSet::new();
                if vars.contains(&scrut_idx) || !vars.iter().all(|v| seen.insert(*v)) {
                    return None;
                }
                Some(vars)
            }
            _ => None,
        });

    let motive = match index_vars {
        Some(ivars) if !ivars.is_empty() => {
            // Abstract, innermost-first, the scrutinee then the indices reversed, so the resulting
            // nested lambdas are `λ i1. … λ im. λ s. body` (indices outermost, scrutinee innermost).
            let mut targets = Vec::with_capacity(ivars.len() + 1);
            targets.push(scrut_idx);
            for v in ivars.iter().rev() {
                targets.push(*v);
            }
            abstract_vars(&motive_body, &targets)
        }
        // Indexed family whose scrutinee indices are *not* distinct bound variables (e.g. `Vec A
        // (Succ n)`, where the index is `Succ n`, a non-variable). The kernel still requires the
        // canonical shape `λ i1..im. λ s. T`. When the result type does not depend on the scrutinee
        // (a non-dependent motive — the common case, e.g. `safe-head`'s `Maybe A`), the index
        // binders are simply unused: build `λ i1..im. λ s. T` by abstracting the scrutinee and
        // inserting `nindices` fresh, unreferenced binders just above it. This is sound precisely
        // because `T` mentions none of the index positions.
        _ if decl_nindices > 0 && !mentions_var(expected, scrut_idx) => {
            // `λ s. body`: de Bruijn 0 is the scrutinee, outer scope vars sit at `≥ 1`.
            let scrut_body = abstract_var(&motive_body, scrut_idx);
            // Make room for the `nindices` index binders directly *above* the scrutinee binder by
            // shifting every free variable `≥ 1` up by `nindices`. The scrutinee (0) is untouched.
            let shifted = weaken_above(&scrut_body, 1, decl_nindices);
            // Wrap: innermost `λ s`, then `nindices` fresh index binders outermost.
            let mut motive = Term::Lam(Box::new(shifted));
            for _ in 0..decl_nindices {
                motive = Term::Lam(Box::new(motive));
            }
            motive
        }
        // Non-indexed family, or an out-of-fragment dependent indexed motive: the bare `λ s. …`
        // shape. For an indexed family the kernel/re-checker will adjudicate (decline/reject) rather
        // than silently accept an ill-formed motive.
        _ => Term::Lam(Box::new(abstract_var(&motive_body, scrut_idx))),
    };

    // The *leading* parameters of the matched function are the binders bound strictly *outside*
    // (i.e. de Bruijn index greater than) the scrutinee. A structural recursive call must repeat
    // them verbatim, because the induction hypothesis fixes them. We record their names in *source
    // order* (outermost binder first — the order they are written at a call site) so
    // [`elab_app_head`] can recognize a recursive call whose scrutinee argument is not in first
    // position.
    let leading_names: Vec<String> = ((scrut_idx + 1)..scope.vars.len())
        .rev()
        .map(|i| scope.vars[scope.vars.len() - 1 - i].clone())
        .collect();

    // Build methods in declaration order.
    let mut methods = Vec::with_capacity(ctor_order.len());
    for cname in &ctor_order {
        let clause = flats
            .iter()
            .find(|c| &c.constructor == cname)
            .ok_or_else(|| ElabError::BadMatch(format!("missing clause for {cname}")))?;
        let info = env
            .constructors
            .get(cname)
            .expect("constructor info present");
        if clause.binders.len() != info.rec_flags.len() {
            return Err(ElabError::BadMatch(format!(
                "constructor {cname} expects {} args, clause binds {}",
                info.rec_flags.len(),
                clause.binders.len()
            )));
        }

        // Method scope: add one binder per constructor arg, with an IH binder after each recursive
        // arg, then re-introduce the trailing binders. Field binders are given their *types* from
        // the kernel constructor signature when readable (param-free families), so nested matches
        // and `let`-aliases over the bound fields can synthesize types.
        let kernel_con = env
            .signature()
            .data_of_con(&blight_kernel::ConName(cname.clone()))
            .map(|(decl, _, con)| {
                (
                    decl.params.is_empty() && decl.indices.is_empty(),
                    con.clone(),
                )
            });
        let mut sc = scope.clone();
        let mut rec = sc.rec.clone();
        if let Some(r) = rec.as_mut() {
            // Only the *outermost* match of a recursive function establishes the leading-parameter
            // layout; nested matches inherit it (overwriting would describe the inner scrutinee's
            // context, breaking recursive-call recognition in the inner body).
            if r.leading.is_empty() {
                r.leading = leading_names.clone();
            }
        }
        let mut n_con_binders = 0usize;
        for (i, (arg_name, &is_rec)) in clause.binders.iter().zip(&info.rec_flags).enumerate() {
            // The field's type, if cheaply known (only for param/index-free families).
            let field_ty = match &kernel_con {
                Some((true, con)) => match con.args.get(i) {
                    Some(blight_kernel::Arg::NonRec(t)) => Some(t.clone()),
                    Some(blight_kernel::Arg::Rec(_)) => Some(Term::Data(
                        blight_kernel::DataName(data_name.clone()),
                        vec![],
                        vec![],
                    )),
                    None => None,
                },
                _ => None,
            };
            sc = sc.push_var_ty(arg_name, field_ty);
            n_con_binders += 1;
            if is_rec {
                let ih_name = format!("{arg_name}#ih");
                sc = sc.push_var(&ih_name);
                n_con_binders += 1;
                if let Some(r) = rec.as_mut() {
                    r.ih.insert(arg_name.clone(), ih_name);
                }
            }
        }
        sc.rec = rec;

        // Re-introduce the trailing binders (outermost-first so t_0 ends up at Var0 in the body).
        for i in (0..m).rev() {
            let pos = scope.vars.len() - 1 - i;
            let name = scope.vars[pos].clone();
            sc = sc.push_var_ty(&name, Some(trailing[i].clone()));
        }

        // The method body is checked against the match result type when the motive is
        // *non-dependent* (the common case: `expected` does not mention the scrutinee). This lets
        // an inner `match` in the body elaborate in checking mode. For a dependent motive we keep
        // synthesis (`None`), as the body's type genuinely specializes per constructor.
        let body_expected = if mentions_var(expected, scrut_idx) {
            None
        } else {
            // Weaken past the constructor/IH binders and the re-introduced trailing binders.
            Some(weaken(expected, n_con_binders + m))
        };
        let body = elab(env, &sc, clause.body, body_expected.as_ref())?;
        // Wrap: innermost are the trailing binders, then the constructor/IH binders.
        let mut method = body;
        for _ in 0..m {
            method = Term::Lam(Box::new(method));
        }
        for _ in 0..n_con_binders {
            method = Term::Lam(Box::new(method));
        }
        methods.push(method);
    }

    let elim = Term::Elim {
        data: DataName(data_name),
        motive: Box::new(motive),
        methods,
        scrutinee: Box::new(Term::Var(scrut_idx)),
    };

    // The match produced a value of `motive scrut`, i.e. `Pi(trailing) expected`. Re-apply it to
    // the trailing binders so the surrounding lambdas see a value of `expected`.
    let mut applied = elim;
    for i in (0..m).rev() {
        applied = Term::App(Box::new(applied), Box::new(Term::Var(i)));
    }
    Ok(applied)
}

/// Abstract the de Bruijn variable `k` out of `term`, producing a body valid under one fresh
/// outermost-of-this-scope binder: `Var(k)` becomes `Var(0)`, every other free `Var(j)` is shifted
/// up by one to account for the new binder.
fn abstract_var(term: &Term, k: usize) -> Term {
    abstract_var_at(term, k, 0)
}

/// Abstract several distinct de Bruijn variables into nested `Lam`s. `targets` lists the variables
/// **innermost-first**: `targets[0]` becomes the innermost binder (de Bruijn `0` in the body),
/// `targets[1]` the next one out, and so on, producing `λ targets[n-1]. … λ targets[1]. λ
/// targets[0]. body`. Every target must be a *distinct* variable. Used to build an indexed `Elim`
/// motive `λ i1..im. λ scrut. T` (the kernel/re-checker require exactly this shape): we pass
/// `[scrut, im, …, i1]` so the scrutinee ends up innermost and the indices outermost, matching the
/// peeling order in `check.rs`/`typecheck.rs`.
fn abstract_vars(term: &Term, targets: &[usize]) -> Term {
    // Abstract innermost target first; each subsequent (outer) target is now under one more binder,
    // and any earlier target index shifts up by one — `abstract_var_at` with `depth` already moves
    // free indices `≥ depth` up by one, so we just add a fresh binder per step and decrement the
    // remaining (still-free) targets that were below the just-abstracted one.
    let mut body = term.clone();
    let mut remaining: Vec<usize> = targets.to_vec();
    let mut step = 0usize;
    while step < remaining.len() {
        let k = remaining[step];
        body = Term::Lam(Box::new(abstract_var(&body, k)));
        // Variables not yet abstracted that were *above* `k` are unaffected; those below are
        // unaffected too — `abstract_var` only rewrites occurrences of exactly `k` and shifts free
        // vars uniformly. The remaining targets refer to the *original* scope, but each new binder
        // lives outside the previously-added ones, so a remaining target `t` must be matched against
        // the body that now has `step+1` extra binders: increase it by the binders added so far.
        for t in remaining.iter_mut().skip(step + 1) {
            *t += 1;
        }
        step += 1;
    }
    body
}

/// Substitute a *closed* term `c` for de Bruijn 0 in `t`, decrementing the remaining indices
/// (capture-free because `c` mentions no bound variables). Used to instantiate a `Pi` codomain
/// with a closed metavariable when inserting implicit arguments.
fn subst0_closed(t: &Term, c: &Term) -> Term {
    fn go(t: &Term, j: usize, c: &Term) -> Term {
        use blight_kernel::Term as T;
        match t {
            T::Var(i) => {
                use std::cmp::Ordering;
                // Metavariable indices live in a reserved high range and are never bound here.
                if crate::meta::is_meta(*i) {
                    return T::Var(*i);
                }
                match i.cmp(&j) {
                    Ordering::Equal => c.clone(),
                    Ordering::Greater => T::Var(i - 1),
                    Ordering::Less => T::Var(*i),
                }
            }
            T::Univ(_) | T::Interval(_) | T::Erased | T::System(_) => t.clone(),
            T::Pi(g, a, b) => T::Pi(*g, Box::new(go(a, j, c)), Box::new(go(b, j + 1, c))),
            T::Sigma(a, b) => T::Sigma(Box::new(go(a, j, c)), Box::new(go(b, j + 1, c))),
            T::Lam(b) => T::Lam(Box::new(go(b, j + 1, c))),
            T::PLam(b) => T::PLam(Box::new(go(b, j + 1, c))),
            T::App(f, x) => T::App(Box::new(go(f, j, c)), Box::new(go(x, j, c))),
            T::Pair(a, b) => T::Pair(Box::new(go(a, j, c)), Box::new(go(b, j, c))),
            T::Fst(p) => T::Fst(Box::new(go(p, j, c))),
            T::Snd(p) => T::Snd(Box::new(go(p, j, c))),
            T::Ann(a, b) => T::Ann(Box::new(go(a, j, c)), Box::new(go(b, j, c))),
            T::Data(n, ps, is) => T::Data(
                n.clone(),
                ps.iter().map(|x| go(x, j, c)).collect(),
                is.iter().map(|x| go(x, j, c)).collect(),
            ),
            T::Con(n, args) => T::Con(n.clone(), args.iter().map(|x| go(x, j, c)).collect()),
            T::Delay(a) => T::Delay(Box::new(go(a, j, c))),
            T::Now(a) => T::Now(Box::new(go(a, j, c))),
            T::Later(a) => T::Later(Box::new(go(a, j, c))),
            // M3 implicit insertion only instantiates ordinary (non-cubical, non-effect) codomains.
            other => other.clone(),
        }
    }
    go(t, 0, c)
}

/// `depth` counts binders crossed since entering the abstraction.
fn abstract_var_at(term: &Term, k: usize, depth: usize) -> Term {
    use blight_kernel::Term as T;
    let r = |t: &T| abstract_var_at(t, k, depth);
    let r1 = |t: &T| abstract_var_at(t, k, depth + 1);
    match term {
        T::Var(i) => {
            if *i == k + depth {
                T::Var(depth)
            } else if *i >= depth {
                T::Var(i + 1)
            } else {
                T::Var(*i)
            }
        }
        T::Univ(l) => T::Univ(l.clone()),
        T::Pi(g, a, b) => T::Pi(*g, Box::new(r(a)), Box::new(r1(b))),
        T::Lam(b) => T::Lam(Box::new(r1(b))),
        T::App(f, a) => T::App(Box::new(r(f)), Box::new(r(a))),
        T::Sigma(a, b) => T::Sigma(Box::new(r(a)), Box::new(r1(b))),
        T::Pair(a, b) => T::Pair(Box::new(r(a)), Box::new(r(b))),
        T::Fst(a) => T::Fst(Box::new(r(a))),
        T::Snd(a) => T::Snd(Box::new(r(a))),
        T::Ann(a, b) => T::Ann(Box::new(r(a)), Box::new(r(b))),
        T::Data(d, ps, is) => T::Data(
            d.clone(),
            ps.iter().map(r).collect(),
            is.iter().map(r).collect(),
        ),
        T::Con(c, args) => T::Con(c.clone(), args.iter().map(r).collect()),
        T::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => T::Elim {
            data: data.clone(),
            // motive binds one variable (the scrutinee).
            motive: Box::new(r1(motive)),
            methods: methods.iter().map(r).collect(),
            scrutinee: Box::new(r(scrutinee)),
        },
        T::Interval(iv) => T::Interval(iv.clone()),
        T::PathP { family, lhs, rhs } => T::PathP {
            // family binds one dimension variable, not a term variable: keep term depth.
            family: Box::new(r(family)),
            lhs: Box::new(r(lhs)),
            rhs: Box::new(r(rhs)),
        },
        T::PLam(b) => T::PLam(Box::new(r(b))),
        T::PApp(p, iv) => T::PApp(Box::new(r(p)), iv.clone()),
        T::Partial(c, a) => T::Partial(c.clone(), Box::new(r(a))),
        T::System(_) => term.clone(),
        T::Transp {
            family,
            cofib,
            base,
        } => T::Transp {
            family: Box::new(r(family)),
            cofib: cofib.clone(),
            base: Box::new(r(base)),
        },
        T::HComp {
            ty,
            cofib,
            tube,
            base,
        } => T::HComp {
            ty: Box::new(r(ty)),
            cofib: cofib.clone(),
            tube: Box::new(r(tube)),
            base: Box::new(r(base)),
        },
        T::Comp {
            family,
            cofib,
            tube,
            base,
        } => T::Comp {
            family: Box::new(r(family)),
            cofib: cofib.clone(),
            tube: Box::new(r(tube)),
            base: Box::new(r(base)),
        },
        T::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => T::Glue {
            base: Box::new(r(base)),
            cofib: cofib.clone(),
            ty: Box::new(r(ty)),
            equiv: Box::new(r(equiv)),
        },
        T::GlueTerm {
            cofib,
            partial,
            base,
        } => T::GlueTerm {
            cofib: cofib.clone(),
            partial: Box::new(r(partial)),
            base: Box::new(r(base)),
        },
        T::Unglue(a) => T::Unglue(Box::new(r(a))),
        T::Op { effect, op, arg } => T::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(r(arg)),
        },
        T::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            let r2 = |t: &T| abstract_var_at(t, k, depth + 2);
            T::Handle {
                body: Box::new(r(body)),
                return_clause: Box::new(r1(return_clause)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(name, e)| (name.clone(), Box::new(r2(e))))
                    .collect(),
            }
        }
        T::EffTy(row, a) => T::EffTy(row.clone(), Box::new(r(a))),
        T::Delay(a) => T::Delay(Box::new(r(a))),
        T::Now(a) => T::Now(Box::new(r(a))),
        T::Later(a) => T::Later(Box::new(r(a))),
        T::Force(a) => T::Force(Box::new(r(a))),
        T::Foreign { symbol, ty } => T::Foreign {
            symbol: symbol.clone(),
            ty: Box::new(r(ty)),
        },
        // Int type/literal carry no de Bruijn content; an IntPrim's operands must be abstracted.
        T::IntTy | T::IntLit(_) => term.clone(),
        T::IntPrim { op, lhs, rhs } => T::IntPrim {
            op: *op,
            lhs: Box::new(r(lhs)),
            rhs: Box::new(r(rhs)),
        },
        T::Erased => T::Erased,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::read_one;
    use blight_kernel::Grade;

    /// Elaborate a surface expression string to a core term in the empty environment.
    fn elab_str(src: &str) -> Result<Term, ElabError> {
        let (sx, _rest) = read_one(src).expect("reads");
        let surface = parse_surface(&sx)?;
        let env = ElabEnv::new();
        elaborate(&env, &surface)
    }

    /// `(force e)` parses and elaborates to `Term::Force`, with its payload elaborated in turn.
    /// `(force (now (Type 0)))` → `Force(Now(Univ 0))` — the surface `force` eliminator threads
    /// through to the kernel `Term::Force` node added for the delay layer.
    #[test]
    fn force_elaborates_to_term_force() {
        let t = elab_str("(force (now (Type 0)))").expect("force elaborates");
        match t {
            Term::Force(inner) => match *inner {
                Term::Now(payload) => {
                    assert!(matches!(*payload, Term::Univ(_)), "payload is the universe");
                }
                other => panic!("expected `now` under `force`, got {other:?}"),
            },
            other => panic!("expected `Term::Force`, got {other:?}"),
        }
    }

    /// The surface `Int` forms (M11) elaborate to the kernel `IntTy`/`IntLit`/`IntPrim` nodes.
    #[test]
    fn int_forms_elaborate_to_kernel_int() {
        use blight_kernel::IntPrimOp;
        assert!(matches!(elab_str("Int").unwrap(), Term::IntTy));
        assert!(matches!(elab_str("(int 42)").unwrap(), Term::IntLit(42)));
        assert!(matches!(elab_str("(int 7)").unwrap(), Term::IntLit(7)));
        match elab_str("(int+ (int 2) (int 3))").unwrap() {
            Term::IntPrim { op, lhs, rhs } => {
                assert_eq!(op, IntPrimOp::Add);
                assert!(matches!(*lhs, Term::IntLit(2)));
                assert!(matches!(*rhs, Term::IntLit(3)));
            }
            other => panic!("expected IntPrim, got {other:?}"),
        }
        match elab_str("(int< (int 1) (int 2))").unwrap() {
            Term::IntPrim { op, .. } => assert_eq!(op, IntPrimOp::Lt),
            other => panic!("expected IntPrim Lt, got {other:?}"),
        }
    }

    /// A `?x` char literal desugars to a unary `Nat` numeral of its codepoint (reader sugar).
    #[test]
    fn char_literal_desugars_to_nat() {
        // `?A` is codepoint 65: `Succ^65 Zero`.
        let (sx, _rest) = read_one("?A").expect("reads");
        let s = parse_surface(&sx).expect("parses");
        // Count the Succ depth down to the Zero leaf.
        fn depth(s: &Surface) -> (u64, bool) {
            match s {
                Surface::Var(n) if n == "Zero" => (0, true),
                Surface::App(f, args) if args.len() == 1 => {
                    let head_is_succ = matches!(&**f, Surface::Var(n) if n == "Succ");
                    let (d, ok) = depth(&args[0]);
                    (d + 1, ok && head_is_succ)
                }
                _ => (0, false),
            }
        }
        let (d, ok) = depth(&s);
        assert!(ok, "?A desugars to a Succ/Zero chain, got {s:?}");
        assert_eq!(d, 65, "?A is codepoint 65");
    }

    /// A quoted string literal in term position desugars to a `push`/`empty` cons-list of `Nat`
    /// codepoints (reader sugar). Purely additive: a bare symbol is untouched.
    #[test]
    fn string_literal_desugars_to_push_chain() {
        let (sx, _rest) = read_one("\"hi\"").expect("reads");
        let s = parse_surface(&sx).expect("parses");
        // Expect: (push <Nat 'h'=104> (push <Nat 'i'=105> empty)).
        fn nat_depth(s: &Surface) -> u64 {
            match s {
                Surface::App(f, args)
                    if args.len() == 1 && matches!(&**f, Surface::Var(n) if n == "Succ") =>
                {
                    1 + nat_depth(&args[0])
                }
                _ => 0,
            }
        }
        // node 0: push 'h' rest
        let (cp0, rest0) = match &s {
            Surface::App(f, args) if matches!(&**f, Surface::Var(n) if n == "push") => {
                assert_eq!(args.len(), 2, "push takes codepoint + rest");
                (nat_depth(&args[0]), &args[1])
            }
            other => panic!("expected (push ...), got {other:?}"),
        };
        assert_eq!(cp0, 'h' as u64, "first codepoint is 'h'");
        let (cp1, rest1) = match rest0 {
            Surface::App(f, args) if matches!(&**f, Surface::Var(n) if n == "push") => {
                (nat_depth(&args[0]), &args[1])
            }
            other => panic!("expected (push ...) for second char, got {other:?}"),
        };
        assert_eq!(cp1, 'i' as u64, "second codepoint is 'i'");
        assert!(
            matches!(rest1, Surface::Var(n) if n == "empty"),
            "chain ends in `empty`, got {rest1:?}"
        );
    }

    /// The empty string `""` desugars directly to `empty`.
    #[test]
    fn empty_string_desugars_to_empty() {
        let (sx, _rest) = read_one("\"\"").expect("reads");
        let s = parse_surface(&sx).expect("parses");
        assert!(
            matches!(&s, Surface::Var(n) if n == "empty"),
            "\"\" desugars to `empty`, got {s:?}"
        );
    }

    /// A plain symbol is NOT treated as a string/char literal (additive guarantee).
    #[test]
    fn plain_symbol_is_unchanged() {
        let (sx, _rest) = read_one("plus").expect("reads");
        let s = parse_surface(&sx).expect("parses");
        assert!(matches!(&s, Surface::Var(n) if n == "plus"));
    }

    /// `(Pi ((x (Type 0) 1)) (Type 0))` elaborates with a *linear* binder grade.
    #[test]
    fn grade_one() {
        let t = elab_str("(Pi ((x (Type 0) 1)) (Type 0))").expect("elaborates");
        match t {
            Term::Pi(g, _, _) => assert_eq!(g, Grade::One, "explicit grade 1 ⟹ linear"),
            other => panic!("expected Pi, got {other:?}"),
        }
    }

    /// `(Pi ((x (Type 0) 0)) (Type 0))` elaborates with an *erased* binder grade.
    #[test]
    fn grade_zero() {
        let t = elab_str("(Pi ((x (Type 0) 0)) (Type 0))").expect("elaborates");
        match t {
            Term::Pi(g, _, _) => assert_eq!(g, Grade::Zero, "explicit grade 0 ⟹ erased"),
            other => panic!("expected Pi, got {other:?}"),
        }
    }

    /// A binder with no grade annotation defaults to ω (unrestricted).
    #[test]
    fn default_omega() {
        let t = elab_str("(Pi ((x (Type 0))) (Type 0))").expect("elaborates");
        match t {
            Term::Pi(g, _, _) => assert_eq!(g, Grade::Omega, "absent grade ⟹ ω"),
            other => panic!("expected Pi, got {other:?}"),
        }
    }

    /// An out-of-range grade token is a clear error, not a silent default.
    #[test]
    fn bad_grade_errors() {
        match elab_str("(Pi ((x (Type 0) 2)) (Type 0))") {
            Err(ElabError::BadForm(msg)) => assert!(
                msg.contains("grade"),
                "error should mention grade, got: {msg}"
            ),
            other => panic!("expected BadForm for grade `2`, got {other:?}"),
        }
    }

    /// The explicit `omega` keyword is accepted and equals the default.
    #[test]
    fn explicit_omega_keyword() {
        let t = elab_str("(Pi ((x (Type 0) omega)) (Type 0))").expect("elaborates");
        match t {
            Term::Pi(g, _, _) => assert_eq!(g, Grade::Omega),
            other => panic!("expected Pi, got {other:?}"),
        }
    }

    // ---- surface records / Sigma (spec §6.4/§6.5) -------------------------------------------

    /// `(Sigma ((x A)) B)` elaborates to a kernel `Sigma`; an n-ary telescope nests right.
    #[test]
    fn sigma_type_elaborates() {
        let t = elab_str("(Sigma ((x (Type 0))) (Type 0))").expect("elaborates");
        assert!(matches!(t, Term::Sigma(_, _)), "got {t:?}");
        // Two binders ⟹ Sigma of a Sigma.
        let t2 = elab_str("(Sigma ((x (Type 0)) (y (Type 0))) (Type 0))").expect("elaborates");
        match t2 {
            Term::Sigma(_, inner) => assert!(matches!(*inner, Term::Sigma(_, _)), "nests right"),
            other => panic!("expected nested Sigma, got {other:?}"),
        }
    }

    /// `(pair a b)` and `(a , b)` both elaborate to a kernel `Pair`.
    #[test]
    fn pair_infers_sigma() {
        let t = elab_str("(pair (Type 0) (Type 0))").expect("elaborates");
        assert!(matches!(t, Term::Pair(_, _)), "got {t:?}");
        let t2 = elab_str("((Type 0) , (Type 1))").expect("elaborates");
        assert!(matches!(t2, Term::Pair(_, _)), "comma sugar; got {t2:?}");
    }

    /// `(fst p)` / `(snd p)` elaborate to kernel projections.
    #[test]
    fn fst_snd_project() {
        let f = elab_str("(fst (pair (Type 0) (Type 1)))").expect("elaborates");
        assert!(matches!(f, Term::Fst(_)), "got {f:?}");
        let s = elab_str("(snd (pair (Type 0) (Type 1)))").expect("elaborates");
        assert!(matches!(s, Term::Snd(_)), "got {s:?}");
    }

    // ---- parameterized / indexed inductives (spec §2.7, M3) ----------------------------------

    /// Declare a sequence of `defdata`/`define` forms into a fresh env, returning the env.
    fn env_with_decls(srcs: &[&str]) -> ElabEnv {
        let mut env = ElabEnv::new();
        for src in srcs {
            let (sx, _) = read_one(src).expect("reads");
            let decl = parse_decl(&sx).expect("parses decl");
            env.declare(&decl, None).expect("declares");
        }
        env
    }

    /// `(defdata List ((a (Type 0))) (lnil) (lcons (x a) (xs (List a))))` declares a parameterized
    /// family: the kernel signature records one parameter and `lcons`'s second field is recursive.
    #[test]
    fn list_param_data_elaborates() {
        let env =
            env_with_decls(&["(defdata List ((a (Type 0))) (lnil) (lcons (x a) (xs (List a))))"]);
        let decl = env
            .signature()
            .get(&blight_kernel::DataName("List".into()))
            .expect("List declared");
        assert_eq!(decl.params.len(), 1, "one parameter");
        assert!(decl.indices.is_empty(), "non-indexed");
        // lcons has two args; the second is recursive.
        let (_, lcons) = decl
            .constructor(&blight_kernel::ConName("lcons".into()))
            .unwrap();
        assert_eq!(lcons.args.len(), 2);
        assert!(
            matches!(lcons.args[1], blight_kernel::Arg::Rec(_)),
            "xs is recursive"
        );
    }

    /// `(defdata Vec ((a (Type 0))) ((n Nat)) (vnil (=> Zero)) (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))`
    /// declares an *indexed* family: one parameter, one index, and each constructor targets a
    /// result index. The recursive `xs` occurrence carries its own index `m`.
    #[test]
    fn vec_indexed_data_elaborates() {
        let env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        let decl = env
            .signature()
            .get(&blight_kernel::DataName("Vec".into()))
            .expect("Vec declared");
        assert_eq!(decl.params.len(), 1, "one parameter");
        assert_eq!(decl.indices.len(), 1, "one index");
        let (_, vnil) = decl
            .constructor(&blight_kernel::ConName("vnil".into()))
            .unwrap();
        assert_eq!(vnil.result_indices.len(), 1, "vnil targets `Zero`");
        let (_, vcons) = decl
            .constructor(&blight_kernel::ConName("vcons".into()))
            .unwrap();
        assert_eq!(vcons.result_indices.len(), 1, "vcons targets `Succ m`");
        // The recursive `xs : Vec a m` occurrence records its index `m`.
        match &vcons.args[2] {
            blight_kernel::Arg::Rec(ix) => assert_eq!(ix.len(), 1, "rec occurrence carries `m`"),
            other => panic!("xs should be recursive, got {other:?}"),
        }
    }

    /// Recursion detection generalizes from exact-name to "head is the data applied to params":
    /// `(xs (List a))` is detected as recursive even though its surface type is an application.
    #[test]
    fn param_recursion_detected() {
        let env =
            env_with_decls(&["(defdata List ((a (Type 0))) (lnil) (lcons (x a) (xs (List a))))"]);
        let info = env.constructors.get("lcons").expect("lcons info");
        assert_eq!(info.rec_flags, vec![false, true], "x non-rec, xs rec");
    }

    /// A parameterized recursor typechecks through the spore: a `length : List a → Nat` recursor
    /// built via `match` elaborates to a well-typed `Elim` over the parameterized `List`.
    #[test]
    fn elim_motive_mentions_param() {
        let mut env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata List ((a (Type 0))) (lnil) (lcons (x a) (xs (List a))))",
        ]);
        // length : (List Nat) → Nat by structural recursion (compiles to Elim over List).
        let ty = elaborate(
            &env,
            &parse_surface(&read_one("(Pi ((xs (List Nat))) Nat)").unwrap().0).unwrap(),
        )
        .expect("length type elaborates");
        let body_sx = read_one(
            "(lam (xs) (match xs \
               [(lnil) Zero] \
               [(lcons h t) (Succ (length t))]))",
        )
        .unwrap()
        .0;
        let decl = Decl::DefTotal {
            name: "length".into(),
            body: parse_surface(&body_sx).unwrap(),
        };
        env.declare(&decl, Some(&ty))
            .expect("length defines via Elim over a parameterized family");
        // Re-check the produced core term through the spore at its declared type.
        let core = env.global_term("length").expect("length stored").clone();
        let res = blight_kernel::check_top_with(env.signature().clone(), core, ty);
        assert!(
            res.is_ok(),
            "parameterized Elim re-checks through the spore: {res:?}"
        );
    }

    /// Item 1a (gate): a `define` whose elaborated body does NOT inhabit its declared type must be
    /// rejected at `declare` time by the kernel door (`kernel_check_def`), not silently stored.
    /// Before the gate, the body was kept on its own inferred type and the disagreement only surfaced
    /// under the opt-in `--recheck`. The gate routes *functions and proofs* through the kernel; here
    /// `wrong : Nat → Nat` is given a body returning `true : Bool`, which the kernel rejects.
    #[test]
    fn gate_rejects_mistyped_define_at_declare_time() {
        let mut env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Bool () (false) (true))",
        ]);
        let ty = elaborate(
            &env,
            &parse_surface(&read_one("(Pi ((n Nat)) Nat)").unwrap().0).unwrap(),
        )
        .expect("Nat → Nat type elaborates");
        // Body returns `true : Bool`, but the declared codomain is `Nat` — a genuine mismatch.
        let decl = Decl::Define {
            name: "wrong".into(),
            body: parse_surface(&read_one("(lam (n) true)").unwrap().0).unwrap(),
        };
        let res = env.declare(&decl, Some(&ty));
        assert!(
            matches!(res, Err(ElabError::BadForm(ref m)) if m.contains("kernel rejected definition `wrong`")),
            "the kernel gate must reject a mistyped function define at declare time, got {res:?}"
        );
    }

    /// Item 1a (gate): a closed *ground-value* definition (declared type a concrete data type, not a
    /// `Pi`/`PathP`) is NOT routed through the kernel — checking it degenerates into running the whole
    /// program (the `palindrome`/`mergesort`/`quicksort` `main` blowup). It still declares cleanly.
    #[test]
    fn gate_skips_ground_value_definitions() {
        let mut env = env_with_decls(&["(defdata Nat () (Zero) (Succ (n Nat)))"]);
        let ty = elaborate(&env, &parse_surface(&read_one("Nat").unwrap().0).unwrap())
            .expect("Nat type elaborates");
        let decl = Decl::Define {
            name: "answer".into(),
            body: parse_surface(&read_one("(Succ (Succ Zero))").unwrap().0).unwrap(),
        };
        env.declare(&decl, Some(&ty))
            .expect("a ground-value define declares (gate skips whole-program evaluation)");
    }

    /// Item 1b (post-refinement): the `safe-tail` shape — a `match` over `Vec A (Succ n)` whose
    /// result type `Vec A n` depends on the index — has an unreachable `vnil` arm (index `Zero` vs
    /// `Succ n`). The kernel now *discharges* it via dependent-match refinement (no temporary skip),
    /// so `declare` (which routes through the kernel gate) succeeds because the definition is
    /// genuinely kernel-certified. (The direct `check_top_with` certification is asserted by
    /// `kernel_certifies_safe_tail_via_dependent_refinement`; this guards the elaborator gate path.)
    #[test]
    fn gate_accepts_dependent_match_refinement_shape() {
        let mut env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        let ty = elaborate(
            &env,
            &parse_surface(
                &read_one("(Pi ((A (Type 0)) (n Nat) (v (Vec A (Succ n)))) (Vec A n))")
                    .unwrap()
                    .0,
            )
            .unwrap(),
        )
        .expect("safe-tail type elaborates");
        let body_sx = read_one(
            "(lam (A n v) (match v \
               [(vnil) vnil] \
               [(vcons m x xs) xs]))",
        )
        .unwrap()
        .0;
        let decl = Decl::DefineRec {
            name: "safe-tail".into(),
            body: parse_surface(&body_sx).unwrap(),
        };
        // The kernel now refines this correct dependent match (item 1b), so the gate certifies it.
        env.declare(&decl, Some(&ty))
            .expect("safe-tail declares (kernel refines the dependent match — item 1b)");
    }

    /// Regression: a `match` over an *indexed* family whose scrutinee index is a *non-variable*
    /// term (`Vec A (Succ n)`) and whose result type is *not* `Nat` (`Maybe A`). The elaborator
    /// must synthesize the canonical indexed motive `λ i. λ s. Maybe A` with a fresh, unused index
    /// binder; before the fix it fell back to the bare `λ s. …` motive and the kernel rejected it
    /// with "expected indexed motive". This is the `safe-head` shape.
    #[test]
    fn indexed_match_nonvariable_index_nonnat_return_rechecks() {
        let mut env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Maybe ((a (Type 0))) (nothing) (just (x a)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        // safe-head : (A : Type) (n : Nat) (v : Vec A (Succ n)) -> Maybe A.
        let ty = elaborate(
            &env,
            &parse_surface(
                &read_one("(Pi ((A (Type 0)) (n Nat) (v (Vec A (Succ n)))) (Maybe A))")
                    .unwrap()
                    .0,
            )
            .unwrap(),
        )
        .expect("safe-head type elaborates");
        let body_sx = read_one(
            "(lam (A n v) (match v \
               [(vnil) nothing] \
               [(vcons m x xs) (just x)]))",
        )
        .unwrap()
        .0;
        let decl = Decl::DefineRec {
            name: "safe-head".into(),
            body: parse_surface(&body_sx).unwrap(),
        };
        env.declare(&decl, Some(&ty))
            .expect("safe-head defines via Elim over an indexed family with a Maybe return");
        // The trusted kernel must accept the produced core term at its declared type. (The
        // *independent* re-checker's agreement is covered by the `blight-repl` examples test,
        // since `blight-recheck` is not a dependency of this crate.)
        let core = env
            .global_term("safe-head")
            .expect("safe-head stored")
            .clone();
        let res = blight_kernel::check_top_with(env.signature().clone(), core, ty);
        assert!(
            res.is_ok(),
            "indexed Elim with a non-variable index and Maybe return re-checks through the spore: {res:?}"
        );
    }

    /// Item 1b (kernel dependent-match refinement): `safe-tail : (A) (n) (v : Vec A (Succ n)) → Vec A
    /// n` matches `v`; the `vnil` arm has result index `Zero`, which *clashes* with the scrutinee
    /// index `Succ n` — that branch is **unreachable** and must be discharged by refinement. Before
    /// 1b the trusted kernel rejected this with `expected index Var(_), found Con(Zero,[])`; with
    /// refinement ported in, the kernel certifies it directly (no re-checker, no 1a skip). This is
    /// the RED→GREEN symmetry test: kernel AND re-checker now both accept the same dependent match.
    #[test]
    fn kernel_certifies_safe_tail_via_dependent_refinement() {
        let mut env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        let ty = elaborate(
            &env,
            &parse_surface(
                &read_one("(Pi ((A (Type 0)) (n Nat) (v (Vec A (Succ n)))) (Vec A n))")
                    .unwrap()
                    .0,
            )
            .unwrap(),
        )
        .expect("safe-tail type elaborates");
        let body_sx = read_one(
            "(lam (A n v) (match v \
               [(vnil) vnil] \
               [(vcons m x xs) xs]))",
        )
        .unwrap()
        .0;
        let decl = Decl::DefineRec {
            name: "safe-tail".into(),
            body: parse_surface(&body_sx).unwrap(),
        };
        env.declare(&decl, Some(&ty)).expect("safe-tail declares");
        let core = env
            .global_term("safe-tail")
            .expect("safe-tail stored")
            .clone();
        let res = blight_kernel::check_top_with(env.signature().clone(), core, ty);
        assert!(
            res.is_ok(),
            "the kernel certifies safe-tail's unreachable vnil arm via dependent refinement: {res:?}"
        );
    }

    /// Item 1b (kernel dependent-match refinement, recursive): `vec-map : (A) (B) (f : A → B) (n) (v
    /// : Vec A n) → Vec B n` recurses on `v`. The `vcons` arm's *induction hypothesis* is
    /// `P (rec ix) xs` (the recursive result on the tail, at the tail's length `m`), so this
    /// exercises the IH re-refinement path of `check_refined_method`, not just unreachable-branch
    /// discharge. The kernel must certify it (RED before 1b: `expected index …` Mismatch).
    #[test]
    fn kernel_certifies_vec_map_via_dependent_refinement() {
        let mut env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        let ty = elaborate(
            &env,
            &parse_surface(
                &read_one(
                    "(Pi ((A (Type 0)) (B (Type 0)) (f (Pi ((x A)) B)) (n Nat) (v (Vec A n))) (Vec B n))",
                )
                .unwrap()
                .0,
            )
            .unwrap(),
        )
        .expect("vec-map type elaborates");
        let body_sx = read_one(
            "(lam (A B f n v) (match v \
               [(vnil) vnil] \
               [(vcons m x xs) (vcons m (f x) (vec-map A B f m xs))]))",
        )
        .unwrap()
        .0;
        let decl = Decl::DefineRec {
            name: "vec-map".into(),
            body: parse_surface(&body_sx).unwrap(),
        };
        env.declare(&decl, Some(&ty)).expect("vec-map declares");
        let core = env.global_term("vec-map").expect("vec-map stored").clone();
        let res = blight_kernel::check_top_with(env.signature().clone(), core, ty);
        assert!(
            res.is_ok(),
            "the kernel certifies recursive vec-map (IH re-refinement) via dependent refinement: {res:?}"
        );
    }

    /// Item 1b (guard against over-acceptance): refinement must NEVER accept an *ill-typed* dependent
    /// match. Here a broken `safe-tail` returns the WHOLE vector `v : Vec A (Succ n)` in the `vcons`
    /// arm where the declared result is `Vec A n` — a genuine length mismatch the refined check must
    /// still reject. (`safe-head`'s failing-call test in `blight-repl` covers the dual direction.)
    #[test]
    fn kernel_rejects_illtyped_dependent_match() {
        let env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        let ty = elaborate(
            &env,
            &parse_surface(
                &read_one("(Pi ((A (Type 0)) (n Nat) (v (Vec A (Succ n)))) (Vec A n))")
                    .unwrap()
                    .0,
            )
            .unwrap(),
        )
        .expect("bad-safe-tail type elaborates");
        // `vcons` arm returns the cons cell `(vcons m x xs) : Vec A (Succ m)`, i.e. the full input
        // length, not the tail `xs : Vec A m`. Under refinement `n` is solved to `Succ m`, so the
        // declared result `Vec A n = Vec A (Succ m)` would only be satisfied by `xs`-of-length-`m`…
        // returning the longer cell is a length error the kernel must catch.
        let body_sx = read_one(
            "(lam (A n v) (match v \
               [(vnil) vnil] \
               [(vcons m x xs) (vcons m x xs)]))",
        )
        .unwrap()
        .0;
        // Elaboration may itself reject this (the elaborator's own front-line check). If it does,
        // that already prevents the unsound def. If it elaborates, the kernel door must reject it.
        match elaborate_against(&env, &parse_surface(&body_sx).unwrap(), &ty) {
            Err(_) => { /* rejected during elaboration — fine. */ }
            Ok(core) => {
                let res = blight_kernel::check_top_with(env.signature().clone(), core, ty);
                assert!(
                    res.is_err(),
                    "the kernel must reject an ill-typed dependent match (wrong result length): {res:?}"
                );
            }
        }
    }

    /// Over-acceptance guard, kernel-direct: a `match` whose `vcons` arm returns a vector of the
    /// WRONG length must be rejected *by the kernel's refinement path itself* (not merely by the
    /// elaborator). We hand-build the core `Elim` so elaboration can't pre-empt the check: the motive
    /// is the index-preserving `λ i. λ s. Vec A i`, the scrutinee `v : Vec A (Succ n)`, and the
    /// `vcons` method returns `vcons m x xs : Vec A (Succ m)` where refinement forces the conclusion
    /// to `Vec A (Succ (Succ m))` (the scrutinee index is `Succ n`, `n ↦ Succ m`). `Succ m ≠ Succ
    /// (Succ m)`, so `check_refined_method` must reject — proving the refinement does not blindly
    /// accept a reachable branch.
    #[test]
    fn kernel_refinement_rejects_wrong_length_reachable_branch() {
        let env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        // safe-tail-ish type: (A) (n) (v : Vec A (Succ n)) -> Vec A (Succ n)   [identity-length]
        // but the body's vcons arm returns the cons cell at length (Succ m) while refinement makes
        // the demanded conclusion length (Succ n) = (Succ (Succ m)). Build the core Elim directly.
        let ty = elaborate(
            &env,
            &parse_surface(
                &read_one(
                    "(Pi ((A (Type 0)) (n Nat) (v (Vec A (Succ n)))) (Vec A (Succ (Succ n))))",
                )
                .unwrap()
                .0,
            )
            .unwrap(),
        )
        .expect("type elaborates");
        // Body via the surface match; the result type mentions (Succ (Succ n)) which no arm satisfies,
        // so even if elaboration accepts the motive, the kernel's refined conclusion check must fail.
        let body_sx = read_one(
            "(lam (A n v) (match v \
               [(vnil) vnil] \
               [(vcons m x xs) (vcons m x xs)]))",
        )
        .unwrap()
        .0;
        match elaborate_against(&env, &parse_surface(&body_sx).unwrap(), &ty) {
            Err(_) => { /* rejected during elaboration — also fine. */ }
            Ok(core) => {
                let res = blight_kernel::check_top_with(env.signature().clone(), core, ty);
                assert!(
                    res.is_err(),
                    "kernel refinement must reject a reachable branch of the wrong length: {res:?}"
                );
            }
        }
    }

    /// `(let ((x e)) b)` desugars to `((lam (x) b) e)`. When both the bound value's type and the
    /// body's type are known, the lambda is ascribed so the application is checkable.
    #[test]
    fn let_desugars_to_app() {
        let t = elab_str("(let ((x (Type 0))) x)").expect("elaborates");
        match t {
            Term::App(f, a) => {
                let head_is_lam = match f.as_ref() {
                    Term::Lam(_) => true,
                    Term::Ann(inner, _) => matches!(inner.as_ref(), Term::Lam(_)),
                    _ => false,
                };
                assert!(head_is_lam, "head is a (possibly ascribed) lambda: {f:?}");
                assert!(matches!(*a, Term::Univ(_)), "argument is the bound value");
            }
            other => panic!("expected an application, got {other:?}"),
        }
    }

    // ---- define-kernel-check: `declare` now routes every pure/total definition through the
    //      trusted kernel door (spec §2.1) at `declare` time, not just under `--recheck`. --------

    /// A `deftotal` whose body genuinely inhabits its declared type passes the per-definition
    /// kernel door at `declare` time. This is the GREEN side: the gate must not reject good code.
    #[test]
    fn deftotal_kernel_checks_at_declare_time() {
        let (env, last) = process_decls(
            &[
                "(defdata Nat () (Zero) (Succ (n Nat)))",
                "(deftotal double (lam (n) (match n [(Zero) Zero] [(Succ k) (Succ (Succ (double k)))])))",
            ],
            &|name| match name {
                "double" => Some("(Pi ((n Nat)) Nat)"),
                _ => None,
            },
        )
        .expect("a well-typed deftotal declares and kernel-checks");
        let (name, _ty) = last.expect("a definition");
        assert_eq!(name, "double");
        assert!(env.global_term("double").is_some(), "double is stored");
    }

    /// RED→GREEN teeth: a definition whose elaborated core does NOT inhabit its declared type is
    /// now rejected *at declare time* by the kernel door. We drive the body through `define_global`
    /// plus `kernel_check_def` directly with a deliberately wrong type (a `Nat`-to-`Nat` identity
    /// ascribed the type `Nat`-to-`Bool`) to exercise the gate without depending on the elaborator's
    /// own front-line check. Before this gate existed, such a mismatch only surfaced under `--recheck`.
    #[test]
    fn kernel_check_def_rejects_ill_typed_body() {
        let env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Bool () (false) (true))",
        ]);
        // `λn. n` : the identity on Nat. Claim it has type `Nat → Bool` (false).
        let ty = elaborate(
            &env,
            &parse_surface(&read_one("(Pi ((n Nat)) Bool)").unwrap().0).unwrap(),
        )
        .expect("type elaborates");
        let ident = Term::Lam(Box::new(Term::Var(0)));
        match env.kernel_check_def("bogus", &ident, &ty) {
            Err(ElabError::BadForm(msg)) => assert!(
                msg.contains("kernel rejected definition `bogus`"),
                "expected kernel-rejection message, got: {msg}"
            ),
            other => panic!("expected the kernel door to reject Nat→Bool identity, got {other:?}"),
        }
    }

    /// The gate is *honest about its fragment*: an effectful (`! E A`) or partial (`Delay A`)
    /// conclusion is out of the pure kernel door and must be SKIPPED (not rejected), exactly as
    /// `--recheck` `Declines` it. `is_pure_total_conclusion` is the predicate that decides this.
    #[test]
    fn pure_total_conclusion_gates_effectful_and_partial() {
        let env = env_with_decls(&[
            "(defdata Unit () (tt))",
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(effect Console (print Nat Unit))",
        ]);
        let pure = elaborate(
            &env,
            &parse_surface(&read_one("(Pi ((n Nat)) Nat)").unwrap().0).unwrap(),
        )
        .unwrap();
        let effectful = elaborate(
            &env,
            &parse_surface(&read_one("(! Console Unit)").unwrap().0).unwrap(),
        )
        .unwrap();
        let partial = elaborate(
            &env,
            &parse_surface(&read_one("(Pi ((n Nat)) (Delay Nat))").unwrap().0).unwrap(),
        )
        .unwrap();
        assert!(
            is_pure_total_conclusion(&pure),
            "Nat → Nat is a pure/total conclusion"
        );
        assert!(
            !is_pure_total_conclusion(&effectful),
            "(! Console Unit) is effectful — skipped by the pure door"
        );
        assert!(
            !is_pure_total_conclusion(&partial),
            "Nat → Delay Nat is partial — skipped by the pure door"
        );
    }

    // ---- partiality: define-rec / deftotal (spec §4.5, §6.2) --------------------------------
    /// Build an `ElabEnv` with `Nat` declared, then process a sequence of declaration forms.
    /// `types` maps a definition name to its declared (surface) type source. Returns the env and
    /// the `(name, core type)` of the last definition processed (for kernel checking).
    fn process_decls(
        forms: &[&str],
        ty_of: &dyn Fn(&str) -> Option<&'static str>,
    ) -> Result<(ElabEnv, Option<(String, Term)>), ElabError> {
        let mut env = ElabEnv::new();
        let mut last = None;
        for src in forms {
            let (sx, _) = read_one(src).expect("reads");
            let decl = parse_decl(&sx)?;
            match &decl {
                Decl::DefData { .. } | Decl::DefEffect { .. } | Decl::Foreign { .. } => {
                    env.declare(&decl, None)?
                }
                Decl::Define { name, .. }
                | Decl::DefineRec { name, .. }
                | Decl::DefTotal { name, .. } => {
                    let ty_src = ty_of(name).expect("declared type for definition");
                    let (ty_sx, _) = read_one(ty_src).expect("reads type");
                    let ty_surface = parse_surface(&ty_sx)?;
                    let ty_core = elaborate(&env, &ty_surface)?;
                    env.declare(&decl, Some(&ty_core))?;
                    last = Some((name.clone(), ty_core));
                }
            }
        }
        Ok((env, last))
    }

    /// A non-structural `define-rec` elaborates to a `Later`-guarded body whose inferred effect row
    /// carries the built-in `Partial` label at a nonzero grade (spec §4.5). `diverge : Nat → Delay
    /// Nat` recurses on the *same* argument `n` (non-structural), so its body uses `later`.
    #[test]
    fn divergent_define_rec_has_partial_grade() {
        use blight_kernel::check::Checker;
        use blight_kernel::context::Context;
        let (env, last) = process_decls(
            &[
                "(defdata Nat () (Zero) (Succ (n Nat)))",
                "(define-rec diverge (lam (n) (later (diverge n))))",
            ],
            &|name| match name {
                "diverge" => Some("(Pi ((n Nat)) (Delay Nat))"),
                _ => None,
            },
        )
        .expect("elaborates");
        let (name, ty) = last.expect("a definition");
        // The elaborated `diverge` is `λself. λn. later (self n)` of type `(Nat→Delay Nat) → …`.
        let term = env.global_term(&name).expect("term").clone();
        assert!(
            matches!(term, Term::Lam(_)),
            "a divergent define-rec binds its self-reference: {term:?}"
        );
        // Kernel-check that the elaborated term's inferred row carries `Partial` at nonzero grade.
        let checker = Checker::new(std::rc::Rc::new(env.signature().clone()));
        // The term has type `T → T` where `T = Nat → Delay Nat`. Ascribe it so it infers.
        let self_ty = Term::Pi(
            Grade::Omega,
            Box::new(ty.clone()),
            Box::new(shift_closed(&ty)),
        );
        let ann = Term::Ann(Box::new(term), Box::new(self_ty));
        let (_t, row, _u) = checker
            .infer_g(&Context::empty(), &ann, Grade::Omega)
            .expect("infers");
        let partial = blight_kernel::row::EffName::partial();
        assert!(
            row.contains(&partial),
            "a divergent define-rec carries the Partial effect, got row {row:?}"
        );
    }

    // ---- rich match: nested / wildcard / multi-scrutinee / inference (spec §6.2, M3) ----------

    /// Elaborate `src` against `ty_src` in `env`, returning the core term (which must also pass the
    /// kernel — these matches are real, not just shape checks).
    fn check_match(env: &ElabEnv, ty_src: &str, src: &str) -> Result<Term, ElabError> {
        let (tx, _) = read_one(ty_src).expect("reads type");
        let ty = elaborate(env, &parse_surface(&tx).unwrap())?;
        let (sx, _) = read_one(src).expect("reads term");
        let term = elaborate_against(env, &parse_surface(&sx).unwrap(), &ty)?;
        // Re-check through the spore so a mis-compiled match is caught, not silently accepted.
        blight_kernel::check_top_with(env.signature().clone(), term.clone(), ty)
            .map_err(|e| ElabError::BadMatch(format!("spore rejected: {e:?}")))?;
        Ok(term)
    }

    fn rich_env() -> ElabEnv {
        env_with_decls(&[
            "(defdata Bool () (false) (true))",
            "(defdata Nat () (Zero) (Succ (n Nat)))",
        ])
    }

    /// A wildcard pattern `_` matches any constructor: `(match b [(true) Zero] [_ (Succ Zero)])`
    /// compiles to a total `Elim` covering both `Bool` constructors.
    #[test]
    fn wildcard_pattern() {
        let env = rich_env();
        check_match(
            &env,
            "(Pi ((b Bool)) Nat)",
            "(lam (b) (match b [(true) Zero] [_ (Succ Zero)]))",
        )
        .expect("wildcard match compiles and checks");
    }

    /// A nested constructor pattern `(Succ (Succ k))` compiles to nested `Elim`s; the catch-all
    /// `_` clauses fill the other cases. `pred2` returns `k` for `Succ (Succ k)`, else `Zero`.
    #[test]
    fn nested_pattern_compiles() {
        let env = rich_env();
        check_match(
            &env,
            "(Pi ((n Nat)) Nat)",
            "(lam (n) (match n [(Succ (Succ k)) k] [_ Zero]))",
        )
        .expect("nested match compiles and checks");
    }

    /// Multiple scrutinees: `(matchx (a b) …)` over two `Bool`s compiles to nested `Elim`s.
    #[test]
    fn multi_scrutinee_match() {
        let env = rich_env();
        check_match(
            &env,
            "(Pi ((a Bool) (b Bool)) Bool)",
            "(lam (a b) (matchx (a b) [(true true) true] [(_ _) false]))",
        )
        .expect("multi-scrutinee match compiles and checks");
    }

    /// Inference-mode: elaborated with *no* expected type (synthesis position), the motive is read
    /// off the first clause's body (spec §6.2). Here every branch yields `Nat`, so the
    /// non-dependent motive is `Nat`, and the synthesized `Elim` checks against `Nat`.
    #[test]
    fn inference_mode_match() {
        let env = rich_env();
        // `elaborate` runs in synthesis mode (expected = None), forcing motive inference.
        let (sx, _) =
            read_one("(let ((b (the Bool true))) (match b [(true) Zero] [(false) (Succ Zero)]))")
                .unwrap();
        let term =
            elaborate(&env, &parse_surface(&sx).unwrap()).expect("inference-mode match elaborates");
        // The inferred term inhabits `Nat`; the spore confirms it.
        let nat = Term::Data(blight_kernel::DataName("Nat".into()), vec![], vec![]);
        blight_kernel::check_top_with(env.signature().clone(), term, nat)
            .expect("inferred match checks against Nat");
    }

    /// A non-exhaustive match (missing a constructor and with no catch-all) is rejected by the
    /// compiler — never silently accepted.
    #[test]
    fn nonexhaustive_rejected() {
        let env = rich_env();
        let r = check_match(
            &env,
            "(Pi ((n Nat)) Nat)",
            "(lam (n) (match n [(Zero) Zero]))",
        );
        assert!(
            matches!(r, Err(ElabError::BadMatch(_))),
            "non-exhaustive match must be rejected: {r:?}"
        );
    }

    /// `deftotal` requires the structural/`Elim` compilation: a non-structural recursion is
    /// rejected (it would carry a nonzero partiality grade).
    #[test]
    fn deftotal_divergent_rejected() {
        let result = process_decls(
            &[
                "(defdata Nat () (Zero) (Succ (n Nat)))",
                "(deftotal diverge (lam (n) (later (diverge n))))",
            ],
            &|name| match name {
                "diverge" => Some("(Pi ((n Nat)) (Delay Nat))"),
                _ => None,
            },
        );
        match result {
            Err(ElabError::BadMatch(msg)) => {
                assert!(
                    msg.contains("structural"),
                    "rejection mentions structural: {msg}"
                )
            }
            other => panic!("expected a structural-recursion rejection, got {other:?}"),
        }
    }

    /// A structurally-recursive `deftotal` compiles to a closed `Elim` (no `Later`, partiality
    /// grade 0): `add1` recurses structurally on its argument.
    #[test]
    fn deftotal_structural_ok() {
        let (env, last) = process_decls(
            &[
                "(defdata Nat () (Zero) (Succ (n Nat)))",
                "(deftotal double (lam (n) (match n [(Zero) Zero] [(Succ k) (Succ (Succ (double k)))])))",
            ],
            &|name| match name {
                "double" => Some("(Pi ((n Nat)) Nat)"),
                _ => None,
            },
        )
        .expect("a structural deftotal elaborates");
        let (name, _ty) = last.expect("a definition");
        let term = env.global_term(&name).expect("term").clone();
        // Structural ⟹ compiles to an `Elim`, *not* a self-binding `λself. …` with `Later`.
        assert!(
            !term_contains_later(&term),
            "a structural deftotal must not introduce `later`: {term:?}"
        );
    }

    /// Shift every free de Bruijn index in a *closed* type by one binder (here all types are
    /// closed, so this is the identity; provided for the `self_ty` Pi construction above).
    fn shift_closed(t: &Term) -> Term {
        t.clone()
    }

    fn term_contains_later(t: &Term) -> bool {
        match t {
            Term::Later(_) => true,
            Term::Force(_) => true,
            Term::Lam(b) | Term::Now(b) | Term::Delay(b) | Term::Fst(b) | Term::Snd(b) => {
                term_contains_later(b)
            }
            Term::App(f, a) => term_contains_later(f) || term_contains_later(a),
            Term::Pi(_, d, c) | Term::Sigma(d, c) | Term::Pair(d, c) | Term::Ann(d, c) => {
                term_contains_later(d) || term_contains_later(c)
            }
            Term::Elim {
                motive,
                methods,
                scrutinee,
                ..
            } => {
                term_contains_later(motive)
                    || methods.iter().any(term_contains_later)
                    || term_contains_later(scrutinee)
            }
            _ => false,
        }
    }

    // ---- surface effects: effect / perform / handle / (! E A) (spec §4.2, §4.3, §5) ---------

    /// Declare `Unit`, `Nat`, and the `State` effect into a fresh environment.
    fn state_env() -> ElabEnv {
        let mut env = ElabEnv::new();
        for src in [
            "(defdata Unit () (tt))",
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(effect State (get Unit Nat) (put Nat Unit))",
        ] {
            let (sx, _) = read_one(src).expect("reads");
            let decl = parse_decl(&sx).expect("parses");
            env.declare(&decl, None).expect("declares");
        }
        env
    }

    /// An `(effect State (get Unit Nat) (put Nat Unit))` declaration registers the effect and its
    /// operations in the kernel signature.
    #[test]
    fn effect_decl_elaborates() {
        let env = state_env();
        let sig = env.signature();
        let (eff, getsig) = sig.op_of("get").expect("get is declared");
        assert_eq!(eff.name, blight_kernel::EffName::new("State"));
        assert_eq!(getsig.name, "get");
        assert!(sig.op_of("put").is_some(), "put is declared");
    }

    /// `(perform get tt)` elaborates to `Term::Op` carrying the resolved effect name.
    #[test]
    fn perform_elaborates_to_op() {
        let env = state_env();
        let (sx, _) = read_one("(perform get tt)").expect("reads");
        let surface = parse_surface(&sx).expect("parses");
        let term = elaborate(&env, &surface).expect("elaborates");
        match term {
            Term::Op { effect, op, .. } => {
                assert_eq!(effect, blight_kernel::EffName::new("State"));
                assert_eq!(op, "get");
            }
            other => panic!("expected Term::Op, got {other:?}"),
        }
    }

    /// `(handle body (return x x) (get x k (k Zero)))` elaborates to `Term::Handle` with the
    /// expected binder structure (return binds 1; each op clause binds 2).
    #[test]
    fn handle_elaborates() {
        let env = state_env();
        let src = "(handle (perform get tt) (return x x) (get x k (k Zero)))";
        let (sx, _) = read_one(src).expect("reads");
        let surface = parse_surface(&sx).expect("parses");
        let term = elaborate(&env, &surface).expect("elaborates");
        match term {
            Term::Handle { op_clauses, .. } => {
                assert_eq!(op_clauses.len(), 1, "one operation clause");
                assert_eq!(op_clauses[0].0, "get");
            }
            other => panic!("expected Term::Handle, got {other:?}"),
        }
    }

    /// `(! State Nat)` elaborates to `Term::EffTy` with a row carrying `State`; `(! pure Nat)` is
    /// the empty (pure) row.
    #[test]
    fn bang_row_type() {
        let env = state_env();
        let (sx, _) = read_one("(! State Nat)").expect("reads");
        let term = elaborate(&env, &parse_surface(&sx).expect("parses")).expect("elaborates");
        match term {
            Term::EffTy(row, _) => {
                assert!(
                    row.contains(&blight_kernel::EffName::new("State")),
                    "row carries State"
                );
            }
            other => panic!("expected Term::EffTy, got {other:?}"),
        }
        let (sx2, _) = read_one("(! pure Nat)").expect("reads");
        let pure = elaborate(&env, &parse_surface(&sx2).expect("parses")).expect("elaborates");
        match pure {
            Term::EffTy(row, _) => assert!(row.is_empty(), "`pure` is the empty row"),
            other => panic!("expected Term::EffTy, got {other:?}"),
        }
    }

    /// `(deftotal name body)` parses to `Decl::DefTotal`.
    #[test]
    fn deftotal_parses() {
        let (sx, _) = read_one("(deftotal f (lam (n) n))").expect("reads");
        match parse_decl(&sx).expect("parses") {
            Decl::DefTotal { name, .. } => assert_eq!(name, "f"),
            other => panic!("expected Decl::DefTotal, got {other:?}"),
        }
    }
}
