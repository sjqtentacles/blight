//! The bidirectional elaborator (spec §6.1): surface terms to core kernel terms. UNTRUSTED.
//!
//! This is the §1.3 governing rule applied to the type checker itself: even "the type system
//! the user experiences" is untrusted tower code. Whatever core term `elaborate` produces is
//! re-checked by the spore; a wrong result is simply rejected (spec §6.1).

use crate::meta::{meta_term, MetaCtx, UnifyError};
use crate::pretty::pretty_term;
use crate::sexpr::Sexpr;
use crate::surface::{Binder, Clause, Cofibration, ConstructorDecl, Decl, Surface};
use blight_kernel::{unshare, Term};
use std::rc::Rc;

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
    /// Per-global **relevant-parameter summary**: for each leading lambda parameter of a top-level
    /// definition, whether its value can reach the function's *result* (a sound over-approximation;
    /// see [`compute_relevance`]). Computed in definition order from earlier summaries, so a caller
    /// can tell which of a callee's arguments actually flow to the result. Consumed by the structural
    /// recursion check ([`elaborate_rec`]) to decide whether a self-call's *varying leading argument*
    /// may be soundly dropped (only when the corresponding parameter is irrelevant — e.g. an erased
    /// index threaded through index-ignoring helpers like `bvar-index`, vs a real accumulator).
    relevant_params: std::collections::HashMap<String, Vec<bool>>,
}

/// How the elaborator fills one leading implicit binder at a use site (spec §6.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplicitSpec {
    /// An ordinary implicit type/value argument, solved by metavariable unification. `name` is the
    /// binder's surface name (e.g. `n` for `{n Nat}`), carried purely for diagnostics (E2) — an
    /// unsolved or ambiguous implicit names *which* binder, not just the definition it belongs to.
    Unify { name: String },
    /// A type-class constraint `{_ (C A)}`: resolved by dictionary search keyed on `C` and the
    /// head symbol of `A` (which is itself usually an earlier implicit, solved first).
    Instance { class: String, name: String },
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
    /// definitions are now kernel-certified directly. As of A3 the elaborator also lowers nested
    /// matches that lift a still-in-scope binder into a *higher-order eliminator motive* (the
    /// `zip-vec` shape) into a core term that BOTH the kernel and the independent re-checker fully
    /// certify — the per-arm index refinement of the lifted binder's type is performed during
    /// lowering (see `lower_match`) — so there is no longer any skip here: every gated definition is
    /// kernel-checked.
    fn kernel_check_def(&self, name: &str, term: &Term, ty: &Term) -> Result<(), ElabError> {
        if !gate_routes_through_kernel(ty) {
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
                let rel = compute_relevance(name, body, &self.relevant_params);
                self.relevant_params.insert(name.clone(), rel);
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
                let rel = compute_relevance(name, body, &self.relevant_params);
                self.relevant_params.insert(name.clone(), rel);
                let term = elaborate_rec(self, name, body, t, false)?;
                self.kernel_check_def(name, &term, t)?;
                self.define_global(name.clone(), term, Some(t.clone()));
                Ok(())
            }
            Decl::DefTotal { name, body } => {
                let t = ty.ok_or_else(|| {
                    ElabError::BadForm(format!("`deftotal {name}` requires a declared type"))
                })?;
                let rel = compute_relevance(name, body, &self.relevant_params);
                self.relevant_params.insert(name.clone(), rel);
                let term = elaborate_rec(self, name, body, t, true)?;
                self.kernel_check_def(name, &term, t)?;
                self.define_global(name.clone(), term, Some(t.clone()));
                Ok(())
            }
            Decl::DefEffect { name, params, ops } => self.declare_effect(name, params, ops),
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
                    ty: Rc::new(core_ty.clone()),
                };
                self.define_global(name.clone(), term, Some(core_ty));
                Ok(())
            }
        }
    }

    /// Elaborate a parameter telescope: each param's type is checked in the scope of the
    /// *preceding* params (so a later param's type may mention an earlier one), and the
    /// resulting scope has every param bound, outermost-first — ready to elaborate whatever comes
    /// next in that scope (a data family's indices/constructors, or an effect's operation
    /// signatures). Shared by [`ElabEnv::declare_data`] and [`ElabEnv::declare_effect`] so their
    /// identical telescope-instantiation convention (spec §2.7's own `DataDecl::params`, mirrored
    /// by [`blight_kernel::EffDecl::params`] for Wave 7/E2) cannot drift between the two.
    fn elab_param_telescope(&self, params: &[Binder]) -> Result<(Scope, Vec<Term>), ElabError> {
        let mut scope = Scope::new();
        let mut terms = Vec::with_capacity(params.len());
        for p in params {
            let ty = elab(self, &scope, &p.ty, None)?;
            terms.push(ty);
            scope = scope.push_var(&p.name);
        }
        Ok((scope, terms))
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
        // Elaborate the parameter telescope. The params become the *outermost* binders of every
        // constructor's argument scope (kernel convention: arg/index terms see
        // `[preceding_args, params]`).
        let (param_scope, param_terms) = self.elab_param_telescope(params)?;
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
    ///
    /// Wave 7/E2 (parameterized effects): `params` is the effect's own type-parameter telescope
    /// (e.g. `Ref`'s single `(A (Type 0))`), scoped exactly like [`ElabEnv::declare_data`]'s
    /// `params` — each param type is elaborated in the scope of the *preceding* params, then
    /// pushed as a bound name so every operation's `param_ty`/`result_ty` may reference it. Empty
    /// for an ordinary (non-parameterized) effect, in which case this is unchanged from before E2.
    fn declare_effect(
        &mut self,
        name: &str,
        params: &[Binder],
        ops: &[(String, Surface, Surface)],
    ) -> Result<(), ElabError> {
        use blight_kernel::{EffDecl, EffName, Grade, OpSig};
        let (param_scope, param_terms) = self.elab_param_telescope(params)?;
        let mut op_sigs = Vec::with_capacity(ops.len());
        for (op_name, param_ty, result_ty) in ops {
            let param_ty = elab(self, &param_scope, param_ty, None)?;
            // The kernel's `result_ty` lives in the scope `[effect params…, x:A]` (`x`, the op's own
            // value argument, is bound *innermost*, at index 0); surface ops are non-dependent on
            // `x` in M2 (only on the effect's own type parameters), so `result_ty` is elaborated in
            // `param_scope` (no binder for `x`) and then *weakened* by one binder to shift every
            // reference to a parameter up past the `x` slot it doesn't itself mention (Wave 7/E2:
            // this matters as soon as `param_scope` is non-empty and `result_ty` actually
            // references a parameter, e.g. `Ref`'s `get : Unit -> A`; before E2 `param_scope` was
            // always empty here, so this weakening was a no-op and the bug was latent).
            let result_ty = elab(self, &param_scope, result_ty, None)?;
            let result_ty = weaken(&result_ty, 1);
            op_sigs.push(OpSig {
                name: op_name.clone(),
                param_ty,
                result_ty,
                cont_grade: Grade::Omega,
            });
        }
        let decl = EffDecl {
            name: EffName::new(name),
            params: param_terms,
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
            // A bare decimal numeral (E1) — `Nat` sugar. Recognized only when every character is
            // an ASCII digit, so `x2`/`2x`/`-5` all stay ordinary symbols (the last elaborates to
            // a clean "unbound variable" error, not a numeral). NOTE: a binder grade slot `(x A 0)`
            // is parsed through this very function (`parse_one_binder` calls `parse_surface` on
            // the grade position), so `0`/`1` there now arrive as `Surface::NatLit` rather than
            // `Surface::Var` — `parse_grade` below matches both forms so grade literals keep their
            // grade meaning rather than being read as `Nat` values.
            if !a.is_empty() && a.bytes().all(|b| b.is_ascii_digit()) {
                if let Ok(n) = a.parse::<u64>() {
                    return Ok(Surface::NatLit(n));
                }
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
            // ---- cubical Kan / Glue layer (plan A2b) ----
            "Partial" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(Partial φ A)".into()));
                }
                return Ok(Surface::Partial(
                    Box::new(parse_cofib(&items[1])?),
                    Box::new(parse_surface(&items[2])?),
                ));
            }
            "system" => {
                let mut branches = Vec::new();
                for b in &items[1..] {
                    let parts = match b {
                        Sexpr::List(p) if p.len() == 2 => p,
                        _ => return Err(ElabError::BadForm("(system (φ t) ...)".into())),
                    };
                    branches.push((parse_cofib(&parts[0])?, parse_surface(&parts[1])?));
                }
                return Ok(Surface::System(branches));
            }
            "Glue" => {
                if items.len() != 5 {
                    return Err(ElabError::BadForm("(Glue A φ T e)".into()));
                }
                return Ok(Surface::Glue(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_cofib(&items[2])?),
                    Box::new(parse_surface(&items[3])?),
                    Box::new(parse_surface(&items[4])?),
                ));
            }
            "glue" => {
                if items.len() != 4 {
                    return Err(ElabError::BadForm("(glue φ t a)".into()));
                }
                return Ok(Surface::GlueTerm(
                    Box::new(parse_cofib(&items[1])?),
                    Box::new(parse_surface(&items[2])?),
                    Box::new(parse_surface(&items[3])?),
                ));
            }
            "unglue" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(unglue g)".into()));
                }
                return Ok(Surface::Unglue(Box::new(parse_surface(&items[1])?)));
            }
            "transp" => {
                if items.len() != 4 {
                    return Err(ElabError::BadForm("(transp (plam (i) A) φ a0)".into()));
                }
                return Ok(Surface::Transp(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_cofib(&items[2])?),
                    Box::new(parse_surface(&items[3])?),
                ));
            }
            "hcomp" => {
                if items.len() != 5 {
                    return Err(ElabError::BadForm("(hcomp A φ (plam (j) u) a0)".into()));
                }
                return Ok(Surface::HComp(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_cofib(&items[2])?),
                    Box::new(parse_surface(&items[3])?),
                    Box::new(parse_surface(&items[4])?),
                ));
            }
            "comp" => {
                if items.len() != 5 {
                    return Err(ElabError::BadForm(
                        "(comp (plam (i) A) φ (plam (j) u) a0)".into(),
                    ));
                }
                return Ok(Surface::Comp(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_cofib(&items[2])?),
                    Box::new(parse_surface(&items[3])?),
                    Box::new(parse_surface(&items[4])?),
                ));
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
                // `(perform op arg)`, or `(perform op (T ...) arg)` for a parameterized effect's
                // operation (Wave 7/E2): the explicit type-argument instantiation is a *list* in
                // the second position, so the two forms are unambiguous by arity.
                match items.len() {
                    3 => {
                        let op = sym(&items[1])?;
                        return Ok(Surface::Perform(
                            op,
                            Vec::new(),
                            Box::new(parse_surface(&items[2])?),
                        ));
                    }
                    4 => {
                        let op = sym(&items[1])?;
                        let type_arg_items = match &items[2] {
                            Sexpr::List(ta) => ta,
                            _ => {
                                return Err(ElabError::BadForm(
                                    "(perform op (T ...) arg): type arguments must be a list"
                                        .into(),
                                ))
                            }
                        };
                        let type_args = type_arg_items.iter().map(parse_surface).collect::<Result<
                            Vec<_>,
                            _,
                        >>(
                        )?;
                        return Ok(Surface::Perform(
                            op,
                            type_args,
                            Box::new(parse_surface(&items[3])?),
                        ));
                    }
                    _ => {
                        return Err(ElabError::BadForm(
                            "(perform op arg) or (perform op (T ...) arg)".into(),
                        ))
                    }
                }
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

/// Parse a surface cofibration `φ` (plan A2b): `ctop`, `cbot`, `(ieq0 r)`, `(ieq1 r)`,
/// `(cand φ ψ)`, `(cor φ ψ)`. Interval subterms `r` are parsed as ordinary surface terms and
/// reduced to kernel intervals later by `elab_interval`.
fn parse_cofib(s: &Sexpr) -> Result<Cofibration, ElabError> {
    match s {
        Sexpr::Atom(a) if a == "ctop" => Ok(Cofibration::Top),
        Sexpr::Atom(a) if a == "cbot" => Ok(Cofibration::Bot),
        Sexpr::List(items) if !items.is_empty() => {
            let head = sym(&items[0])?;
            match (head.as_str(), &items[1..]) {
                ("ieq0", [r]) => Ok(Cofibration::Eq0(Box::new(parse_surface(r)?))),
                ("ieq1", [r]) => Ok(Cofibration::Eq1(Box::new(parse_surface(r)?))),
                ("cand", [p, q]) => Ok(Cofibration::And(
                    Box::new(parse_cofib(p)?),
                    Box::new(parse_cofib(q)?),
                )),
                ("cor", [p, q]) => Ok(Cofibration::Or(
                    Box::new(parse_cofib(p)?),
                    Box::new(parse_cofib(q)?),
                )),
                _ => Err(ElabError::BadForm(
                    "expected a cofibration: ctop, cbot, (ieq0 r), (ieq1 r), (cand φ ψ), (cor φ ψ)"
                        .into(),
                )),
            }
        }
        _ => Err(ElabError::BadForm(
            "expected a cofibration: ctop, cbot, (ieq0 r), (ieq1 r), (cand φ ψ), (cor φ ψ)".into(),
        )),
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
            // (effect E (op A B) ...), or the parameterized form (Wave 7/E2)
            // (effect E (params...) (op A B) ...). An operation is always the 3-element list
            // `(name A B)`; a parameter telescope is a list of 2-element binders `(x T)`, so
            // `is_binder_list` (as for `defdata`'s index telescope) tells the two apart: an op's
            // head is a bare symbol, a param telescope's head (if any) is itself a list.
            if items.len() < 2 {
                return Err(ElabError::BadForm("(effect E (op A B) ...)".into()));
            }
            let name = sym(&items[1])?;
            let (params, op_start) = if items.len() >= 3 && is_binder_list(&items[2]) {
                (parse_binders(&items[2])?, 3)
            } else {
                (Vec::new(), 2)
            };
            let mut ops = Vec::new();
            for op in &items[op_start..] {
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
            Ok(Decl::DefEffect { name, params, ops })
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
    /// `true` when the function's declared conclusion is an *effectful* computation (`! E A`, non-
    /// empty row). A structural `Elim` *fixes* the leading parameters and evaluates each induction
    /// hypothesis (`self field`) eagerly; for an effectful body that both **reorders** the per-step
    /// effects (the eager IH runs before the method's own `perform`) and, when a leading parameter is
    /// silently varied (e.g. an accumulator `(Succ i)`), drops the change — a miscompile that the
    /// kernel's *type* re-check cannot catch (effect order is not in the type). So for an effectful
    /// recursor we require the leading arguments to be the leading parameters *verbatim*; a varying
    /// leading argument falls through to the sound partial (`later`-guarded) step. Pure/total indexed
    /// families (e.g. `vec-map`, where a leading *index* legitimately varies and the IH's specialized
    /// type subsumes it) keep the lenient recognition.
    effectful: bool,
    /// Scope depth of the function's *parameters*, recorded lazily at the outermost `match`. Only a
    /// match whose scrutinee is a function parameter (absolute scope position `< param_depth`) may
    /// establish structural induction hypotheses for self-calls. A scrutinee bound by a *nested*
    /// match (a constructor field, position `>= param_depth`) is **not** the recursion variable: its
    /// IH belongs to that inner eliminator, not to `self`. Offering it to a self-call is unsound — it
    /// is exactly the `fib (n-2)` / Ackermann course-of-values boundary the language deliberately
    /// rejects (`deftotal` errors; `define-rec` guards under `later`). Without this gate the
    /// elaborator silently bound such a call to the inner IH and miscompiled (e.g. `fib 5 = 65`).
    param_depth: Option<usize>,
    /// This function's own **relevant-parameter summary** (see [`compute_relevance`]): for each
    /// leading lambda parameter (by position), whether its value can reach the result. Shared (`Rc`)
    /// so the frequent `RecCtx` clones stay cheap.
    ///
    /// Why: a structural `Elim` *fixes* the leading parameters at their outer values and supplies the
    /// induction hypothesis `self field` for the scrutinee, so binding a self-call to that IH
    /// **drops** the call's own leading arguments. That is sound only when a varying leading argument
    /// cannot influence the result — i.e. when that parameter is *irrelevant* here. A varied leading
    /// argument at an irrelevant position (e.g. the index `g`/`a` in `btm-size`/`berase`, threaded
    /// only through index-ignoring helpers, or the erased length `n` in `vec-length`) is dropped
    /// exactly; a varied one at a *relevant* position is a real **accumulator** (e.g. `acc` in
    /// `sum-acc`/`foldl`, returned in a base case) whose dropped change would silently reuse the stale
    /// value — a meaning bug the kernel's *type* re-check cannot see (both are `Nat`). So a
    /// non-verbatim leading argument is accepted only at an irrelevant position; otherwise the call
    /// falls through (a `deftotal` error / a `define-rec` `later`-guard).
    relevance: std::rc::Rc<Vec<bool>>,
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

/// Resolve a surface interval expression to a kernel [`Interval`]. Beyond the endpoints `i0`/`i1`
/// and dimension variables, the De Morgan structure of the interval is exposed as ordinary
/// application sugar: `(~ r)` is negation, `(imin r s)` / `(r /\ s)` is meet, `(imax r s)` /
/// `(r \/ s)` is join. These are pure elaborator sugar over the kernel's `Interval::{Neg,Min,Max}`
/// (which the kernel already validates), so they add nothing to the TCB; they let tower code write
/// the connection terms that singleton-contraction / `id-equiv`-style proofs require.
fn elab_interval(scope: &Scope, term: &Surface) -> Result<blight_kernel::Interval, ElabError> {
    use blight_kernel::Interval;
    match term {
        Surface::Var(v) if v == "i0" => Ok(Interval::I0),
        Surface::Var(v) if v == "i1" => Ok(Interval::I1),
        Surface::Var(v) => scope
            .dim_index(v)
            .map(Interval::Dim)
            .ok_or_else(|| ElabError::Unbound(format!("dimension `{v}`"))),
        // De Morgan combinators, written as applications of reserved interval operators.
        Surface::App(head, args) => match (&**head, args.as_slice()) {
            (Surface::Var(op), [r]) if op == "~" || op == "ineg" => {
                Ok(Interval::Neg(Box::new(elab_interval(scope, r)?)))
            }
            (Surface::Var(op), [r, s]) if op == "imin" || op == "/\\" => Ok(Interval::Min(
                Box::new(elab_interval(scope, r)?),
                Box::new(elab_interval(scope, s)?),
            )),
            (Surface::Var(op), [r, s]) if op == "imax" || op == "\\/" => Ok(Interval::Max(
                Box::new(elab_interval(scope, r)?),
                Box::new(elab_interval(scope, s)?),
            )),
            _ => Err(ElabError::BadForm(
                "expected an interval expression (i0, i1, a dim, (~ r), (imin r s), (imax r s))"
                    .into(),
            )),
        },
        _ => Err(ElabError::BadForm("expected an interval expression".into())),
    }
}

/// Elaborate a surface [`Cofibration`] to the kernel [`blight_kernel::Cofib`], reducing its interval
/// subterms via [`elab_interval`] (plan A2b).
fn elab_cofib(scope: &Scope, cofib: &Cofibration) -> Result<blight_kernel::Cofib, ElabError> {
    use blight_kernel::Cofib;
    match cofib {
        Cofibration::Top => Ok(Cofib::Top),
        Cofibration::Bot => Ok(Cofib::Bot),
        Cofibration::Eq0(r) => Ok(Cofib::Eq0(elab_interval(scope, r)?)),
        Cofibration::Eq1(r) => Ok(Cofib::Eq1(elab_interval(scope, r)?)),
        Cofibration::And(p, q) => Ok(Cofib::And(
            Box::new(elab_cofib(scope, p)?),
            Box::new(elab_cofib(scope, q)?),
        )),
        Cofibration::Or(p, q) => Ok(Cofib::Or(
            Box::new(elab_cofib(scope, p)?),
            Box::new(elab_cofib(scope, q)?),
        )),
    }
}

// ---- Wave 7 / E1: row polymorphism (tower-first) ---------------------------------------------
//
// `crate::row::Row` (blight-kernel) already carries an optional open tail (`RowVar`) for
// Koka-style row unification, but nothing ever constructs one: `Row::union`/`leq` document it as
// "a forward-compatible stub, not a correctness hazard *here*" because every row the kernel ever
// actually sees is closed. Growing that kernel algebra is exactly what the roadmap says to do
// *only if unavoidable* — and it is not: the closed-row kernel representation is already exactly
// what a resolved row polymorphic signature needs. So row polymorphism lives *entirely* in this
// elaborator as a small, sound unification device: a surface pattern `(L1 L2 ... | r)` names an
// open tail `r`; `RowVarScope::unify` resolves `r` against a real computation's actual (already
// kernel-computed, via `Checker::infer_g`) row, and the elaborator only ever emits a closed
// `Term::EffTy` afterward. The kernel's `RowVar`/open-tail plumbing stays completely dormant.

/// A row-polymorphic effect-row pattern as written in surface syntax, `(L1 L2 ... | r)`: explicit
/// labels the row is asserted to carry, plus an optional named tail variable standing for
/// "whatever else" the row may additionally carry. Purely elaborator-side scaffolding — never
/// reaches the kernel as such.
#[derive(Debug, Clone, PartialEq, Eq)]
struct RowPattern {
    labels: Vec<blight_kernel::EffName>,
    tail: Option<String>,
}

impl RowPattern {
    /// The pattern as a plain closed row (0, 1, or more labels, each at grade `ω` — matching the
    /// pre-E1 single-label convention), or `None` if it names an open tail that still needs
    /// resolving against a real computation's row.
    fn closed_row(&self) -> Option<blight_kernel::Row> {
        if self.tail.is_some() {
            return None;
        }
        let mut row = blight_kernel::Row::empty();
        for l in &self.labels {
            row = row.union(&blight_kernel::Row::single(
                l.clone(),
                blight_kernel::Grade::Omega,
            ));
        }
        Some(row)
    }
}

/// Parse the `E` position of a surface `(! E A)` into a [`RowPattern`]. Accepts: `pure` (the empty
/// row); a single effect name (pre-E1 surface); a parenthesized list of effect names
/// `(L1 L2 ...)` (a closed, multi-label row — new in Wave 7/E1); or a list ending `... | r`,
/// naming an open row-variable tail `r` (Wave 7/E1 row polymorphism).
fn parse_row_pattern(eff: &Surface) -> Result<RowPattern, ElabError> {
    use blight_kernel::EffName;
    fn name_of(s: &Surface) -> Result<String, ElabError> {
        match s {
            Surface::Var(n) => Ok(n.clone()),
            _ => Err(ElabError::BadForm(
                "(! (L1 L2 ... | r) A): each effect must be a plain name".into(),
            )),
        }
    }
    match eff {
        Surface::Var(name) if name == "pure" => Ok(RowPattern {
            labels: vec![],
            tail: None,
        }),
        Surface::Var(name) => Ok(RowPattern {
            labels: vec![EffName::new(name.clone())],
            tail: None,
        }),
        Surface::App(head, args) => {
            let mut spine: Vec<&Surface> = vec![head.as_ref()];
            spine.extend(args.iter());
            let bar = spine
                .iter()
                .position(|s| matches!(s, Surface::Var(n) if n == "|"));
            match bar {
                None => {
                    let mut labels = Vec::with_capacity(spine.len());
                    for s in &spine {
                        labels.push(EffName::new(name_of(s)?));
                    }
                    Ok(RowPattern { labels, tail: None })
                }
                Some(i) => {
                    if i + 2 != spine.len() {
                        return Err(ElabError::BadForm(
                            "(! (L1 L2 ... | r) A): exactly one row variable must follow `|`"
                                .into(),
                        ));
                    }
                    let mut labels = Vec::with_capacity(i);
                    for s in &spine[..i] {
                        labels.push(EffName::new(name_of(s)?));
                    }
                    let tail = name_of(spine[i + 1])?;
                    Ok(RowPattern {
                        labels,
                        tail: Some(tail),
                    })
                }
            }
        }
        _ => Err(ElabError::BadForm(
            "(! E A): E must be `pure`, a single effect name, a list of effect names, \
             or `(L1 L2 ... | r)`"
                .into(),
        )),
    }
}

/// Row-variable bindings resolved so far within one elaboration scope. A fresh scope is created
/// per ascription (row variables are never shared across unrelated top-level forms).
#[derive(Debug, Clone, Default)]
struct RowVarScope(std::collections::BTreeMap<String, blight_kernel::Row>);

impl RowVarScope {
    fn new() -> Self {
        RowVarScope::default()
    }

    /// Unify `pattern` against the `concrete` row a real computation was inferred to have (spec
    /// Wave 7/E1). Every explicit label in `pattern` must actually be present in `concrete`; what
    /// remains after discharging them all — the row's *extension* — is what the pattern's tail
    /// variable stands for. A tail variable already bound in this scope must resolve to the exact
    /// same extension a second time: two incompatible resolutions are a clean [`ElabError`], never
    /// a kernel panic (row unification is entirely tower-side; the kernel only ever sees the
    /// final, closed `concrete` row). Returns `concrete` unchanged on success.
    fn unify(
        &mut self,
        pattern: &RowPattern,
        concrete: &blight_kernel::Row,
    ) -> Result<blight_kernel::Row, ElabError> {
        for label in &pattern.labels {
            if !concrete.contains(label) {
                return Err(ElabError::BadForm(format!(
                    "row mismatch: declared effect `{}` is not present in the actual row {concrete:?}",
                    label.0
                )));
            }
        }
        let mut extension = concrete.clone();
        for label in &pattern.labels {
            extension = extension.discharge(label);
        }
        if let Some(name) = &pattern.tail {
            match self.0.get(name) {
                Some(existing) if existing != &extension => {
                    return Err(ElabError::BadForm(format!(
                        "row variable `{name}` unifies with two incompatible tails \
                         ({existing:?} vs {extension:?})"
                    )));
                }
                Some(_) => {}
                None => {
                    self.0.insert(name.clone(), extension);
                }
            }
        }
        Ok(concrete.clone())
    }
}

/// Elaborate the shared body of a `(handle body (return x r) (op x k e) ...)` surface form to a
/// `Term::Handle`. Factored out so the ordinary [`Surface::Handle`] arm and the row-polymorphic
/// ascription path ([`try_elab_row_polymorphic_handle`]) share one implementation.
fn elab_handle(
    env: &ElabEnv,
    scope: &Scope,
    body: &Surface,
    return_clause: &(String, Box<Surface>),
    op_clauses: &[(String, String, String, Surface)],
) -> Result<Term, ElabError> {
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
        op_clauses_c.push((op.clone(), Rc::new(clause_c)));
    }
    Ok(Term::Handle {
        body: Rc::new(body_c),
        return_clause: Rc::new(return_c),
        op_clauses: op_clauses_c,
    })
}

/// `(the (! (L1 .. | r) A) (handle body clauses...))` — a row-polymorphic handler ascription
/// (spec Wave 7/E1). When the declared type names an open row tail and the ascribed term is
/// directly a `Handle`, resolve the tail by inferring the handle's actual (already-discharged)
/// row through the trusted kernel checker (`Checker::infer_g`, the same rule `check_top_with`
/// uses) and unifying the declared pattern against it, then re-ascribe with the concrete, closed
/// result — the kernel never sees an open tail. Returns `Ok(None)` when this shape does not apply
/// (an ordinary ascription, or an open tail used somewhere other than directly ascribing a
/// `handle`), so the caller falls back to plain elaboration — which itself gives a clear
/// `ElabError` for a tail that never gets resolved, rather than silently accepting or dropping it.
fn try_elab_row_polymorphic_handle(
    env: &ElabEnv,
    scope: &Scope,
    ty: &Surface,
    e: &Surface,
) -> Result<Option<Term>, ElabError> {
    let Surface::Bang(eff, a) = ty else {
        return Ok(None);
    };
    let pattern = parse_row_pattern(eff)?;
    if pattern.tail.is_none() {
        return Ok(None);
    }
    let Surface::Handle {
        body,
        return_clause,
        op_clauses,
    } = e
    else {
        return Ok(None);
    };
    let handle_term = elab_handle(env, scope, body, return_clause, op_clauses)?;
    let a_c = elab(env, scope, a, None)?;
    let checker = blight_kernel::Checker::new(std::rc::Rc::new(env.signature().clone()));
    let ctx = blight_kernel::Context::empty();
    let (_result_ty, result_row, _usage) = checker
        .infer_g(&ctx, &handle_term, blight_kernel::Grade::Omega)
        .map_err(|err| {
            ElabError::BadForm(format!(
                "row-polymorphic handler ascription: kernel could not infer the handled \
                 computation's row: {err}"
            ))
        })?;
    let mut row_vars = RowVarScope::new();
    let resolved = row_vars.unify(&pattern, &result_row)?;
    let ty_resolved = Term::EffTy(resolved, Rc::new(a_c));
    Ok(Some(Term::Ann(
        Rc::new(handle_term),
        Rc::new(ty_resolved),
    )))
}

fn elab(
    env: &ElabEnv,
    scope: &Scope,
    term: &Surface,
    expected: Option<&Term>,
) -> Result<Term, ElabError> {
    use blight_kernel::ConName;
    match term {
        Surface::NatLit(n) => {
            // Sugar: `(Succ (Succ … Zero))`, `n` deep — elaborate exactly as if the user had
            // written the expansion by hand (E1). Delegating to `nat_to_surface` keeps this a
            // single source of truth with the char/string literal desugarings above, which build
            // the same chain.
            elab(env, scope, &nat_to_surface(*n), expected)
        }
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
                    Some(ty) => Term::Ann(Rc::new(t.clone()), Rc::new(ty.clone())),
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
                        Some(ty) => Term::Ann(Rc::new(t.clone()), Rc::new(ty.clone())),
                        None => t.clone(),
                    });
                }
            }
            Err(ElabError::Unbound(name.clone()))
        }

        Surface::The(ty, e) => {
            // Row-polymorphic handler ascription (Wave 7/E1): `(the (! (.. | r) A) (handle ..))`
            // resolves `r` by unifying against the handle's actual, kernel-inferred row instead of
            // going through the ordinary check-against-declared-type path below.
            if let Some(term) = try_elab_row_polymorphic_handle(env, scope, ty, e)? {
                return Ok(term);
            }
            let ty_c = elab(env, scope, ty, None)?;
            let e_c = elab(env, scope, e, Some(&ty_c))?;
            Ok(Term::Ann(Rc::new(e_c), Rc::new(ty_c)))
        }

        Surface::Univ(l) => Ok(Term::Univ(nat_level(*l))),

        Surface::Lam(names, body) => {
            // Peel the expected Pi-telescope binder-by-binder, recording each binder's domain type
            // so that a `match` on an outer binder can generalize over later binders.
            let mut sc = scope.clone();
            let mut cur = expected.cloned();
            for n in names {
                let (dom, cod) = match cur {
                    Some(Term::Pi(_, dom, cod)) => (Some(unshare(dom)), Some(unshare(cod))),
                    _ => (None, None),
                };
                sc = sc.push_var_ty(n, dom);
                cur = cod;
            }
            let mut core = elab(env, &sc, body, cur.as_ref())?;
            for _ in names {
                core = Term::Lam(Rc::new(core));
            }
            Ok(core)
        }

        Surface::Pi(binders, cod) => elab_pi(env, scope, binders, cod),

        Surface::App(f, args) => {
            // A recursive self-call `(self …)` must be recognized as the induction hypothesis
            // *before* the implicit-global path below, and takes priority even when a same-named
            // global already exists with implicit binders. This matters on an idempotent re-load
            // (`(load …)` of a module a second time): the definition being re-elaborated is already
            // registered as a global carrying its implicit spec, so without this guard its own body's
            // `(self A …)` self-call would be mis-routed through `elab_implicit_app` — treating the
            // explicitly-passed leading argument as the *first explicit* argument and failing to
            // unify. Inside a recursive definition the self-name always denotes the recursion.
            let is_self_call = matches!(f.as_ref(), Surface::Var(g)
                if scope.rec.as_ref().is_some_and(|r| &r.self_name == g)
                    && scope.var_index(g).is_none());
            // Implicit-argument insertion: a global head with leading implicit binders gets its
            // implicits solved (metavariable + unification) before the explicit args are applied.
            if !is_self_call {
                if let Surface::Var(g) = f.as_ref() {
                    let k = env.implicit_arity(g);
                    if k > 0 && scope.var_index(g).is_none() {
                        if let Some((gt, Some(gty))) = env.globals.get(g) {
                            let g_term = Term::Ann(Rc::new(gt.clone()), Rc::new(gty.clone()));
                            let specs = env.implicits.get(g).cloned().unwrap_or_default();
                            return elab_implicit_app(
                                env, scope, g, &g_term, gty, &specs, args, expected,
                            );
                        }
                    }
                }
            }
            if let Some(t) = elab_app_head(env, scope, f, args)? {
                return Ok(t);
            }
            let mut head = elab(env, scope, f, None)?;
            for a in args {
                head = Term::App(Rc::new(head), Rc::new(elab(env, scope, a, None)?));
            }
            Ok(head)
        }

        Surface::Path(a, x, y) => {
            let sc_dim = scope.push_dim("_");
            let family = elab(env, &sc_dim, a, None)?;
            let lhs = elab(env, scope, x, None)?;
            let rhs = elab(env, scope, y, None)?;
            Ok(Term::PathP {
                family: Rc::new(family),
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
            })
        }

        Surface::PLam(dim, body) => {
            let sc = scope.push_dim(dim);
            let core = elab(env, &sc, body, None)?;
            Ok(Term::PLam(Rc::new(core)))
        }

        Surface::PApp(p, r) => {
            let pc = elab(env, scope, p, None)?;
            let rc = elab_interval(scope, r)?;
            Ok(Term::PApp(Rc::new(pc), rc))
        }

        // ---- cubical Kan / Glue layer (plan A2b) ----
        Surface::Partial(cofib, a) => {
            let c = elab_cofib(scope, cofib)?;
            let a_c = elab(env, scope, a, None)?;
            Ok(Term::Partial(c, Rc::new(a_c)))
        }
        Surface::System(branches) => {
            let mut bs = Vec::with_capacity(branches.len());
            for (cofib, t) in branches {
                let face = elab_cofib(scope, cofib)?;
                let term = elab(env, scope, t, None)?;
                bs.push(blight_kernel::SystemBranch { face, term });
            }
            Ok(Term::System(bs))
        }
        Surface::Glue(base, cofib, ty, equiv) => {
            let base_c = elab(env, scope, base, None)?;
            let c = elab_cofib(scope, cofib)?;
            let ty_c = elab(env, scope, ty, None)?;
            let equiv_c = elab(env, scope, equiv, None)?;
            Ok(Term::Glue {
                base: Rc::new(base_c),
                cofib: c,
                ty: Rc::new(ty_c),
                equiv: Rc::new(equiv_c),
            })
        }
        Surface::GlueTerm(cofib, partial, base) => {
            let c = elab_cofib(scope, cofib)?;
            let partial_c = elab(env, scope, partial, None)?;
            let base_c = elab(env, scope, base, None)?;
            Ok(Term::GlueTerm {
                cofib: c,
                partial: Rc::new(partial_c),
                base: Rc::new(base_c),
            })
        }
        Surface::Unglue(g) => Ok(Term::Unglue(Rc::new(elab(env, scope, g, None)?))),
        Surface::Transp(line, cofib, base) => {
            // The line is `(plam (i) A)`; elaborate it to a `PLam`, then unwrap to the bare body so
            // the kernel's `Transp { family, .. }` sees the dimension-binding family directly.
            let line_c = elab(env, scope, line, None)?;
            let family = match line_c {
                Term::PLam(body) => unshare(body),
                other => {
                    return Err(ElabError::BadForm(format!(
                        "(transp line φ a0): line must be `(plam (i) A)`, got {other:?}"
                    )))
                }
            };
            let c = elab_cofib(scope, cofib)?;
            let base_c = elab(env, scope, base, None)?;
            Ok(Term::Transp {
                family: Rc::new(family),
                cofib: c,
                base: Rc::new(base_c),
            })
        }

        Surface::HComp(ty, cofib, tube, base) => {
            let ty_c = elab(env, scope, ty, None)?;
            let c = elab_cofib(scope, cofib)?;
            // The tube line is `(plam (j) u)`; unwrap to the bare dimension-binding body so the
            // kernel's `HComp { tube, .. }` sees it directly, mirroring `Transp`'s `family` handling.
            let tube_c = elab(env, scope, tube, None)?;
            let tube_body = match tube_c {
                Term::PLam(body) => unshare(body),
                other => {
                    return Err(ElabError::BadForm(format!(
                        "(hcomp A φ line a0): line must be `(plam (j) u)`, got {other:?}"
                    )))
                }
            };
            let base_c = elab(env, scope, base, None)?;
            Ok(Term::HComp {
                ty: Rc::new(ty_c),
                cofib: c,
                tube: Rc::new(tube_body),
                base: Rc::new(base_c),
            })
        }

        Surface::Comp(family, cofib, tube, base) => {
            let sc_dim = scope.push_dim("_");
            let family_c = elab(env, &sc_dim, family, None)?;
            let family_body = match family_c {
                Term::PLam(body) => unshare(body),
                other => {
                    return Err(ElabError::BadForm(format!(
                        "(comp line φ tube a0): line must be `(plam (i) A)`, got {other:?}"
                    )))
                }
            };
            let c = elab_cofib(scope, cofib)?;
            let tube_c = elab(env, scope, tube, None)?;
            let tube_body = match tube_c {
                Term::PLam(body) => unshare(body),
                other => {
                    return Err(ElabError::BadForm(format!(
                        "(comp line φ tube a0): tube must be `(plam (j) u)`, got {other:?}"
                    )))
                }
            };
            let base_c = elab(env, scope, base, None)?;
            Ok(Term::Comp {
                family: Rc::new(family_body),
                cofib: c,
                tube: Rc::new(tube_body),
                base: Rc::new(base_c),
            })
        }

        Surface::Match(scruts, clauses) => {
            use crate::surface::Pattern;
            // E3 coverage pre-pass: a clear up-front non-exhaustive/duplicate/unreachable diagnostic
            // before column compilation. Runs at every match level (nested/multi re-enter here).
            check_match_coverage(env, scruts, clauses)?;
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
        Surface::Delay(a) => Ok(Term::Delay(Rc::new(elab(env, scope, a, None)?))),
        Surface::Now(a) => {
            // When checking against `Delay A`, the payload is checked against `A`.
            let inner_expected = match expected {
                Some(Term::Delay(a_ty)) => Some(a_ty.as_ref()),
                _ => None,
            };
            Ok(Term::Now(Rc::new(elab(env, scope, a, inner_expected)?)))
        }
        Surface::Later(d) => {
            // `later d : Delay A` when `d : Delay A`: the guarded continuation has the same type.
            Ok(Term::Later(Rc::new(elab(env, scope, d, expected)?)))
        }
        Surface::Force(d) => {
            // `force d : A` when `d : Delay A`. When checking against an expected `A`, the payload
            // is checked against `Delay A`; otherwise it is inferred.
            let inner_expected = expected.map(|a| Term::Delay(Rc::new(a.clone())));
            Ok(Term::Force(Rc::new(elab(
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
                lhs: Rc::new(lhs),
                rhs: Rc::new(rhs),
            })
        }

        // ---- effects (spec §4.2, §4.3) ----
        Surface::Perform(op, type_args, arg) => {
            // Resolve which effect declares this operation from the signature.
            let (eff, _sig) = env
                .signature()
                .op_of(op)
                .ok_or_else(|| ElabError::Unbound(format!("operation `{op}`")))?;
            let effect = eff.name.clone();
            // Wave 7/E2: a parameterized effect's `perform` site must supply exactly one type
            // argument per entry in the effect's declared telescope. Caught here (a clean
            // `ElabError`) rather than only at the kernel's `infer_g`, matching this elaborator's
            // convention of surfacing arity mismatches before they reach the kernel.
            if type_args.len() != eff.params.len() {
                return Err(ElabError::BadForm(format!(
                    "operation `{op}` of effect {:?} expects {} type argument(s), got {}",
                    eff.name,
                    eff.params.len(),
                    type_args.len()
                )));
            }
            let type_args_c = type_args
                .iter()
                .map(|ta| elab(env, scope, ta, None))
                .collect::<Result<Vec<_>, _>>()?;
            let arg_c = elab(env, scope, arg, None)?;
            Ok(Term::Op {
                effect,
                op: op.clone(),
                type_args: type_args_c,
                arg: Rc::new(arg_c),
            })
        }
        Surface::Handle {
            body,
            return_clause,
            op_clauses,
        } => elab_handle(env, scope, body, return_clause, op_clauses),
        Surface::Bang(eff, a) => {
            // `E` is `pure`, a single effect name, a closed multi-label list, or `(L.. | r)` — see
            // `parse_row_pattern`. An open tail can only be elaborated here if it was already
            // resolved by `try_elab_row_polymorphic_handle` (which never calls back into this
            // generic path with the same unresolved pattern); reaching here with a still-open tail
            // is a clear, honest `ElabError` rather than a silently dropped or invented row.
            let pattern = parse_row_pattern(eff)?;
            let row = pattern.closed_row().ok_or_else(|| {
                let name = pattern.tail.clone().unwrap_or_default();
                ElabError::BadForm(format!(
                    "(! (.. | {name}) A): an open row-variable tail can only be resolved by \
                     directly ascribing a `handle` expression, e.g. \
                     `(the (! (.. | {name}) A) (handle ...))`"
                ))
            })?;
            let a_c = elab(env, scope, a, None)?;
            Ok(Term::EffTy(row, Rc::new(a_c)))
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
            Ok(Term::Pair(Rc::new(a_c), Rc::new(b_c)))
        }
        Surface::Fst(p) => Ok(Term::Fst(Rc::new(elab(env, scope, p, None)?))),
        Surface::Snd(p) => Ok(Term::Snd(Rc::new(elab(env, scope, p, None)?))),
        Surface::Let(x, e, body) => {
            // `(let ((x e)) b)` ⤳ `((lam (x) b) e)`. Elaborate `e` first (inference), then the body
            // under a binder. When both the bound value's type and the expected result type are
            // known, ascribe the lambda `(λx. b) : Π(x:E). expected` so the application is
            // *checkable* (a bare `Lam` head cannot be inferred by the kernel).
            let e_c = elab(env, scope, e, None)?;
            let e_ty = synth_type(env, scope, &e_c);
            let sc = scope.push_var_ty(x, e_ty.clone());
            // `expected` lives in `scope` (size n); `sc` has one extra binder (the let-bound `x`),
            // so any free variables in `expected` referring to outer-scope binders must be shifted
            // up by 1 to remain valid indices in `sc` — the same weakening `cod` below performs.
            // Passing `expected` unweakened here mixes de Bruijn baselines and was rejected only
            // deep inside the kernel (a `Pi`/`compare`-typed value leaking in where a universe or
            // the true expected type was wanted) whenever `expected` mentioned an outer variable.
            let expected_in_sc = expected.map(|c| weaken(c, 1));
            let body_c = elab(env, &sc, body, expected_in_sc.as_ref())?;
            let lam = Term::Lam(Rc::new(body_c.clone()));
            // The codomain: the expected result if known, else the body's synthesized type
            // (strengthened back past the `x` binder so it is valid in the outer scope).
            let cod = match expected {
                Some(c) => Some(weaken(c, 1)),
                None => synth_type(env, &sc, &body_c),
            };
            let fun = match (e_ty, cod) {
                (Some(dom), Some(cod)) => {
                    let pi = Term::Pi(blight_kernel::Grade::Omega, Rc::new(dom), Rc::new(cod));
                    Term::Ann(Rc::new(lam), Rc::new(pi))
                }
                _ => lam,
            };
            Ok(Term::App(Rc::new(fun), Rc::new(e_c)))
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
            // See the `Surface::Let` case above: `expected` lives in `scope`, but `sc` has one
            // extra binder, so it must be weakened by 1 before checking `body` against it.
            let expected_in_sc = expected.map(|c| weaken(c, 1));
            let body_c = elab(env, &sc, body, expected_in_sc.as_ref())?;
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
            let pi = Term::Pi(blight_kernel::Grade::One, Rc::new(rgn_ty), Rc::new(cod));
            let fun = Term::Ann(Rc::new(Term::Lam(Rc::new(body_c))), Rc::new(pi));
            Ok(Term::App(Rc::new(fun), Rc::new(tok)))
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
            Ok(Term::Pi(grade, Rc::new(dom), Rc::new(cod_c)))
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
                    Some(c) if env.is_class(&c) => out.push(ImplicitSpec::Instance {
                        class: c,
                        name: b.name.clone(),
                    }),
                    _ => out.push(ImplicitSpec::Unify {
                        name: b.name.clone(),
                    }),
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
            T::Pi(g, a, b) => T::Pi(*g, Rc::new(go(a, j, d)), Rc::new(go(b, j + 1, d))),
            T::Sigma(a, b) => T::Sigma(Rc::new(go(a, j, d)), Rc::new(go(b, j + 1, d))),
            T::Lam(b) => T::Lam(Rc::new(go(b, j + 1, d))),
            T::PLam(b) => T::PLam(Rc::new(go(b, j + 1, d))),
            T::App(f, x) => T::App(Rc::new(go(f, j, d)), Rc::new(go(x, j, d))),
            T::Pair(a, b) => T::Pair(Rc::new(go(a, j, d)), Rc::new(go(b, j, d))),
            T::Fst(p) => T::Fst(Rc::new(go(p, j, d))),
            T::Snd(p) => T::Snd(Rc::new(go(p, j, d))),
            T::Ann(a, b) => T::Ann(Rc::new(go(a, j, d)), Rc::new(go(b, j, d))),
            T::Data(n, ps, is) => T::Data(
                n.clone(),
                ps.iter().map(|x| go(x, j, d)).collect(),
                is.iter().map(|x| go(x, j, d)).collect(),
            ),
            T::Con(n, args) => T::Con(n.clone(), args.iter().map(|x| go(x, j, d)).collect()),
            T::Delay(a) => T::Delay(Rc::new(go(a, j, d))),
            T::Now(a) => T::Now(Rc::new(go(a, j, d))),
            T::Later(a) => T::Later(Rc::new(go(a, j, d))),
            other => other.clone(),
        }
    }
    go(t, cutoff, d)
}

/// Render an explicit-argument unification failure during implicit-argument insertion (E2): an
/// [`UnifyError::Ambiguous`] names both candidate types the elaborator saw for the same implicit
/// (e.g. two list elements of visibly different types pinning a shared `{A (Type 0)}` two ways);
/// anything else falls back to the declared-vs-actual domain/argument types, still pretty-printed
/// rather than silent.
fn implicit_unify_error(
    g: &str,
    mc: &MetaCtx,
    err: UnifyError,
    dom: &Term,
    at: &Term,
) -> ElabError {
    match err {
        UnifyError::Ambiguous(pair) => ElabError::BadForm(format!(
            "ambiguous implicit argument of `{g}`: saw both `{}` and `{}`",
            pretty_term(&pair.0),
            pretty_term(&pair.1)
        )),
        UnifyError::Mismatch => ElabError::BadForm(format!(
            "implicit-argument mismatch for `{g}`: expected `{}`, got `{}`",
            pretty_term(&mc.zonk(dom)),
            pretty_term(&mc.zonk(at))
        )),
    }
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
        Unify {
            name: String,
            meta: Term,
        },
        Instance {
            class: String,
            name: String,
            dom: Term,
        },
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
            ImplicitSpec::Unify { name } => {
                let id = mc.fresh();
                let m = meta_term(id);
                slots.push(Slot::Unify {
                    name: name.clone(),
                    meta: m.clone(),
                });
                ty = subst0_closed(&cod, &m);
            }
            ImplicitSpec::Instance { class, name } => {
                // Defer: the dictionary occupies this binder; advance the type with a placeholder
                // meta so dependent later binders still type. The placeholder is solved only if it
                // is later constrained; the dictionary value is filled by search below.
                let id = mc.fresh();
                let placeholder = meta_term(id);
                slots.push(Slot::Instance {
                    class: class.clone(),
                    name: name.clone(),
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
                .map_err(|e| implicit_unify_error(g, &mc, e, &dom, &at))?;
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
            Slot::Unify { name, meta } => {
                let z = mc.zonk(&meta);
                if mc.has_unsolved(&z) {
                    return Err(ElabError::BadForm(format!(
                        "could not infer implicit argument `{name}` of `{g}` (add an annotation)"
                    )));
                }
                inserted.push(z);
            }
            Slot::Instance { class, name, dom } => {
                // The constraint type `(class A)`: A is the first type argument; resolve its head.
                let dom_z = mc.zonk(&dom);
                let head = instance_head_of(&class, &dom_z).ok_or_else(|| {
                    ElabError::BadForm(format!(
                        "could not determine the instance head for implicit `{name}` (`{class}`) \
                         in `{g}`"
                    ))
                })?;
                let dict = env.lookup_instance(&class, &head).ok_or_else(|| {
                    ElabError::BadForm(format!(
                        "no instance `{class} {head}` in scope, needed for implicit `{name}` of \
                         `{g}`"
                    ))
                })?;
                inserted.push(dict.clone());
            }
        }
    }
    // 5. Build `((g implicit…) explicit…)`.
    let mut head = g_term.clone();
    for s in inserted {
        head = Term::App(Rc::new(head), Rc::new(s));
    }
    for e in explicit {
        head = Term::App(Rc::new(head), Rc::new(e));
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
            Ok(Term::Sigma(Rc::new(dom), Rc::new(cod_c)))
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
///
/// `0`/`1` in a grade slot arrive as `Surface::NatLit` (E1's bare-decimal sugar parses through the
/// same `parse_surface` used for the grade position), not `Surface::Var` — matched here so a
/// grade literal keeps meaning a grade, never a `Nat` value.
fn parse_grade(grade: Option<&Surface>) -> Result<blight_kernel::Grade, ElabError> {
    use blight_kernel::Grade;
    match grade {
        None => Ok(Grade::Omega),
        Some(Surface::NatLit(0)) => Ok(Grade::Zero),
        Some(Surface::NatLit(1)) => Ok(Grade::One),
        Some(Surface::NatLit(other)) => Err(ElabError::BadForm(format!(
            "binder grade must be 0, 1, or omega; got `{other}`"
        ))),
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
                                // Binding a self-call to the scrutinee's induction hypothesis *drops*
                                // the call's leading arguments (the `Elim` fixes the leading params at
                                // their outer values). That is sound only when every leading argument
                                // that *varies* from its parameter is irrelevant to the runtime value:
                                //
                                //   * an erased (grade-0) **index** — e.g. the length `m` in
                                //     `vec-length A m xs` — leaves no runtime trace, and the IH already
                                //     carries the specialized result type, so dropping it is exact; but
                                //   * a grade-1 **accumulator** — e.g. `sum-acc (Succ acc) m` — *does*
                                //     determine the value, so dropping `(Succ acc)` silently reuses the
                                //     stale `acc` (a meaning bug the kernel's type re-check can't see:
                                //     both are `Nat`).
                                //
                                // We therefore require each leading argument to be EITHER the leading
                                // parameter verbatim OR at an erased position. (An effectful recursor
                                // additionally reorders the eager per-step `perform`s, so it keeps the
                                // strict verbatim rule.) A varying runtime leading argument falls
                                // through: `deftotal` errors, `define-rec` takes the `later`-guard.
                                let leading_ok = (0..k).all(|j| {
                                    let verbatim = matches!(
                                        &args[j], Surface::Var(v) if *v == rec.leading[j]
                                    );
                                    // A non-verbatim (varying) leading argument may be dropped only
                                    // when its parameter is *irrelevant* to the result (so the IH's
                                    // value is unaffected). An effectful recursor additionally
                                    // reorders the eager per-step `perform`s, so it keeps the strict
                                    // verbatim rule. An unknown/missing summary entry defaults to
                                    // relevant (not droppable) — the safe direction.
                                    let irrelevant = !rec.relevance.get(j).copied().unwrap_or(true);
                                    verbatim || (!rec.effectful && irrelevant)
                                });
                                if leading_ok {
                                    if let Some(idx) = scope.var_index(ih_name) {
                                        let mut head = Term::Var(idx);
                                        for a in &args[k + 1..] {
                                            head = Term::App(
                                                Rc::new(head),
                                                Rc::new(elab(env, scope, a, None)?),
                                            );
                                        }
                                        return Ok(Some(head));
                                    }
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
                                    Term::App(Rc::new(head), Rc::new(elab(env, scope, a, None)?));
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
                    head = Term::App(Rc::new(head), Rc::new(elab(env, scope, a, None)?));
                }
                return Ok(Some(Term::Later(Rc::new(head))));
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

/// Whether `ty`'s conclusion (after peeling `Pi` binders) is an *effectful* computation type
/// `! E A` with a non-empty effect row. Used by [`elaborate_rec`] to require verbatim leading
/// arguments for effectful structural recursors (where eager induction-hypothesis evaluation would
/// reorder/drop per-step effects), while leaving pure indexed families on the lenient recognition.
fn has_effectful_conclusion(ty: &Term) -> bool {
    let mut t = ty;
    loop {
        match t {
            Term::Pi(_, _, cod) => t = cod,
            Term::EffTy(row, inner) => {
                if !row.is_empty() {
                    return true;
                }
                t = inner;
            }
            _ => return false,
        }
    }
}

/// Collect every parameter name whose value can reach the function's *result* — used by
/// [`compute_relevance`]. Scans `s` for `Surface::Var` occurrences, but skips the argument positions
/// that provably never reach the result:
///
///   * the first `k` (leading) arguments of a **self-call** `(self a0 … a_{k-1} scrut trailing…)`,
///     which the structural `Elim` drops (it fixes the leading parameters at their outer values); and
///   * the *irrelevant* argument positions of a call to a **known callee** (per its already-computed
///     summary in `callees`) — e.g. the index args of `bvar-index`, which that function never lets
///     reach its own result, so they cannot reach this one through it either.
///
/// Every other occurrence — base-case returns, trailing self-call arguments (applied to the
/// induction hypothesis), constructor arguments, arguments at relevant callee positions, type
/// positions, and *all* arguments of an unknown head (a local, a constructor, a partial application)
/// — is counted. Skipping only provably-dropped/-ignored positions guarantees we never undercount an
/// escape, so the criterion built on this set is sound (worst case: over-rejection, never a silent
/// miscompile).
fn collect_escaping_vars(
    s: &Surface,
    self_name: &str,
    k: usize,
    callees: &std::collections::HashMap<String, Vec<bool>>,
    out: &mut std::collections::HashSet<String>,
) {
    use Surface::*;
    let go = |x: &Surface, out: &mut std::collections::HashSet<String>| {
        collect_escaping_vars(x, self_name, k, callees, out)
    };
    match s {
        Var(name) => {
            out.insert(name.clone());
        }
        App(f, args) => {
            go(f, out);
            // Decide, per argument position, whether it can reach this application's result (and so
            // the function's result). A self-call drops its leading args; a known callee drops its
            // own irrelevant positions; anything else (constructor, local, partial app) keeps all.
            let summary: Option<&Vec<bool>> = match &**f {
                Var(h) if h == self_name => None, // self-call: handled by `k` below
                Var(h) => callees.get(h),
                _ => None,
            };
            let is_self = matches!(&**f, Var(h) if h == self_name);
            for (i, a) in args.iter().enumerate() {
                let reaches_result = if is_self {
                    i >= k
                } else {
                    // Known callee: only relevant positions reach the result. Positions beyond the
                    // summary (e.g. over-application) are treated as reaching it (conservative).
                    summary
                        .map(|s| s.get(i).copied().unwrap_or(true))
                        .unwrap_or(true)
                };
                if reaches_result {
                    go(a, out);
                }
            }
        }
        The(a, b) | PApp(a, b) | Bang(a, b) | Pair(a, b) | IntPrim(_, a, b) => {
            go(a, out);
            go(b, out);
        }
        Lam(_, b)
        | PLam(_, b)
        | Delay(b)
        | Now(b)
        | Later(b)
        | Force(b)
        | Fst(b)
        | Snd(b)
        | Region(_, b)
        | Unglue(b)
        | Partial(_, b) => go(b, out),
        Perform(_, type_args, b) => {
            for t in type_args {
                go(t, out);
            }
            go(b, out);
        }
        Pi(binders, cod) | Sigma(binders, cod) => {
            for b in binders {
                go(&b.ty, out);
            }
            go(cod, out);
        }
        Path(a, b, c) | Glue(a, _, b, c) => {
            go(a, out);
            go(b, out);
            go(c, out);
        }
        GlueTerm(_, t, e) | Transp(t, _, e) => {
            go(t, out);
            go(e, out);
        }
        // Conservative: every operand can reach the result (the Kan layer has no dedicated
        // relevance analysis, so all of `ty`/`tube`/`base` — and `family` for `Comp` — count).
        HComp(a, _, b, c) | Comp(a, _, b, c) => {
            go(a, out);
            go(b, out);
            go(c, out);
        }
        Match(scruts, clauses) => {
            for sc in scruts {
                go(sc, out);
            }
            for c in clauses {
                go(&c.body, out);
            }
        }
        Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            go(body, out);
            go(&return_clause.1, out);
            for (_, _, _, e) in op_clauses {
                go(e, out);
            }
        }
        Let(_, e, b) => {
            go(e, out);
            go(b, out);
        }
        System(arms) => {
            for (_, e) in arms {
                go(e, out);
            }
        }
        // Leaves with no variable sub-terms.
        Univ(_) | IntTy | IntLit(_) | NatLit(_) => {}
    }
}

/// Peel the leading lambda parameters of a definition body, in source order.
fn peel_lam_params(body: &Surface) -> Vec<String> {
    let mut params = Vec::new();
    let mut t = body;
    while let Surface::Lam(binders, inner) = t {
        params.extend(binders.iter().cloned());
        t = inner;
    }
    params
}

/// The number of *leading* parameters before the structural recursion variable: the position of the
/// outermost `match`'s (first) scrutinee among the peeled lambda parameters. Returns `0` when the
/// shape is not the recognized `λ params. (match param …)` (so a self-call drops nothing — the safe,
/// over-approximating direction). This is the same `k` the structural `Elim` lowering uses; computing
/// it syntactically here lets the relevance summary be a pure function of the surface definition.
fn syntactic_leading_k(body: &Surface, params: &[String]) -> usize {
    let mut t = body;
    while let Surface::Lam(_, inner) = t {
        t = inner;
    }
    if let Surface::Match(scruts, _) = t {
        if let Some(Surface::Var(s)) = scruts.first() {
            if let Some(pos) = params.iter().position(|p| p == s) {
                return pos;
            }
        }
    }
    0
}

/// Compute the relevant-parameter summary of a definition: for each leading lambda parameter, whether
/// its value can reach the result. `callees` holds the summaries of earlier definitions (used to see
/// through index-ignoring helpers). See [`collect_escaping_vars`] for the soundness argument.
fn compute_relevance(
    name: &str,
    body: &Surface,
    callees: &std::collections::HashMap<String, Vec<bool>>,
) -> Vec<bool> {
    let params = peel_lam_params(body);
    let k = syntactic_leading_k(body, &params);
    let mut esc = std::collections::HashSet::new();
    collect_escaping_vars(body, name, k, callees, &mut esc);
    params.iter().map(|p| esc.contains(p)).collect()
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
            effectful: has_effectful_conclusion(ty),
            param_depth: None,
            relevance: std::rc::Rc::new(env.relevant_params.get(name).cloned().unwrap_or_default()),
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
                effectful: has_effectful_conclusion(ty),
                param_depth: None,
                relevance: std::rc::Rc::new(
                    env.relevant_params.get(name).cloned().unwrap_or_default(),
                ),
            });
            // `body` is checked against `ty` under the extra `self` binder; `ty` mentions no
            // bound vars (it is closed), so no shifting is needed for it.
            let inner = elab(env, &scope, body, Some(ty))?;
            Ok(Term::Lam(Rc::new(inner)))
        }
    }
}

/// Coverage pre-pass over a surface `match`'s first-column patterns (E3, v0.1 roadmap). Runs at
/// every `Surface::Match` level — including the flat sub-matches [`lower_match`] produces for
/// nested/multi-scrutinee patterns, since those re-enter `elab` — so a missing *nested* case
/// (`(just (nothing))` with no `(just (just _))`) is caught when its inner match is elaborated.
///
/// Produces a clear, up-front diagnostic where the old behavior surfaced a generic
/// "no clause for constructor `X`" one constructor at a time, deep in column compilation:
///   * **non-exhaustive** — lists *every* missing constructor of the scrutinee's data type at once;
///   * **duplicate arm** — the same constructor matched twice (single-scrutinee only, where a
///     repeat is unambiguously redundant — a multi-scrutinee `matchx` legitimately repeats a
///     first-column constructor while refining a later column);
///   * **unreachable arm** — a clause following a first-column catch-all `_`/var (single-scrutinee).
///
/// Conservative by construction: it only *rejects*; it never changes which constructor set is
/// required (that stays the kernel's `Elim`). When the data type can't be determined (all-wildcard
/// column, or an unknown/foreign constructor) it returns `Ok`, deferring to the main elaborator.
fn check_match_coverage(
    env: &ElabEnv,
    scruts: &[Surface],
    clauses: &[Clause],
) -> Result<(), ElabError> {
    use crate::surface::Pattern;
    if clauses.is_empty() {
        return Ok(()); // an empty match is diagnosed elsewhere
    }
    let single = scruts.len() == 1;
    // The scrutinee's data type, read off the first first-column constructor pattern.
    let data = clauses.iter().find_map(|c| match c.patterns.first() {
        Some(Pattern::Con(con, _)) => env.constructors.get(con).map(|i| i.data.clone()),
        _ => None,
    });
    let Some(data) = data else {
        return Ok(()); // all wildcards/vars, or no patterns — nothing to check here
    };
    let Some(all_ctors) = env.datas.get(&data).cloned() else {
        return Ok(());
    };

    // A first-column constructor pattern is *saturating* when all its sub-patterns are variables or
    // wildcards — it then matches every value of that constructor, so a later arm with the same
    // constructor is unreachable. A *nested* arm (`(just (nothing))`) is not saturating: a sibling
    // arm with the same constructor but a different refinement (`(just (just x))`) is legitimate, so
    // only saturating repeats are flagged as duplicates.
    fn is_saturating(subs: &[Pattern]) -> bool {
        subs.iter()
            .all(|s| matches!(s, Pattern::Var(_) | Pattern::Wild))
    }
    let mut covered: Vec<String> = Vec::new();
    let mut saturated: Vec<String> = Vec::new();
    let mut catch_all: Option<usize> = None;
    for (i, c) in clauses.iter().enumerate() {
        // A clause after a first-column catch-all can never match (single-scrutinee only: with more
        // columns a "catch-all" in column 0 still refines later columns, so later rows are live).
        if single {
            if let Some(prev) = catch_all {
                return Err(ElabError::BadMatch(format!(
                    "unreachable `match` arm: clause {} can never match — clause {} already \
                     catches every remaining `{data}` value",
                    i + 1,
                    prev + 1
                )));
            }
        }
        match c.patterns.first() {
            Some(Pattern::Con(con, subs)) => {
                // A constructor of a *different* type in the column: not our business — the main
                // elaborator produces the (type-mismatch) error.
                if env.constructors.get(con).map(|inf| inf.data.as_str()) != Some(data.as_str()) {
                    return Ok(());
                }
                // A previous saturating arm for this constructor already matches all its values, so
                // this arm — saturating or nested — is unreachable (single-scrutinee only).
                if single && saturated.contains(con) {
                    return Err(ElabError::BadMatch(format!(
                        "duplicate `match` arm: constructor `{con}` of `{data}` is matched more \
                         than once (an earlier arm already matches every `{con}` value)"
                    )));
                }
                if is_saturating(subs) && !saturated.contains(con) {
                    saturated.push(con.clone());
                }
                if !covered.contains(con) {
                    covered.push(con.clone());
                }
            }
            Some(Pattern::Var(_)) | Some(Pattern::Wild) => catch_all = Some(i),
            None => return Ok(()),
        }
    }
    // A first-column catch-all covers every remaining constructor — exhaustive.
    if catch_all.is_some() {
        return Ok(());
    }
    let missing: Vec<&String> = all_ctors.iter().filter(|c| !covered.contains(c)).collect();
    if !missing.is_empty() {
        let names = missing
            .iter()
            .map(|c| format!("`{c}`"))
            .collect::<Vec<_>>()
            .join(", ");
        let plural = if missing.len() == 1 { "" } else { "s" };
        return Err(ElabError::BadMatch(format!(
            "non-exhaustive `match` on `{data}`: missing case{plural} {names}"
        )));
    }
    Ok(())
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
        Term::Pi(g, a, b) => Some((g, unshare(a), unshare(b))),
        _ => None,
    }
}

/// Reduce a type term toward a `Sigma` head (see [`whnf_pi`]). Returns `(domain, codomain)`.
fn whnf_sigma(t: &Term) -> Option<(Term, Term)> {
    match whnf_head(t) {
        Term::Sigma(a, b) => Some((unshare(a), unshare(b))),
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
            Term::Ann(e, _) => unshare(e),
            Term::App(f, x) => match whnf_head(&f) {
                Term::Lam(b) => subst0_closed(&b, &x),
                other => return Term::App(Rc::new(other), x),
            },
            Term::Fst(p) => match whnf_head(&p) {
                Term::Pair(a, _) => unshare(a),
                other => return Term::Fst(Rc::new(other)),
            },
            Term::Snd(p) => match whnf_head(&p) {
                Term::Pair(_, b) => unshare(b),
                other => return Term::Snd(Rc::new(other)),
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
            Term::Lam(b) => Term::Lam(Rc::new(go(b, depth + 1, d))),
            Term::Now(b) => Term::Now(Rc::new(go(b, depth, d))),
            Term::Later(b) => Term::Later(Rc::new(go(b, depth, d))),
            Term::Delay(b) => Term::Delay(Rc::new(go(b, depth, d))),
            Term::Force(b) => Term::Force(Rc::new(go(b, depth, d))),
            Term::PLam(b) => Term::PLam(Rc::new(go(b, depth + 1, d))),
            Term::Pi(gr, a, b) => Term::Pi(
                *gr,
                Rc::new(go(a, depth, d)),
                Rc::new(go(b, depth + 1, d)),
            ),
            Term::Sigma(a, b) => {
                Term::Sigma(Rc::new(go(a, depth, d)), Rc::new(go(b, depth + 1, d)))
            }
            Term::App(f, x) => Term::App(Rc::new(go(f, depth, d)), Rc::new(go(x, depth, d))),
            Term::Pair(a, b) => Term::Pair(Rc::new(go(a, depth, d)), Rc::new(go(b, depth, d))),
            Term::Fst(p) => Term::Fst(Rc::new(go(p, depth, d))),
            Term::Snd(p) => Term::Snd(Rc::new(go(p, depth, d))),
            Term::Ann(e, ty) => Term::Ann(Rc::new(go(e, depth, d)), Rc::new(go(ty, depth, d))),
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
                                  // An IH binder is deliberately excluded from trailing generalization even though it now
                                  // carries a real type (for `synth_type`'s sake — see the IH-typing note above): reusing it
                                  // here would eagerly wrap unrelated inner matches in a Pi-telescope over the (function-
                                  // typed) induction hypothesis, a behavior change unrelated to giving self-calls an
                                  // inferable type. Treat it exactly as the untyped case: bail out to `m = 0`, matching the
                                  // pre-existing behavior for any match nested below an IH binder.
        let is_ih_binder = scope.vars[pos].ends_with("#ih");
        match scope.var_types[pos].clone() {
            // The stored type lives in a scope of size `pos`; lift it into the full scope (size
            // `n_vars`) by shifting its free variables up by `n_vars - pos`.
            Some(ty) if !is_ih_binder => trailing.push(weaken(&ty, n_vars - pos)),
            _ => {
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
        motive_body = Term::Pi(Grade::Omega, Rc::new(dom), Rc::new(motive_body));
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

    // The scrutinee's actual type parameters `p0 .. p_{k-1}` (from its type `D p0..p_{k-1}
    // i1..im`), rebased into the full current scope exactly like `index_vars` above. A
    // constructor's declared field types are expressed relative to the family's OWN param
    // telescope (e.g. `just : Pi (x a) (Maybe a)`'s field type is the bare param variable `a`), so
    // reading a field's type in the *caller's* scope for a parametric — not just param-free —
    // family requires substituting these concrete values in first (see `field_ty` below).
    let scrut_params: Option<Vec<Term>> = scope
        .var_types
        .get(scrut_pos)
        .and_then(|o| o.as_ref())
        .map(|ty| weaken(ty, n_vars - scrut_pos))
        .and_then(|ty| match whnf_head(&ty) {
            Term::Data(d, ps, is) if d.0 == data_name && is.len() == decl_nindices => Some(ps),
            _ => None,
        });

    // For per-method *index refinement* of the re-introduced trailing binders: when this match's
    // scrutinee `s : D ps i1..im` has variable indices `ivars`, each constructor's arm refines those
    // index variables to the constructor's result-index expressions (e.g. matching `v : Vec A n`
    // against `vcons m …` refines `n ↦ Succ m`). A trailing binder whose stored type mentions one of
    // those index variables (e.g. a second vector `w : Vec B n` still in scope) must be re-bound at
    // its *refined* type (`Vec B (Succ m)`) so that a nested match on it elaborates against the type
    // the kernel will actually see. Without this, the elaborator builds the nested match's motive by
    // abstracting a stale bare index variable that no longer matches the kernel's refined scrutinee
    // index — the `zip-vec` inner-match de Bruijn/index mismatch.
    let refine_ivars: Vec<usize> = index_vars.clone().unwrap_or_default();
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
            let mut motive = Term::Lam(Rc::new(shifted));
            for _ in 0..decl_nindices {
                motive = Term::Lam(Rc::new(motive));
            }
            motive
        }
        // Non-indexed family, or an out-of-fragment dependent indexed motive: the bare `λ s. …`
        // shape. For an indexed family the kernel/re-checker will adjudicate (decline/reject) rather
        // than silently accept an ill-formed motive.
        _ => Term::Lam(Rc::new(abstract_var(&motive_body, scrut_idx))),
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

    // Is this match on a *function parameter* (the recursion variable) or on a field exposed by a
    // *nested* match? Only the former may establish structural induction hypotheses for self-calls
    // (see `RecCtx::param_depth`). The parameter depth is the scope size at the outermost match; a
    // scrutinee whose absolute scope position is below it is a parameter. The outermost match itself
    // (no `param_depth` recorded yet) is, by definition, on a parameter.
    let scrut_abs = scope.vars.len() - 1 - scrut_idx;
    let scrutinee_is_param = match scope.rec.as_ref().and_then(|r| r.param_depth) {
        Some(pd) => scrut_abs < pd,
        None => true,
    };

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
        // the kernel constructor signature when readable — any index-free family, parametric or
        // not, whose scrutinee's actual parameter values we could read off above (`scrut_params`) —
        // so nested matches and `let`-aliases over the bound fields can synthesize types. (Indexed
        // families are excluded: substituting their field types would additionally need the
        // per-method index *refinement* this function already computes separately below, and mixing
        // the two is more machinery than any current stdlib use needs.)
        let kernel_con = env
            .signature()
            .data_of_con(&blight_kernel::ConName(cname.clone()))
            .map(|(decl, _, con)| (decl.params.len(), decl.indices.is_empty(), con.clone()));
        let mut sc = scope.clone();
        let mut rec = sc.rec.clone();
        if let Some(r) = rec.as_mut() {
            // Record the parameter depth at the outermost match so nested matches can tell their
            // (field) scrutinees apart from the recursion variable.
            if r.param_depth.is_none() {
                r.param_depth = Some(scope.vars.len());
            }
            // Only the *outermost* match of a recursive function establishes the leading-parameter
            // layout; nested matches inherit it (overwriting would describe the inner scrutinee's
            // context, breaking recursive-call recognition in the inner body).
            if r.leading.is_empty() {
                r.leading = leading_names.clone();
            }
        }
        let mut n_con_binders = 0usize;
        for (i, (arg_name, &is_rec)) in clause.binders.iter().zip(&info.rec_flags).enumerate() {
            // The field's type, if cheaply known: an index-free family (params substituted in via
            // `scrut_params`, empty for a param-free family) whose declared arg type we can read.
            let field_ty = kernel_con
                .as_ref()
                .and_then(|(nparams, indices_empty, con)| {
                    if !*indices_empty {
                        return None;
                    }
                    let ps: Vec<Term> = if *nparams == 0 {
                        vec![]
                    } else {
                        scrut_params.clone()?
                    };
                    match con.args.get(i) {
                        Some(blight_kernel::Arg::NonRec(t)) => {
                            // The declared field type lives in a scope of exactly `nparams` param
                            // binders (param 0 outermost, so at index `nparams-1`; the last-declared
                            // param innermost, at index 0). Substitute innermost-first so each
                            // `subst0_closed` call always targets the current `Var(0)`.
                            let mut ft = t.clone();
                            for p in ps.iter().rev() {
                                ft = subst0_closed(&ft, p);
                            }
                            Some(ft)
                        }
                        Some(blight_kernel::Arg::Rec(_)) => Some(Term::Data(
                            blight_kernel::DataName(data_name.clone()),
                            ps,
                            vec![],
                        )),
                        None => None,
                    }
                });
            sc = sc.push_var_ty(arg_name, field_ty);
            n_con_binders += 1;
            if is_rec {
                let ih_name = format!("{arg_name}#ih");
                // Give the IH binder a real type when we can, rather than leaving it opaque to
                // `synth_type`. For a non-indexed family the whole match's motive is exactly
                // `λs. Π(trailing). expected'` (see `motive_body` above, pre-index-abstraction);
                // the IH for a structurally-smaller field is that same shape with the scrutinee
                // replaced by the field. Concretely: weaken `motive_body` (built relative to
                // `scope`) into `sc`'s current scope (which has `n_con_binders` more binders — the
                // fields/IHs introduced so far for this constructor, including this field's own
                // `arg_name` binder just pushed above), then substitute the (now-shifted) free
                // occurrence of the scrutinee for `arg_name`'s own `Var(0)`. Without this, a
                // self-call's result type is `None` under `synth_type`, and consuming it (e.g. in
                // a further `match`, or a `let`) forces an unascribed `Lam`/`Pair` into inference
                // position — the "cannot infer a type" bug this fixes (indexed families are left
                // opaque; their IH additionally needs the *refined* indices, computed only later).
                let ih_ty = if decl_nindices == 0 {
                    let shifted = weaken(&motive_body, n_con_binders);
                    Some(subst_var(
                        &shifted,
                        scrut_idx + n_con_binders,
                        &Term::Var(0),
                    ))
                } else {
                    None
                };
                sc = sc.push_var_ty(&ih_name, ih_ty);
                n_con_binders += 1;
                // The IH binder is always introduced (the kernel `Elim` supplies `self field` for
                // every recursive field), but it is only offered to *self-calls* when this match is
                // on a function parameter. A nested match's field IH belongs to the inner eliminator,
                // not to `self`; registering it would silently miscompile a course-of-values call.
                if scrutinee_is_param {
                    if let Some(r) = rec.as_mut() {
                        r.ih.insert(arg_name.clone(), ih_name);
                    }
                }
            }
        }
        sc.rec = rec;

        // Per-method *index refinement* of the trailing binder types (see `refine_ivars` above).
        // We compute, for this constructor, the refined value of each matched index variable — the
        // constructor's `result_indices[d]` re-expressed in *this method's* de Bruijn scope — and
        // substitute it for the (weakened) outer index variable in every trailing binder type. We
        // handle the standard fragment where each result index is built from the constructor's own
        // arguments (e.g. `vcons`'s `Succ m`); if a result index references a *parameter* or is
        // otherwise outside this fragment we leave the trailing types unrefined (the kernel /
        // re-checker still adjudicate — they will reject or decline rather than silently accept).
        let refined_indices: Option<Vec<Term>> = if refine_ivars.is_empty() {
            None
        } else {
            kernel_con.as_ref().and_then(|(_, _, con)| {
                if con.result_indices.len() != refine_ivars.len() {
                    return None;
                }
                let num_args = info.rec_flags.len();
                // Map each constructor argument (source order) to its de Bruijn index within the
                // con/IH binder block (the block sits *above* the not-yet-introduced trailing
                // binders, so within the block the innermost binder is de Bruijn 0).
                let mut seq: Vec<bool> = Vec::new(); // true = real arg, false = IH binder
                for &is_rec in info.rec_flags.iter() {
                    seq.push(true);
                    if is_rec {
                        seq.push(false);
                    }
                }
                let total = seq.len();
                debug_assert_eq!(total, n_con_binders);
                let mut arg_db: Vec<usize> = Vec::with_capacity(num_args);
                for (k, is_arg) in seq.iter().enumerate() {
                    if *is_arg {
                        // The k-th binder from the *outside* of the block sits at de Bruijn
                        // `total - 1 - k` (innermost = 0). But trailing binders will be pushed
                        // *below* (inside) these, so when we substitute into a trailing type the
                        // con/IH binders are at de Bruijn `total - 1 - k` *plus* the trailing depth;
                        // we record the in-block index and add the local `depth` during `conv`.
                        arg_db.push(total - 1 - k);
                    }
                }
                // Convert one `result_index` term from constructor-arg de Bruijn (innermost = last
                // arg; params follow the args) into this method's scope. Returns `None` if it
                // references anything we can't map (e.g. a parameter).
                fn conv(t: &Term, depth: usize, num_args: usize, arg_db: &[usize]) -> Option<Term> {
                    use blight_kernel::Term as T;
                    Some(match t {
                        T::Var(v) => {
                            if *v < depth {
                                T::Var(*v)
                            } else {
                                let a = *v - depth; // constructor-arg index (0 = last arg)
                                if a < num_args {
                                    let src_pos = num_args - 1 - a; // source order position
                                    T::Var(arg_db[src_pos] + depth)
                                } else {
                                    // A parameter or out-of-range: outside the supported fragment.
                                    return None;
                                }
                            }
                        }
                        T::Con(c, args) => T::Con(
                            c.clone(),
                            args.iter()
                                .map(|x| conv(x, depth, num_args, arg_db))
                                .collect::<Option<Vec<_>>>()?,
                        ),
                        T::Data(d, ps, is) => T::Data(
                            d.clone(),
                            ps.iter()
                                .map(|x| conv(x, depth, num_args, arg_db))
                                .collect::<Option<Vec<_>>>()?,
                            is.iter()
                                .map(|x| conv(x, depth, num_args, arg_db))
                                .collect::<Option<Vec<_>>>()?,
                        ),
                        T::App(f, x) => T::App(
                            Rc::new(conv(f, depth, num_args, arg_db)?),
                            Rc::new(conv(x, depth, num_args, arg_db)?),
                        ),
                        // Anything richer is outside the fragment we refine.
                        _ => return None,
                    })
                }
                let mut out = Vec::with_capacity(con.result_indices.len());
                for rix in &con.result_indices {
                    out.push(conv(rix, 0, num_args, &arg_db)?);
                }
                Some(out)
            })
        };

        // Re-introduce the trailing binders (outermost-first so t_0 ends up at Var0 in the body).
        for i in (0..m).rev() {
            let pos = scope.vars.len() - 1 - i;
            let name = scope.vars[pos].clone();
            // Lift the trailing type into this method's scope (past the `n_con_binders` con/IH
            // binders), then apply the per-method index refinement.
            let mut ty = weaken(&trailing[i], n_con_binders);
            if let Some(refined) = &refined_indices {
                for (d, &iv) in refine_ivars.iter().enumerate() {
                    // The outer index variable `iv` now sits `n_con_binders` deeper.
                    ty = subst_var(&ty, iv + n_con_binders, &refined[d]);
                }
            }
            sc = sc.push_var_ty(&name, Some(ty));
        }

        // The method body is checked against the match result type when the motive is
        // *non-dependent* (the common case: `expected` does not mention the scrutinee). This lets
        // an inner `match` in the body elaborate in checking mode. For a dependent motive we keep
        // synthesis (`None`), as the body's type genuinely specializes per constructor.
        let body_expected = if mentions_var(expected, scrut_idx) {
            None
        } else {
            // Weaken past the constructor/IH binders and the re-introduced trailing binders, then
            // apply the same per-method index refinement as the trailing binders: in this arm the
            // matched index variables are specialized to the constructor's result indices, so the
            // body's expected type must use the refined indices (e.g. `Vec (Pair A B) n` becomes
            // `Vec (Pair A B) (Succ m)` in `vcons`). Without this a nested match in the body would
            // be checked against a stale index the kernel has already refined away.
            let mut exp = weaken(expected, n_con_binders + m);
            if let Some(refined) = &refined_indices {
                for (d, &iv) in refine_ivars.iter().enumerate() {
                    exp = subst_var(&exp, iv + n_con_binders + m, &weaken(&refined[d], m));
                }
            }
            Some(exp)
        };
        let body = elab(env, &sc, clause.body, body_expected.as_ref())?;
        // Wrap: innermost are the trailing binders, then the constructor/IH binders.
        let mut method = body;
        for _ in 0..m {
            method = Term::Lam(Rc::new(method));
        }
        for _ in 0..n_con_binders {
            method = Term::Lam(Rc::new(method));
        }
        methods.push(method);
    }

    let elim = Term::Elim {
        data: DataName(data_name),
        motive: Rc::new(motive),
        methods,
        scrutinee: Rc::new(Term::Var(scrut_idx)),
    };

    // The match produced a value of `motive scrut`, i.e. `Pi(trailing) expected`. Re-apply it to
    // the trailing binders so the surrounding lambdas see a value of `expected`.
    let mut applied = elim;
    for i in (0..m).rev() {
        applied = Term::App(Rc::new(applied), Rc::new(Term::Var(i)));
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
    // Parallel (simultaneous) abstraction. `targets[j]` (a de Bruijn index in the *original* scope)
    // becomes bound variable `j` in the body (so `targets[0]` is the innermost new binder). Every
    // free variable that is NOT a target is shifted up by `p = targets.len()` to make room for the
    // new binders; every occurrence of `targets[j]` is rewritten to that binder.
    //
    // A *sequential* fold (`abstract_var` per target) is WRONG when more than one target is
    // abstracted: each wrapping `Lam` shifts the still-unabstracted free variables, so a later
    // target index can collide with an already-shifted *non*-target (this is exactly the
    // higher-order-motive `zip-vec` bug — abstracting the index `n` after the scrutinee `v` made
    // `n`'s adjusted index coincide with the shifted element-type parameter `B`). Doing it in one
    // pass with a fixed target→binder map avoids the collision entirely.
    let p = targets.len();
    // `binder_of[t] = Some(j)` means original de Bruijn `t` is `targets[j]`.
    let binder_of = |t: usize| -> Option<usize> { targets.iter().position(|&x| x == t) };
    fn go(t: &Term, depth: usize, p: usize, binder_of: &dyn Fn(usize) -> Option<usize>) -> Term {
        use blight_kernel::Term as T;
        let r = |x: &T| go(x, depth, p, binder_of);
        let r1 = |x: &T| go(x, depth + 1, p, binder_of);
        match t {
            T::Var(i) => {
                if crate::meta::is_meta(*i) {
                    return T::Var(*i);
                }
                if *i < depth {
                    // Bound by a binder introduced *inside* `term` (below the abstraction point).
                    T::Var(*i)
                } else {
                    let orig = *i - depth;
                    match binder_of(orig) {
                        // A target: bind to its new binder `j`, re-adding the local `depth`.
                        Some(j) => T::Var(depth + j),
                        // A non-target free var: shift up by `p` to make room for the new binders.
                        None => T::Var(*i + p),
                    }
                }
            }
            T::Univ(_)
            | T::Interval(_)
            | T::Erased
            | T::IntTy
            | T::IntLit(_)
            | T::Foreign { .. } => t.clone(),
            T::Pi(g, a, b) => T::Pi(*g, Rc::new(r(a)), Rc::new(r1(b))),
            T::Sigma(a, b) => T::Sigma(Rc::new(r(a)), Rc::new(r1(b))),
            T::Lam(b) => T::Lam(Rc::new(r1(b))),
            T::PLam(b) => T::PLam(Rc::new(r(b))),
            T::PApp(pp, iv) => T::PApp(Rc::new(r(pp)), iv.clone()),
            T::App(f, a) => T::App(Rc::new(r(f)), Rc::new(r(a))),
            T::Pair(a, b) => T::Pair(Rc::new(r(a)), Rc::new(r(b))),
            T::Fst(a) => T::Fst(Rc::new(r(a))),
            T::Snd(a) => T::Snd(Rc::new(r(a))),
            T::Ann(a, b) => T::Ann(Rc::new(r(a)), Rc::new(r(b))),
            T::Data(d, ps, is) => T::Data(
                d.clone(),
                ps.iter().map(&r).collect(),
                is.iter().map(&r).collect(),
            ),
            T::Con(c, args) => T::Con(c.clone(), args.iter().map(&r).collect()),
            T::PCon {
                data,
                name,
                args,
                dim,
            } => T::PCon {
                data: data.clone(),
                name: name.clone(),
                args: args.iter().map(&r).collect(),
                dim: dim.clone(),
            },
            T::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => T::Elim {
                data: data.clone(),
                // The motive binds one variable (the scrutinee).
                motive: Rc::new(r1(motive)),
                methods: methods.iter().map(&r).collect(),
                scrutinee: Rc::new(r(scrutinee)),
            },
            T::PathP { family, lhs, rhs } => T::PathP {
                // `family` binds one dimension variable, not a term variable: keep term depth.
                family: Rc::new(r(family)),
                lhs: Rc::new(r(lhs)),
                rhs: Rc::new(r(rhs)),
            },
            T::Partial(c, a) => T::Partial(c.clone(), Rc::new(r(a))),
            T::System(_) => t.clone(),
            T::Transp {
                family,
                cofib,
                base,
            } => T::Transp {
                family: Rc::new(r(family)),
                cofib: cofib.clone(),
                base: Rc::new(r(base)),
            },
            T::HComp {
                ty,
                cofib,
                tube,
                base,
            } => T::HComp {
                ty: Rc::new(r(ty)),
                cofib: cofib.clone(),
                tube: Rc::new(r(tube)),
                base: Rc::new(r(base)),
            },
            T::Comp {
                family,
                cofib,
                tube,
                base,
            } => T::Comp {
                family: Rc::new(r(family)),
                cofib: cofib.clone(),
                tube: Rc::new(r(tube)),
                base: Rc::new(r(base)),
            },
            T::Glue {
                base,
                cofib,
                ty,
                equiv,
            } => T::Glue {
                base: Rc::new(r(base)),
                cofib: cofib.clone(),
                ty: Rc::new(r(ty)),
                equiv: Rc::new(r(equiv)),
            },
            T::GlueTerm {
                cofib,
                partial,
                base,
            } => T::GlueTerm {
                cofib: cofib.clone(),
                partial: Rc::new(r(partial)),
                base: Rc::new(r(base)),
            },
            T::Unglue(a) => T::Unglue(Rc::new(r(a))),
            T::Op {
                effect,
                op,
                type_args,
                arg,
            } => T::Op {
                effect: effect.clone(),
                op: op.clone(),
                type_args: type_args.iter().map(&r).collect(),
                arg: Rc::new(r(arg)),
            },
            T::Handle {
                body,
                return_clause,
                op_clauses,
            } => T::Handle {
                body: Rc::new(r(body)),
                // `return_clause` binds the result value `x` (1 binder).
                return_clause: Rc::new(r1(return_clause)),
                // each op clause binds the operation argument `x` then the continuation `k`
                // (2 binders).
                op_clauses: op_clauses
                    .iter()
                    .map(|(name, cl)| (name.clone(), Rc::new(go(cl, depth + 2, p, binder_of))))
                    .collect(),
            },
            T::EffTy(row, a) => T::EffTy(row.clone(), Rc::new(r(a))),
            T::Delay(a) => T::Delay(Rc::new(r(a))),
            T::Now(a) => T::Now(Rc::new(r(a))),
            T::Later(a) => T::Later(Rc::new(r(a))),
            T::Force(a) => T::Force(Rc::new(r(a))),
            T::IntPrim { op, lhs, rhs } => T::IntPrim {
                op: *op,
                lhs: Rc::new(r(lhs)),
                rhs: Rc::new(r(rhs)),
            },
        }
    }
    let mut body = go(term, 0, p, &binder_of);
    for _ in 0..p {
        body = Term::Lam(Rc::new(body));
    }
    body
}

/// Substitute `c` for de Bruijn 0 in `t`, decrementing the remaining indices. Capture-avoiding for
/// *any* `c` (not just a closed one): each time the traversal descends under a binder, the
/// insertion site sits `j` binders deeper than where `c` was valid, so `c` itself must be shifted
/// by `j` at the point of insertion (`weaken(c, j)`), exactly as ordinary substitution requires.
///
/// This was previously named `subst0_closed` and skipped that shift (`c.clone()` regardless of
/// `j`), on the documented assumption that `c` "mentions no bound variables". That assumption did
/// not hold at every call site — e.g. [`synth_type`]'s `App` case substitutes an *argument's*
/// elaborated term, which is routinely a plain variable reference such as a type parameter `V` —
/// so whenever the target `t` mentioned the substituted de Bruijn index at more than one nesting
/// depth (e.g. a polymorphic function's codomain like `Pi (mv : Maybe V) (Maybe V)`, which uses `V`
/// both in the domain and, one binder deeper, in the codomain), only the *shallowest* occurrence
/// substituted correctly; deeper ones inserted an unshifted (too-low) index, silently corrupting
/// the synthesized type. This surfaced as spurious kernel `not definitionally equal` rejections —
/// a `Data(...)` value appearing where a universe (or the real expected type) was wanted — for any
/// `let`/`match` whose scrutinee was a call to a polymorphic function. Since `weaken(c, 0) == c`,
/// this is a strict generalization: still correct when `c` happens to be closed.
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
                    Ordering::Equal => weaken(c, j),
                    Ordering::Greater => T::Var(i - 1),
                    Ordering::Less => T::Var(*i),
                }
            }
            T::Univ(_) | T::Interval(_) | T::Erased | T::System(_) => t.clone(),
            T::Pi(g, a, b) => T::Pi(*g, Rc::new(go(a, j, c)), Rc::new(go(b, j + 1, c))),
            T::Sigma(a, b) => T::Sigma(Rc::new(go(a, j, c)), Rc::new(go(b, j + 1, c))),
            T::Lam(b) => T::Lam(Rc::new(go(b, j + 1, c))),
            T::PLam(b) => T::PLam(Rc::new(go(b, j + 1, c))),
            T::App(f, x) => T::App(Rc::new(go(f, j, c)), Rc::new(go(x, j, c))),
            T::Pair(a, b) => T::Pair(Rc::new(go(a, j, c)), Rc::new(go(b, j, c))),
            T::Fst(p) => T::Fst(Rc::new(go(p, j, c))),
            T::Snd(p) => T::Snd(Rc::new(go(p, j, c))),
            T::Ann(a, b) => T::Ann(Rc::new(go(a, j, c)), Rc::new(go(b, j, c))),
            T::Data(n, ps, is) => T::Data(
                n.clone(),
                ps.iter().map(|x| go(x, j, c)).collect(),
                is.iter().map(|x| go(x, j, c)).collect(),
            ),
            T::Con(n, args) => T::Con(n.clone(), args.iter().map(|x| go(x, j, c)).collect()),
            T::Delay(a) => T::Delay(Rc::new(go(a, j, c))),
            T::Now(a) => T::Now(Rc::new(go(a, j, c))),
            T::Later(a) => T::Later(Rc::new(go(a, j, c))),
            // M3 implicit insertion only instantiates ordinary (non-cubical, non-effect) codomains.
            other => other.clone(),
        }
    }
    go(t, 0, c)
}

/// Substitute the free de Bruijn variable `target` with `repl` everywhere in `t`, **without**
/// renumbering the other variables (an in-place replacement, not a binder elimination). `repl` is
/// shifted up as the traversal crosses binders so it remains valid at each occurrence. Used for
/// per-method index refinement of trailing-binder types (e.g. replacing the matched index variable
/// `n` with a constructor's refined index `Succ m`).
fn subst_var(t: &Term, target: usize, repl: &Term) -> Term {
    fn go(t: &Term, j: usize, target: usize, repl: &Term) -> Term {
        use blight_kernel::Term as T;
        let r = |x: &T| go(x, j, target, repl);
        let r1 = |x: &T| go(x, j + 1, target, repl);
        match t {
            T::Var(i) => {
                if crate::meta::is_meta(*i) {
                    T::Var(*i)
                } else if *i == j + target {
                    // Shift the replacement past the `j` binders crossed so far.
                    weaken(repl, j)
                } else {
                    T::Var(*i)
                }
            }
            T::Univ(_)
            | T::Interval(_)
            | T::Erased
            | T::System(_)
            | T::IntTy
            | T::IntLit(_)
            | T::Foreign { .. } => t.clone(),
            T::Pi(g, a, b) => T::Pi(*g, Rc::new(r(a)), Rc::new(r1(b))),
            T::Sigma(a, b) => T::Sigma(Rc::new(r(a)), Rc::new(r1(b))),
            T::Lam(b) => T::Lam(Rc::new(r1(b))),
            T::PLam(b) => T::PLam(Rc::new(r(b))),
            T::PApp(p, iv) => T::PApp(Rc::new(r(p)), iv.clone()),
            T::App(f, x) => T::App(Rc::new(r(f)), Rc::new(r(x))),
            T::Pair(a, b) => T::Pair(Rc::new(r(a)), Rc::new(r(b))),
            T::Fst(p) => T::Fst(Rc::new(r(p))),
            T::Snd(p) => T::Snd(Rc::new(r(p))),
            T::Ann(a, b) => T::Ann(Rc::new(r(a)), Rc::new(r(b))),
            T::Data(n, ps, is) => T::Data(
                n.clone(),
                ps.iter().map(&r).collect(),
                is.iter().map(&r).collect(),
            ),
            T::Con(n, args) => T::Con(n.clone(), args.iter().map(&r).collect()),
            T::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => T::Elim {
                data: data.clone(),
                motive: Rc::new(r1(motive)),
                methods: methods.iter().map(&r).collect(),
                scrutinee: Rc::new(r(scrutinee)),
            },
            T::Delay(a) => T::Delay(Rc::new(r(a))),
            T::Now(a) => T::Now(Rc::new(r(a))),
            T::Later(a) => T::Later(Rc::new(r(a))),
            T::Force(a) => T::Force(Rc::new(r(a))),
            // Refinement only ever touches simple type/term structure (Pi/Sigma/Data/Con/App over
            // the index variables); cubical/effect nodes are left structurally untouched here. If a
            // trailing type contained one, its inner free vars would not be refined — but those are
            // outside the supported fragment and the kernel/re-checker still adjudicate.
            other => other.clone(),
        }
    }
    go(t, 0, target, repl)
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
        T::Pi(g, a, b) => T::Pi(*g, Rc::new(r(a)), Rc::new(r1(b))),
        T::Lam(b) => T::Lam(Rc::new(r1(b))),
        T::App(f, a) => T::App(Rc::new(r(f)), Rc::new(r(a))),
        T::Sigma(a, b) => T::Sigma(Rc::new(r(a)), Rc::new(r1(b))),
        T::Pair(a, b) => T::Pair(Rc::new(r(a)), Rc::new(r(b))),
        T::Fst(a) => T::Fst(Rc::new(r(a))),
        T::Snd(a) => T::Snd(Rc::new(r(a))),
        T::Ann(a, b) => T::Ann(Rc::new(r(a)), Rc::new(r(b))),
        T::Data(d, ps, is) => T::Data(
            d.clone(),
            ps.iter().map(r).collect(),
            is.iter().map(r).collect(),
        ),
        T::Con(c, args) => T::Con(c.clone(), args.iter().map(r).collect()),
        T::PCon {
            data,
            name,
            args,
            dim,
        } => T::PCon {
            data: data.clone(),
            name: name.clone(),
            args: args.iter().map(r).collect(),
            dim: dim.clone(),
        },
        T::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => T::Elim {
            data: data.clone(),
            // motive binds one variable (the scrutinee).
            motive: Rc::new(r1(motive)),
            methods: methods.iter().map(r).collect(),
            scrutinee: Rc::new(r(scrutinee)),
        },
        T::Interval(iv) => T::Interval(iv.clone()),
        T::PathP { family, lhs, rhs } => T::PathP {
            // family binds one dimension variable, not a term variable: keep term depth.
            family: Rc::new(r(family)),
            lhs: Rc::new(r(lhs)),
            rhs: Rc::new(r(rhs)),
        },
        T::PLam(b) => T::PLam(Rc::new(r(b))),
        T::PApp(p, iv) => T::PApp(Rc::new(r(p)), iv.clone()),
        T::Partial(c, a) => T::Partial(c.clone(), Rc::new(r(a))),
        T::System(_) => term.clone(),
        T::Transp {
            family,
            cofib,
            base,
        } => T::Transp {
            family: Rc::new(r(family)),
            cofib: cofib.clone(),
            base: Rc::new(r(base)),
        },
        T::HComp {
            ty,
            cofib,
            tube,
            base,
        } => T::HComp {
            ty: Rc::new(r(ty)),
            cofib: cofib.clone(),
            tube: Rc::new(r(tube)),
            base: Rc::new(r(base)),
        },
        T::Comp {
            family,
            cofib,
            tube,
            base,
        } => T::Comp {
            family: Rc::new(r(family)),
            cofib: cofib.clone(),
            tube: Rc::new(r(tube)),
            base: Rc::new(r(base)),
        },
        T::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => T::Glue {
            base: Rc::new(r(base)),
            cofib: cofib.clone(),
            ty: Rc::new(r(ty)),
            equiv: Rc::new(r(equiv)),
        },
        T::GlueTerm {
            cofib,
            partial,
            base,
        } => T::GlueTerm {
            cofib: cofib.clone(),
            partial: Rc::new(r(partial)),
            base: Rc::new(r(base)),
        },
        T::Unglue(a) => T::Unglue(Rc::new(r(a))),
        T::Op {
            effect,
            op,
            type_args,
            arg,
        } => T::Op {
            effect: effect.clone(),
            op: op.clone(),
            type_args: type_args.iter().map(&r).collect(),
            arg: Rc::new(r(arg)),
        },
        T::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            let r2 = |t: &T| abstract_var_at(t, k, depth + 2);
            T::Handle {
                body: Rc::new(r(body)),
                return_clause: Rc::new(r1(return_clause)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(name, e)| (name.clone(), Rc::new(r2(e))))
                    .collect(),
            }
        }
        T::EffTy(row, a) => T::EffTy(row.clone(), Rc::new(r(a))),
        T::Delay(a) => T::Delay(Rc::new(r(a))),
        T::Now(a) => T::Now(Rc::new(r(a))),
        T::Later(a) => T::Later(Rc::new(r(a))),
        T::Force(a) => T::Force(Rc::new(r(a))),
        T::Foreign { symbol, ty } => T::Foreign {
            symbol: symbol.clone(),
            ty: Rc::new(r(ty)),
        },
        // Int type/literal carry no de Bruijn content; an IntPrim's operands must be abstracted.
        T::IntTy | T::IntLit(_) => term.clone(),
        T::IntPrim { op, lhs, rhs } => T::IntPrim {
            op: *op,
            lhs: Rc::new(r(lhs)),
            rhs: Rc::new(r(rhs)),
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
            Term::Force(inner) => match unshare(inner) {
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

    /// Regression (varying-leading-argument soundness): a `deftotal` whose recursive call varies a
    /// *runtime-relevant* leading argument — a genuine **accumulator** — must be rejected, not
    /// silently compiled to a structural `Elim` that drops the change. `sum-acc acc n` recurses on
    /// `n` while threading `acc` forward via `(Succ acc)`; the `Elim` fixes the leading `acc` at its
    /// outer value, so binding the call to `n`'s induction hypothesis would discard `(Succ acc)` and
    /// the function would always return its initial `acc` (e.g. `sum-acc Zero 3 = 0`, not `3`). The
    /// kernel's *type* re-check cannot catch this (both are `Nat`), so the elaborator must refuse it.
    #[test]
    fn deftotal_rejects_varying_leading_accumulator() {
        let env = env_with_decls(&["(defdata Nat () (Zero) (Succ (n Nat)))"]);
        let ty = elaborate(
            &env,
            &parse_surface(&read_one("(Pi ((acc Nat) (n Nat)) Nat)").unwrap().0).unwrap(),
        )
        .expect("sum-acc type elaborates");
        let body = parse_surface(
            &read_one(
                "(lam (acc) (lam (n) (match n \
                   [(Zero) acc] \
                   [(Succ m) (sum-acc (Succ acc) m)])))",
            )
            .unwrap()
            .0,
        )
        .unwrap();
        let decl = Decl::DefTotal {
            name: "sum-acc".into(),
            body,
        };
        let mut env = env;
        let res = env.declare(&decl, Some(&ty));
        assert!(
            matches!(res, Err(ElabError::BadMatch(ref m)) if m.contains("structural sub-term")),
            "a deftotal varying a runtime-relevant leading accumulator must be rejected, got {res:?}"
        );
    }

    /// Companion to the above: a structural fold whose varied leading argument is *irrelevant* to the
    /// result must still be accepted. `vec-length` varies its leading length index `n` (→ the
    /// constructor's predecessor `m`) in the recursive call, but the spine length it computes is
    /// independent of `n`, so dropping the varied index is exact. The interprocedural relevance
    /// analysis must see this and not over-reject (the dual hazard of the accumulator fix).
    #[test]
    fn defrec_accepts_varying_irrelevant_leading_index() {
        let env = env_with_decls(&[
            "(defdata Nat () (Zero) (Succ (n Nat)))",
            "(defdata Vec ((a (Type 0))) ((n Nat)) \
                (vnil (=> Zero)) \
                (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))",
        ]);
        let ty = elaborate(
            &env,
            &parse_surface(
                &read_one("(Pi ((A (Type 0)) (n Nat) (v (Vec A n))) Nat)")
                    .unwrap()
                    .0,
            )
            .unwrap(),
        )
        .expect("vec-length type elaborates");
        let body = parse_surface(
            &read_one(
                "(lam (A n v) (match v \
                   [(vnil) Zero] \
                   [(vcons m x xs) (Succ (vec-length A m xs))]))",
            )
            .unwrap()
            .0,
        )
        .unwrap();
        let decl = Decl::DefineRec {
            name: "vec-length".into(),
            body,
        };
        let mut env = env;
        env.declare(&decl, Some(&ty))
            .expect("a structural fold whose varied leading index is irrelevant must be accepted");
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
        let ident = Term::Lam(Rc::new(Term::Var(0)));
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
            Rc::new(ty.clone()),
            Rc::new(shift_closed(&ty)),
        );
        let ann = Term::Ann(Rc::new(term), Rc::new(self_ty));
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

    /// `(! (State Extra) Nat)` elaborates to `Term::EffTy` with a row carrying both labels (Wave
    /// 7/E1: closed multi-label rows — previously only a single label was expressible).
    #[test]
    fn bang_multi_label_row_type() {
        let mut env = state_env();
        let (sx, _) = read_one("(effect Extra (bump Nat Nat))").expect("reads");
        let decl = parse_decl(&sx).expect("parses");
        env.declare(&decl, None).expect("declares");

        let (sx, _) = read_one("(! (State Extra) Nat)").expect("reads");
        let term = elaborate(&env, &parse_surface(&sx).expect("parses")).expect("elaborates");
        match term {
            Term::EffTy(row, _) => {
                assert!(row.contains(&blight_kernel::EffName::new("State")));
                assert!(row.contains(&blight_kernel::EffName::new("Extra")));
            }
            other => panic!("expected Term::EffTy, got {other:?}"),
        }
    }

    /// An open row-variable tail used somewhere other than directly ascribing a `handle` is a
    /// clean `ElabError`, not a silent accept or a dropped tail (Wave 7/E1).
    #[test]
    fn bang_open_tail_without_handle_ascription_rejected() {
        let env = state_env();
        let (sx, _) = read_one("(! (State | r) Nat)").expect("reads");
        let err = elaborate(&env, &parse_surface(&sx).expect("parses"))
            .expect_err("an unresolved row-variable tail must be rejected, not accepted");
        assert!(
            matches!(err, ElabError::BadForm(_)),
            "expected a clean BadForm, got {err:?}"
        );
    }

    /// Row-variable unification (Wave 7/E1): `{State | r}` unified against the concrete row
    /// `{State, Extra}` succeeds, resolving `r` to the row's *extension* `{Extra}` — whatever the
    /// pattern didn't explicitly name.
    #[test]
    fn row_var_unifies_with_extension() {
        use blight_kernel::{EffName, Grade, Row};
        let pattern = RowPattern {
            labels: vec![EffName::new("State")],
            tail: Some("r".to_string()),
        };
        let concrete = Row::single(EffName::new("State"), Grade::Omega)
            .union(&Row::single(EffName::new("Extra"), Grade::Omega));
        let mut scope = RowVarScope::new();
        let resolved = scope.unify(&pattern, &concrete).expect("unifies");
        assert_eq!(
            resolved, concrete,
            "unify returns the concrete row unchanged on success"
        );
        assert_eq!(
            scope.0.get("r"),
            Some(&Row::single(EffName::new("Extra"), Grade::Omega)),
            "r resolves to the extension {{Extra}}"
        );
    }

    /// Two incompatible resolutions of the same row variable are a clean `ElabError`, never a
    /// kernel panic — the mandated reject twin for row-variable unification (Wave 7/E1).
    #[test]
    fn row_tail_mismatch_rejected() {
        use blight_kernel::{EffName, Grade, Row};
        let pattern = RowPattern {
            labels: vec![EffName::new("State")],
            tail: Some("r".to_string()),
        };
        let mut scope = RowVarScope::new();
        let first = Row::single(EffName::new("State"), Grade::Omega)
            .union(&Row::single(EffName::new("Extra1"), Grade::Omega));
        scope
            .unify(&pattern, &first)
            .expect("first resolution unifies");

        let second = Row::single(EffName::new("State"), Grade::Omega)
            .union(&Row::single(EffName::new("Extra2"), Grade::Omega));
        let err = scope
            .unify(&pattern, &second)
            .expect_err("a second, incompatible resolution of `r` must be rejected");
        assert!(
            matches!(err, ElabError::BadForm(_)),
            "expected a clean BadForm, got {err:?}"
        );
    }

    /// A declared label that is not actually present in the concrete row is also a clean reject.
    #[test]
    fn row_pattern_missing_label_rejected() {
        use blight_kernel::{EffName, Grade, Row};
        let pattern = RowPattern {
            labels: vec![EffName::new("State")],
            tail: Some("r".to_string()),
        };
        let mut scope = RowVarScope::new();
        let concrete = Row::single(EffName::new("Extra"), Grade::Omega);
        let err = scope
            .unify(&pattern, &concrete)
            .expect_err("State is not present in the concrete row");
        assert!(matches!(err, ElabError::BadForm(_)));
    }

    /// `(the (! (Extra1 | r) Nat) (handle (perform get tt) (return x (perform bump1 (perform
    /// bump2 x))) (get u k (k Zero))))` — a row-polymorphic handler ascription (Wave 7/E1). The
    /// handler discharges `State` (its only clause); the return clause performs two further
    /// effects, `Extra1` and `Extra2`. `r` is unified against the handle's actual, kernel-inferred
    /// row, resolving to `{Extra2}` — the "whatever else" the declared type didn't name. This
    /// exercises the full elaboration path end to end (the elaborator-level twin of
    /// `stdlib::row_polymorphic_handler_composes`, which exercises the same mechanism through a
    /// real `examples/`-backed program and the `Program` driver).
    #[test]
    fn row_polymorphic_handler_ascription_resolves_tail() {
        let mut env = state_env();
        for src in [
            "(effect Extra1 (bump1 Nat Nat))",
            "(effect Extra2 (bump2 Nat Nat))",
        ] {
            let (sx, _) = read_one(src).expect("reads");
            let decl = parse_decl(&sx).expect("parses");
            env.declare(&decl, None).expect("declares");
        }
        let src = "(the (! (Extra1 | r) Nat) \
                     (handle (perform get tt) \
                       (return x (perform bump1 (perform bump2 x))) \
                       (get u k (k Zero))))";
        let (sx, _) = read_one(src).expect("reads");
        let term = elaborate(&env, &parse_surface(&sx).expect("parses")).expect("elaborates");
        match term {
            Term::Ann(inner, ty) => {
                assert!(
                    matches!(*inner, Term::Handle { .. }),
                    "the ascribed term is the Handle, unchanged"
                );
                match unshare(ty) {
                    Term::EffTy(row, _) => {
                        assert!(
                            row.contains(&blight_kernel::EffName::new("Extra1")),
                            "Extra1 is present, as declared"
                        );
                        assert!(
                            row.contains(&blight_kernel::EffName::new("Extra2")),
                            "Extra2 is present -- the resolved tail"
                        );
                        assert!(
                            !row.contains(&blight_kernel::EffName::new("State")),
                            "State was discharged by the handler"
                        );
                    }
                    other => panic!("expected Term::EffTy, got {other:?}"),
                }
            }
            other => panic!("expected Term::Ann, got {other:?}"),
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
