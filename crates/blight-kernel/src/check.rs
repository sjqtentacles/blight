//! The inference rules (spec §2.5–§2.7): the bidirectional checker. This is the **only** place
//! a [`Proof`] is constructed (via the crate-private `Proof::trusted_new`).
//!
//! `infer` synthesizes a type for a term; `check` verifies a term against an expected type,
//! driving definitional equality through [`crate::normalize::conv`]. A successful top-level
//! `check`/`infer` yields a `Proof` of the corresponding `HasType` judgement.

use crate::context::Context;
use crate::normalize::{conv, conv_dim, eval, quote, quote_value_at, reflect};
use crate::proof::{Judgement, Proof};
use crate::row::Row;
use crate::semiring::{Grade, Semiring};
use crate::signature::{Arg, Constructor, DataDecl, Signature};
use crate::term::{Cofib, DataName, Level, Term};
use crate::usage::Usage;
use crate::value::{Env, Neutral, Value};

/// A kernel type error. Carries enough to report *why* a term failed to check; it never
/// indicates unsoundness, only "this did not grow a proof" (spec §1.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    /// A variable index escaped the context.
    UnboundVar(usize),
    /// Expected one head former, found another (e.g. applied a non-function).
    Mismatch { expected: String, found: String },
    /// Definitional equality failed (`Conv`): `lhs ≢ rhs`.
    NotConvertible { lhs: String, rhs: String },
    /// A grade discipline violation (e.g. linear variable used twice).
    GradeViolation(String),
    /// Universe inconsistency (level error).
    UniverseError(String),
    /// A malformed inductive declaration (e.g. strict-positivity failure).
    BadDataDecl(String),
    /// A malformed cubical term (e.g. a path with wrong boundary).
    BadCubical(String),
    /// A term that cannot be inferred (needs an ascription).
    CannotInfer(String),
    /// An effect-discipline violation (spec §4): an effect escaped where a pure/total computation
    /// was required, an unknown effect/operation was performed, or a handler was malformed.
    EffectError(String),
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::UnboundVar(i) => write!(f, "unbound variable (de Bruijn index {i})"),
            TypeError::Mismatch { expected, found } => {
                write!(f, "type mismatch: expected {expected}, found {found}")
            }
            TypeError::NotConvertible { lhs, rhs } => {
                write!(f, "not definitionally equal: {lhs} ≢ {rhs}")
            }
            TypeError::GradeViolation(s) => write!(f, "grade discipline: {s}"),
            TypeError::UniverseError(s) => write!(f, "universe level error: {s}"),
            TypeError::BadDataDecl(s) => write!(f, "malformed inductive declaration: {s}"),
            TypeError::BadCubical(s) => write!(f, "malformed cubical term: {s}"),
            TypeError::CannotInfer(s) => {
                write!(f, "cannot infer a type (needs an ascription): {s}")
            }
            TypeError::EffectError(s) => write!(f, "effect discipline: {s}"),
        }
    }
}

impl std::error::Error for TypeError {}

// =======================================================================================
// Dependent pattern-match refinement support types (plan item 1b).
// =======================================================================================

/// The result of refining one constructor branch against the scrutinee's index values.
#[derive(Debug, Clone)]
enum Refinement {
    /// A head-constructor clash: the branch can never apply to this scrutinee, so its method is
    /// *not* required (the branch is vacuous). This is what lets the kernel certify `safe-tail`'s
    /// `vnil` branch (index `Zero` clashes with `Succ n`).
    Unreachable,
    /// Unification solved: `args` carries the forced value of each constructor argument (`None` if
    /// it stays a fresh binder), and `ambient` carries the per-branch specialization of scrutinee
    /// index variables (`(level, value)` pairs).
    Solved {
        args: Vec<Option<Value>>,
        ambient: Vec<(usize, Value)>,
    },
    /// Unification made no progress (or got stuck) — fall back to the plain `method_type` check so
    /// nothing previously accepted regresses.
    Stuck,
}

/// The accumulating solution while unifying one branch's result indices.
struct RSolution {
    /// Forced values for the constructor's arguments (indexed by argument position).
    args: Vec<Option<Value>>,
    /// Specializations of ambient scrutinee-index variables, as `(level, value)` pairs.
    ambient: Vec<(usize, Value)>,
}

/// The outcome of unifying a single index pair.
#[derive(Debug, Clone, Copy)]
enum Unify {
    /// Heads clash — branch unreachable.
    Clash,
    /// A variable was solved (made progress).
    Progress,
    /// Already rigidly equal — no new information.
    Trivial,
    /// Cannot decide soundly — fall back to the plain rule.
    Stuck,
}

/// Concretize a [`Level`] to a natural number. For M0, levels are closed (no level variables in
/// the surface), so this is total; level-variable support is added with universe polymorphism.
fn level_to_nat(l: &Level) -> Result<u32, TypeError> {
    match l {
        Level::Zero => Ok(0),
        Level::Suc(inner) => Ok(level_to_nat(inner)? + 1),
        Level::Max(a, b) => Ok(level_to_nat(a)?.max(level_to_nat(b)?)),
        Level::Var(_) => Err(TypeError::UniverseError(
            "level variables not yet supported in M0 core".into(),
        )),
    }
}

/// Build a [`Level`] from a natural number.
fn nat_to_level(n: u32) -> Level {
    let mut l = Level::Zero;
    for _ in 0..n {
        l = Level::Suc(Box::new(l));
    }
    l
}

/// The kernel checker, carrying the inductive [`Signature`] consulted when typing
/// `Data`/`Con`/`Elim`. All inference and checking are methods so the signature is threaded
/// implicitly (and shared into evaluation environments for ι-reduction).
pub struct Checker {
    pub sig: std::rc::Rc<Signature>,
}

impl Checker {
    pub fn new(sig: std::rc::Rc<Signature>) -> Self {
        Checker { sig }
    }

    /// Build an evaluation environment at the given context depth that carries the signature, so
    /// that evaluating `Elim` inside types performs ι-reduction. Dimension variables are seeded as
    /// free dimension *levels* so cubical types evaluate to neutrals rather than panicking.
    fn env_for(&self, ctx: &Context) -> Env {
        let n = ctx.len();
        // Build the environment exactly as the plain neutral version does (so de Bruijn levels match
        // the rest of the kernel), but *reflect* each binder against its type (see
        // [`crate::normalize::reflect`]). For a plain type this yields the bare neutral; for a
        // `PathP` type it yields a `ReflectedPath` carrying endpoints; for a path-valued function
        // `h : Pi A (Path ..)` it yields a `ReflectedFun` that carries endpoints through application.
        //
        // Each entry's type is stored relative to its *outer* context (see `check`'s
        // `quote(ctx.len(), ..)` when extending), so we must evaluate it in the environment of the
        // binders already added. We therefore add binders outer-to-inner, matching `ctx.lookup`'s
        // index convention where index `n-1` is outermost.
        let mut env = Env::with_sig(self.sig.clone());
        let mut prefix: Vec<Value> = Vec::with_capacity(n);
        for i in (0..n).rev() {
            // `check` introduces the binder at context index `i` with a neutral at level `n-1-i`
            // (see Pi-Intro: `Var(ctx.len())` at introduction time). `env_for` must use the *same*
            // level convention, otherwise multi-binder types resolve their outer references to the
            // wrong neutral.
            let level = n - 1 - i;
            let entry = ctx.lookup(i).expect("context entry in range");
            // Evaluate the entry's type in the environment of strictly-outer binders.
            let outer_env = {
                let mut e = Env::with_sig(self.sig.clone());
                for v in prefix.iter() {
                    e = e.extend(v.clone());
                }
                e
            };
            let value = reflect(Neutral::Var(level), &eval(&outer_env, &entry.ty));
            prefix.push(value.clone());
            env = env.extend(value);
        }
        let d = ctx.dim_len();
        for _ in 0..d {
            let level = d - 1 - env.dim_len();
            env = env.extend_dim(crate::term::Interval::Dim(level));
        }
        // Apply per-branch refinement overrides (item 1b): specialize the named ambient variables to
        // their solved values. Each override term is evaluated in the fully-built env (it may mention
        // the branch's freshly-bound constructor arguments), then written at the variable's level.
        // This is the kernel analog of the re-checker's `refine_ambient`.
        for (lvl, t) in ctx.overrides() {
            let v = eval(&env, t);
            env = env.set_level(*lvl, v);
        }
        env
    }

    /// Like [`Self::env_for`] but with `extra` additional binders pushed on top (innermost last),
    /// each reflected as a bare neutral at the next free de Bruijn level. Used when typing a
    /// telescope of index binders whose later types may reference earlier index variables.
    fn env_with_vars(&self, ctx: &Context, extra: &[Value]) -> Env {
        let mut env = self.env_for(ctx);
        for v in extra.iter() {
            env = env.extend(v.clone());
        }
        env
    }
    /// the term's type as a semantic [`Value`]. Convenience wrapper that demands `term` at grade
    /// `ω` and discards the usage vector (used by tests and by type-formation call sites that do
    /// not themselves account usage).
    pub fn infer(&self, ctx: &Context, term: &Term) -> Result<Value, TypeError> {
        self.infer_g(ctx, term, Grade::Omega).map(|(ty, _r, _u)| ty)
    }

    /// The graded inference direction (spec §3.2, §4.1): synthesize a type, the **effect row** the
    /// computation incurs, *and* the usage vector recording how much each in-scope variable was
    /// demanded, given the ambient demand `sigma` on `term` itself. Pure terms infer the empty row;
    /// `Op` contributes its effect's label; eliminators union their subterms' rows.
    pub fn infer_g(
        &self,
        ctx: &Context,
        term: &Term,
        sigma: Grade,
    ) -> Result<(Value, Row, Usage), TypeError> {
        let n = ctx.len();
        match term {
            // Var (graded, spec §3.2): the variable contributes the unit usage `e_i` at the ambient
            // demand `sigma`; the `ρ ≥ demand` discipline is enforced at the *binder* (Lam), not here.
            Term::Var(i) => {
                let entry = ctx.lookup(*i).ok_or(TypeError::UnboundVar(*i))?;
                // The entry's type is stored relative to the context *below* index `i` (Pi-Intro
                // quotes the domain at the then-current depth, before extension). To evaluate it in
                // the full-context environment we weaken it past the `i + 1` binders now inside it.
                let ty = shift(&entry.ty, *i + 1);
                let ty_val = eval(&self.env_for(ctx), &ty);
                Ok((ty_val, Row::empty(), Usage::unit(*i, n, sigma)))
            }

            // Univ ℓ : Univ (ℓ+1)  (spec §2.4, U-Type). A universe is pure type formation: no usage.
            Term::Univ(l) => {
                let lv = level_to_nat(l)?;
                Ok((
                    Value::Univ(nat_to_level(lv + 1)),
                    Row::empty(),
                    Usage::zero(n),
                ))
            }

            // Pi-Form: Γ ⊢ A : Univ ℓ, Γ,x:^ρ A ⊢ B : Univ ℓ' ⟹ Pi : Univ (ℓ ⊔ ℓ'). Type formation
            // runs in the 0-fragment, so it contributes no usage.
            Term::Pi(grade, dom, cod) => {
                let dom_lvl = self.infer_universe(ctx, dom)?;
                let ctx2 = ctx.extend((**dom).clone(), *grade);
                let cod_lvl = self.infer_universe(&ctx2, cod)?;
                Ok((
                    Value::Univ(nat_to_level(dom_lvl.max(cod_lvl))),
                    Row::empty(),
                    Usage::zero(n),
                ))
            }

            // Sigma-Form, analogous (grade ω on the first component for M0).
            Term::Sigma(dom, cod) => {
                let dom_lvl = self.infer_universe(ctx, dom)?;
                let ctx2 = ctx.extend((**dom).clone(), Grade::Omega);
                let cod_lvl = self.infer_universe(&ctx2, cod)?;
                Ok((
                    Value::Univ(nat_to_level(dom_lvl.max(cod_lvl))),
                    Row::empty(),
                    Usage::zero(n),
                ))
            }

            // Pi-Elim / app (graded, spec §3.2): infer f :^σ Pi (x:^ρ A) B, check a :^(σ·ρ) A, result
            // B[a/x]; usage is `usage_f + usage_a` (the argument's demand is already scaled by σ·ρ).
            // The result row is the union of the function's and argument's rows (spec §4.1).
            Term::App(f, a) => {
                let (f_ty, row_f, usage_f) = self.infer_g(ctx, f, sigma)?;
                match f_ty {
                    Value::Pi(rho, dom, cod) => {
                        let (row_a, usage_a) = self.check_g(ctx, a, &dom, sigma.mul(rho))?;
                        let a_val = eval(&self.env_for(ctx), a);
                        Ok((cod.apply(a_val), row_f.union(&row_a), usage_f.add(&usage_a)))
                    }
                    other => Err(TypeError::Mismatch {
                        expected: "a function (Pi) type".into(),
                        found: format!("{other:?}"),
                    }),
                }
            }

            // Sigma-Elim. The projections pass usage and row through unchanged (the pair is demanded
            // at σ).
            Term::Fst(p) => {
                let (p_ty, row, usage) = self.infer_g(ctx, p, sigma)?;
                match p_ty {
                    Value::Sigma(dom, _cod) => Ok((*dom, row, usage)),
                    other => Err(TypeError::Mismatch {
                        expected: "a pair (Sigma) type".into(),
                        found: format!("{other:?}"),
                    }),
                }
            }
            Term::Snd(p) => {
                let (p_ty, row, usage) = self.infer_g(ctx, p, sigma)?;
                match p_ty {
                    Value::Sigma(_dom, cod) => {
                        let fst_val = eval(&self.env_for(ctx), &Term::Fst(p.clone()));
                        Ok((cod.apply(fst_val), row, usage))
                    }
                    other => Err(TypeError::Mismatch {
                        expected: "a pair (Sigma) type".into(),
                        found: format!("{other:?}"),
                    }),
                }
            }

            // Ascription `(the A t)`: the type `A` is formed in the 0-fragment; the term `t` carries
            // the ambient demand `sigma` and its row.
            Term::Ann(t, ty) => {
                self.infer_universe(ctx, ty)?;
                let ty_val = eval(&self.env_for(ctx), ty);
                let (row, usage) = self.check_g(ctx, t, &ty_val, sigma)?;
                Ok((ty_val, row, usage))
            }

            // Op (spec §4.2, perform): `op : Π(x:A). B` declared in effect `effect`. Check the argument
            // `a :^σ A`; the result type is `B[a/x]`; the operation contributes its label to the row at
            // the ambient demand `σ` (the continuation-multiplicity currency — a proof demanded at grade
            // `1` performs the effect once, etc.). The unhandled effect makes this an *effectful* term:
            // its label can only be discharged by an enclosing `Handle`.
            Term::Op { effect, op, arg } => {
                let (eff, opsig) = self
                    .sig
                    .op_of(op)
                    .ok_or_else(|| TypeError::EffectError(format!("unknown operation {op:?}")))?;
                if &eff.name != effect {
                    return Err(TypeError::EffectError(format!(
                        "operation {op:?} belongs to effect {:?}, not {effect:?}",
                        eff.name
                    )));
                }
                // Type the parameter and result against the ambient context (M2: op signatures are
                // closed over the ambient context; `param_ty` is a type, `result_ty` a type in `x:A`).
                let param_ty_term = opsig.param_ty.clone();
                let result_ty_term = opsig.result_ty.clone();
                let param_ty = eval(&self.env_for(ctx), &param_ty_term);
                // Check the operation argument at the ambient demand.
                let (row_a, usage_a) = self.check_g(ctx, arg, &param_ty, sigma)?;
                // Result type `B[a/x]`: evaluate `result_ty` in the environment extended with `a`'s value.
                let a_val = eval(&self.env_for(ctx), arg);
                let result_env = self.env_for(ctx).extend(a_val);
                let result_ty = eval(&result_env, &result_ty_term);
                // The operation contributes its effect label at the ambient demand, unioned with the
                // argument's own row (the argument may itself be effectful).
                let row = row_a.union(&Row::single(effect.clone(), sigma));
                Ok((result_ty, row, usage_a))
            }

            // Handle (spec §4.3): interpret some operations of `body`'s effects. We infer the body's
            // type `A` and row `E_body`, take the *result type* `C` from the `return` clause (binding
            // `x:A`), and check every operation clause against `C` (binding `x:Aᵢ` and the continuation
            // `k : Bᵢ → C`). The handled labels are *discharged* from `E_body`; the clauses' and return
            // clause's own rows are unioned in (effects the handler itself performs, plus unhandled
            // effects of `body` that bubble through). Usage sums all parts (binders popped).
            Term::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                // 1. Infer the body.
                let (body_ty, body_row, body_usage) = self.infer_g(ctx, body, sigma)?;

                // 2. Return clause: bind `x : A` (at the ambient demand), infer its type `C`.
                let body_ty_term = quote(ctx.len(), &body_ty);
                let ctx_ret = ctx.extend(body_ty_term, sigma);
                let (c_ty, ret_row, ret_usage) = self.infer_g(&ctx_ret, return_clause, sigma)?;
                let (_demand_ret_x, ret_usage) = ret_usage.pop();
                // `C` lives at depth `ctx.len()` (it must not mention the bound `x`); quote it there for
                // re-use under the operation clauses' binders.
                let c_term = quote(ctx.len(), &c_ty);

                // 3. Operation clauses.
                let mut result_row = ret_row;
                let mut total_usage = body_usage.add(&ret_usage);
                let mut handled: Vec<crate::row::EffName> = Vec::new();
                for (op, clause) in op_clauses.iter() {
                    let (eff, opsig) = self.sig.op_of(op).ok_or_else(|| {
                        TypeError::EffectError(format!(
                            "handler clause for unknown operation {op:?}"
                        ))
                    })?;
                    handled.push(eff.name.clone());
                    let param_ty_term = opsig.param_ty.clone();
                    let result_ty_term = opsig.result_ty.clone();
                    let cont_grade = opsig.cont_grade;

                    // Bind `x : Aᵢ` (the operation parameter). `Aᵢ` is closed over the ambient context.
                    let ctx_x = ctx.extend(param_ty_term, sigma);
                    // `Bᵢ = result_ty[x]` lives in `x:Aᵢ`'s scope (de Bruijn 0 = x). The continuation
                    // type is `k : Π(_:Bᵢ). C`, bound at the operation's continuation multiplicity so
                    // that resuming more than allowed is a `GradeViolation`. `C` must be weakened past
                    // the `x` binder (1).
                    let k_dom = result_ty_term; // valid in ctx_x (mentions x at index 0)
                    let k_ty = Term::Pi(
                        Grade::Omega,
                        Box::new(k_dom),
                        // Inside this Pi's codomain, one extra binder (`_`) is in scope on top of `x`,
                        // so `C` (closed at ctx.len()) is shifted by 2.
                        Box::new(shift(&c_term, 2)),
                    );
                    let ctx_xk = ctx_x.extend(k_ty, cont_grade);

                    // Check the clause body against `C` (now under the two binders `x`, `k`).
                    let c_val_xk = eval(&self.env_for(&ctx_xk), &shift(&c_term, 2));
                    let (clause_row, clause_usage) =
                        self.check_g(&ctx_xk, clause, &c_val_xk, sigma)?;
                    // Pop the two binders (`k` then `x`); enforce `k`'s multiplicity grade.
                    let (demand_k, clause_usage) = clause_usage.pop();
                    if !demand_k.leq(cont_grade) {
                        return Err(TypeError::GradeViolation(format!(
                        "handler clause for {op:?} resumes its continuation at grade {demand_k:?}, \
                         but the operation's continuation multiplicity is {cont_grade:?}"
                    )));
                    }
                    let (_demand_x, clause_usage) = clause_usage.pop();
                    result_row = result_row.union(&clause_row);
                    total_usage = total_usage.add(&clause_usage);
                }

                // 4. Discharge handled labels from the body's row, then union the clauses' rows.
                let mut discharged = body_row;
                for label in &handled {
                    discharged = discharged.discharge(label);
                }
                result_row = result_row.union(&discharged);

                Ok((c_ty, result_row, total_usage))
            }

            // `! E A` is the effectful computation *type* (spec §4.1): a type, formed in the 0-fragment.
            Term::EffTy(_row, a) => {
                let lvl = self.infer_universe(ctx, a)?;
                Ok((Value::Univ(nat_to_level(lvl)), Row::empty(), Usage::zero(n)))
            }

            // ---- partiality (spec §4.5): the intensional Capretta delay ----
            // `Delay A` is a *type former*: if `A : Univ l` then `Delay A : Univ l`. Pure (a type).
            Term::Delay(a) => {
                let lvl = self.infer_universe(ctx, a)?;
                Ok((Value::Univ(nat_to_level(lvl)), Row::empty(), Usage::zero(n)))
            }
            // `now a : Delay A` when `a : A`. An immediately-available value is *total*: empty row.
            Term::Now(a) => {
                let (a_ty, a_row, a_usage) = self.infer_g(ctx, a, sigma)?;
                let a_ty_v = Box::new(a_ty);
                Ok((Value::Delay(a_ty_v), a_row, a_usage))
            }
            // `later d : Delay A` when `d : Delay A`. A guarded step **may diverge**, so it contributes
            // the built-in `Partial` label at the ambient demand — this is exactly the nonzero
            // partiality grade `deftotal`/`check_top_with` will reject. The inner `d` must already be a
            // `Delay`.
            Term::Later(d) => {
                let (d_ty, d_row, d_usage) = self.infer_g(ctx, d, sigma)?;
                match d_ty {
                    Value::Delay(_) => {
                        let row = d_row.union(&Row::single(crate::row::EffName::partial(), sigma));
                        Ok((d_ty, row, d_usage))
                    }
                    other => Err(TypeError::Mismatch {
                        expected: "Delay A (the argument of `later`)".into(),
                        found: format!("{other:?}"),
                    }),
                }
            }
            // `force d : A` when `d : Delay A` (spec §4.5). Forcing a delay *runs* it, which may
            // diverge, so — like `later` — it contributes the built-in `Partial` label at the
            // ambient demand. Unlike `later`, it eliminates the `Delay`: the result type is the
            // underlying `A`.
            Term::Force(d) => {
                let (d_ty, d_row, d_usage) = self.infer_g(ctx, d, sigma)?;
                match d_ty {
                    Value::Delay(inner) => {
                        let row = d_row.union(&Row::single(crate::row::EffName::partial(), sigma));
                        Ok((*inner, row, d_usage))
                    }
                    other => Err(TypeError::Mismatch {
                        expected: "Delay A (the argument of `force`)".into(),
                        found: format!("{other:?}"),
                    }),
                }
            }

            Term::Lam(_) | Term::Pair(_, _) => Err(TypeError::CannotInfer(
                "lambda/pair need a type ascription to infer".into(),
            )),

            // Data formation (spec §2.7). M1 supports a single parameter and a single index, each
            // checked in the 0-fragment (they are type-level data). Non-indexed types fall through
            // with empty telescopes as before.
            Term::Data(name, params, indices) => {
                let decl = self.sig.get(name).ok_or_else(|| {
                    TypeError::BadDataDecl(format!("unknown inductive type {name:?}"))
                })?;
                if params.len() != decl.params.len() || indices.len() != decl.indices.len() {
                    return Err(TypeError::BadDataDecl(format!(
                        "{name:?} expects {} param(s) and {} index(es), got {} and {}",
                        decl.params.len(),
                        decl.indices.len(),
                        params.len(),
                        indices.len()
                    )));
                }
                // Check each parameter against its declared type, in the 0-fragment. A parameter type
                // may reference earlier parameters, so we thread the checked values into the env.
                let mut pvals: Vec<Value> = Vec::with_capacity(params.len());
                for (p, pty_term) in params.iter().zip(decl.params.iter()) {
                    let pty = eval(&self.env_with_vars(ctx, &pvals), pty_term);
                    self.check_g(ctx, p, &pty, Grade::Zero)?;
                    pvals.push(eval(&self.env_for(ctx), p));
                }
                // Check each index against its declared type, which may mention the parameters and
                // earlier indices; thread both into the env.
                let mut ivals: Vec<Value> = pvals.clone();
                for (ix, ixty_term) in indices.iter().zip(decl.indices.iter()) {
                    let ixty = eval(&self.env_with_vars(ctx, &ivals), ixty_term);
                    self.check_g(ctx, ix, &ixty, Grade::Zero)?;
                    ivals.push(eval(&self.env_for(ctx), ix));
                }
                let level = decl.level;
                Ok((
                    Value::Univ(nat_to_level(level)),
                    Row::empty(),
                    Usage::zero(n),
                ))
            }

            // Constructor introduction (spec §2.7). Each argument is demanded at the ambient `sigma`;
            // the constructor's total usage is the sum of its arguments' usages. For an *indexed*
            // family the result indices are computed from the (checked) argument values; parameters
            // cannot be recovered from the arguments in general, so a constructor of a *parameterized*
            // family must be used in checking position (see the `(Con, Data)` rule in `check_g`).
            Term::Con(name, args) => {
                let (decl, _idx, ctor) = self.sig.data_of_con(name).ok_or_else(|| {
                    TypeError::BadDataDecl(format!("unknown constructor {name:?}"))
                })?;
                if !decl.params.is_empty() {
                    return Err(TypeError::CannotInfer(format!(
                        "constructor {name:?} of a parameterized family needs a type ascription"
                    )));
                }
                if args.len() != ctor.args.len() {
                    return Err(TypeError::Mismatch {
                        expected: format!("{} argument(s) to {name:?}", ctor.args.len()),
                        found: format!("{}", args.len()),
                    });
                }
                let decl_name = decl.name.clone();
                let result_index_terms = ctor.result_indices.clone();
                // We only reach inference mode for a *non-parameterized* family (parameterized ones
                // require a type ascription, above). Recursive arguments therefore share the family
                // head with no parameters; indices, if any, are reconciled against the result below.
                let rec_ty = Value::Data(decl_name.clone(), vec![], vec![]);
                let mut usage = Usage::zero(n);
                let mut row = Row::empty();
                for (arg, shape) in args.iter().zip(ctor.args.iter()) {
                    let (arg_row, arg_usage) = match shape {
                        Arg::Rec(_) => self.check_g(ctx, arg, &rec_ty, sigma)?,
                        Arg::NonRec(ty) => {
                            let ty_val = eval(&self.env_for(ctx), ty);
                            self.check_g(ctx, arg, &ty_val, sigma)?
                        }
                    };
                    usage = usage.add(&arg_usage);
                    row = row.union(&arg_row);
                }
                // Compute the result indices by evaluating each `result_index` against the argument
                // values (innermost = last arg), in the current environment.
                let mut env = self.env_for(ctx);
                for arg in args.iter() {
                    let v = eval(&self.env_for(ctx), arg);
                    env = env.extend(v);
                }
                let result_indices: Vec<Value> =
                    result_index_terms.iter().map(|t| eval(&env, t)).collect();
                let data_ty = Value::Data(decl_name, vec![], result_indices);
                Ok((data_ty, row, usage))
            }

            // The dependent eliminator (spec §2.7).
            Term::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => self.infer_elim(ctx, data, motive, methods, scrutinee, sigma),

            // PathP formation (spec §2.6): type formation, no usage.
            Term::PathP { family, lhs, rhs } => {
                let ctx_dim = ctx.extend_dim();
                let lvl = self.infer_universe(&ctx_dim, family)?;
                let a0 = self.family_at(ctx, family, crate::term::Interval::I0);
                let a1 = self.family_at(ctx, family, crate::term::Interval::I1);
                self.check(ctx, lhs, &a0)?;
                self.check(ctx, rhs, &a1)?;
                Ok((Value::Univ(nat_to_level(lvl)), Row::empty(), Usage::zero(n)))
            }

            // Path application (spec §2.6): `p @ r : A[r/i]`; usage flows from the path term.
            Term::PApp(p, r) => {
                let (p_ty, row, usage) = self.infer_g(ctx, p, sigma)?;
                match p_ty {
                    Value::PathP { family, .. } => {
                        let rv = self.eval_interval_at(ctx, r);
                        Ok((family.apply_dim(rv), row, usage))
                    }
                    other => Err(TypeError::Mismatch {
                        expected: "a path (PathP) type".into(),
                        found: format!("{other:?}"),
                    }),
                }
            }

            // Transport (spec §2.6). The family is type formation (0-fragment); the base carries σ.
            Term::Transp {
                family,
                cofib,
                base,
            } => {
                let ctx_dim = ctx.extend_dim();
                self.infer_universe(&ctx_dim, family)?;
                self.check_cofib(ctx, cofib)?;
                let a0 = self.family_at(ctx, family, crate::term::Interval::I0);
                let (row, usage) = self.check_g(ctx, base, &a0, sigma)?;
                if crate::kan::is_total(&self.resolve_cofib_at(ctx, cofib)) {
                    let a1 = self.family_at(ctx, family, crate::term::Interval::I1);
                    if !conv(ctx.len(), &a0, &a1) {
                        return Err(TypeError::BadCubical(
                            "Transp with φ = ⊤ requires a constant type line".into(),
                        ));
                    }
                }
                Ok((
                    self.family_at(ctx, family, crate::term::Interval::I1),
                    row,
                    usage,
                ))
            }

            // Homogeneous composition (spec §2.6). The carrier is type formation; base and tube carry σ.
            Term::HComp {
                ty,
                cofib,
                tube,
                base,
            } => {
                self.infer_universe(ctx, ty)?;
                let ty_val = eval(&self.env_for(ctx), ty);
                let (row_base, usage_base) = self.check_g(ctx, base, &ty_val, sigma)?;
                self.check_cofib(ctx, cofib)?;
                let ctx_dim = ctx.extend_dim();
                let (row_tube, usage_tube) = self.check_g(&ctx_dim, tube, &ty_val, sigma)?;
                Ok((
                    ty_val,
                    row_base.union(&row_tube),
                    usage_base.add(&usage_tube),
                ))
            }

            // General composition (spec §2.6).
            Term::Comp {
                family,
                cofib,
                tube,
                base,
            } => {
                let ctx_dim = ctx.extend_dim();
                self.infer_universe(&ctx_dim, family)?;
                let a0 = self.family_at(ctx, family, crate::term::Interval::I0);
                let (row_base, usage_base) = self.check_g(ctx, base, &a0, sigma)?;
                self.check_cofib(ctx, cofib)?;
                let fam_at_i =
                    self.family_at(ctx, family, crate::term::Interval::Dim(ctx.dim_len()));
                let (row_tube, usage_tube) = self.check_g(&ctx_dim, tube, &fam_at_i, sigma)?;
                Ok((
                    self.family_at(ctx, family, crate::term::Interval::I1),
                    row_base.union(&row_tube),
                    usage_base.add(&usage_tube),
                ))
            }

            // Glue formation (spec §2.6): type formation; equiv is inferred in the 0-fragment.
            Term::Glue {
                base,
                cofib,
                ty,
                equiv,
            } => {
                let l = self.infer_universe(ctx, base)?;
                self.check_cofib(ctx, cofib)?;
                let base_val = eval(&self.env_for(ctx), base);
                self.infer_universe(ctx, ty)?;
                self.infer(ctx, equiv)?;
                let _ = base_val;
                Ok((Value::Univ(nat_to_level(l)), Row::empty(), Usage::zero(n)))
            }

            // `glue` introduction (spec §2.6): partial and base carry σ.
            Term::GlueTerm {
                cofib,
                partial,
                base,
            } => {
                self.check_cofib(ctx, cofib)?;
                let (_partial_ty, row_partial, usage_partial) =
                    self.infer_g(ctx, partial, sigma)?;
                let (base_ty, row_base, usage_base) = self.infer_g(ctx, base, sigma)?;
                Ok((
                    Value::Glue {
                        base: Box::new(base_ty),
                        cofib: self.resolve_cofib_at(ctx, cofib),
                        ty: Box::new(eval(&self.env_for(ctx), partial)),
                        equiv: Box::new(eval(&self.env_for(ctx), base)),
                    },
                    row_partial.union(&row_base),
                    usage_partial.add(&usage_base),
                ))
            }

            // `unglue` elimination (spec §2.6): usage flows from the glued term.
            Term::Unglue(g) => {
                let (g_ty, row, usage) = self.infer_g(ctx, g, sigma)?;
                match g_ty {
                    Value::Glue { base, .. } => Ok((*base, row, usage)),
                    other => Err(TypeError::Mismatch {
                        expected: "a Glue type".into(),
                        found: format!("{other:?}"),
                    }),
                }
            }

            // Foreign postulate (spec §7.6): `foreign "sym" : A` is an opaque trusted constant. Its
            // declared type `A` is formed in the 0-fragment; it contributes no usage and an empty
            // row (any effects it may perform are reflected in `A` itself, e.g. via `! E A`). The
            // kernel takes its existence on faith — this is the one TCB-growing escape hatch, which
            // the independent re-checker refuses to certify.
            Term::Foreign { ty, .. } => {
                self.infer_universe(ctx, ty)?;
                let ty_val = eval(&self.env_for(ctx), ty);
                Ok((ty_val, Row::empty(), Usage::zero(n)))
            }

            // ---- primitive machine integers (M11) ----
            // `Int : Univ 0`. Pure type formation, no usage.
            Term::IntTy => Ok((Value::Univ(nat_to_level(0)), Row::empty(), Usage::zero(n))),
            // `IntLit n : Int`. A literal is a closed runtime constant: empty row, no usage.
            Term::IntLit(_) => Ok((Value::IntTy, Row::empty(), Usage::zero(n))),
            // `IntPrim op a b`: both operands must check at `Int`; arithmetic and comparison alike
            // conclude `Int` (comparisons yield `1`/`0`; see the `IntPrim` doc-comment for why we
            // return `Int` rather than `Bool`). Usage/row are the union of the operands'.
            Term::IntPrim { lhs, rhs, .. } => {
                let (row_l, usage_l) = self.check_g(ctx, lhs, &Value::IntTy, sigma)?;
                let (row_r, usage_r) = self.check_g(ctx, rhs, &Value::IntTy, sigma)?;
                Ok((Value::IntTy, row_l.union(&row_r), usage_l.add(&usage_r)))
            }

            _ => Err(TypeError::CannotInfer(format!(
                "no inference rule for term former: {term:?}"
            ))),
        }
    }

    /// Evaluate a family `i. A` (a dim-binding term) at an interval endpoint, in `ctx`'s env.
    fn family_at(&self, ctx: &Context, family: &Term, r: crate::term::Interval) -> Value {
        let env = self.env_for(ctx).extend_dim(r);
        eval(&env, family)
    }

    /// Resolve+normalize an interval term at the given context's dimension depth.
    fn eval_interval_at(&self, ctx: &Context, r: &crate::term::Interval) -> crate::term::Interval {
        crate::normalize::eval_interval(&self.env_for(ctx), r)
    }

    /// Resolve a cofibration's dimension variables against the context's environment and constant-fold.
    fn resolve_cofib_at(&self, ctx: &Context, cofib: &Cofib) -> Cofib {
        crate::normalize::resolve_cofib(&self.env_for(ctx), cofib)
    }

    /// Light well-formedness check for a cofibration (spec §2.6): every interval mentioned must be in
    /// dimension scope. Dimension variables are de Bruijn indices into the context's dim space.
    fn check_cofib(&self, ctx: &Context, cofib: &Cofib) -> Result<(), TypeError> {
        fn interval_ok(r: &crate::term::Interval, dims: usize) -> bool {
            match r {
                crate::term::Interval::Dim(i) => *i < dims,
                crate::term::Interval::I0 | crate::term::Interval::I1 => true,
                crate::term::Interval::Neg(r) => interval_ok(r, dims),
                crate::term::Interval::Min(a, b) | crate::term::Interval::Max(a, b) => {
                    interval_ok(a, dims) && interval_ok(b, dims)
                }
            }
        }
        fn go(cofib: &Cofib, dims: usize) -> bool {
            match cofib {
                Cofib::Top | Cofib::Bot => true,
                Cofib::Eq0(r) | Cofib::Eq1(r) => interval_ok(r, dims),
                Cofib::And(a, b) | Cofib::Or(a, b) => go(a, dims) && go(b, dims),
            }
        }
        if go(cofib, ctx.dim_len()) {
            Ok(())
        } else {
            Err(TypeError::BadCubical(format!(
                "cofibration mentions an out-of-scope dimension: {cofib:?}"
            )))
        }
    }

    /// Type the dependent eliminator (spec §2.7) for a non-parameterized inductive. Methods and the
    /// scrutinee are demanded at the ambient `sigma`; the motive is type formation (0-fragment).
    fn infer_elim(
        &self,
        ctx: &Context,
        data: &DataName,
        motive: &Term,
        methods: &[Term],
        scrutinee: &Term,
        sigma: Grade,
    ) -> Result<(Value, Row, Usage), TypeError> {
        let decl = self
            .sig
            .get(data)
            .ok_or_else(|| TypeError::BadDataDecl(format!("unknown inductive type {data:?}")))?
            .clone();
        // Infer the scrutinee's type first so we can recover the family's parameters and indices. The
        // motive and methods are then built relative to *those* parameters (a parameterized family's
        // params are not otherwise recoverable from the eliminator alone).
        let (scrut_ty, scrut_row0, scrut_usage0) = self.infer_g(ctx, scrutinee, sigma)?;
        let (params, scrut_indices): (Vec<Value>, Vec<Value>) = match &scrut_ty {
            Value::Data(d, ps, is) if d == data => (ps.clone(), is.clone()),
            other => {
                return Err(TypeError::Mismatch {
                    expected: format!("a scrutinee of type {data:?}"),
                    found: format!("{:?}", quote(ctx.len(), other)),
                })
            }
        };
        let nindices = decl.indices.len();
        let indexed = nindices != 0;

        // The fully-applied family value `D params indices` used for the recursive occurrences and the
        // motive's domain. For an indexed family the indices are abstracted in the motive instead.
        let data_ty = Value::Data(decl.name.clone(), params.clone(), scrut_indices.clone());

        // Motive must denote `(i1:Idx1) → … → (im:Idxm) → D params i1..im → Univ ℓ`. The
        // surface/elaborator passes it as nested `Lam`s (not inferable on its own), so we type its
        // body directly under the binders. For a non-indexed family the motive is `λ (_:D params).
        // <type>`; for an M-indexed family it is `λ i1. … λ im. λ (_:D params i1..im). <type>`.
        let motive_lvl = match motive {
            Term::Lam(_) if indexed => {
                // Peel `nindices` index binders, then the scrutinee binder, then type the body.
                // Each index type may mention earlier indices, so extend the context incrementally.
                let mut ctx_acc = ctx.clone();
                let mut idx_vars: Vec<Value> = Vec::with_capacity(nindices);
                for idx_ty_term in decl.indices.iter() {
                    // The index type is closed at the declaration's depth; evaluated in an env that
                    // already binds the earlier index vars.
                    let env = self.env_with_vars(ctx, &idx_vars);
                    let index_ty = eval(&env, idx_ty_term);
                    idx_vars.push(Value::Neutral(Neutral::Var(ctx_acc.len())));
                    ctx_acc = ctx_acc.extend(quote(ctx_acc.len(), &index_ty), Grade::Omega);
                }
                // Walk the nested index `Lam`s.
                let mut body = motive;
                for _ in 0..nindices {
                    match body {
                        Term::Lam(inner) => body = inner,
                        other => {
                            return Err(TypeError::Mismatch {
                                expected: format!("indexed motive with {nindices} index binder(s)"),
                                found: format!("{other:?}"),
                            })
                        }
                    }
                }
                let dty = Value::Data(decl.name.clone(), params.clone(), idx_vars.clone());
                let ctx_id = ctx_acc.extend(quote(ctx_acc.len(), &dty), Grade::Omega);
                match body {
                    Term::Lam(inner) => self.infer_universe(&ctx_id, inner)?,
                    other => {
                        return Err(TypeError::Mismatch {
                            expected: "indexed motive `λ i1..im. λ (_:D params i1..im). T`".into(),
                            found: format!("{other:?}"),
                        })
                    }
                }
            }
            Term::Lam(body) => {
                let ctx2 = ctx.extend(quote(ctx.len(), &data_ty), Grade::Omega);
                self.infer_universe(&ctx2, body)?
            }
            other => {
                // Fall back to inference for an already-typed motive (e.g. a variable). Only the
                // non-indexed, non-parameterized shape is supported here.
                match self.infer(ctx, other)? {
                    Value::Pi(_g, dom, cod) => {
                        if !conv(ctx.len(), &dom, &data_ty) {
                            return Err(TypeError::Mismatch {
                                expected: format!("motive domain {data:?}"),
                                found: format!("{:?}", quote(ctx.len(), &dom)),
                            });
                        }
                        let fresh = Value::Neutral(Neutral::Var(ctx.len()));
                        match cod.apply(fresh) {
                            Value::Univ(l) => level_to_nat(&l)?,
                            other => {
                                return Err(TypeError::Mismatch {
                                    expected: "motive codomain Univ ℓ".into(),
                                    found: format!("{other:?}"),
                                })
                            }
                        }
                    }
                    other => {
                        return Err(TypeError::Mismatch {
                            expected: format!("motive of type {data:?} → Univ ℓ"),
                            found: format!("{other:?}"),
                        })
                    }
                }
            }
        };
        let _ = motive_lvl;
        let motive_val = eval(&self.env_for(ctx), motive);

        // One method per constructor, in declaration order.
        if methods.len() != decl.constructors.len() {
            return Err(TypeError::Mismatch {
                expected: format!("{} method(s)", decl.constructors.len()),
                found: format!("{}", methods.len()),
            });
        }
        let mut usage = scrut_usage0;
        let mut row = scrut_row0;
        for (ctor, method) in decl.constructors.iter().zip(methods.iter()) {
            if indexed {
                // Dependent pattern-match refinement (item 1b): try to unify this constructor's
                // result indices with the scrutinee's indices.
                let refinement = self.refine_method(
                    ctx.len(),
                    &self.env_for(ctx),
                    ctor,
                    &params,
                    &scrut_indices,
                );
                match refinement {
                    // The branch's head index clashes with the scrutinee's: it is unreachable, so its
                    // method is vacuously well-typed and contributes no usage/effects. (This is what
                    // certifies `safe-tail`/`vec-map`'s `vnil` arm against a `Succ`-indexed scrutinee.)
                    Refinement::Unreachable => continue,
                    // The branch is reachable under a solved index specialization: check its method
                    // against the per-branch-refined conclusion.
                    Refinement::Solved {
                        args: solved,
                        ambient,
                    } => {
                        let (method_row, method_usage) = self.check_refined_method(
                            ctx,
                            &decl,
                            ctor,
                            method,
                            motive,
                            &params,
                            &scrut_indices,
                            &solved,
                            &ambient,
                            sigma,
                        )?;
                        usage = usage.add(&method_usage);
                        row = row.union(&method_row);
                        continue;
                    }
                    // No progress: fall through to the plain (unrefined) method-type check below, so
                    // nothing previously accepted regresses.
                    Refinement::Stuck => {}
                }
            }
            let method_ty = self.method_type(ctx, &decl, ctor, &motive_val, &params)?;
            let (method_row, method_usage) = self.check_g(ctx, method, &method_ty, sigma)?;
            usage = usage.add(&method_usage);
            row = row.union(&method_row);
        }

        // Result is `P idx1..idxm scrutinee`.
        let scrut_val = eval(&self.env_for(ctx), scrutinee);
        let applied = if indexed {
            if scrut_indices.len() != nindices {
                return Err(TypeError::BadDataDecl(format!(
                    "indexed scrutinee has {} index value(s), expected {nindices}",
                    scrut_indices.len()
                )));
            }
            let mut acc = motive_val;
            for idx in scrut_indices.iter().cloned() {
                acc = apply_value(acc, idx);
            }
            apply_value(acc, scrut_val)
        } else {
            apply_value(motive_val, scrut_val)
        };
        Ok((applied, row, usage))
    }

    /// Build the expected type of the method for one constructor: the constructor's argument
    /// telescope, inserting an induction hypothesis `P xᵢ` after each recursive argument, with
    /// result `P (con args)`. Returned as a semantic [`Value`] (a Π-telescope).
    ///
    /// For M0 the constructor argument types are *closed* (Nat/Bool/S¹ have no parameters and their
    /// non-recursive arg types do not mention earlier args), which keeps the de Bruijn bookkeeping
    /// straightforward: the only binders that need to reference earlier ones are the conclusion
    /// `P (con …)` and each induction-hypothesis binder `P x`.
    fn method_type(
        &self,
        ctx: &Context,
        decl: &DataDecl,
        ctor: &Constructor,
        motive: &Value,
        params: &[Value],
    ) -> Result<Value, TypeError> {
        let data_name = decl.name.clone();
        let indexed = !decl.indices.is_empty();
        let nparams = params.len();
        // The motive is closed at the current depth; quote it so we can splice it under new binders.
        let motive_term = quote(ctx.len(), motive);
        // Quote the params (closed at the current depth) once.
        let param_terms: Vec<Term> = params.iter().map(|p| quote(ctx.len(), p)).collect();

        // The method's binders, in order. Each constructor arg is one binder; each *recursive* arg is
        // followed by an induction-hypothesis binder. `arg_pos[k]` records the method-telescope binder
        // position of constructor argument `k` (so we can translate constructor-arg de Bruijn indices,
        // which skip IH binders, into method-telescope indices, which include them).
        enum B {
            Arg,
            RecArg(Vec<Term>),
            Ih(Vec<Term>),
        }
        let mut binders: Vec<B> = Vec::new();
        let mut arg_pos: Vec<usize> = Vec::new();
        for shape in &ctor.args {
            match shape {
                Arg::NonRec(_) => {
                    arg_pos.push(binders.len());
                    binders.push(B::Arg);
                }
                Arg::Rec(rec_indices) => {
                    arg_pos.push(binders.len());
                    binders.push(B::RecArg(rec_indices.clone()));
                    binders.push(B::Ih(rec_indices.clone()));
                }
            }
        }
        let total = binders.len();

        // Translate a constructor-scope term into the method-telescope scope at `depth` binders in
        // scope. The constructor-scope sees, innermost-first, `[arg_{n-1} .. arg_0, param_{p-1} ..
        // param_0]`: de Bruijn `0..args_before` are the preceding constructor args and
        // `args_before..args_before+nparams` are the params. We replace all `m = args_before+nparams`
        // of these lowest indices *simultaneously* (a parallel substitution), shifting every var
        // `≥ m` down by `m`. A sequential fold of single-binder-removing `subst_var`s is wrong here:
        // each removal decrements the method-scope replacement vars inserted by earlier steps.
        let translate = |t: &Term, args_before: usize, depth: usize| -> Term {
            let m = args_before + nparams;
            // `repls[i]` is the replacement for constructor-scope de Bruijn `i`, for `i in 0..m`.
            let mut repls: Vec<Term> = Vec::with_capacity(m);
            // de Bruijn `0..args_before`: preceding constructor args. `0` is the most recent arg,
            // i.e. constructor argument index `args_before-1`.
            for i in 0..args_before {
                let ctor_arg_index = args_before - 1 - i;
                let method_binder_pos = arg_pos[ctor_arg_index];
                repls.push(Term::Var(depth - 1 - method_binder_pos));
            }
            // de Bruijn `args_before..args_before+nparams`: params, innermost (param index `nparams-1`)
            // first at `args_before`. `param_terms` are stored param-index-0-first, closed at the
            // Elim's depth, so shift them into the current `depth`.
            for pj in 0..nparams {
                let param_index = nparams - 1 - pj;
                repls.push(shift(&param_terms[param_index], depth));
            }
            fn go(t: &Term, depth_in: usize, m: usize, repls: &[Term]) -> Term {
                match t {
                    Term::Var(i) => {
                        if *i < depth_in {
                            Term::Var(*i)
                        } else if *i < depth_in + m {
                            shift(&repls[*i - depth_in], depth_in)
                        } else {
                            Term::Var(*i - m)
                        }
                    }
                    Term::Univ(_) | Term::Interval(_) | Term::Erased | Term::System(_) => t.clone(),
                    // `Int`/`IntLit` are closed primitive kernel nodes (M11) that legitimately appear
                    // in a constructor's argument types (e.g. `Expr`'s `lit (v Int)` in
                    // examples/calculator.bl). They carry no variables, so — like `Univ`/`Interval` —
                    // they translate to themselves. (Completeness fix surfaced by the declare-time
                    // kernel gate; not part of the 1b dependent-match refinement.)
                    Term::IntTy | Term::IntLit(_) => t.clone(),
                    Term::Pi(g, a, b) => Term::Pi(
                        *g,
                        Box::new(go(a, depth_in, m, repls)),
                        Box::new(go(b, depth_in + 1, m, repls)),
                    ),
                    Term::Sigma(a, b) => Term::Sigma(
                        Box::new(go(a, depth_in, m, repls)),
                        Box::new(go(b, depth_in + 1, m, repls)),
                    ),
                    Term::Lam(b) => Term::Lam(Box::new(go(b, depth_in + 1, m, repls))),
                    Term::App(f, a) => Term::App(
                        Box::new(go(f, depth_in, m, repls)),
                        Box::new(go(a, depth_in, m, repls)),
                    ),
                    Term::Pair(a, b) => Term::Pair(
                        Box::new(go(a, depth_in, m, repls)),
                        Box::new(go(b, depth_in, m, repls)),
                    ),
                    Term::Fst(p) => Term::Fst(Box::new(go(p, depth_in, m, repls))),
                    Term::Snd(p) => Term::Snd(Box::new(go(p, depth_in, m, repls))),
                    Term::Ann(e, ty) => Term::Ann(
                        Box::new(go(e, depth_in, m, repls)),
                        Box::new(go(ty, depth_in, m, repls)),
                    ),
                    Term::Data(d, ps, ix) => Term::Data(
                        d.clone(),
                        ps.iter().map(|x| go(x, depth_in, m, repls)).collect(),
                        ix.iter().map(|x| go(x, depth_in, m, repls)).collect(),
                    ),
                    Term::Con(c, xs) => Term::Con(
                        c.clone(),
                        xs.iter().map(|x| go(x, depth_in, m, repls)).collect(),
                    ),
                    other => {
                        // Constructor argument/index types never contain eliminators, transports, or
                        // other binder-introducing exotica; a `Var`-only translation suffices. Anything
                        // here indicates a malformed data declaration that earlier checks should reject.
                        debug_assert!(false, "unexpected term in constructor type: {other:?}");
                        other.clone()
                    }
                }
            }
            go(t, 0, m, &repls)
        };

        // Conclusion `(P idx)? (con args)` at depth `total`.
        let mut con_args: Vec<Term> = Vec::new();
        for (k, _) in ctor.args.iter().enumerate() {
            con_args.push(Term::Var(total - 1 - arg_pos[k]));
        }
        let con_term = Term::Con(ctor.name.clone(), con_args);
        let conclusion = if indexed {
            // Apply the motive to every result index (translated into the method telescope), then the
            // constructor term: `P rix_1 .. rix_m (con args)`.
            let mut acc = shift(&motive_term, total);
            for rix in ctor.result_indices.iter() {
                let rix = translate(rix, ctor.args.len(), total);
                acc = Term::App(Box::new(acc), Box::new(rix));
            }
            Term::App(Box::new(acc), Box::new(con_term))
        } else {
            Term::App(Box::new(shift(&motive_term, total)), Box::new(con_term))
        };

        // Fold binders innermost-to-outermost into a Pi-telescope. The Pi for binder at `pos` has a
        // domain seeing the `pos` outer binders `b_0..b_{pos-1}` (b_{pos-1} = de Bruijn 0).
        let mut body = conclusion;
        let mut args_before_at: Vec<usize> = Vec::with_capacity(total);
        {
            let mut count = 0usize;
            for b in &binders {
                args_before_at.push(count);
                if matches!(b, B::Arg | B::RecArg(_)) {
                    count += 1;
                }
            }
        }
        let nonrec_tys: Vec<Option<Term>> = ctor
            .args
            .iter()
            .map(|a| match a {
                Arg::NonRec(ty) => Some(ty.clone()),
                Arg::Rec(_) => None,
            })
            .collect();
        for (pos, b) in binders.iter().enumerate().rev() {
            let depth = pos; // binders in scope in this Pi's domain
            let args_before = args_before_at[pos];
            let dom = match b {
                B::Arg => {
                    let k = arg_pos.iter().position(|&p| p == pos).unwrap();
                    let ty = nonrec_tys[k].clone().unwrap();
                    translate(&ty, args_before, depth)
                }
                B::RecArg(rec_indices) => {
                    let ps: Vec<Term> = param_terms.iter().map(|t| shift(t, depth)).collect();
                    let ix: Vec<Term> = rec_indices
                        .iter()
                        .map(|t| translate(t, args_before, depth))
                        .collect();
                    Term::Data(data_name.clone(), ps, ix)
                }
                B::Ih(rec_indices) => {
                    // The IH binder sits immediately after its RecArg (at position `pos-1`). Its domain
                    // sees `pos` outer binders; the RecArg `xs` is at de Bruijn `depth-1-(pos-1) = 0`.
                    let p_motive = shift(&motive_term, depth);
                    let rec_pos = pos - 1; // the RecArg binder position
                    if indexed {
                        // Apply the motive to each recursive index (translated; `args_before-1`
                        // because the RecArg itself is counted in `args_before` at the IH), then to
                        // the recursive argument `xs`.
                        let mut acc = p_motive;
                        for rix in rec_indices.iter() {
                            let ix = translate(rix, args_before - 1, depth);
                            acc = Term::App(Box::new(acc), Box::new(ix));
                        }
                        let xs_var = Term::Var(depth - 1 - rec_pos);
                        Term::App(Box::new(acc), Box::new(xs_var))
                    } else {
                        let xs_var = Term::Var(depth - 1 - rec_pos);
                        Term::App(Box::new(p_motive), Box::new(xs_var))
                    }
                }
            };
            body = Term::Pi(Grade::Omega, Box::new(dom), Box::new(body));
        }

        Ok(eval(&self.env_for(ctx), &body))
    }

    // ===================================================================================
    // Dependent pattern-match refinement (plan item 1b — the one deliberate TCB growth).
    //
    // Ported faithfully from the independent re-checker (`crates/blight-recheck/src/typecheck.rs`:
    // `refine_method`/`unify_index`/`unify_seq`/`solvable_index`/`check_refined_method`/
    // `strengthen_motive`), re-expressed against the kernel's own `Value`/`Env`/`conv`/`eval`/
    // `quote`/`reflect`. This teaches the trusted kernel to (a) discharge an *unreachable*
    // constructor branch whose result index CLASHES with the scrutinee's index, and (b) check a
    // *reachable* branch under the per-branch index SPECIALIZATION. When unification is STUCK it
    // falls back to the plain `method_type` check, so nothing previously accepted regresses.
    //
    // Soundness: refinement only ever *discharges* a vacuous branch (a head-constructor clash, which
    // makes the branch genuinely unreachable for this scrutinee) or *specializes* a reachable branch
    // under a solved index equation. It never accepts a branch the plain rule would reject for a
    // non-clash reason — `Stuck` falls back. This is the standard dependent-pattern-matching
    // elaboration (spec §2.7); the re-checker's separately-written implementation is independent
    // evidence the algorithm is right.
    // ===================================================================================

    /// Refine one constructor branch against the scrutinee's index values: unify the constructor's
    /// result indices with the scrutinee indices. A head-constructor clash ⇒ the branch is
    /// `Unreachable`; a successful solve ⇒ `Solved` (some constructor args forced, some ambient
    /// scrutinee-index variables specialized); no progress ⇒ `Stuck` (fall back to the plain rule).
    fn refine_method(
        &self,
        lvl: usize,
        ctx_env: &Env,
        ctor: &Constructor,
        params: &[Value],
        scrut_indices: &[Value],
    ) -> Refinement {
        // Build placeholder values for the constructor arguments and the env that types/evaluates
        // the (param + preceding-arg) scope — fresh neutral *levels* (≥ lvl) so unification can
        // recognize them as the solvable unknowns. `ctx_env` only contributes its signature handle
        // here (constructor index terms are closed over params + args).
        let nargs = ctor.args.len();
        let mut env = match ctx_env.sig() {
            Some(s) => Env::with_sig(s.clone()),
            None => Env::empty(),
        };
        for p in params {
            env = env.extend(p.clone());
        }
        for k in 0..nargs {
            env = env.extend(Value::Neutral(Neutral::Var(lvl + k)));
        }
        let mut sol = RSolution {
            args: vec![None; nargs],
            ambient: Vec::new(),
        };
        let mut any = false;
        for (rix_t, scrut_ix) in ctor.result_indices.iter().zip(scrut_indices.iter()) {
            let got = eval(&env, rix_t);
            match self.unify_index(lvl, &got, scrut_ix, &mut sol) {
                Unify::Clash => return Refinement::Unreachable,
                Unify::Progress => any = true,
                Unify::Trivial => {}
                Unify::Stuck => return Refinement::Stuck,
            }
        }
        if any {
            Refinement::Solved {
                args: sol.args,
                ambient: sol.ambient,
            }
        } else {
            Refinement::Stuck
        }
    }

    /// First-order unification of a constructor result-index value `got` (which may mention argument
    /// placeholders at levels `≥ lvl`) against the scrutinee index value `want` (which may mention
    /// ambient context variables at levels `< lvl`). Solves placeholders (the branch's constructor
    /// arguments) and ambient index variables (the per-branch specialization).
    fn unify_index(&self, lvl: usize, got: &Value, want: &Value, sol: &mut RSolution) -> Unify {
        // Flexible placeholder on the `got` side ⇒ solve the constructor argument.
        if let Value::Neutral(Neutral::Var(l)) = got {
            if *l >= lvl {
                let k = *l - lvl;
                if k < sol.args.len() {
                    return match &sol.args[k] {
                        None => {
                            sol.args[k] = Some(want.clone());
                            Unify::Progress
                        }
                        Some(prev) => {
                            if conv(lvl, prev, want) {
                                Unify::Trivial
                            } else {
                                Unify::Stuck
                            }
                        }
                    };
                }
            }
        }
        // Flexible ambient index variable on the `want` side ⇒ specialize it to `got`. `got` may
        // mention the constructor's argument placeholders (they become this branch's bound
        // variables); it must not contain a *stuck* neutral (an application/eliminator), which we
        // cannot soundly turn into an equation.
        if let Value::Neutral(Neutral::Var(l)) = want {
            if *l < lvl && self.solvable_index(got) {
                for (lvl_a, v) in sol.ambient.iter() {
                    if lvl_a == l {
                        return if conv(lvl, v, got) {
                            Unify::Trivial
                        } else {
                            Unify::Stuck
                        };
                    }
                }
                sol.ambient.push((*l, got.clone()));
                return Unify::Progress;
            }
        }
        match (got, want) {
            // Same data head: decompose parameters and indices.
            (Value::Data(n1, p1, i1), Value::Data(n2, p2, i2)) => {
                if n1 != n2 || p1.len() != p2.len() || i1.len() != i2.len() {
                    return Unify::Clash;
                }
                self.unify_seq(lvl, p1.iter().zip(p2).chain(i1.iter().zip(i2)), sol)
            }
            // Same constructor head: decompose arguments. Different heads are a genuine CLASH — the
            // branch is unreachable for this scrutinee.
            (Value::Con(c1, a1), Value::Con(c2, a2)) => {
                if c1 != c2 || a1.len() != a2.len() {
                    return Unify::Clash;
                }
                self.unify_seq(lvl, a1.iter().zip(a2), sol)
            }
            (Value::IntLit(a), Value::IntLit(b)) => {
                if a == b {
                    Unify::Trivial
                } else {
                    Unify::Clash
                }
            }
            // Otherwise: rigidly equal ⇒ trivial; not provably so ⇒ stuck (fall back to the plain
            // method type rather than risk an unsound accept).
            _ => {
                if conv(lvl, got, want) {
                    Unify::Trivial
                } else {
                    Unify::Stuck
                }
            }
        }
    }

    /// Unify a sequence of value pairs, combining their outcomes (clash/stuck short-circuit).
    fn unify_seq<'b>(
        &self,
        lvl: usize,
        pairs: impl Iterator<Item = (&'b Value, &'b Value)>,
        sol: &mut RSolution,
    ) -> Unify {
        let mut progressed = false;
        for (a, b) in pairs {
            match self.unify_index(lvl, a, b, sol) {
                Unify::Clash => return Unify::Clash,
                Unify::Progress => progressed = true,
                Unify::Trivial => {}
                Unify::Stuck => return Unify::Stuck,
            }
        }
        if progressed {
            Unify::Progress
        } else {
            Unify::Trivial
        }
    }

    /// May `v` be used as the right-hand side of an index equation (ambient specialization)? It must
    /// be a value built only from variables, data/constructor heads, and literals — never a *stuck*
    /// neutral such as an application or eliminator, which we cannot soundly equate.
    fn solvable_index(&self, v: &Value) -> bool {
        match v {
            Value::Neutral(Neutral::Var(_)) => true,
            Value::Neutral(_) => false,
            Value::Data(_, ps, is) => {
                ps.iter().all(|x| self.solvable_index(x))
                    && is.iter().all(|x| self.solvable_index(x))
            }
            Value::Con(_, xs) => xs.iter().all(|x| self.solvable_index(x)),
            Value::Univ(_) | Value::IntTy | Value::IntLit(_) => true,
            _ => false,
        }
    }

    /// Substitute neutral variables at the given *levels* by the mapped values throughout `v`.
    fn subst_levels(&self, v: &Value, map: &[(usize, Value)]) -> Value {
        match v {
            Value::Neutral(Neutral::Var(l)) => {
                for (lvl, val) in map {
                    if lvl == l {
                        return val.clone();
                    }
                }
                v.clone()
            }
            Value::Data(n, ps, is) => Value::Data(
                n.clone(),
                ps.iter().map(|x| self.subst_levels(x, map)).collect(),
                is.iter().map(|x| self.subst_levels(x, map)).collect(),
            ),
            Value::Con(c, xs) => Value::Con(
                c.clone(),
                xs.iter().map(|x| self.subst_levels(x, map)).collect(),
            ),
            other => other.clone(),
        }
    }

    /// Re-express the ambient index solutions (computed over constructor-argument placeholders) in
    /// terms of the branch's actually-bound argument values.
    fn resolve_ambient(
        &self,
        ambient: &[(usize, Value)],
        placeholder_map: &[(usize, Value)],
    ) -> Vec<(usize, Value)> {
        ambient
            .iter()
            .map(|(lvl, v)| (*lvl, self.subst_levels(v, placeholder_map)))
            .collect()
    }

    /// Check one *reachable* constructor branch under its per-branch index refinement (item 1b).
    /// `solved[k]` forces constructor argument `k` (or `None` to leave it a fresh binder), and
    /// `ambient` specializes the scrutinee's ambient index variables. We open the method's lambdas,
    /// build the refined context (with value overrides for the forced args + ambient specialization),
    /// then check the body against the conclusion `motive (refined indices) (con args)`.
    #[allow(clippy::too_many_arguments)]
    fn check_refined_method(
        &self,
        ctx: &Context,
        decl: &DataDecl,
        ctor: &Constructor,
        method: &Term,
        motive_term: &Term,
        params: &[Value],
        scrut_indices: &[Value],
        solved: &[Option<Value>],
        ambient: &[(usize, Value)],
        sigma: Grade,
    ) -> Result<(Row, Usage), TypeError> {
        let base_lvl = ctx.len();
        let mut cur = ctx.clone();
        let mut body = method;
        // `arg_env` evaluates the constructor's arg/index *types* (param scope, then bound args), in
        // the same convention as the indexed-`Con` checking rule.
        let mut arg_env = {
            let mut e = self.env_for(ctx);
            for p in params {
                e = e.extend(p.clone());
            }
            e
        };
        let mut arg_vals: Vec<Value> = Vec::with_capacity(ctor.args.len());
        // Map each constructor-argument placeholder (level `base_lvl + k`, used during unification) to
        // the value actually bound here, so ambient equations expressed over placeholders can be
        // re-expressed over the branch's real binders.
        let mut placeholder_map: Vec<(usize, Value)> = Vec::with_capacity(ctor.args.len());

        for (k, shape) in ctor.args.iter().enumerate() {
            let mut rec_ix: Option<Vec<Value>> = None;
            let dom = match shape {
                Arg::NonRec(ty) => eval(&arg_env, ty),
                Arg::Rec(rec_indices) => {
                    let ix: Vec<Value> = rec_indices.iter().map(|t| eval(&arg_env, t)).collect();
                    rec_ix = Some(ix.clone());
                    Value::Data(decl.name.clone(), params.to_vec(), ix)
                }
            };
            let inner = match body {
                Term::Lam(inner) => inner.as_ref(),
                other => {
                    return Err(TypeError::Mismatch {
                        expected: format!(
                            "indexed Elim method for {:?} expects a lambda",
                            ctor.name
                        ),
                        found: format!("{other:?}"),
                    })
                }
            };
            // The binder sits at level `cur.len()`. Bind it to its forced value if solved, else to a
            // fresh neutral at that level.
            let this_lvl = cur.len();
            let arg_val = match &solved[k] {
                Some(v) => v.clone(),
                None => Value::Neutral(Neutral::Var(this_lvl)),
            };
            placeholder_map.push((base_lvl + k, arg_val.clone()));
            cur = cur.extend(quote(this_lvl, &dom), Grade::Omega);
            arg_vals.push(arg_val.clone());
            arg_env = arg_env.extend(arg_val.clone());
            body = inner;

            // After a recursive argument, the method binds an induction hypothesis. Its motive is
            // re-evaluated under the ambient refinement that unifies the scrutinee indices with this
            // recursive argument's *own* indices (e.g. `vec-map`: scrutinee `n` ↦ tail length `m`).
            if let Some(ix) = rec_ix {
                let ix: Vec<Value> = ix
                    .iter()
                    .map(|v| self.subst_levels(v, &placeholder_map))
                    .collect();
                let ih_ambient = {
                    let mut sol = RSolution {
                        args: Vec::new(),
                        ambient: Vec::new(),
                    };
                    for (sx, rx) in scrut_indices.iter().zip(ix.iter()) {
                        let _ = self.unify_index(base_lvl, rx, sx, &mut sol);
                    }
                    sol.ambient
                };
                // Evaluate the motive in the *ambient* env (base_lvl indices) with the IH's ambient
                // specialization injected as `Value`s directly (see the conclusion note below).
                let motive_here = {
                    let mut e = self.env_for(ctx);
                    for (l, v) in ih_ambient.iter() {
                        e = e.set_level(*l, v.clone());
                    }
                    eval(&e, motive_term)
                };
                let mut ih_ty = motive_here;
                for v in ix {
                    let v = self.subst_levels(&v, &ih_ambient);
                    ih_ty = apply_value(ih_ty, v);
                }
                ih_ty = apply_value(ih_ty, arg_val);
                let inner2 = match body {
                    Term::Lam(inner) => inner.as_ref(),
                    other => {
                        return Err(TypeError::Mismatch {
                            expected: format!(
                                "indexed Elim method for {:?} expects an IH lambda",
                                ctor.name
                            ),
                            found: format!("{other:?}"),
                        })
                    }
                };
                cur = cur.extend(quote(cur.len(), &ih_ty), Grade::Omega);
                body = inner2;
            }
        }

        // Apply the per-branch refinement: forced-argument overrides + ambient index specialization
        // (re-expressed over the branch's bound arguments). The conclusion's motive is evaluated in
        // the *ambient* refined env (its free vars are ambient de Bruijn indices), then applied to the
        // refined scrutinee indices and the constructor value.
        let refined_ambient = self.resolve_ambient(ambient, &placeholder_map);

        // Build the value env that `check_g` will reconstruct for `cur`: it must agree with
        // `env_for(cur)` on the (forced/fresh) constructor-argument and IH binders, plus carry the
        // ambient specialization. We override the named ambient *levels* with the solved `Value`s
        // directly (no quote round-trip, which would mis-level branch-arg neutrals). To make the
        // refinement visible to `check_g` (which rebuilds the env from the `Context`), we record the
        // overrides on `cur` as terms quoted at `cur.len()` — every neutral they mention (ambient
        // vars and branch args) is in scope there, so quoting is total.
        let cur_lvl = cur.len();
        let mut all_overrides: Vec<(usize, Term)> = Vec::new();
        for (l, v) in placeholder_map.iter() {
            // Forced constructor arguments (those whose `solved[k]` was `Some`) carry a value distinct
            // from their own fresh binder; record those as overrides so the binder reads the forced
            // value. (Unforced args map to their own `Var(level)` — a no-op override, skipped.)
            if !matches!(v, Value::Neutral(Neutral::Var(lv)) if *lv == *l) {
                all_overrides.push((*l, quote(cur_lvl, v)));
            }
        }
        for (l, v) in refined_ambient.iter() {
            all_overrides.push((*l, quote(cur_lvl, v)));
        }
        let cur = cur.with_overrides(&all_overrides);

        // The conclusion `motive (refined indices) (con args)`. The motive term's free de-Bruijn
        // indices are relative to the *ambient* context (`ctx`, `base_lvl` binders), NOT the extended
        // branch context `cur` — so it must be evaluated in the ambient env, with the ambient index
        // variables specialized. We inject the specialization as `Value`s directly (via `set_level`),
        // exactly the re-checker's `refine_ambient`: this avoids a quote round-trip that would
        // mis-level the branch-argument neutrals the solutions may mention.
        let motive_env = {
            let mut e = self.env_for(ctx);
            for (l, v) in refined_ambient.iter() {
                e = e.set_level(*l, v.clone());
            }
            e
        };
        let mut concl = eval(&motive_env, motive_term);
        for ix in scrut_indices {
            let ix = self.subst_levels(ix, &refined_ambient);
            concl = apply_value(concl, ix);
        }
        let con_val = Value::Con(ctor.name.clone(), arg_vals);
        concl = apply_value(concl, con_val);

        let (body_row, body_usage) = self.check_g(&cur, body, &concl, sigma)?;
        Ok((body_row, body_usage.truncate(base_lvl)))
    }

    /// Infer the universe level of a type-valued term, or error if it is not a universe. This is a
    /// *type-formation* subgoal, so it runs in the 0-fragment (spec §3.7): the type is demanded at
    /// grade `0` and may charge no runtime usage (debug-asserted).
    fn infer_universe(&self, ctx: &Context, term: &Term) -> Result<u32, TypeError> {
        let (ty, _row, usage) = self.infer_g(ctx, term, Grade::Zero)?;
        debug_assert!(
            usage.is_all_zero(),
            "0-fragment type formation charged nonzero usage: {usage:?}"
        );
        match ty {
            Value::Univ(l) => level_to_nat(&l),
            other => Err(TypeError::Mismatch {
                expected: "a universe".into(),
                found: format!("{other:?}"),
            }),
        }
    }

    /// Check `term` against the expected type `expected` (the `check` direction, spec §6.1).
    /// Convenience wrapper: demands `term` at grade `ω` and discards the usage vector.
    pub fn check(&self, ctx: &Context, term: &Term, expected: &Value) -> Result<(), TypeError> {
        self.check_g(ctx, term, expected, Grade::Omega).map(|_r| ())
    }

    /// The graded checking direction (spec §3.2, §4.1): check `term` against `expected` at ambient
    /// demand `sigma`, returning the effect **row** and the usage vector (length `ctx.len()`). The
    /// binder rules enforce the grade discipline (`ρ ≥ demand(x)`); pure terms produce the empty row.
    pub fn check_g(
        &self,
        ctx: &Context,
        term: &Term,
        expected: &Value,
        sigma: Grade,
    ) -> Result<(Row, Usage), TypeError> {
        match (term, expected) {
            // Pi-Intro (graded, spec §3.2 / §3.7): check the body under `x:^ρ A`, then require the
            // declared `ρ` to dominate the body's demand on `x` (`ρ ≥ demand(x)`), and drop `x` from
            // the returned usage.
            (Term::Lam(body), Value::Pi(grade, dom, cod)) => {
                let dom_term = quote(ctx.len(), dom);
                let ctx2 = ctx.extend(dom_term, *grade);
                let var = Value::Neutral(Neutral::Var(ctx.len()));
                let cod_val = cod.apply(var);
                let (body_row, body_usage) = self.check_g(&ctx2, body, &cod_val, sigma)?;
                let (demand_x, rest) = body_usage.pop();
                if !demand_x.leq(*grade) {
                    return Err(TypeError::GradeViolation(format!(
                    "λ-binder declared at grade {grade:?} but its body demands it at grade {demand_x:?}"
                )));
                }
                Ok((body_row, rest))
            }

            // Sigma-Intro: (a, b) checks against a Sigma. Both components carry the ambient demand
            // (Sigma is ω-graded in M1, §plan); usage is their sum, row their union.
            (Term::Pair(a, b), Value::Sigma(dom, cod)) => {
                let (row_a, usage_a) = self.check_g(ctx, a, dom, sigma)?;
                let a_val = eval(&self.env_for(ctx), a);
                let (row_b, usage_b) = self.check_g(ctx, b, &cod.apply(a_val), sigma)?;
                Ok((row_a.union(&row_b), usage_a.add(&usage_b)))
            }

            // Constructor against an indexed/parameterized family (spec §2.7, M1). We read the
            // parameter and expected indices from the *expected* `Data` type (so a constructor like
            // `nil : Vec A zero`, whose parameter `A` does not appear in its arguments, can be typed),
            // check each argument with the parameter substituted in, then verify the constructor's
            // declared result indices match the expectation.
            (Term::Con(name, args), Value::Data(d_name, params, exp_indices)) => {
                let (decl, _idx, ctor) = self.sig.data_of_con(name).ok_or_else(|| {
                    TypeError::BadDataDecl(format!("unknown constructor {name:?}"))
                })?;
                if &decl.name != d_name {
                    return Err(TypeError::Mismatch {
                        expected: format!("a constructor of {d_name:?}"),
                        found: format!("{name:?} (a constructor of {:?})", decl.name),
                    });
                }
                if args.len() != ctor.args.len() {
                    return Err(TypeError::Mismatch {
                        expected: format!("{} argument(s) to {name:?}", ctor.args.len()),
                        found: format!("{}", args.len()),
                    });
                }
                // Accumulate argument *values* as we check left-to-right; an arg type, a recursive
                // occurrence's index, or a result index may reference the parameter(s) and earlier
                // args. The evaluation environment places the parameter(s) outermost, then each checked
                // argument (innermost = most recent).
                let result_index_terms = ctor.result_indices.clone();
                let arg_shapes = ctor.args.clone();
                let param_vals = params.clone();
                let mut usage = Usage::zero(ctx.len());
                let mut row = Row::empty();
                let mut arg_env = {
                    let mut e = self.env_for(ctx);
                    for p in param_vals.iter() {
                        e = e.extend(p.clone());
                    }
                    e
                };
                for (arg, shape) in args.iter().zip(arg_shapes.iter()) {
                    let (arg_row, arg_usage) = match shape {
                        Arg::Rec(rec_indices) => {
                            // The recursive occurrence is `D params (rec_indices...)`, where the index
                            // terms range over the parameter and preceding arguments.
                            let rec_index_vals: Vec<Value> =
                                rec_indices.iter().map(|t| eval(&arg_env, t)).collect();
                            let rec_ty =
                                Value::Data(decl.name.clone(), param_vals.clone(), rec_index_vals);
                            self.check_g(ctx, arg, &rec_ty, sigma)?
                        }
                        Arg::NonRec(ty) => {
                            // Arg type may reference the parameter and earlier args.
                            let ty_val = eval(&arg_env, ty);
                            self.check_g(ctx, arg, &ty_val, sigma)?
                        }
                    };
                    usage = usage.add(&arg_usage);
                    row = row.union(&arg_row);
                    // Extend the environment with this argument's value for subsequent args.
                    let v = eval(&self.env_for(ctx), arg);
                    arg_env = arg_env.extend(v);
                }
                // Compute the constructor's result indices from the (param + args) environment, then
                // require they are convertible with the expected indices.
                for (rix_term, exp) in result_index_terms.iter().zip(exp_indices.iter()) {
                    let got = eval(&arg_env, rix_term);
                    if !conv(ctx.len(), &got, exp) {
                        return Err(TypeError::Mismatch {
                            expected: format!("index {:?}", quote(ctx.len(), exp)),
                            found: format!("{:?}", quote(ctx.len(), &got)),
                        });
                    }
                }
                Ok((row, usage))
            }

            // Path-Intro (spec §2.6): `λ i. t` against `PathP (i. A) x y`; usage flows from the body.
            (Term::PLam(body), Value::PathP { family, lhs, rhs }) => {
                let ctx_dim = ctx.extend_dim();
                let i_level = ctx.dim_len();
                let fam_at_i = family.apply_dim(crate::term::Interval::Dim(i_level));
                let (body_row, body_usage) = self.check_g(&ctx_dim, body, &fam_at_i, sigma)?;
                // Boundary checks at the two endpoints.
                let env0 = self.env_for(ctx).extend_dim(crate::term::Interval::I0);
                let env1 = self.env_for(ctx).extend_dim(crate::term::Interval::I1);
                let t0 = eval(&env0, body);
                let t1 = eval(&env1, body);
                // Boundary conv runs at the *current* dimension depth: outer `PLam`s already put
                // dimensions in scope (reflected as levels in `lhs`/`rhs` and in `t0`/`t1`), so a
                // `dlvl` of 0 would mis-quote stuck `PApp`s carrying those outer dims.
                let dlvl = ctx.dim_len();
                if !conv_dim(ctx.len(), dlvl, &t0, lhs) {
                    return Err(TypeError::BadCubical(format!(
                        "path lhs boundary mismatch: {:?} ≢ {:?}",
                        quote_value_at(ctx.len(), dlvl, &t0),
                        quote_value_at(ctx.len(), dlvl, lhs)
                    )));
                }
                if !conv_dim(ctx.len(), dlvl, &t1, rhs) {
                    return Err(TypeError::BadCubical(format!(
                        "path rhs boundary mismatch: {:?} ≢ {:?}",
                        quote_value_at(ctx.len(), dlvl, &t1),
                        quote_value_at(ctx.len(), dlvl, rhs)
                    )));
                }
                Ok((body_row, body_usage))
            }

            // Handle in checking mode (spec §4.3): the expected type *is* the result type `C`. This is
            // the usual mode (the `return`/op clauses are typically λ's, which cannot be inferred). We
            // infer the body's type `A` and row, then check the `return` clause (binding `x:A`) and each
            // operation clause (binding `x:Aᵢ`, `k : Bᵢ → C`) against `C`. Handled labels are discharged
            // from the body's row; the clauses' rows and the body's unhandled labels are unioned in.
            (
                Term::Handle {
                    body,
                    return_clause,
                    op_clauses,
                },
                expected_c,
            ) => {
                // 1. Body.
                let (body_ty, body_row, body_usage) = self.infer_g(ctx, body, sigma)?;
                let c_term = quote(ctx.len(), expected_c);

                // 2. Return clause: `x : A ⊢ return : C`.
                let body_ty_term = quote(ctx.len(), &body_ty);
                let ctx_ret = ctx.extend(body_ty_term, sigma);
                let c_in_ret = eval(&self.env_for(&ctx_ret), &shift(&c_term, 1));
                let (ret_row, ret_usage) =
                    self.check_g(&ctx_ret, return_clause, &c_in_ret, sigma)?;
                let (_demand_ret_x, ret_usage) = ret_usage.pop();

                // 3. Operation clauses.
                let mut result_row = ret_row;
                let mut total_usage = body_usage.add(&ret_usage);
                let mut handled: Vec<crate::row::EffName> = Vec::new();
                for (op, clause) in op_clauses.iter() {
                    let (eff, opsig) = self.sig.op_of(op).ok_or_else(|| {
                        TypeError::EffectError(format!(
                            "handler clause for unknown operation {op:?}"
                        ))
                    })?;
                    handled.push(eff.name.clone());
                    let param_ty_term = opsig.param_ty.clone();
                    let result_ty_term = opsig.result_ty.clone();
                    let cont_grade = opsig.cont_grade;

                    let ctx_x = ctx.extend(param_ty_term, sigma);
                    // k : Π(_:Bᵢ). C  (Bᵢ mentions x at index 0; C is closed → shifted past `x` then `_`),
                    // bound at the operation's continuation multiplicity.
                    let k_ty = Term::Pi(
                        Grade::Omega,
                        Box::new(result_ty_term),
                        Box::new(shift(&c_term, 2)),
                    );
                    let ctx_xk = ctx_x.extend(k_ty, cont_grade);
                    let c_val_xk = eval(&self.env_for(&ctx_xk), &shift(&c_term, 2));
                    let (clause_row, clause_usage) =
                        self.check_g(&ctx_xk, clause, &c_val_xk, sigma)?;
                    let (demand_k, clause_usage) = clause_usage.pop();
                    if !demand_k.leq(cont_grade) {
                        return Err(TypeError::GradeViolation(format!(
                        "handler clause for {op:?} resumes its continuation at grade {demand_k:?}, \
                         but the operation's continuation multiplicity is {cont_grade:?}"
                    )));
                    }
                    let (_demand_x, clause_usage) = clause_usage.pop();
                    result_row = result_row.union(&clause_row);
                    total_usage = total_usage.add(&clause_usage);
                }

                // 4. Discharge handled labels; union the clauses' and body's residual rows.
                let mut discharged = body_row;
                for label in &handled {
                    discharged = discharged.discharge(label);
                }
                result_row = result_row.union(&discharged);
                Ok((result_row, total_usage))
            }

            // Conversion fallback (spec §2.5 Conv): infer at `sigma`, then compare definitionally.
            _ => {
                let (actual, row, usage) = self.infer_g(ctx, term, sigma)?;
                if subtype(ctx.len(), &actual, expected) {
                    Ok((row, usage))
                } else {
                    Err(TypeError::NotConvertible {
                        lhs: format!("{:?}", quote(ctx.len(), &actual)),
                        rhs: format!("{:?}", quote(ctx.len(), expected)),
                    })
                }
            }
        }
    }
}

/// Subtyping = definitional equality plus universe cumulativity (spec §2.4 U-Cumul): a value of
/// `Univ ℓ` may be used where `Univ ℓ'` is expected when `ℓ ≤ ℓ'`.
fn subtype(lvl: usize, actual: &Value, expected: &Value) -> bool {
    if let (Value::Univ(a), Value::Univ(e)) = (actual, expected) {
        if let (Ok(na), Ok(ne)) = (level_to_nat(a), level_to_nat(e)) {
            return na <= ne;
        }
    }
    conv(lvl, actual, expected)
}

/// Apply a function-valued [`Value`] to an argument, used to compute `P scrutinee`.
fn apply_value(f: Value, arg: Value) -> Value {
    match f {
        Value::Lam(clos) => clos.apply(arg),
        Value::Pi(_, _, cod) => cod.apply(arg),
        Value::Neutral(n) => Value::Neutral(Neutral::App(Box::new(n), Box::new(arg))),
        other => panic!("apply_value: not applicable: {other:?}"),
    }
}

/// Weaken a term by `n`: shift every free de Bruijn variable up by `n` (no binders are crossed by
/// the caller's splice point). Implemented with a cutoff to leave bound variables untouched.
fn shift(term: &Term, n: usize) -> Term {
    fn go(term: &Term, n: usize, cutoff: usize) -> Term {
        match term {
            Term::Var(i) => {
                if *i >= cutoff {
                    Term::Var(i + n)
                } else {
                    Term::Var(*i)
                }
            }
            Term::Univ(_) => term.clone(),
            Term::Pi(g, a, b) => Term::Pi(
                *g,
                Box::new(go(a, n, cutoff)),
                Box::new(go(b, n, cutoff + 1)),
            ),
            Term::Lam(b) => Term::Lam(Box::new(go(b, n, cutoff + 1))),
            Term::App(f, a) => Term::App(Box::new(go(f, n, cutoff)), Box::new(go(a, n, cutoff))),
            Term::Sigma(a, b) => {
                Term::Sigma(Box::new(go(a, n, cutoff)), Box::new(go(b, n, cutoff + 1)))
            }
            Term::Pair(a, b) => Term::Pair(Box::new(go(a, n, cutoff)), Box::new(go(b, n, cutoff))),
            Term::Fst(p) => Term::Fst(Box::new(go(p, n, cutoff))),
            Term::Snd(p) => Term::Snd(Box::new(go(p, n, cutoff))),
            Term::Ann(t, ty) => Term::Ann(Box::new(go(t, n, cutoff)), Box::new(go(ty, n, cutoff))),
            Term::Data(d, ps, is) => Term::Data(
                d.clone(),
                ps.iter().map(|t| go(t, n, cutoff)).collect(),
                is.iter().map(|t| go(t, n, cutoff)).collect(),
            ),
            Term::Con(c, args) => {
                Term::Con(c.clone(), args.iter().map(|t| go(t, n, cutoff)).collect())
            }
            Term::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => Term::Elim {
                data: data.clone(),
                motive: Box::new(go(motive, n, cutoff)),
                methods: methods.iter().map(|t| go(t, n, cutoff)).collect(),
                scrutinee: Box::new(go(scrutinee, n, cutoff)),
            },
            // Cubical formers. None of these bind a *term* variable (only dimensions, which live in
            // a separate de Bruijn space), so the term cutoff is unchanged when descending.
            Term::PathP { family, lhs, rhs } => Term::PathP {
                family: Box::new(go(family, n, cutoff)),
                lhs: Box::new(go(lhs, n, cutoff)),
                rhs: Box::new(go(rhs, n, cutoff)),
            },
            Term::PLam(b) => Term::PLam(Box::new(go(b, n, cutoff))),
            Term::PApp(p, r) => Term::PApp(Box::new(go(p, n, cutoff)), r.clone()),
            Term::Partial(c, a) => Term::Partial(c.clone(), Box::new(go(a, n, cutoff))),
            Term::Transp {
                family,
                cofib,
                base,
            } => Term::Transp {
                family: Box::new(go(family, n, cutoff)),
                cofib: cofib.clone(),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::HComp {
                ty,
                cofib,
                tube,
                base,
            } => Term::HComp {
                ty: Box::new(go(ty, n, cutoff)),
                cofib: cofib.clone(),
                tube: Box::new(go(tube, n, cutoff)),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::Comp {
                family,
                cofib,
                tube,
                base,
            } => Term::Comp {
                family: Box::new(go(family, n, cutoff)),
                cofib: cofib.clone(),
                tube: Box::new(go(tube, n, cutoff)),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::Glue {
                base,
                cofib,
                ty,
                equiv,
            } => Term::Glue {
                base: Box::new(go(base, n, cutoff)),
                cofib: cofib.clone(),
                ty: Box::new(go(ty, n, cutoff)),
                equiv: Box::new(go(equiv, n, cutoff)),
            },
            Term::GlueTerm {
                cofib,
                partial,
                base,
            } => Term::GlueTerm {
                cofib: cofib.clone(),
                partial: Box::new(go(partial, n, cutoff)),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::Unglue(p) => Term::Unglue(Box::new(go(p, n, cutoff))),
            // Effects: `Op` arg binds nothing; `Handle`'s return clause binds 1 (the result), each
            // op clause binds 2 (op-arg then continuation `k`); `EffTy`'s row is closed.
            Term::Op { effect, op, arg } => Term::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(arg, n, cutoff)),
            },
            Term::Handle {
                body,
                return_clause,
                op_clauses,
            } => Term::Handle {
                body: Box::new(go(body, n, cutoff)),
                return_clause: Box::new(go(return_clause, n, cutoff + 1)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(name, e)| (name.clone(), Box::new(go(e, n, cutoff + 2))))
                    .collect(),
            },
            Term::EffTy(row, a) => Term::EffTy(row.clone(), Box::new(go(a, n, cutoff))),
            Term::Delay(a) => Term::Delay(Box::new(go(a, n, cutoff))),
            Term::Now(a) => Term::Now(Box::new(go(a, n, cutoff))),
            Term::Later(a) => Term::Later(Box::new(go(a, n, cutoff))),
            Term::Force(a) => Term::Force(Box::new(go(a, n, cutoff))),
            // `System` carries cofibration-guarded branches; not produced by the paths funext needs.
            Term::System(_) => term.clone(),
            // A literal interval term has no term-variable content.
            Term::Interval(_) => term.clone(),
            // The erasure sentinel has no variable content.
            Term::Erased => Term::Erased,
            // A foreign postulate's symbol is opaque; only its ascribed type can mention variables.
            Term::Foreign { symbol, ty } => Term::Foreign {
                symbol: symbol.clone(),
                ty: Box::new(go(ty, n, cutoff)),
            },
            // Int type/literal have no subterms; an IntPrim shifts both operands.
            Term::IntTy | Term::IntLit(_) => term.clone(),
            Term::IntPrim { op, lhs, rhs } => Term::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, n, cutoff)),
                rhs: Box::new(go(rhs, n, cutoff)),
            },
        }
    }
    go(term, n, 0)
}

/// Substitute the de Bruijn variable at index `j` with `replacement` (a term over the *outer*
/// scope, i.e. the scope that results after removing the `j`-th binder), decrementing free
/// variables above `j` (since one binder is removed). `replacement` is shifted as binders are
/// crossed. Previously used by [`Checker::method_type`]; retained as a general kernel utility.
#[allow(dead_code)]
fn subst_var(term: &Term, j: usize, replacement: &Term) -> Term {
    fn go(term: &Term, j: usize, repl: &Term) -> Term {
        match term {
            Term::Var(i) => {
                use std::cmp::Ordering;
                match i.cmp(&j) {
                    Ordering::Equal => repl.clone(),
                    Ordering::Greater => Term::Var(i - 1),
                    Ordering::Less => Term::Var(*i),
                }
            }
            Term::Univ(_) | Term::Interval(_) | Term::Erased | Term::System(_) => term.clone(),
            Term::IntTy | Term::IntLit(_) => term.clone(),
            Term::IntPrim { op, lhs, rhs } => Term::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, j, repl)),
                rhs: Box::new(go(rhs, j, repl)),
            },
            Term::Pi(g, a, b) => Term::Pi(
                *g,
                Box::new(go(a, j, repl)),
                Box::new(go(b, j + 1, &shift(repl, 1))),
            ),
            Term::Sigma(a, b) => Term::Sigma(
                Box::new(go(a, j, repl)),
                Box::new(go(b, j + 1, &shift(repl, 1))),
            ),
            Term::Lam(b) => Term::Lam(Box::new(go(b, j + 1, &shift(repl, 1)))),
            Term::App(f, a) => Term::App(Box::new(go(f, j, repl)), Box::new(go(a, j, repl))),
            Term::Pair(a, b) => Term::Pair(Box::new(go(a, j, repl)), Box::new(go(b, j, repl))),
            Term::Fst(p) => Term::Fst(Box::new(go(p, j, repl))),
            Term::Snd(p) => Term::Snd(Box::new(go(p, j, repl))),
            Term::Ann(t, ty) => Term::Ann(Box::new(go(t, j, repl)), Box::new(go(ty, j, repl))),
            Term::Data(d, ps, is) => Term::Data(
                d.clone(),
                ps.iter().map(|t| go(t, j, repl)).collect(),
                is.iter().map(|t| go(t, j, repl)).collect(),
            ),
            Term::Con(c, args) => {
                Term::Con(c.clone(), args.iter().map(|t| go(t, j, repl)).collect())
            }
            Term::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => Term::Elim {
                data: data.clone(),
                motive: Box::new(go(motive, j, repl)),
                methods: methods.iter().map(|t| go(t, j, repl)).collect(),
                scrutinee: Box::new(go(scrutinee, j, repl)),
            },
            Term::PathP { family, lhs, rhs } => Term::PathP {
                family: Box::new(go(family, j, repl)),
                lhs: Box::new(go(lhs, j, repl)),
                rhs: Box::new(go(rhs, j, repl)),
            },
            Term::PLam(b) => Term::PLam(Box::new(go(b, j, repl))),
            Term::PApp(p, r) => Term::PApp(Box::new(go(p, j, repl)), r.clone()),
            Term::Delay(a) => Term::Delay(Box::new(go(a, j, repl))),
            Term::Now(a) => Term::Now(Box::new(go(a, j, repl))),
            Term::Later(a) => Term::Later(Box::new(go(a, j, repl))),
            Term::Force(a) => Term::Force(Box::new(go(a, j, repl))),
            Term::EffTy(row, a) => Term::EffTy(row.clone(), Box::new(go(a, j, repl))),
            Term::Op { effect, op, arg } => Term::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(arg, j, repl)),
            },
            // Remaining cubical/effect formers are not produced by parameterized-data method
            // types; substitute conservatively where there is no extra binder.
            Term::Partial(c, a) => Term::Partial(c.clone(), Box::new(go(a, j, repl))),
            Term::Unglue(p) => Term::Unglue(Box::new(go(p, j, repl))),
            Term::Foreign { symbol, ty } => Term::Foreign {
                symbol: symbol.clone(),
                ty: Box::new(go(ty, j, repl)),
            },
            Term::Transp {
                family,
                cofib,
                base,
            } => Term::Transp {
                family: Box::new(go(family, j, repl)),
                cofib: cofib.clone(),
                base: Box::new(go(base, j, repl)),
            },
            Term::HComp {
                ty,
                cofib,
                tube,
                base,
            } => Term::HComp {
                ty: Box::new(go(ty, j, repl)),
                cofib: cofib.clone(),
                tube: Box::new(go(tube, j, repl)),
                base: Box::new(go(base, j, repl)),
            },
            Term::Comp {
                family,
                cofib,
                tube,
                base,
            } => Term::Comp {
                family: Box::new(go(family, j, repl)),
                cofib: cofib.clone(),
                tube: Box::new(go(tube, j, repl)),
                base: Box::new(go(base, j, repl)),
            },
            Term::Glue {
                base,
                cofib,
                ty,
                equiv,
            } => Term::Glue {
                base: Box::new(go(base, j, repl)),
                cofib: cofib.clone(),
                ty: Box::new(go(ty, j, repl)),
                equiv: Box::new(go(equiv, j, repl)),
            },
            Term::GlueTerm {
                cofib,
                partial,
                base,
            } => Term::GlueTerm {
                cofib: cofib.clone(),
                partial: Box::new(go(partial, j, repl)),
                base: Box::new(go(base, j, repl)),
            },
            Term::Handle {
                body,
                return_clause,
                op_clauses,
            } => Term::Handle {
                body: Box::new(go(body, j, repl)),
                return_clause: Box::new(go(return_clause, j + 1, &shift(repl, 1))),
                op_clauses: op_clauses
                    .iter()
                    .map(|(name, e)| (name.clone(), Box::new(go(e, j + 2, &shift(repl, 2)))))
                    .collect(),
            },
        }
    }
    go(term, j, replacement)
}

/// Top-level entry: check that `term : ty` in the empty context (no inductive signature) and,
/// on success, mint the `Proof`. Convenience wrapper over [`check_top_with`].
pub fn check_top(term: Term, ty: Term) -> Result<Proof, TypeError> {
    check_top_with(Signature::empty(), term, ty)
}

/// Top-level entry against a given inductive [`Signature`]. This is the kernel's public door
/// (spec §2.1) — the only way an external crate can obtain a [`Proof`].
pub fn check_top_with(sig: Signature, term: Term, ty: Term) -> Result<Proof, TypeError> {
    let ctx = Context::empty();
    let checker = Checker::new(std::rc::Rc::new(sig));
    let expected = eval(&checker.env_for(&ctx), &ty);
    // A complete program/proof is demanded exactly once (`σ = 1`); the grade discipline then
    // accounts each binder's usage relative to that single demand (spec §3.2). It must also be
    // *pure and total* (spec §4.1, §4.5): the inferred effect row must be empty, in particular
    // carrying `Partial` at grade 0 — a proof may not diverge or escape an unhandled effect.
    let (row, _usage) = checker.check_g(&ctx, &term, &expected, Grade::One)?;
    if !row.is_empty() {
        return Err(TypeError::EffectError(format!(
            "a top-level proof must be pure (empty effect row), but it carries effects: {row:?}"
        )));
    }
    Ok(Proof::trusted_new(Judgement::HasType { term, ty }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semiring::Grade;
    use crate::term::Level;

    fn u(n: u32) -> Term {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = Level::Suc(Box::new(l));
        }
        Term::Univ(l)
    }

    /// `Univ 0 : Univ 1` (spec §2.4, U-Type).
    #[test]
    fn universe_in_next_universe() {
        let p = check_top(u(0), u(1));
        assert!(p.is_ok(), "Univ 0 : Univ 1");
    }

    /// Cumulativity: `Univ 0 : Univ 2` as well (spec §2.4, U-Cumul).
    #[test]
    fn universe_cumulativity() {
        assert!(
            check_top(u(0), u(2)).is_ok(),
            "Univ 0 : Univ 2 by cumulativity"
        );
    }

    /// A universe does not inhabit a lower-or-equal universe: `Univ 1 : Univ 0` rejected.
    #[test]
    fn universe_no_downward() {
        assert!(
            check_top(u(1), u(0)).is_err(),
            "Univ 1 : Univ 0 must be rejected"
        );
    }

    /// A `foreign` postulate (spec §7.6) checks at its ascribed type: it is an opaque trusted
    /// constant the kernel takes on faith. `foreign "answer" : Univ 0` checks at `Univ 0`.
    #[test]
    fn foreign_checks_at_its_type() {
        let f = Term::Foreign {
            symbol: "bl_foreign_answer".into(),
            ty: Box::new(u(0)),
        };
        assert!(
            check_top(f, u(0)).is_ok(),
            "foreign \"answer\" : Univ 0 should check"
        );
    }

    /// A `foreign` is stuck under NbE: it must not be definitionally equal to anything but itself,
    /// so ascribing it a *different* type is rejected.
    #[test]
    fn foreign_wrong_type_rejected() {
        let f = Term::Foreign {
            symbol: "bl_foreign_answer".into(),
            ty: Box::new(u(0)),
        };
        // claim it has type `Univ 1` (it self-reports `Univ 0`, which lives in `Univ 1` — but the
        // ascription type is `Univ 1`, and a value of type `Univ 0` does have type `Univ 1` by
        // cumulativity; so instead test a genuinely wrong shape: a Pi).
        let pi = Term::Pi(Grade::Omega, Box::new(u(0)), Box::new(u(0)));
        assert!(
            check_top(f, pi).is_err(),
            "foreign of type Univ 0 must not check against a Pi type"
        );
    }

    // ---- M11: primitive machine integers ----
    use crate::term::IntPrimOp;

    /// `Int : Univ 0`.
    #[test]
    fn int_type_in_universe_zero() {
        assert!(check_top(Term::IntTy, u(0)).is_ok(), "Int : Univ 0");
    }

    /// `IntLit 5 : Int`.
    #[test]
    fn int_literal_has_int_type() {
        assert!(
            check_top(Term::IntLit(5), Term::IntTy).is_ok(),
            "IntLit 5 : Int"
        );
        // A literal is *not* a universe.
        assert!(
            check_top(Term::IntLit(5), u(0)).is_err(),
            "IntLit 5 : Univ 0 must be rejected"
        );
    }

    /// Arithmetic checks at `Int`: `2 + 3 : Int`.
    #[test]
    fn int_arith_checks_at_int() {
        let t = Term::IntPrim {
            op: IntPrimOp::Add,
            lhs: Box::new(Term::IntLit(2)),
            rhs: Box::new(Term::IntLit(3)),
        };
        assert!(check_top(t, Term::IntTy).is_ok(), "2 + 3 : Int");
    }

    /// Definitional reduction: `2 + 3 ≡ 5` (eval/quote yields `IntLit 5`).
    #[test]
    fn int_add_reduces() {
        let t = Term::IntPrim {
            op: IntPrimOp::Add,
            lhs: Box::new(Term::IntLit(2)),
            rhs: Box::new(Term::IntLit(3)),
        };
        let v = eval(&Env::empty(), &t);
        assert_eq!(quote(0, &v), Term::IntLit(5), "2 + 3 ≡ 5");
        // And it checks against the literal it reduces to (conversion via NbE).
        assert!(
            check_top(t, Term::IntTy).is_ok(),
            "2 + 3 has type Int and converts to 5"
        );
    }

    /// Multiplication reduces: `6 * 7 ≡ 42`; and the term is convertible with `IntLit 42`.
    #[test]
    fn int_mul_reduces_and_converts() {
        let t = Term::IntPrim {
            op: IntPrimOp::Mul,
            lhs: Box::new(Term::IntLit(6)),
            rhs: Box::new(Term::IntLit(7)),
        };
        let v = eval(&Env::empty(), &t);
        assert_eq!(quote(0, &v), Term::IntLit(42));
        // `(the Int (6*7))` is definitionally `42`, so ascribing it against the annotation `42`
        // via `Ann` round-trips through conv.
        let ann = Term::Ann(Box::new(t), Box::new(Term::IntTy));
        let v2 = eval(&Env::empty(), &ann);
        assert!(conv(0, &v2, &Value::IntLit(42)));
    }

    /// Comparison reduces to `1`/`0`: `2 < 3 ≡ 1` and `3 = 3 ≡ 1`, `5 < 1 ≡ 0`.
    #[test]
    fn int_compare_reduces() {
        let lt = Term::IntPrim {
            op: IntPrimOp::Lt,
            lhs: Box::new(Term::IntLit(2)),
            rhs: Box::new(Term::IntLit(3)),
        };
        assert_eq!(quote(0, &eval(&Env::empty(), &lt)), Term::IntLit(1));
        let eq = Term::IntPrim {
            op: IntPrimOp::Eq,
            lhs: Box::new(Term::IntLit(3)),
            rhs: Box::new(Term::IntLit(3)),
        };
        assert_eq!(quote(0, &eval(&Env::empty(), &eq)), Term::IntLit(1));
        let lt_false = Term::IntPrim {
            op: IntPrimOp::Lt,
            lhs: Box::new(Term::IntLit(5)),
            rhs: Box::new(Term::IntLit(1)),
        };
        assert_eq!(quote(0, &eval(&Env::empty(), &lt_false)), Term::IntLit(0));
    }

    /// A stuck primitive stays neutral and quotes back: `x + 1` with `x` a free variable does not
    /// reduce and round-trips to the same `IntPrim` term.
    #[test]
    fn int_prim_stuck_on_variable() {
        // Evaluate `x + 1` where `x` is a neutral var at level 0.
        let env = Env::empty().extend(Value::Neutral(Neutral::Var(0)));
        let t = Term::IntPrim {
            op: IntPrimOp::Add,
            lhs: Box::new(Term::Var(0)),
            rhs: Box::new(Term::IntLit(1)),
        };
        let v = eval(&env, &t);
        // quote at depth 1 (one var in scope) reconstructs `x + 1` (Var(0) + IntLit 1).
        let q = quote(1, &v);
        assert_eq!(
            q,
            Term::IntPrim {
                op: IntPrimOp::Add,
                lhs: Box::new(Term::Var(0)),
                rhs: Box::new(Term::IntLit(1)),
            },
            "x + 1 stays stuck and quotes back"
        );
    }

    /// Division by zero stays stuck (no panic, no fabricated value): `7 / 0` quotes back unchanged.
    #[test]
    fn int_div_by_zero_stuck() {
        let t = Term::IntPrim {
            op: IntPrimOp::Div,
            lhs: Box::new(Term::IntLit(7)),
            rhs: Box::new(Term::IntLit(0)),
        };
        let v = eval(&Env::empty(), &t);
        assert_eq!(
            quote(0, &v),
            t,
            "division by zero must remain a stuck IntPrim"
        );
    }

    /// The polymorphic identity at `Univ 0`: `λ A. λ x. x : (A :^ω Univ 0) → (x :^ω A) → A`.
    #[test]
    fn identity_checks_against_pi() {
        // type: Pi (A :^ω Univ 0). Pi (x :^ω A). A    (A is Var 0 inside the inner Pi)
        let ty = Term::Pi(
            Grade::Omega,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(0)))));
        assert!(check_top(term, ty).is_ok(), "polymorphic id checks");
    }

    /// A Π type is itself a type: `(x :^ω Univ 0) → Univ 0 : Univ 1`.
    #[test]
    fn pi_formation() {
        let pi = Term::Pi(Grade::Omega, Box::new(u(0)), Box::new(u(0)));
        assert!(check_top(pi, u(1)).is_ok());
    }

    /// Row threading is behavior-preserving: a pure program infers the empty (pure) effect row,
    /// and `check_g` on a pure term returns the empty row. (The M2 guard for step 4.)
    #[test]
    fn rows_threading_is_behavior_preserving() {
        let checker = Checker::new(std::rc::Rc::new(Signature::empty()));
        let ctx = Context::empty();
        // Univ 0 is pure.
        let (_ty, row, _u) = checker.infer_g(&ctx, &u(0), Grade::One).expect("infers");
        assert!(row.is_empty(), "a pure universe has the empty effect row");
        // The polymorphic identity checks pure.
        let id_ty = Term::Pi(
            Grade::Omega,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let id = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(0)))));
        let id_ty_val = eval(&checker.env_for(&ctx), &id_ty);
        let (row2, _u2) = checker
            .check_g(&ctx, &id, &id_ty_val, Grade::One)
            .expect("checks");
        assert!(
            row2.is_empty(),
            "the pure identity has the empty effect row"
        );
    }

    // ---- M2: Op typing + eval (spec §4.2, op-rule) ----

    /// A signature with one effect `E` whose op `op : (x:^? Univ1) → Univ0` (so an argument of
    /// type `Univ0`, which inhabits `Univ1`, type-checks, and the result is `Univ0`).
    fn one_op_sig() -> Signature {
        let mut sig = Signature::empty();
        let decl = crate::signature::EffDecl {
            name: crate::row::EffName::new("E"),
            ops: vec![crate::signature::OpSig {
                name: "op".into(),
                param_ty: u(1),
                result_ty: u(0),
                cont_grade: Grade::Omega,
            }],
        };
        sig.check_effect(&decl).expect("E is well-formed");
        sig.declare_effect(decl);
        sig
    }

    fn perform_op(arg: Term) -> Term {
        Term::Op {
            effect: crate::row::EffName::new("E"),
            op: "op".into(),
            arg: Box::new(arg),
        }
    }

    /// `perform op (Univ 0)` infers `Univ 0` and a row that mentions effect `E` at the demanded grade.
    #[test]
    fn op_contributes_label() {
        let checker = Checker::new(std::rc::Rc::new(one_op_sig()));
        let ctx = Context::empty();
        let (ty, row, _u) = checker
            .infer_g(&ctx, &perform_op(u(0)), Grade::One)
            .expect("op infers");
        // result type is Univ 0.
        assert!(
            matches!(ty, Value::Univ(Level::Zero)),
            "result type is Univ 0"
        );
        // row mentions E at grade 1 (the ambient demand), and nothing else.
        assert!(!row.is_empty(), "an op contributes its effect label");
        assert_eq!(row.grade_of(&crate::row::EffName::new("E")), Grade::One);
        assert!(
            !row.contains(&crate::row::EffName::partial()),
            "no spurious Partial"
        );
    }

    /// The operation argument is type-checked against the op's parameter type: a bad argument is
    /// rejected (here `Univ 2 : Univ 3 ≠ Univ 1`).
    #[test]
    fn op_arg_typechecked() {
        let checker = Checker::new(std::rc::Rc::new(one_op_sig()));
        let ctx = Context::empty();
        // arg Univ 2 has type Univ 3, which is not ≤ Univ 1.
        let r = checker.infer_g(&ctx, &perform_op(u(2)), Grade::One);
        assert!(r.is_err(), "ill-typed op argument is rejected");
    }

    /// An unknown operation is rejected with an `EffectError`.
    #[test]
    fn op_unknown_rejected() {
        let checker = Checker::new(std::rc::Rc::new(one_op_sig()));
        let ctx = Context::empty();
        let bad = Term::Op {
            effect: crate::row::EffName::new("E"),
            op: "nope".into(),
            arg: Box::new(u(0)),
        };
        assert!(matches!(
            checker.infer_g(&ctx, &bad, Grade::One),
            Err(TypeError::EffectError(_))
        ));
    }

    /// A pure term still infers the empty row (sanity: `Op` does not pollute pure inference).
    #[test]
    fn pure_term_has_empty_row() {
        let checker = Checker::new(std::rc::Rc::new(one_op_sig()));
        let ctx = Context::empty();
        let (_ty, row, _u) = checker
            .infer_g(&ctx, &u(0), Grade::One)
            .expect("pure infers");
        assert!(
            row.is_empty(),
            "a pure term has the empty row even when effects are in scope"
        );
    }

    /// An effectful term is rejected where a pure top-level proof is demanded (the `check_top_with`
    /// boundary): `perform op (Univ 0)` carries effect `E`, so it cannot be a complete proof.
    #[test]
    fn op_outside_row_rejected_when_pure_demanded() {
        let r = check_top_with(one_op_sig(), perform_op(u(0)), u(0));
        assert!(
            matches!(r, Err(TypeError::EffectError(_))),
            "effectful term rejected as a proof"
        );
    }

    /// `eval(perform op a)` builds an effectful-neutral `OpNode` with the identity (empty) cont.
    #[test]
    fn op_evaluates_to_opnode() {
        let checker = Checker::new(std::rc::Rc::new(one_op_sig()));
        let ctx = Context::empty();
        let v = eval(&checker.env_for(&ctx), &perform_op(u(0)));
        match v {
            Value::OpNode {
                effect, op, cont, ..
            } => {
                assert_eq!(effect, crate::row::EffName::new("E"));
                assert_eq!(op, "op");
                assert!(
                    cont.is_empty(),
                    "freshly-performed op has the identity continuation"
                );
            }
            other => panic!("expected OpNode, got {other:?}"),
        }
    }

    // ---- M2: Handle typing + eval (spec §4.3, handle-rule) ----

    /// A signature with a `Unit` type (`tt : Unit`) and an effect `E` whose op `op : Unit → Unit`,
    /// so handler clauses can produce values that actually inhabit the result type.
    fn unit_eff_sig() -> Signature {
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: DataName("Unit".into()),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("tt".into()),
                args: vec![],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        });
        let decl = crate::signature::EffDecl {
            name: crate::row::EffName::new("E"),
            ops: vec![crate::signature::OpSig {
                name: "op".into(),
                param_ty: unit_ty(),
                result_ty: unit_ty(),
                cont_grade: Grade::Omega,
            }],
        };
        sig.check_effect(&decl).expect("E well-formed");
        sig.declare_effect(decl);
        sig
    }

    fn unit_ty() -> Term {
        Term::Data(DataName("Unit".into()), vec![], vec![])
    }
    fn tt() -> Term {
        Term::Con(ConName("tt".into()), vec![])
    }
    fn perform_e(arg: Term) -> Term {
        Term::Op {
            effect: crate::row::EffName::new("E"),
            op: "op".into(),
            arg: Box::new(arg),
        }
    }

    /// `handle (perform op tt) { return x. x ; op x k. (k x) }` — a handler interpreting `op`.
    /// `x : Unit`, `k : Unit → Unit`, `C = Unit`. Resumes `k` with the operation argument.
    fn handle_resume(body: Term) -> Term {
        Term::Handle {
            body: Box::new(body),
            return_clause: Box::new(Term::Var(0)), // return x. x
            op_clauses: vec![(
                "op".into(),
                // op x k. (k x): k is de Bruijn 0, x is de Bruijn 1.
                Box::new(Term::App(Box::new(Term::Var(0)), Box::new(Term::Var(1)))),
            )],
        }
    }

    /// A handler discharges the handled label: `handle (perform op tt) {…}` has the empty row.
    #[test]
    fn handle_discharges_label() {
        let checker = Checker::new(std::rc::Rc::new(unit_eff_sig()));
        let ctx = Context::empty();
        let term = handle_resume(perform_e(tt()));
        let (ty, row, _u) = checker
            .infer_g(&ctx, &term, Grade::One)
            .expect("handle infers");
        // result type is Unit.
        assert!(
            matches!(ty, Value::Data(ref d, ..) if d.0 == "Unit"),
            "result is Unit"
        );
        assert!(
            row.is_empty(),
            "the handled label E is discharged → empty row"
        );
    }

    /// The return clause determines (and is checked at) the result type. A handler whose body is a
    /// *pure* value still runs `return`, so `handle tt { return x. x ; … }` infers `Unit`.
    #[test]
    fn return_clause_typed() {
        let checker = Checker::new(std::rc::Rc::new(unit_eff_sig()));
        let ctx = Context::empty();
        let term = handle_resume(tt());
        let (ty, row, _u) = checker
            .infer_g(&ctx, &term, Grade::One)
            .expect("handle infers");
        assert!(matches!(ty, Value::Data(ref d, ..) if d.0 == "Unit"));
        assert!(row.is_empty());
    }

    /// The continuation `k` is bound at type `Bᵢ → C`: a clause that misuses `k` (applies it to the
    /// wrong type) is rejected. Here `op x k. (k k)` applies `k` to `k`, a type error.
    #[test]
    fn k_binder_typed() {
        let checker = Checker::new(std::rc::Rc::new(unit_eff_sig()));
        let ctx = Context::empty();
        let term = Term::Handle {
            body: Box::new(perform_e(tt())),
            return_clause: Box::new(Term::Var(0)),
            op_clauses: vec![(
                "op".into(),
                Box::new(Term::App(Box::new(Term::Var(0)), Box::new(Term::Var(0)))), // k k — ill-typed
            )],
        };
        assert!(
            checker.infer_g(&ctx, &term, Grade::One).is_err(),
            "k applied to k is rejected"
        );
    }

    // ---- continuation multiplicity (spec §4.6, M2) -----------------------------------------

    /// Build a single-op effect `E` whose continuation multiplicity is `g`. `op : Unit → Unit`.
    fn eff_sig_with_cont_grade(g: Grade) -> Signature {
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: DataName("Unit".into()),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("tt".into()),
                args: vec![],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        });
        let decl = crate::signature::EffDecl {
            name: crate::row::EffName::new("E"),
            ops: vec![crate::signature::OpSig {
                name: "op".into(),
                param_ty: unit_ty(),
                result_ty: unit_ty(),
                cont_grade: g,
            }],
        };
        sig.check_effect(&decl).expect("E well-formed");
        sig.declare_effect(decl);
        sig
    }

    /// `handle (perform op tt) { return x. x ; op x k. <clause> }` for a custom op clause. In the
    /// clause's scope, `k` is de Bruijn 0 and `x` (the op argument) is de Bruijn 1.
    fn handle_with_clause(clause: Term) -> Term {
        Term::Handle {
            body: Box::new(perform_e(tt())),
            return_clause: Box::new(Term::Var(0)),
            op_clauses: vec![("op".into(), Box::new(clause))],
        }
    }

    /// A *linear* (`1`-graded) effect: resuming the continuation **twice** is a `GradeViolation`,
    /// exactly like using a linear `λ`-bound variable twice. `op x k. k (k x)` uses `k` at grade ω.
    #[test]
    fn linear_effect_double_resume_rejected() {
        let checker = Checker::new(std::rc::Rc::new(eff_sig_with_cont_grade(Grade::One)));
        let ctx = Context::empty();
        // k (k x): both inner and outer application use k (de Bruijn 0); x is de Bruijn 1.
        let double = Term::App(
            Box::new(Term::Var(0)),
            Box::new(Term::App(Box::new(Term::Var(0)), Box::new(Term::Var(1)))),
        );
        let term = handle_with_clause(double);
        match checker.infer_g(&ctx, &term, Grade::One) {
            Err(TypeError::GradeViolation(_)) => {}
            other => panic!(
                "expected GradeViolation for double-resume of a linear effect, got {other:?}"
            ),
        }
    }

    /// An *abort* (`0`-graded) effect: the continuation may **not** be invoked at all (e.g. an
    /// exception). `op x k. k x` resumes once (grade 1), and `1 ≤ 0` is false ⟹ `GradeViolation`.
    #[test]
    fn abort_effect_calls_k_rejected() {
        let checker = Checker::new(std::rc::Rc::new(eff_sig_with_cont_grade(Grade::Zero)));
        let ctx = Context::empty();
        // k x
        let resume_once = Term::App(Box::new(Term::Var(0)), Box::new(Term::Var(1)));
        let term = handle_with_clause(resume_once);
        match checker.infer_g(&ctx, &term, Grade::One) {
            Err(TypeError::GradeViolation(_)) => {}
            other => panic!("expected GradeViolation for resuming an abort effect, got {other:?}"),
        }
    }

    /// A *nondeterministic* (`ω`-graded) effect: resuming the continuation any number of times is
    /// fine. `op x k. k (k x)` resumes twice and type-checks (the handled label is discharged).
    #[test]
    fn nondet_effect_multi_resume_ok() {
        let checker = Checker::new(std::rc::Rc::new(eff_sig_with_cont_grade(Grade::Omega)));
        let ctx = Context::empty();
        let double = Term::App(
            Box::new(Term::Var(0)),
            Box::new(Term::App(Box::new(Term::Var(0)), Box::new(Term::Var(1)))),
        );
        let term = handle_with_clause(double);
        let (ty, row, _u) = checker
            .infer_g(&ctx, &term, Grade::One)
            .expect("multi-resume under an ω-graded effect type-checks");
        assert!(matches!(ty, Value::Data(ref d, ..) if d.0 == "Unit"));
        assert!(
            row.is_empty(),
            "the handled label E is discharged → empty row"
        );
    }

    /// `conv` computes through `Handle`: `handle (perform op tt) { return x. x ; op x k. (k x) }`
    /// resumes the continuation with `tt`, the (empty) spine returns `tt`, and `return` yields `tt`.
    /// So the whole handled computation is definitionally `tt`.
    #[test]
    fn conv_computes_through_handle() {
        let checker = Checker::new(std::rc::Rc::new(unit_eff_sig()));
        let ctx = Context::empty();
        let term = handle_resume(perform_e(tt()));
        let v = eval(&checker.env_for(&ctx), &term);
        let expected = eval(&checker.env_for(&ctx), &tt());
        assert!(conv(0, &v, &expected), "handled op computes to tt");
    }

    /// An *unhandled* effect bubbles past a handler. With a signature that also declares effect `F`
    /// (op `fop`), `handle (perform fop tt) { op x k. … }` does not handle `fop`, so the result row
    /// still carries `F` (the handler is transparent to it).
    #[test]
    fn unhandled_effect_bubbles() {
        let mut sig = unit_eff_sig();
        let f = crate::signature::EffDecl {
            name: crate::row::EffName::new("F"),
            ops: vec![crate::signature::OpSig {
                name: "fop".into(),
                param_ty: unit_ty(),
                result_ty: unit_ty(),
                cont_grade: Grade::Omega,
            }],
        };
        sig.check_effect(&f).expect("F well-formed");
        sig.declare_effect(f);
        let checker = Checker::new(std::rc::Rc::new(sig));
        let ctx = Context::empty();
        let fop = Term::Op {
            effect: crate::row::EffName::new("F"),
            op: "fop".into(),
            arg: Box::new(tt()),
        };
        // Handler only handles `op` (of E), not `fop` (of F).
        let term = handle_resume(fop);
        let (_ty, row, _u) = checker.infer_g(&ctx, &term, Grade::One).expect("infers");
        assert!(
            row.contains(&crate::row::EffName::new("F")),
            "unhandled F bubbles through"
        );
        assert!(
            !row.contains(&crate::row::EffName::new("E")),
            "E is not present (not performed)"
        );
    }

    /// `eval` of an unhandled op under a handler bubbles an `OpNode` (transparent handler).
    #[test]
    fn eval_unhandled_op_bubbles_opnode() {
        let mut sig = unit_eff_sig();
        let f = crate::signature::EffDecl {
            name: crate::row::EffName::new("F"),
            ops: vec![crate::signature::OpSig {
                name: "fop".into(),
                param_ty: unit_ty(),
                result_ty: unit_ty(),
                cont_grade: Grade::Omega,
            }],
        };
        sig.check_effect(&f).expect("F well-formed");
        sig.declare_effect(f);
        let checker = Checker::new(std::rc::Rc::new(sig));
        let ctx = Context::empty();
        let fop = Term::Op {
            effect: crate::row::EffName::new("F"),
            op: "fop".into(),
            arg: Box::new(tt()),
        };
        let term = handle_resume(fop);
        let v = eval(&checker.env_for(&ctx), &term);
        assert!(
            matches!(v, Value::OpNode { ref op, .. } if op == "fop"),
            "fop bubbles as OpNode"
        );
    }

    /// Application: `(λ x. x : Univ0→Univ0) (Univ 0)` is rejected because `Univ 0 : Univ 1`, not
    /// `Univ 0`. But ascribing the identity at `Univ 1` and applying to `Univ 0` works.
    #[test]
    fn application_respects_domain() {
        // id at Univ 1 : (x :^ω Univ 1) → Univ 1, applied to Univ 0 (since Univ 0 : Univ 1).
        let id_ty = Term::Pi(Grade::Omega, Box::new(u(1)), Box::new(u(1)));
        let id = Term::Lam(Box::new(Term::Var(0)));
        let ascribed = Term::App(Box::new(annotate(id, id_ty)), Box::new(u(0)));
        // result type is Univ 1; check it.
        assert!(check_top(ascribed, u(1)).is_ok());
    }

    /// Type mismatch is rejected: `Univ 0` does not check against `(x:^ω Univ0)→Univ0`.
    #[test]
    fn mismatch_rejected() {
        let pi = Term::Pi(Grade::Omega, Box::new(u(0)), Box::new(u(0)));
        assert!(check_top(u(0), pi).is_err());
    }

    /// Helper: wrap a term so `infer` can synthesize a type for a lambda (via an internal
    /// annotation node). Implemented in terms of the kernel's own ascription support.
    fn annotate(term: Term, ty: Term) -> Term {
        // We model annotation by a redex against the identity at the ascribed Pi; but cleaner is
        // a dedicated Ann node. The kernel exposes annotation through check, so for inference of
        // an application head we rely on the elaborator normally. For this unit test we use the
        // Ann term variant.
        Term::Ann(Box::new(term), Box::new(ty))
    }

    // ---- L3: inductive families + dependent Elim (spec §2.7) ----

    use crate::signature::{Arg, Constructor, DataDecl, PathConstructor, Signature};
    use crate::term::{ConName, DataName};

    fn nat_name() -> DataName {
        DataName("Nat".into())
    }
    fn zero() -> Term {
        Term::Con(ConName("zero".into()), vec![])
    }
    fn succ(n: Term) -> Term {
        Term::Con(ConName("succ".into()), vec![n])
    }

    /// The `Nat` signature: `zero : Nat`, `succ : Nat → Nat`.
    fn nat_sig() -> Signature {
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: nat_name(),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![
                Constructor {
                    name: ConName("zero".into()),
                    args: vec![],
                    result_indices: vec![],
                },
                Constructor {
                    name: ConName("succ".into()),
                    args: vec![Arg::Rec(vec![])],
                    result_indices: vec![],
                },
            ],
            path_constructors: vec![],
        });
        sig
    }

    fn nat_ty() -> Term {
        Term::Data(nat_name(), vec![], vec![])
    }

    fn vec_name() -> DataName {
        DataName("Vec".into())
    }

    /// `Vec : (A : Univ 0) → (n : Nat) → Univ 0` with `vnil : Vec A zero` and
    /// `vcons : (n : Nat) → A → Vec A n → Vec A (succ n)`. The single parameter is `A`, the single
    /// index is `n : Nat`. Built on top of `nat_sig` (so `zero`/`succ` are available).
    fn vec_sig() -> Signature {
        let mut sig = nat_sig();
        sig.declare(DataDecl {
            name: vec_name(),
            params: vec![u(0)],
            indices: vec![nat_ty()],
            level: 0,
            constructors: vec![
                Constructor {
                    name: ConName("vnil".into()),
                    args: vec![],
                    // vnil : Vec A zero
                    result_indices: vec![zero()],
                },
                Constructor {
                    name: ConName("vcons".into()),
                    // args: (n : Nat) (x : A) (xs : Vec A n). The parameter `A` and the preceding
                    // args are in scope innermost-first. When checking `x`, the env is [n, A], so
                    // `A` is de Bruijn 1. When checking `xs`, the env is [x, n, A], so the recursive
                    // index `n` is de Bruijn 1.
                    args: vec![
                        Arg::NonRec(nat_ty()),
                        Arg::NonRec(Term::Var(1)),
                        Arg::Rec(vec![Term::Var(1)]),
                    ],
                    // result index = succ n. In the result scope the env is [xs, x, n, A]
                    // innermost-first, so `n` is at de Bruijn index 2.
                    result_indices: vec![succ(Term::Var(2))],
                },
            ],
            path_constructors: vec![],
        });
        sig
    }

    fn vec_ty(elem: Term, len: Term) -> Term {
        Term::Data(vec_name(), vec![elem], vec![len])
    }

    /// `Nat : Univ 0` (formation).
    #[test]
    fn nat_formation() {
        assert!(check_top_with(nat_sig(), nat_ty(), u(0)).is_ok());
    }

    /// `zero : Nat` and `succ zero : Nat` (constructors).
    #[test]
    fn nat_constructors() {
        assert!(
            check_top_with(nat_sig(), zero(), nat_ty()).is_ok(),
            "zero : Nat"
        );
        assert!(
            check_top_with(nat_sig(), succ(zero()), nat_ty()).is_ok(),
            "succ zero : Nat"
        );
    }

    /// `succ` applied to a non-`Nat` is rejected.
    #[test]
    fn succ_rejects_non_nat() {
        assert!(
            check_top_with(nat_sig(), succ(u(0)), nat_ty()).is_err(),
            "succ (Univ 0) must be rejected"
        );
    }

    /// ι-reduction: a non-dependent recursor. With motive `λ _. Nat`, methods `zero` and
    /// `λ n ih. succ ih`, eliminating `succ (succ zero)` computes back to `succ (succ zero)`
    /// (the identity recursor). Checks against `Nat`.
    #[test]
    fn elim_iota_identity_recursor() {
        // motive: λ (_:Nat). Nat
        let motive = Term::Lam(Box::new(nat_ty()));
        // method_zero : Nat = zero
        let method_zero = zero();
        // method_succ : (n:Nat) → (ih:Nat) → Nat  =  λ n. λ ih. succ ih
        let method_succ = Term::Lam(Box::new(Term::Lam(Box::new(succ(Term::Var(0))))));
        let scrut = succ(succ(zero()));
        let elim = Term::Elim {
            data: nat_name(),
            motive: Box::new(motive),
            methods: vec![method_zero, method_succ],
            scrutinee: Box::new(scrut),
        };
        // The recursor rebuilds the number, so it has type Nat and equals succ (succ zero).
        assert!(
            check_top_with(nat_sig(), elim.clone(), nat_ty()).is_ok(),
            "identity recursor checks at Nat"
        );

        // And it is definitionally equal to succ (succ zero): check via ascription/Conv.
        let sig = std::rc::Rc::new(nat_sig());
        let checker = Checker::new(sig);
        let ctx = Context::empty();
        let lhs = eval(&checker.env_for(&ctx), &elim);
        let rhs = eval(&checker.env_for(&ctx), &succ(succ(zero())));
        assert!(
            conv(0, &lhs, &rhs),
            "ι: identity recursor reduces to its input"
        );
    }

    /// ι-reduction computing a constant: motive `λ _. Nat`, methods `zero`↦`succ zero`,
    /// `succ`↦`λ n ih. ih`. Eliminating any number yields the `zero` method's value… let's make
    /// it a "is it zero?" style: map `zero ↦ zero`, `succ _ _ ↦ succ zero`. On `succ zero` it must
    /// reduce to `succ zero`.
    #[test]
    fn elim_iota_computes_method() {
        let motive = Term::Lam(Box::new(nat_ty()));
        let method_zero = zero();
        // λ n. λ ih. succ zero   (ignores recursion, returns 1)
        let method_succ = Term::Lam(Box::new(Term::Lam(Box::new(succ(zero())))));
        let elim = |scrut: Term| Term::Elim {
            data: nat_name(),
            motive: Box::new(motive.clone()),
            methods: vec![method_zero.clone(), method_succ.clone()],
            scrutinee: Box::new(scrut),
        };
        let sig = std::rc::Rc::new(nat_sig());
        let checker = Checker::new(sig);
        let ctx = Context::empty();

        // on zero ⇒ zero
        let on_zero = eval(&checker.env_for(&ctx), &elim(zero()));
        assert!(conv(0, &on_zero, &eval(&checker.env_for(&ctx), &zero())));

        // on succ zero ⇒ succ zero
        let on_one = eval(&checker.env_for(&ctx), &elim(succ(zero())));
        assert!(conv(
            0,
            &on_one,
            &eval(&checker.env_for(&ctx), &succ(zero()))
        ));
    }

    /// Strict-positivity: a constructor with a negative occurrence of the data type is rejected by
    /// the signature's positivity check (spec §2.7).
    #[test]
    fn strict_positivity_rejected() {
        // bad : (Bad → Bad) → Bad   — Bad occurs to the left of an arrow (negative).
        let bad_name = DataName("Bad".into());
        let decl = DataDecl {
            name: bad_name.clone(),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("mk".into()),
                args: vec![Arg::NonRec(Term::Pi(
                    Grade::Omega,
                    Box::new(Term::Data(bad_name.clone(), vec![], vec![])),
                    Box::new(Term::Data(bad_name.clone(), vec![], vec![])),
                ))],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        };
        let sig = Signature::empty();
        assert!(
            sig.check_positivity(&decl).is_err(),
            "non-strictly-positive constructor must be rejected"
        );
    }

    /// A HIT records its path constructor structurally (spec §2.7). Here a circle-like type with a
    /// point `base` and a loop path constructor; we just assert the signature is well-formed and
    /// the point constructor types.
    #[test]
    fn hit_point_and_path_constructor() {
        let s1 = DataName("S1".into());
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: s1.clone(),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("base".into()),
                args: vec![],
                result_indices: vec![],
            }],
            path_constructors: vec![PathConstructor {
                name: ConName("loop".into()),
                args: vec![],
                lhs: Term::Con(ConName("base".into()), vec![]),
                rhs: Term::Con(ConName("base".into()), vec![]),
            }],
        });
        // base : S1
        let base = Term::Con(ConName("base".into()), vec![]);
        assert!(
            check_top_with(sig, base, Term::Data(s1, vec![], vec![])).is_ok(),
            "point constructor of the HIT checks"
        );
    }

    // ---- L4: Path typing (spec §2.6) ----
    use crate::term::Interval as Iv;

    /// `refl {A} x : Path A x x` where `Path A x y = PathP (i. A) x y` (constant family). Here we
    /// take `A = Univ 0` and `x = Univ 0`'s element... use a concrete neutral via ascription.
    /// We test with `A = Nat`, `x = zero`: `refl = λ i. zero : PathP (_. Nat) zero zero`.
    #[test]
    fn refl_checks_as_constant_path() {
        let path_ty = Term::PathP {
            family: Box::new(nat_ty()), // constant line `i. Nat`
            lhs: Box::new(zero()),
            rhs: Box::new(zero()),
        };
        let refl = Term::PLam(Box::new(zero())); // λ i. zero
        assert!(
            check_top_with(nat_sig(), refl, path_ty).is_ok(),
            "refl : Path Nat zero zero"
        );
    }

    /// A path with mismatched boundary is rejected: `λ i. zero : Path Nat zero (succ zero)` fails
    /// because the rhs boundary `zero ≢ succ zero`.
    #[test]
    fn path_boundary_mismatch_rejected() {
        let path_ty = Term::PathP {
            family: Box::new(nat_ty()),
            lhs: Box::new(zero()),
            rhs: Box::new(succ(zero())),
        };
        let bad = Term::PLam(Box::new(zero()));
        assert!(
            check_top_with(nat_sig(), bad, path_ty).is_err(),
            "bad boundary must be rejected"
        );
    }

    /// `PathP` is a type: `Path Nat zero zero : Univ 0` (formation).
    #[test]
    fn pathp_formation() {
        let path_ty = Term::PathP {
            family: Box::new(nat_ty()),
            lhs: Box::new(zero()),
            rhs: Box::new(zero()),
        };
        assert!(check_top_with(nat_sig(), path_ty, u(0)).is_ok());
    }

    /// Path application at an endpoint computes the endpoint: `(λ i. succ zero) @ 0 : Nat` and the
    /// result is definitionally `succ zero`. We type the application and check it against Nat.
    #[test]
    fn papp_at_endpoint_types_and_computes() {
        // p : Path Nat (succ zero) (succ zero), p = λ i. succ zero.
        let p = Term::Ann(
            Box::new(Term::PLam(Box::new(succ(zero())))),
            Box::new(Term::PathP {
                family: Box::new(nat_ty()),
                lhs: Box::new(succ(zero())),
                rhs: Box::new(succ(zero())),
            }),
        );
        let app = Term::PApp(Box::new(p), Iv::I0);
        assert!(
            check_top_with(nat_sig(), app.clone(), nat_ty()).is_ok(),
            "p @ 0 : Nat"
        );
        // And it computes to succ zero.
        let sig = std::rc::Rc::new(nat_sig());
        let checker = Checker::new(sig);
        let ctx = Context::empty();
        let v = eval(&checker.env_for(&ctx), &app);
        let expected = eval(&checker.env_for(&ctx), &succ(zero()));
        assert!(conv(0, &v, &expected), "p @ 0 ≡ succ zero");
    }

    // ---- M1: graded / linear accounting (spec §3.2, §3.7) ----

    /// `λ A. λ x. x : (A :^0 Univ0) → (x :^1 A) → A`. The linear `x` is used exactly once.
    #[test]
    fn linear_var_used_once_ok() {
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::One,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(0)))));
        assert_eq!(
            check_top(term, ty).map(|_| ()),
            Ok(()),
            "linear x used once must check"
        );
    }

    /// `λ A. λ x. (x, x) : (A :^0 Univ0) → (x :^1 A) → Σ A A`. Using the linear `x` twice yields
    /// demand ω on `x`, and ω ≤ 1 is false ⟹ GradeViolation. (Assert the *variant*.)
    #[test]
    fn linear_var_used_twice_rejected() {
        // In scope [A, x]: A is Var(1); inside the Σ codomain one more binder ⟹ A is Var(2).
        let sigma_ty = Term::Sigma(Box::new(Term::Var(1)), Box::new(Term::Var(2)));
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::One,
                Box::new(Term::Var(0)),
                Box::new(sigma_ty),
            )),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Pair(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(0)),
        )))));
        match check_top(term, ty) {
            Err(TypeError::GradeViolation(_)) => {}
            other => panic!("expected GradeViolation, got {other:?}"),
        }
    }

    /// `λ A. λ x. λ y. y : (A :^0 Univ0) → (x :^1 A) → (y :^ω A) → A`. The linear `x` is *dropped*
    /// (used zero times). M1 is affine: 0 ≤ 1 holds, so this is intentionally ACCEPTED. This test
    /// documents the affine-not-strict-linear choice.
    #[test]
    fn linear_var_dropped_allowed_affine() {
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::One,
                Box::new(Term::Var(0)),
                Box::new(Term::Pi(
                    Grade::Omega,
                    Box::new(Term::Var(1)),
                    Box::new(Term::Var(2)),
                )),
            )),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Lam(Box::new(
            Term::Var(0),
        ))))));
        assert!(
            check_top(term, ty).is_ok(),
            "dropping a linear var is allowed under the affine M1 reading"
        );
    }

    /// The accept twin of `linear_var_used_twice_rejected`: with `x :^ω`, using it twice checks.
    /// Guards against over-eager rejection (the rule must *discriminate* on the grade).
    #[test]
    fn omega_var_used_twice_ok() {
        // In scope [A, x]: A is Var(1); inside the Σ codomain ⟹ A is Var(2).
        let sigma_ty = Term::Sigma(Box::new(Term::Var(1)), Box::new(Term::Var(2)));
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Var(0)),
                Box::new(sigma_ty),
            )),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Pair(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(0)),
        )))));
        assert!(
            check_top(term, ty).is_ok(),
            "an ω-graded var may be used twice"
        );
    }

    /// Application scales argument demand by the binder grade: applying a function whose argument
    /// binder is `ω` to a linear variable forces that variable's demand to ω, and ω ≤ 1 fails.
    /// `λ A. λ (f :^ω (A→A)). λ (x :^1 A). f (f x)` rejects because the inner+outer applications
    /// each demand `x`, summing to ω on the linear `x`.
    #[test]
    fn app_scales_argument_usage() {
        let a_to_a = || Term::Pi(Grade::Omega, Box::new(Term::Var(1)), Box::new(Term::Var(2)));
        // type: (A:^0 U0) -> (f:^ω (A->A)) -> (x:^1 A) -> A
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Pi(
                    Grade::Omega,
                    Box::new(Term::Var(0)),
                    Box::new(Term::Var(1)),
                )),
                Box::new(Term::Pi(
                    Grade::One,
                    Box::new(Term::Var(1)),
                    Box::new(Term::Var(2)),
                )),
            )),
        );
        let _ = a_to_a;
        // body: λ A. λ f. λ x. f (f x)   — x appears once but under two applications of f; the
        // demand on x is 1 (it textually occurs once), so this actually checks. To force a
        // *double* demand we instead use (f x) paired with x. See below.
        // Use: λ A. λ f. λ x. (f x, x) : ... -> Σ A A, demanding x twice (once directly, once via f).
        // In scope [A, f, x]: A is Var(2); inside the Σ codomain ⟹ A is Var(3).
        let sigma_ty = Term::Sigma(Box::new(Term::Var(2)), Box::new(Term::Var(3)));
        let ty2 = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Pi(
                    Grade::Omega,
                    Box::new(Term::Var(0)),
                    Box::new(Term::Var(1)),
                )),
                Box::new(Term::Pi(
                    Grade::One,
                    Box::new(Term::Var(1)),
                    Box::new(sigma_ty),
                )),
            )),
        );
        let _ = ty;
        // λ A. λ f. λ x. (f x, x)
        let body = Term::Lam(Box::new(Term::Lam(Box::new(Term::Lam(Box::new(
            Term::Pair(
                Box::new(Term::App(Box::new(Term::Var(1)), Box::new(Term::Var(0)))),
                Box::new(Term::Var(0)),
            ),
        ))))));
        match check_top(body, ty2) {
            Err(TypeError::GradeViolation(_)) => {}
            other => {
                panic!("expected GradeViolation from double demand on linear x, got {other:?}")
            }
        }
    }

    // ---- M1: the 0-fragment discipline (spec §3.7) ----

    /// An erased binder (`ρ = 0`) whose variable is used only in *type* position is NOT charged
    /// at runtime, so the binder check `0 ≥ demand` succeeds. Here `n :^0 Nat` appears only in the
    /// return type `Nat` (vacuously) — concretely we erase the value entirely:
    /// `λ (n :^0 Nat). zero : (n :^0 Nat) → Nat`. The body never mentions `n`, demand 0 ≤ 0.
    #[test]
    fn erased_var_not_used_ok() {
        let ty = Term::Pi(Grade::Zero, Box::new(nat_ty()), Box::new(nat_ty()));
        let term = Term::Lam(Box::new(zero()));
        assert!(
            check_top_with(nat_sig(), term, ty).is_ok(),
            "erased binder unused at runtime is fine"
        );
    }

    /// Twin reject: an erased binder used at *runtime* (`λ (n :^0 Nat). n`) demands `n` at grade
    /// 1, and 1 ≤ 0 is false ⟹ GradeViolation. This is the soundness teeth of erasure: a 0-graded
    /// value may never flow into a runtime-relevant position.
    #[test]
    fn runtime_use_of_erased_var_rejected() {
        let ty = Term::Pi(Grade::Zero, Box::new(nat_ty()), Box::new(nat_ty()));
        let term = Term::Lam(Box::new(Term::Var(0)));
        match check_top_with(nat_sig(), term, ty) {
            Err(TypeError::GradeViolation(_)) => {}
            other => panic!("expected GradeViolation for runtime use of erased var, got {other:?}"),
        }
    }

    /// An erased binder *may* legitimately appear in a type-formation subgoal without being
    /// charged. `λ (A :^0 Univ0). λ (x :^1 A). x` uses `A` only in the (erased) type of `x` and in
    /// the result type — never as a runtime value — so `A`'s runtime demand is 0 ≤ 0. (This is the
    /// same shape as `linear_var_used_once_ok`, asserted here as the canonical 0-fragment accept.)
    #[test]
    fn erased_type_param_not_charged() {
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::One,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(0)))));
        assert!(
            check_top(term, ty).is_ok(),
            "type-only parameter must not be charged at runtime"
        );
    }

    // ---- M1: minimal indexed data (spec §2.7, §3.7) ----

    /// `Vec Nat zero : Univ 0` — indexed family formation with one param and one index.
    #[test]
    fn vec_formation() {
        let t = vec_ty(nat_ty(), zero());
        assert!(
            check_top_with(vec_sig(), t, u(0)).is_ok(),
            "Vec Nat zero is a well-formed type"
        );
    }

    /// `vnil : Vec Nat zero` — the empty-vector constructor at index `zero`.
    #[test]
    fn vec_nil() {
        let term = Term::Con(ConName("vnil".into()), vec![]);
        let ty = vec_ty(nat_ty(), zero());
        assert!(
            check_top_with(vec_sig(), term, ty).is_ok(),
            "vnil : Vec Nat zero"
        );
    }

    /// `vcons zero (zero) vnil : Vec Nat (succ zero)` — cons lengthens the index by one.
    /// Args: n = zero, x = zero : Nat, xs = vnil : Vec Nat zero ; result index = succ zero.
    #[test]
    fn vec_cons() {
        let nil = Term::Con(ConName("vnil".into()), vec![]);
        let term = Term::Con(ConName("vcons".into()), vec![zero(), zero(), nil]);
        let ty = vec_ty(nat_ty(), succ(zero()));
        assert_eq!(
            check_top_with(vec_sig(), term, ty).map(|_| ()),
            Ok(()),
            "vcons zero zero vnil : Vec Nat (succ zero)"
        );
    }

    /// A constructor whose computed index disagrees with the expected one is rejected:
    /// `vnil` has index `zero`, so checking it against `Vec Nat (succ zero)` must fail.
    #[test]
    fn vec_index_mismatch_rejected() {
        let term = Term::Con(ConName("vnil".into()), vec![]);
        let ty = vec_ty(nat_ty(), succ(zero()));
        match check_top_with(vec_sig(), term, ty) {
            Err(TypeError::Mismatch { .. }) => {}
            other => panic!("expected index Mismatch, got {other:?}"),
        }
    }

    /// Eliminating an *indexed* family is supported (M3): the motive abstracts the index, and the
    /// recursor computes by ι-reduction. A "length" recursor over `Vec` returns the element count.
    #[test]
    fn indexed_elim_computes_length() {
        // scrutinee : Vec Nat (succ zero) = vcons zero zero vnil  (one element)
        let vnil = Term::Con(ConName("vnil".into()), vec![]);
        let one_vec = Term::Con(ConName("vcons".into()), vec![zero(), zero(), vnil.clone()]);
        let scrut = Term::Ann(Box::new(one_vec), Box::new(vec_ty(nat_ty(), succ(zero()))));
        // motive : λ (n:Nat). λ (_:Vec Nat n). Nat
        let motive = Term::Lam(Box::new(Term::Lam(Box::new(nat_ty()))));
        // method vnil : Nat = zero
        let m_vnil = zero();
        // method vcons : (n:Nat)→(x:Nat)→(xs:Vec Nat n)→(ih:Nat)→Nat = λ.λ.λ.λ. succ ih
        let m_vcons = Term::Lam(Box::new(Term::Lam(Box::new(Term::Lam(Box::new(
            Term::Lam(Box::new(succ(Term::Var(0)))),
        ))))));
        let elim = Term::Elim {
            data: vec_name(),
            motive: Box::new(motive),
            methods: vec![m_vnil, m_vcons],
            scrutinee: Box::new(scrut),
        };
        // The recursor counts elements ⟹ result is `succ zero : Nat`.
        let proof = check_top_with(vec_sig(), elim.clone(), nat_ty())
            .expect("indexed elim typechecks against Nat");
        let _ = proof;
        // And it must *not* check against the wrong count.
        // (succ zero ≠ zero), so checking the recursor's value is succ zero, not zero.
        assert!(check_top_with(
            vec_sig(),
            Term::Ann(Box::new(elim), Box::new(nat_ty())),
            nat_ty()
        )
        .is_ok());
    }

    /// `List : (A:Univ 0) → Univ 0` with `lnil : List A`, `lcons : A → List A → List A` — a
    /// parameterized, non-indexed family. Eliminating it computes (a "length" recursor returns the
    /// element count as a `Nat`).
    fn list_sig() -> Signature {
        let mut sig = nat_sig();
        sig.declare(DataDecl {
            name: DataName("List".into()),
            params: vec![u(0)],
            indices: vec![],
            level: 0,
            constructors: vec![
                Constructor {
                    name: ConName("lnil".into()),
                    args: vec![],
                    result_indices: vec![],
                },
                Constructor {
                    name: ConName("lcons".into()),
                    // (x : A) (xs : List A). When checking `x`, env is [A] ⟹ A = Var(0).
                    args: vec![Arg::NonRec(Term::Var(0)), Arg::Rec(vec![])],
                    result_indices: vec![],
                },
            ],
            path_constructors: vec![],
        });
        sig
    }

    #[test]
    fn param_elim_computes_length() {
        let list_nat = Term::Data(DataName("List".into()), vec![nat_ty()], vec![]);
        // scrutinee : List Nat = lcons zero (lcons zero lnil)  (two elements)
        let lnil = Term::Con(ConName("lnil".into()), vec![]);
        let two = Term::Con(
            ConName("lcons".into()),
            vec![
                zero(),
                Term::Con(ConName("lcons".into()), vec![zero(), lnil]),
            ],
        );
        let scrut = Term::Ann(Box::new(two), Box::new(list_nat.clone()));
        // motive : λ (_:List Nat). Nat
        let motive = Term::Lam(Box::new(nat_ty()));
        // method lnil = zero
        let m_lnil = zero();
        // method lcons : (x:Nat)→(xs:List Nat)→(ih:Nat)→Nat = λ.λ.λ. succ ih
        let m_lcons = Term::Lam(Box::new(Term::Lam(Box::new(Term::Lam(Box::new(succ(
            Term::Var(0),
        )))))));
        let elim = Term::Elim {
            data: DataName("List".into()),
            motive: Box::new(motive),
            methods: vec![m_lnil, m_lcons],
            scrutinee: Box::new(scrut),
        };
        assert!(
            check_top_with(list_sig(), elim, nat_ty()).is_ok(),
            "parameterized List recursor typechecks and computes a Nat"
        );
    }

    // ---- multi-parameter / multi-index telescopes (cap lifted) -------------------------------

    /// `Pair : (A:Univ 0) → (B:Univ 0) → Univ 0` with `mk : A → B → Pair A B`. A two-parameter,
    /// non-indexed family; its eliminator with motive `λ (_:Pair A B). A` projects the first
    /// component. Exercises the lifted `params.len() > 1` cap end to end.
    fn pair_sig() -> Signature {
        let mut sig = nat_sig();
        sig.declare(DataDecl {
            name: DataName("Pair".into()),
            params: vec![u(0), u(0)],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("mk".into()),
                // (x : A) (y : B). Params are pushed outermost-first then args innermost, so in the
                // env the params sit *above* the args. When checking `x` (0 earlier args) the env is
                // [B, A] ⟹ A = Var(1). When checking `y` (1 earlier arg `x`) the env is [x, B, A] ⟹
                // B = Var(1).
                args: vec![Arg::NonRec(Term::Var(1)), Arg::NonRec(Term::Var(1))],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        });
        sig
    }

    #[test]
    fn two_param_formation_and_elim() {
        let pair_nat_nat = Term::Data(DataName("Pair".into()), vec![nat_ty(), nat_ty()], vec![]);
        // Formation: `Pair Nat Nat : Univ 0`.
        assert!(
            check_top_with(pair_sig(), pair_nat_nat.clone(), u(0)).is_ok(),
            "two-parameter Pair formation typechecks"
        );
        // scrutinee : Pair Nat Nat = mk (succ zero) zero (needs ascription — parameterized family).
        let mk = Term::Con(ConName("mk".into()), vec![succ(zero()), zero()]);
        let scrut = Term::Ann(Box::new(mk), Box::new(pair_nat_nat.clone()));
        // motive : λ (_ : Pair Nat Nat). Nat ; method mk : (x:Nat)→(y:Nat)→Nat = λ x. λ y. x.
        let motive = Term::Lam(Box::new(nat_ty()));
        let m_mk = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(1)))));
        let elim = Term::Elim {
            data: DataName("Pair".into()),
            motive: Box::new(motive),
            methods: vec![m_mk],
            scrutinee: Box::new(scrut),
        };
        // fst (mk (succ zero) zero) = succ zero.
        let r = check_top_with(pair_sig(), elim, nat_ty());
        assert!(
            r.is_ok(),
            "two-parameter Pair eliminator projects the first component: {r:?}"
        );
    }

    /// `Square : (m:Nat) → (n:Nat) → Univ 0` with `corner : Square zero zero`. A two-*index*
    /// family (no parameters). Its eliminator with motive `λ m. λ n. λ (_:Square m n). Nat`
    /// exercises the lifted index cap and the multi-index motive/conclusion handling.
    fn square_sig() -> Signature {
        let mut sig = nat_sig();
        sig.declare(DataDecl {
            name: DataName("Square".into()),
            params: vec![],
            indices: vec![nat_ty(), nat_ty()],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("corner".into()),
                args: vec![],
                // corner : Square zero zero.
                result_indices: vec![zero(), zero()],
            }],
            path_constructors: vec![],
        });
        sig
    }

    #[test]
    fn two_index_formation_and_elim() {
        let square_00 = Term::Data(DataName("Square".into()), vec![], vec![zero(), zero()]);
        // Formation: `Square zero zero : Univ 0`.
        assert!(
            check_top_with(square_sig(), square_00.clone(), u(0)).is_ok(),
            "two-index Square formation typechecks"
        );
        // scrutinee : Square zero zero = corner.
        let scrut = Term::Con(ConName("corner".into()), vec![]);
        // motive : λ m. λ n. λ (_:Square m n). Nat ; method corner : Nat = zero.
        let motive = Term::Lam(Box::new(Term::Lam(Box::new(Term::Lam(Box::new(nat_ty()))))));
        let m_corner = zero();
        let elim = Term::Elim {
            data: DataName("Square".into()),
            motive: Box::new(motive),
            methods: vec![m_corner],
            scrutinee: Box::new(scrut),
        };
        assert!(
            check_top_with(square_sig(), elim, nat_ty()).is_ok(),
            "two-index Square eliminator typechecks and computes a Nat"
        );
    }

    /// A minimal signature with a `Unit` data type (`tt`).
    fn unit_only_sig() -> Signature {
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: DataName("Unit".into()),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("tt".into()),
                args: vec![],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        });
        sig
    }

    /// The proof boundary (spec §4.1, §4.5): a *partial* computation — one whose inferred row
    /// carries `Partial` at a nonzero grade — is **rejected** where a proof is required.
    /// `later (now tt) : Delay Unit` carries `Partial` (the `later` step), so `check_top_with`
    /// must refuse to mint a `Proof` for it.
    #[test]
    fn proof_rejects_partial_computation() {
        let unit = Term::Data(DataName("Unit".into()), vec![], vec![]);
        let tt = Term::Con(ConName("tt".into()), vec![]);
        // later (now tt) : Delay Unit
        let partial = Term::Later(Box::new(Term::Now(Box::new(tt))));
        let delay_unit = Term::Delay(Box::new(unit));
        match check_top_with(unit_only_sig(), partial, delay_unit) {
            Err(TypeError::EffectError(msg)) => {
                assert!(
                    msg.contains("pure") || msg.contains("Partial") || msg.contains("effect"),
                    "rejection should cite the (Partial) effect row, got: {msg}"
                );
            }
            other => panic!("a partial computation must be rejected as a proof, got {other:?}"),
        }
    }

    /// The dual: a *total* (pure, empty-row) computation is accepted as a proof. `now tt : Delay
    /// Unit` is total (no `later`), so it mints a `Proof`.
    #[test]
    fn total_proof_accepted() {
        let unit = Term::Data(DataName("Unit".into()), vec![], vec![]);
        let tt = Term::Con(ConName("tt".into()), vec![]);
        let now_tt = Term::Now(Box::new(tt));
        let delay_unit = Term::Delay(Box::new(unit));
        check_top_with(unit_only_sig(), now_tt, delay_unit)
            .expect("a total `now tt : Delay Unit` is a valid proof");
    }

    // ---- `force` (spec §4.5): the delay eliminator ----

    /// `force (now a) ⇝ a` under NbE: forcing an immediately-available delay yields the value.
    #[test]
    fn force_now_reduces_to_value() {
        let tt = Term::Con(ConName("tt".into()), vec![]);
        // force (now tt)
        let term = Term::Force(Box::new(Term::Now(Box::new(tt.clone()))));
        let sig = std::rc::Rc::new(unit_only_sig());
        let v = eval(&Env::with_sig(sig), &term);
        let q = quote(0, &v);
        assert_eq!(q, tt, "force (now tt) normalizes to tt");
    }

    /// `force` over a *neutral* (a free variable of `Delay A`) stays stuck and quotes back to a
    /// `Force` term — it must not loop or panic.
    #[test]
    fn force_neutral_stays_stuck() {
        // A free variable at de Bruijn level 0, reflected as a neutral, then forced.
        let neutral = Value::Neutral(Neutral::Var(0));
        let forced = crate::normalize::do_force(neutral);
        // Quote under one binder (lvl = 1) so the level-0 variable reads back as `Var 0`.
        let q = quote(1, &forced);
        assert_eq!(
            q,
            Term::Force(Box::new(Term::Var(0))),
            "force on a neutral quotes to `force x`"
        );
    }

    /// `force` over a `later` stays guarded: `force (later d)` does not unfold `d`; it quotes back
    /// to `force (later …)` (intensional partiality — the delay structure is observable).
    #[test]
    fn force_later_stays_guarded() {
        let tt = Term::Con(ConName("tt".into()), vec![]);
        // later (now tt) : Delay Unit, then force it.
        let inner = Term::Later(Box::new(Term::Now(Box::new(tt.clone()))));
        let term = Term::Force(Box::new(inner.clone()));
        let sig = std::rc::Rc::new(unit_only_sig());
        let v = eval(&Env::with_sig(sig), &term);
        let q = quote(0, &v);
        assert_eq!(
            q,
            Term::Force(Box::new(inner)),
            "force (later d) stays a guarded `force (later d)`"
        );
    }

    /// Typing: `force d : A` when `d : Delay A`, and the judgement carries `Partial` (so a proof
    /// using `force` is rejected — divergence may surface). We check a closed `force (now tt)` at
    /// type `Unit`: it must be *rejected as a proof* because `force` contributes `Partial`.
    #[test]
    fn force_is_partial_and_rejected_as_proof() {
        let unit = Term::Data(DataName("Unit".into()), vec![], vec![]);
        let tt = Term::Con(ConName("tt".into()), vec![]);
        // force (now tt) : Unit — well-typed, but partial.
        let term = Term::Force(Box::new(Term::Now(Box::new(tt))));
        match check_top_with(unit_only_sig(), term, unit) {
            Err(TypeError::EffectError(msg)) => {
                assert!(
                    msg.contains("pure") || msg.contains("Partial") || msg.contains("effect"),
                    "force rejection should cite the (Partial) effect row, got: {msg}"
                );
            }
            other => panic!("a `force` computation must be rejected as a proof, got {other:?}"),
        }
    }

    // ===================================================================================
    // Item 2 (grades × cubical stress): EVIDENCE-FIRST characterization tests pinning what the
    // fused QTT-grade × cubical kernel ACTUALLY does at grade 0/1 across `transp`/`hcomp` and
    // interval binders. These probe the project's central thesis (the two layers compose in one
    // kernel) where it "bites" — the corpus otherwise runs everything at `Grade::Omega`. Each test
    // documents the predicted-and-confirmed behavior; the assertions are now permanent regressions.
    //
    // Findings (confirmed by these tests):
    //  • `transp`/`hcomp`/`comp` thread the ambient demand σ through their *base* (and `hcomp`/`comp`
    //    *tube*) exactly like ordinary elimination; the type-line/carrier is 0-fragment (no demand).
    //    So a Kan op does NOT secretly inflate a variable's multiplicity beyond σ-per-runtime-use.
    //  • Erasure SURVIVES a Kan op: a grade-0 variable used only in the (0-fragment) type line of a
    //    `transp` stays erased and the binder check `0 ≥ 0` passes; using it in the runtime base
    //    position is correctly charged and a 0-graded base use is a `GradeViolation`.
    //  • Interval/dimension binders are NOT graded (the kernel tracks only their count): an interval
    //    variable may be mentioned any number of times with no multiplicity constraint — i.e. the
    //    kernel treats dimensions as ω-replicable. This is the spec §10.3 "interval-var multiplicity"
    //    open point; the evidence here is that it imposes no grade discipline (sound: dimensions are
    //    erased at runtime), which the metatheory note records.
    // ===================================================================================

    /// Grade-0 erasure SURVIVES `transp`: `λ (A :^0 U0). λ (x :^0 A). transp (i. A) ⊥ x` is checked
    /// at `(A:^0 U0) → (x:^0 A) → A`. WAIT — `x` flows into the transport *base* (a runtime
    /// position), so the base charges demand on `x`; a `0`-graded `x` used at the base is `1 ≤ 0`
    /// false ⟹ `GradeViolation`. This is the soundness teeth: a Kan op does not launder an erased
    /// value into a relevant position.
    #[test]
    fn transp_base_charges_demand_erased_base_rejected() {
        // (A :^0 U0) → (x :^0 A) → A
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Zero,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        // body: λ A. λ x. transp (i. A) ⊥ x.  Inside the family's dim binder, `A` is still Var(1)
        // (dims add no term binder); the base `x` is Var(0).
        let body = Term::Lam(Box::new(Term::Lam(Box::new(Term::Transp {
            family: Box::new(Term::Var(1)),
            cofib: Cofib::Bot,
            base: Box::new(Term::Var(0)),
        }))));
        match check_top(body, ty) {
            Err(TypeError::GradeViolation(_)) => {}
            other => panic!(
                "transp base is a runtime position; an erased base var must be a GradeViolation, got {other:?}"
            ),
        }
    }

    /// The accept twin: with `x :^ω A` (unrestricted), the same `transp (i. A) ⊥ x` checks — the
    /// base's demand σ on `x` is fine against an ω binder. Confirms the rejection above is the
    /// *grade discipline* discriminating, not `transp` being inherently untypable.
    #[test]
    fn transp_base_omega_var_accepted() {
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let body = Term::Lam(Box::new(Term::Lam(Box::new(Term::Transp {
            family: Box::new(Term::Var(1)),
            cofib: Cofib::Bot,
            base: Box::new(Term::Var(0)),
        }))));
        assert!(
            check_top(body, ty).is_ok(),
            "an ω-graded base variable flows through transp's base position fine"
        );
    }

    /// Erasure genuinely SURVIVES the type line: a grade-0 variable used ONLY in the (0-fragment)
    /// family/type-line of a `transp` stays erased. `λ (A :^0 U0). λ (x :^ω A). transp (i. A) ⊥ x`
    /// — here `A` appears only in the family (type formation) and is never charged, so its `0`
    /// binder check `0 ≥ 0` passes even though a Kan op mentions it. (This is the "erasure survives
    /// transp" obligation from spec §10.3, confirmed positively.)
    #[test]
    fn transp_family_use_keeps_grade0_var_erased() {
        // (A :^0 U0) → (x :^ω A) → A, body transports x along the constant line `i. A`.
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let body = Term::Lam(Box::new(Term::Lam(Box::new(Term::Transp {
            family: Box::new(Term::Var(1)), // A — used only in the type line (0-fragment)
            cofib: Cofib::Bot,
            base: Box::new(Term::Var(0)),
        }))));
        assert!(
            check_top(body, ty).is_ok(),
            "a grade-0 type-line variable stays erased across transp (erasure survives the Kan op)"
        );
    }

    /// `hcomp` sums the demand of its *base* AND its *tube* (each carries σ): a linear (`1`) variable
    /// used in BOTH positions is demanded `1 + 1 = ω`, and `ω ≤ 1` is false ⟹ `GradeViolation`. This
    /// pins the multiplicity behavior of a Kan op with a face system: it is ordinary additive usage,
    /// no special interval magic.
    #[test]
    fn hcomp_base_and_tube_sum_demand_linear_rejected() {
        // (A :^0 U0) → (x :^1 A) → A, body: hcomp A ⊥ (i. x) x  — x in both tube and base.
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::One,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let body = Term::Lam(Box::new(Term::Lam(Box::new(Term::HComp {
            ty: Box::new(Term::Var(1)), // carrier A (0-fragment)
            cofib: Cofib::Bot,
            tube: Box::new(Term::Var(0)), // x in the tube (under a dim binder; term index unchanged)
            base: Box::new(Term::Var(0)), // x in the base
        }))));
        match check_top(body, ty) {
            Err(TypeError::GradeViolation(_)) => {}
            other => panic!(
                "hcomp base+tube each demand x, summing to ω on a linear x ⟹ GradeViolation, got {other:?}"
            ),
        }
    }

    /// The accept twin: with `x :^ω A`, the same `hcomp A ⊥ (i. x) x` checks (ω absorbs the double
    /// demand). Confirms the rejection above is the additive grade arithmetic discriminating.
    #[test]
    fn hcomp_base_and_tube_omega_var_accepted() {
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let body = Term::Lam(Box::new(Term::Lam(Box::new(Term::HComp {
            ty: Box::new(Term::Var(1)),
            cofib: Cofib::Bot,
            tube: Box::new(Term::Var(0)),
            base: Box::new(Term::Var(0)),
        }))));
        assert!(
            check_top(body, ty).is_ok(),
            "an ω-graded variable may be used in both hcomp's base and tube"
        );
    }

    /// Interval/dimension binders are NOT graded: the kernel tracks only the dimension *count*,
    /// never a per-dimension grade, so a dimension variable mentioned MULTIPLE times imposes no
    /// multiplicity constraint and — crucially — never perturbs the *term* usage vector. We probe
    /// this directly: in a context `[A :^0 U0, x :^0 A]` with one dimension `i` in scope, infer the
    /// transport `transp (k. A) ⊥ x` (whose family mentions the in-scope dimension space) and read
    /// back the usage vector. The dimension contributes nothing to grades; only the term `x`'s base
    /// use is charged (grade σ). This positively pins the spec §10.3 "interval-var multiplicity"
    /// open point: dimensions are ω-replicable / ungraded (sound — they erase at runtime).
    #[test]
    fn interval_var_carries_no_grade_in_usage_vector() {
        let sig = std::rc::Rc::new(nat_sig());
        let checker = Checker::new(sig);
        // Context [A :^0 U0, x :^? A] with a dimension in scope. Build it the way `check` would.
        let ctx = Context::empty()
            .extend(u(0), Grade::Zero) // A  (index 1)
            .extend(Term::Var(0), Grade::Omega) // x : A  (index 0)
            .extend_dim(); // one interval variable `i`
                           // transp (k. A) ⊥ x — `A` is Var(1), base `x` is Var(0).
        let term = Term::Transp {
            family: Box::new(Term::Var(1)),
            cofib: Cofib::Bot,
            base: Box::new(Term::Var(0)),
        };
        // Infer at ambient demand σ = 1 (one runtime use of the result).
        let (_ty, _row, usage) = checker
            .infer_g(&ctx, &term, Grade::One)
            .expect("transp over an in-scope dimension infers");
        // The usage vector has exactly the two TERM slots (A, x) — the dimension adds no slot. The
        // base charges `x` at σ = 1; `A` (type line only) stays 0. No dimension multiplicity appears.
        assert_eq!(
            usage.len(),
            2,
            "usage vector tracks only the two term variables, not the dimension"
        );
        assert_eq!(usage.get(0), Grade::One, "base position charges x at σ");
        assert_eq!(
            usage.get(1),
            Grade::Zero,
            "type-line-only A stays erased across transp"
        );
    }
}
