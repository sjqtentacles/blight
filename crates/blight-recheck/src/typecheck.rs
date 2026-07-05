//! The independent bidirectional checker over values: `infer`/`check` with the kernel's
//! grade-usage discipline, but a wholly separate implementation built on this crate's value-based
//! NbE. Free variables are reflected against their types so η and path boundaries fire correctly.

use crate::conv::{conv, fresh_var, kan_line_grade_skeleton_eq, subtype};
use crate::normalize::{apply, eval, quote};
use crate::term::{RGrade, RInterval, RRow, RTerm};
use crate::value::{Env, Neutral, RValue};
use crate::RecheckError;
use blight_kernel::signature::{Arg, Constructor, DataDecl, Signature};
use blight_kernel::DataName;
use std::rc::Rc;

type RResult<T> = Result<T, RecheckError>;

fn reject(msg: impl Into<String>) -> RecheckError {
    RecheckError::Rejected(msg.into())
}

/// The built-in `Partial` effect label (spec §4.5): a `later`/`force` contributes it, marking the
/// computation as possibly-divergent. Its own independent copy of the kernel's reserved label.
fn partial_label() -> blight_kernel::EffName {
    blight_kernel::EffName::partial()
}

/// An *honest refusal*: the judgement uses a construct outside the supported core fragment (or one
/// whose type the re-checker cannot synthesize without an annotation — the kernel's `CannotInfer`),
/// so the re-checker neither accepts nor (unsoundly) rejects it. The build treats this as "not
/// re-checked" rather than a soundness alarm. Declining is always sound: it abstains, never certifies.
fn decline(msg: impl Into<String>) -> RecheckError {
    RecheckError::Declined(msg.into())
}

/// Does this value's neutral spine bottom out at an *un-run effect operation* — a stuck `perform`
/// (`Op`) or `handle` (`Handle`)? The re-checker deliberately does not run effect semantics
/// (`normalize.rs`), so such a value is stuck for good: no reduction available here will ever expose
/// its canonical form. A conversion *against* it is therefore undecidable in the re-checker, and the
/// only sound verdict is to **decline** (abstain) — never to `reject` a program the kernel accepted
/// (a false soundness alarm), and of course never to certify it. Declining here can only ever
/// downgrade a would-be rejection to abstention, so it cannot introduce a false `Ok`. Follows the
/// neutral spine (application, projection, path-application, eliminator, force); a `Var` or `IntPrim`
/// head is ordinary neutrality, not an effect, so it does not trigger abstention.
fn is_stuck_on_effect(v: &RValue) -> bool {
    fn spine(n: &Neutral) -> bool {
        match n {
            Neutral::Op { .. } | Neutral::Handle { .. } => true,
            Neutral::App(h, _)
            | Neutral::Fst(h)
            | Neutral::Snd(h)
            | Neutral::PApp(h, _)
            | Neutral::Force(h) => spine(h),
            Neutral::Elim { scrutinee, .. } => spine(scrutinee),
            // An `if-zero` stuck on a neutral scrutinee is not itself effect-stuck (the Int fragment
            // does not bubble effects — same stance as `IntPrim`).
            Neutral::Var(_) | Neutral::IntPrim { .. } | Neutral::IfZero { .. } => false,
        }
    }
    matches!(v, RValue::Neutral(n) if spine(n))
}

/// A usage vector: demand on each in-scope variable (index 0 = innermost).
#[derive(Debug, Clone)]
struct Usage(Vec<RGrade>);

impl Usage {
    fn zero(n: usize) -> Self {
        Usage(vec![RGrade::Zero; n])
    }
    fn unit(i: usize, n: usize, sigma: RGrade) -> Self {
        let mut v = vec![RGrade::Zero; n];
        if i < n {
            v[i] = sigma;
        }
        Usage(v)
    }
    fn add(&self, other: &Usage) -> Usage {
        Usage(
            self.0
                .iter()
                .zip(&other.0)
                .map(|(a, b)| a.add(*b))
                .collect(),
        )
    }
    fn pop(&self) -> (RGrade, Usage) {
        let mut v = self.0.clone();
        let head = if v.is_empty() {
            RGrade::Zero
        } else {
            v.remove(0)
        };
        (head, Usage(v))
    }
    /// Keep only the demand on the innermost-... outermost `n` ambient variables, dropping the
    /// leading entries that correspond to locally-introduced (method) binders.
    fn truncate(&self, n: usize) -> Usage {
        let len = self.0.len();
        if n >= len {
            Usage(self.0.clone())
        } else {
            Usage(self.0[len - n..].to_vec())
        }
    }
}

/// One term-binder context entry: its *type as a value*, and the binder grade.
#[derive(Debug, Clone)]
struct Entry {
    ty: RValue,
    #[allow(dead_code)]
    grade: RGrade,
}

/// The typing context: a list of term entries (index 0 = innermost), the evaluation environment
/// that binds each as a reflected fresh variable, and dimension counters.
#[derive(Clone)]
struct Ctx {
    entries: Vec<Entry>, // innermost-first
    env: Env,            // value environment (term + dim bindings)
    lvl: usize,          // number of term binders (de Bruijn level depth)
    dlvl: usize,         // number of dimension binders
    /// Number of prenex universe-level variables in scope (T2.3): `RLevel::Var(u)` is well-formed
    /// iff `u < ulvl`. Constant through a derivation (the prenex design has no level binder inside
    /// a term), set once at the door from the `n_levels` the leveled entry is *told* — the
    /// re-checker never re-derives it from the term (scanning for the max `Var` would make the
    /// well-formedness gate vacuous).
    ulvl: usize,
}

impl Ctx {
    /// The plain empty context (no prenex level variables) — `leveled(0)`.
    #[cfg(test)]
    fn empty() -> Self {
        Ctx::leveled(0)
    }

    /// The empty context under `n_levels` prenex universe-level variables (T2.3); `leveled(0)` is
    /// the plain empty context.
    fn leveled(n_levels: usize) -> Self {
        Ctx {
            entries: Vec::new(),
            env: Env::new(),
            lvl: 0,
            dlvl: 0,
            ulvl: n_levels,
        }
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    /// Extend with a term binder of value-type `ty` at grade `g`, binding it in the environment as
    /// a reflected fresh variable at the current level.
    fn extend(&self, sig: &Signature, ty: RValue, g: RGrade) -> Ctx {
        let fresh = fresh_var(sig, self.lvl, &ty);
        let mut entries = self.entries.clone();
        entries.insert(0, Entry { ty, grade: g });
        Ctx {
            entries,
            env: self.env.extend(fresh),
            lvl: self.lvl + 1,
            dlvl: self.dlvl,
            ulvl: self.ulvl,
        }
    }

    /// Extend with a term binder whose environment value is `val` (rather than a fresh variable):
    /// used by dependent pattern matching to bind a constructor argument that unification has
    /// *forced* to a specific value, while still recording the binder's declared type.
    fn extend_with(&self, _sig: &Signature, ty: RValue, g: RGrade, val: RValue) -> Ctx {
        let mut entries = self.entries.clone();
        entries.insert(0, Entry { ty, grade: g });
        Ctx {
            entries,
            env: self.env.extend(val),
            lvl: self.lvl + 1,
            dlvl: self.dlvl,
            ulvl: self.ulvl,
        }
    }

    /// Extend with a dimension binder, binding a fresh dimension level in the environment.
    fn extend_dim(&self) -> Ctx {
        Ctx {
            entries: self.entries.clone(),
            env: self.env.extend_dim(RInterval::Dim(self.dlvl)),
            lvl: self.lvl,
            dlvl: self.dlvl + 1,
            ulvl: self.ulvl,
        }
    }

    fn lookup(&self, i: usize) -> Option<RValue> {
        self.entries.get(i).map(|e| e.ty.clone())
    }

    /// Apply per-branch ambient index specializations `(level, value)`: rebind those levels in the
    /// environment so subsequent evaluation sees the refined indices (dependent pattern matching).
    fn refine_ambient(&self, ambient: &[(usize, RValue)]) -> Ctx {
        let mut c = self.clone();
        for (lvl, v) in ambient {
            c.env = c.env.set_level(*lvl, v.clone());
        }
        c
    }
}

/// The re-checker over a fixed signature.
pub struct Recheck<'a> {
    sig: &'a Signature,
}

impl<'a> Recheck<'a> {
    pub fn new(sig: &'a Signature) -> Self {
        Recheck { sig }
    }

    /// Top-level re-check: `term : ty` in the empty context, demanded once, independently
    /// re-deriving the effect row + grade discipline along the way (continuation multiplicities,
    /// `Op`/`later`/`force` labels, handler discharge).
    ///
    /// `require_pure` selects which of the kernel's two top-level disciplines to re-derive:
    /// * `false` — the general *typing* judgement door (the kernel's `Checker`, used for buildable
    ///   programs): a definition may legitimately be **partial or effectful** (e.g. a `define-rec`
    ///   whose `later`-guarded body carries `Partial`, like `ackermann`), so any top-level row is
    ///   accepted. The row discipline is still re-derived (so a handler over-resuming its
    ///   continuation is Rejected), it just is not required to be empty. This is what
    ///   [`crate::recheck_judgement`] uses.
    /// * `true` — the *proof* door, mirroring [`blight_kernel::check_top_with`] (spec §4.1, §4.5):
    ///   a complete proof must additionally be **pure and total** — its independently inferred
    ///   effect row must be *empty* (in particular `Partial` at grade 0). A proof can only ever be
    ///   minted by the kernel after this check, so re-deriving it is the second opinion on the
    ///   purity invariant. This is what [`crate::recheck_proof`] uses.
    ///
    /// (Retained for the crate's white-box tests; the public doors now route through
    /// [`Self::check_top_leveled`], of which this is the `n_levels == 0` case.)
    #[cfg(test)]
    pub fn check_top(&self, term: &RTerm, ty: &RTerm, require_pure: bool) -> RResult<()> {
        self.check_top_leveled(term, ty, require_pure, 0)
    }

    /// Like [`Self::check_top`], but under `n_levels` prenex universe-level variables (T2.3) — the
    /// re-checker's twin of the kernel's `check_top_leveled` door. The declared type is re-formed
    /// first (so a `Univ (Var u)` with `u ≥ n_levels` is Rejected here, at formation), then the
    /// term is checked against it, all under the told level count. `n_levels == 0` is exactly
    /// [`Self::check_top`], so the closed fragment is unchanged.
    pub fn check_top_leveled(
        &self,
        term: &RTerm,
        ty: &RTerm,
        require_pure: bool,
        n_levels: usize,
    ) -> RResult<()> {
        let ctx = Ctx::leveled(n_levels);
        self.infer_universe(&ctx, ty)?;
        let ty_val = eval(self.sig, &ctx.env, ty);
        let (row, _u) = self.check(&ctx, term, &ty_val, RGrade::One)?;
        if require_pure && !row.is_empty() {
            return Err(reject(format!(
                "a top-level proof must be pure (empty effect row), but it independently \
                 re-derives effects: {row:?}"
            )));
        }
        Ok(())
    }

    /// Infer the (value) type of `term`, its independently-derived effect [`RRow`], and its usage
    /// vector, at ambient demand `sigma`. Pure terms infer the empty row; `Op` contributes its
    /// effect's label; `later`/`force` contribute `Partial`; eliminators/applications union their
    /// subterms' rows — mirroring the kernel's `infer_g` exactly (`check.rs`).
    fn infer(&self, ctx: &Ctx, term: &RTerm, sigma: RGrade) -> RResult<(RValue, RRow, Usage)> {
        let n = ctx.len();
        match term {
            RTerm::Var(i) => {
                let ty = ctx
                    .lookup(*i)
                    .ok_or_else(|| reject(format!("unbound de Bruijn index {i}")))?;
                Ok((ty, RRow::empty(), Usage::unit(*i, n, sigma)))
            }
            // `Univ ℓ : Univ (suc ℓ)` — symbolic formation (T2.3), after the level well-formedness
            // gate: `Var(u)` is valid iff `u < ulvl`, the prenex count this judgement was checked
            // under. This is the re-checker's own `level_wf` — the only user-supplied level is the
            // one `Univ` carries, so gating it here closes the door on out-of-scope universes.
            RTerm::Univ(l) => {
                if !crate::term::rlevel_wf(l, ctx.ulvl) {
                    return Err(reject(format!(
                        "universe level {l:?} mentions a level variable out of scope \
                         (n_levels = {})",
                        ctx.ulvl
                    )));
                }
                Ok((
                    RValue::Univ(crate::term::rlevel_suc(l)),
                    RRow::empty(),
                    Usage::zero(n),
                ))
            }
            RTerm::Pi(grade, dom, cod) => {
                let dl = self.infer_universe(ctx, dom)?;
                let dom_v = eval(self.sig, &ctx.env, dom);
                let ctx2 = ctx.extend(self.sig, dom_v, *grade);
                let cl = self.infer_universe(&ctx2, cod)?;
                Ok((
                    RValue::Univ(crate::term::rlevel_max(&dl, &cl)),
                    RRow::empty(),
                    Usage::zero(n),
                ))
            }
            RTerm::Sigma(dom, cod) => {
                let dl = self.infer_universe(ctx, dom)?;
                let dom_v = eval(self.sig, &ctx.env, dom);
                let ctx2 = ctx.extend(self.sig, dom_v, RGrade::Omega);
                let cl = self.infer_universe(&ctx2, cod)?;
                Ok((
                    RValue::Univ(crate::term::rlevel_max(&dl, &cl)),
                    RRow::empty(),
                    Usage::zero(n),
                ))
            }
            // App: the result row is the union of the function's and argument's rows (spec §4.1).
            RTerm::App(f, a) => {
                let (f_ty, row_f, usage_f) = self.infer(ctx, f, sigma)?;
                match f_ty {
                    RValue::Pi(rho, dom, cod) => {
                        let (row_a, usage_a) = self.check(ctx, a, &dom, sigma.mul(rho))?;
                        let a_val = eval(self.sig, &ctx.env, a);
                        let result = cod.apply(self.sig, a_val);
                        Ok((result, row_f.union(&row_a), usage_f.add(&usage_a)))
                    }
                    other => Err(reject(format!("applied a non-function of type {other:?}"))),
                }
            }
            // Projections pass the pair's row and usage through unchanged.
            RTerm::Fst(p) => {
                let (p_ty, row, usage) = self.infer(ctx, p, sigma)?;
                match p_ty {
                    RValue::Sigma(dom, _cod) => Ok((crate::value::unshare_rvalue(dom), row, usage)),
                    other => Err(reject(format!("Fst of a non-pair of type {other:?}"))),
                }
            }
            RTerm::Snd(p) => {
                let (p_ty, row, usage) = self.infer(ctx, p, sigma)?;
                match p_ty {
                    RValue::Sigma(_dom, cod) => {
                        let p_val = eval(self.sig, &ctx.env, p);
                        let fst = crate::normalize::vfst(p_val);
                        Ok((cod.apply(self.sig, fst), row, usage))
                    }
                    other => Err(reject(format!("Snd of a non-pair of type {other:?}"))),
                }
            }
            RTerm::Ann(t, ty) => {
                self.infer_universe(ctx, ty)?;
                let ty_v = eval(self.sig, &ctx.env, ty);
                let (row, usage) = self.check(ctx, t, &ty_v, sigma)?;
                Ok((ty_v, row, usage))
            }
            RTerm::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => self.infer_elim(ctx, data, motive, methods, scrutinee, sigma),
            RTerm::PApp(p, r) => {
                let (p_ty, row, usage) = self.infer(ctx, p, sigma)?;
                match p_ty {
                    RValue::PathP { family, .. } => {
                        let r_v = crate::normalize::eval_interval(&ctx.env, r);
                        Ok((family.apply_dim(self.sig, r_v), row, usage))
                    }
                    other => Err(reject(format!("path-applied a non-path of type {other:?}"))),
                }
            }
            // A type former: pure (empty row). Endpoints are checked in the 0-fragment.
            RTerm::PathP { family, lhs, rhs } => {
                let ctx_dim = ctx.extend_dim();
                let l = self.infer_universe(&ctx_dim, family)?;
                // Endpoints inhabit the family at 0 and 1.
                let fam0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, family)
                };
                let fam1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, family)
                };
                self.check(ctx, lhs, &fam0, RGrade::Zero)?;
                self.check(ctx, rhs, &fam1, RGrade::Zero)?;
                Ok((RValue::Univ(l), RRow::empty(), Usage::zero(n)))
            }
            RTerm::Data(name, ps, is) => {
                let decl = self
                    .sig
                    .get(name)
                    .ok_or_else(|| reject(format!("unknown inductive type {name:?}")))?
                    .clone();
                // Arity + 0-fragment type checking of parameters and indices, mirroring the kernel's
                // `Term::Data` rule (`kernel/check.rs`). Previously ignored (`_ps`/`_is`), so recheck
                // returned `Ok` on a malformed `Data` the kernel rejects (soundness audit
                // 2026-07-03, R-P2). Declared param/index types form a telescope (de Bruijn over the
                // preceding params, then indices), so each is evaluated against the accumulated
                // supplied values — the same pattern as `check_con`.
                if ps.len() != decl.params.len() || is.len() != decl.indices.len() {
                    return Err(reject(format!(
                        "{name:?} expects {} param(s) and {} index(es), got {} and {}",
                        decl.params.len(),
                        decl.indices.len(),
                        ps.len(),
                        is.len()
                    )));
                }
                let mut tele = Env::new();
                for (p, pty_kt) in ps.iter().zip(decl.params.iter()) {
                    let pty_rt = crate::term::from_kernel(pty_kt)?;
                    let pty_val = eval(self.sig, &tele, &pty_rt);
                    self.check(ctx, p, &pty_val, RGrade::Zero)?;
                    tele = tele.extend(eval(self.sig, &ctx.env, p));
                }
                for (ix, ixty_kt) in is.iter().zip(decl.indices.iter()) {
                    let ixty_rt = crate::term::from_kernel(ixty_kt)?;
                    let ixty_val = eval(self.sig, &tele, &ixty_rt);
                    self.check(ctx, ix, &ixty_val, RGrade::Zero)?;
                    tele = tele.extend(eval(self.sig, &ctx.env, ix));
                }
                Ok((
                    RValue::Univ(crate::term::rlevel_of_nat(decl.level)),
                    RRow::empty(),
                    Usage::zero(n),
                ))
            }
            RTerm::Con(name, args) => self.infer_con(ctx, name, args, sigma),
            // A bare introduction form (λ / pair / path-λ) in *inference* position has no synthesizable
            // type — exactly the kernel's `CannotInfer`. This is a fragment limitation, not a type
            // error: the re-checker *declines* (abstains) rather than (unsoundly) rejecting a
            // kernel-valid program. Such redexes arise in compiled `define-rec` eliminator forms whose
            // motive/methods the re-checker reaches in inference position.
            RTerm::Lam(_) | RTerm::Pair(_, _) | RTerm::PLam(_) => Err(decline(format!(
                "introduction form needs a type annotation to be inferred: {term:?}"
            ))),
            RTerm::Interval(_) => Err(reject("a bare interval has no type in the term layer")),

            // Cubical Kan operations: re-derive the result type independently (the kernel already
            // checked the inputs; we re-evaluate the family/endpoints to read off the conclusion).
            // `Transp (i.A) φ a0 : A i1`; `HComp A φ u a0 : A`; `Comp (i.A) φ u a0 : A i1`.
            // The base inhabits the *source* type (`A i0` for transp/comp, `A` for hcomp), so we
            // **check** it there (it may be a bare constructor needing the expected type) and read
            // the conclusion off the *target* (`A i1` / `A`). The base's row passes through.
            RTerm::Transp { family, base, .. } => {
                let ctx_dim = ctx.extend_dim();
                self.infer_universe(&ctx_dim, family)?;
                let ty_at_0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, family)
                };
                let (b_row, b_usage) = self.check(ctx, base, &ty_at_0, sigma)?;
                let ty_at_1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, family)
                };
                self.reject_heterogeneous_grade_line(ctx, &ty_at_0, &ty_at_1)?;
                Ok((ty_at_1, b_row, b_usage))
            }
            RTerm::HComp { ty, base, .. } => {
                self.infer_universe(ctx, ty)?;
                let ty_val = eval(self.sig, &ctx.env, ty);
                let (b_row, b_usage) = self.check(ctx, base, &ty_val, sigma)?;
                Ok((ty_val, b_row, b_usage))
            }
            RTerm::Comp { family, base, .. } => {
                let ctx_dim = ctx.extend_dim();
                self.infer_universe(&ctx_dim, family)?;
                let ty_at_0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, family)
                };
                let (b_row, b_usage) = self.check(ctx, base, &ty_at_0, sigma)?;
                let ty_at_1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, family)
                };
                self.reject_heterogeneous_grade_line(ctx, &ty_at_0, &ty_at_1)?;
                Ok((ty_at_1, b_row, b_usage))
            }

            // Partiality (spec §4.5), modeled independently. `Delay A : Univ ℓ` is a pure type
            // former. `now a` is *total* (the row of `a`). `later`/`force` **may diverge**, so each
            // contributes the built-in `Partial` label at the ambient demand — exactly the nonzero
            // partiality grade the top-level purity check rejects in a proof.
            RTerm::Delay(a) => {
                let l = self.infer_universe(ctx, a)?;
                Ok((RValue::Univ(l), RRow::empty(), Usage::zero(n)))
            }
            // `now a : Delay A` where `A` is the inferred type of `a` (row = `a`'s row).
            RTerm::Now(a) => {
                let (a_ty, row, usage) = self.infer(ctx, a, sigma)?;
                Ok((RValue::Delay(Rc::new(a_ty)), row, usage))
            }
            // `later d : Delay A` where `d : Delay A` (the inferred type of `d` is already a Delay).
            RTerm::Later(d) => {
                let (d_ty, d_row, usage) = self.infer(ctx, d, sigma)?;
                match d_ty {
                    RValue::Delay(_) => {
                        let row = d_row.union(&RRow::single(partial_label(), sigma));
                        Ok((d_ty, row, usage))
                    }
                    other => Err(reject(format!("`later` of a non-Delay of type {other:?}"))),
                }
            }
            // `force d : A` when `d : Delay A`.
            RTerm::Force(d) => {
                let (d_ty, d_row, usage) = self.infer(ctx, d, sigma)?;
                match d_ty {
                    RValue::Delay(inner) => {
                        let row = d_row.union(&RRow::single(partial_label(), sigma));
                        Ok((crate::value::unshare_rvalue(inner), row, usage))
                    }
                    other => Err(reject(format!("`force` of a non-Delay of type {other:?}"))),
                }
            }

            // Effects and handlers (spec §4). `! E A : Univ ℓ` is a pure type former (the row `E` is
            // part of the *type*, not the formation's effect). `perform op a` contributes its
            // effect's label at the ambient demand. `handle` discharges the labels it interprets.
            RTerm::EffTy(a) => {
                let l = self.infer_universe(ctx, a)?;
                Ok((RValue::Univ(l), RRow::empty(), Usage::zero(n)))
            }
            // `perform op a`: look up the op; check `a` against `param_ty`; the type is
            // `result_ty[a/x]`; the row is `a`'s row unioned with `{effect : σ}`.
            //
            // Wave 7/E2 (parameterized effects, lockstep with `check.rs`'s kernel rule): a
            // parameterized effect's `perform` site supplies one type argument per entry in the
            // effect's declared telescope, each independently re-checked in the 0-fragment against
            // its declared type — mirroring `RTerm::Data`'s own parameters. `param_ty`/`result_ty`
            // are terms over `[effect params…, x:A]`; we thread the instantiated type-argument
            // values into the evaluation env before the parameter/result type, exactly as the
            // kernel does. Empty `type_args` (a non-parameterized effect) makes this identical to
            // the pre-E2 behavior.
            RTerm::Op {
                effect,
                op,
                type_args,
                arg,
            } => {
                let (eff, opsig) = self
                    .sig
                    .op_of(op)
                    .ok_or_else(|| reject(format!("unknown operation {op:?}")))?;
                if &eff.name != effect {
                    return Err(reject(format!(
                        "operation {op:?} belongs to effect {:?}, not {effect:?}",
                        eff.name
                    )));
                }
                if type_args.len() != eff.params.len() {
                    return Err(reject(format!(
                        "operation {op:?} of effect {:?} expects {} type argument(s), got {}",
                        eff.name,
                        eff.params.len(),
                        type_args.len()
                    )));
                }
                let mut penv = Env::new();
                let mut pvals: Vec<RValue> = Vec::with_capacity(type_args.len());
                for (ta, pty_term) in type_args.iter().zip(eff.params.iter()) {
                    let pty_rt = crate::term::from_kernel(pty_term)?;
                    let pty_val = eval(self.sig, &penv, &pty_rt);
                    self.check(ctx, ta, &pty_val, RGrade::Zero)?;
                    let ta_val = eval(self.sig, &ctx.env, ta);
                    penv = penv.extend(ta_val.clone());
                    pvals.push(ta_val);
                }
                // Translate and evaluate the op's parameter/result types in the env extended with
                // the instantiated type parameters.
                let param_rt = crate::term::from_kernel(&opsig.param_ty)?;
                let result_rt = crate::term::from_kernel(&opsig.result_ty)?;
                let param_val = eval(self.sig, &penv, &param_rt);
                let (row_a, usage) = self.check(ctx, arg, &param_val, sigma)?;
                // `result_ty` mentions the parameter as de Bruijn 0 (innermost, after the effect's
                // own params): evaluate it in an env that also binds the argument's value.
                let arg_val = eval(self.sig, &ctx.env, arg);
                let result_env = penv.extend(arg_val);
                let result_val = eval(self.sig, &result_env, &result_rt);
                let row = row_a.union(&RRow::single(effect.clone(), sigma));
                Ok((result_val, row, usage))
            }
            // `handle body { return x. r ; (op x k. e)... }`: infer body's type `A`; the return
            // clause binds `x:A` and infers the result type `C`; each op clause is checked against
            // `C` under `x:Aᵢ`, `k:Π(_:Bᵢ).C` at the operation's continuation multiplicity. The
            // Handle's type is `C`; the handled labels are discharged from the body's row.
            RTerm::Handle {
                body,
                return_clause,
                op_clauses,
            } => self.infer_handle(ctx, body, return_clause, op_clauses, None, sigma),

            // ---- primitive machine integers (M11): pure arithmetic ----
            RTerm::IntTy => Ok((
                RValue::Univ(crate::term::RLevel::Zero),
                RRow::empty(),
                Usage::zero(n),
            )),
            RTerm::IntLit(_) => Ok((RValue::IntTy, RRow::empty(), Usage::zero(n))),
            RTerm::IntPrim { lhs, rhs, .. } => {
                let (rl, ul) = self.check(ctx, lhs, &RValue::IntTy, sigma)?;
                let (rr, ur) = self.check(ctx, rhs, &RValue::IntTy, sigma)?;
                Ok((RValue::IntTy, rl.union(&rr), ul.add(&ur)))
            }
            // `if-zero` (T1a): scrutinee at `Int`; result type inferred from the then-branch and the
            // else-branch checked against it. Usage = sum of scrutinee + branches (so a linear var
            // spent in both branches is `1+1 = ω`, rejected), row = union — mirroring the kernel.
            RTerm::IfZero { scrut, then_, else_ } => {
                let (rs, us) = self.check(ctx, scrut, &RValue::IntTy, sigma)?;
                let (then_ty, rt, ut) = self.infer(ctx, then_, sigma)?;
                let (re, ue) = self.check(ctx, else_, &then_ty, sigma)?;
                Ok((
                    then_ty,
                    rs.union(&rt).union(&re),
                    us.add(&ut).add(&ue),
                ))
            }
        }
    }

    /// Infer a term that must be a type, returning its universe level. Type formation lives in the
    /// 0-fragment, so its effect row is discarded (it is empty by construction — every label is
    /// added at grade 0, the absent grade — matching the kernel's `infer_universe`).
    fn infer_universe(&self, ctx: &Ctx, ty: &RTerm) -> RResult<crate::term::RLevel> {
        let (k, _row, _u) = self.infer(ctx, ty, RGrade::Zero)?;
        match k {
            RValue::Univ(l) => Ok(l),
            other => Err(reject(format!(
                "expected a type (Univ ℓ) but found {other:?}"
            ))),
        }
    }

    /// Obligation 1.3.2 (`docs/metatheory.md` §1.3): independently re-derive the kernel's
    /// `Transp`/`Comp` grade-skeleton restriction. `a0`/`a1` are a Kan line's two endpoints; if
    /// they are not already definitionally equal (genuinely differing types are fine — that is the
    /// point of `transp`/`ua`), any `Pi`-formers occurring at corresponding positions must still
    /// agree in declared grade, or the checked base's usage discipline would be laundered across
    /// the line with no re-verification. See `kan_line_grade_skeleton_eq`'s doc comment and the
    /// kernel's identical `check.rs` restriction for the full soundness argument.
    fn reject_heterogeneous_grade_line(&self, ctx: &Ctx, a0: &RValue, a1: &RValue) -> RResult<()> {
        if !conv(self.sig, ctx.lvl, ctx.dlvl, a0, a1)
            && !kan_line_grade_skeleton_eq(self.sig, ctx.lvl, a0, a1)
        {
            return Err(reject(
                "a Kan line whose Pi-formers disagree in grade would launder the base's usage \
                 discipline (obligation 1.3.2, docs/metatheory.md §1.3)",
            ));
        }
        Ok(())
    }

    /// Re-derive a `handle`'s result type `C` and effect row (spec §4.3), an independent port of the
    /// kernel's `Handle` rule. Infer the body's type `A` and row `E_body`; bind `x:A` and infer the
    /// return clause's type `C`; for each op clause bind `x:Aᵢ` then `k:Π(_:Bᵢ).C` (at the
    /// operation's **continuation multiplicity** `cont_grade`) and check the clause body against `C`.
    /// The handled labels are *discharged* from `E_body`; the clauses' and return clause's own rows
    /// are unioned in. The Handle's type is `C`. **B2: the continuation grade is now enforced** —
    /// resuming `k` at a grade exceeding `cont_grade` is Rejected, mirroring the kernel.
    fn infer_handle(
        &self,
        ctx: &Ctx,
        body: &RTerm,
        return_clause: &RTerm,
        op_clauses: &[(blight_kernel::signature::OpName, Box<RTerm>)],
        expected: Option<&RValue>,
        sigma: RGrade,
    ) -> RResult<(RValue, RRow, Usage)> {
        // 1. Infer the body's type `A` and row `E_body`.
        let (body_ty, body_row, body_usage) = self.infer(ctx, body, sigma)?;

        // 2. Return clause: bind `x : A`. In *check* mode (`expected` given) the handle's result
        // type `C` is already known, so check the return clause against it — this is what lets a
        // *parameterized*/state-passing handler (whose clauses are bare lambdas `λs. …`) re-check
        // instead of declining, exactly mirroring the kernel's check-mode `Handle` rule
        // (`check.rs`). In infer mode (`expected == None`) infer `C` from the return clause as before.
        let ctx_ret = ctx.extend(self.sig, body_ty, sigma);
        let (c_ty, ret_row, ret_usage) = match expected {
            Some(c) => {
                let (row, usage) = self.check(&ctx_ret, return_clause, c, sigma)?;
                ((*c).clone(), row, usage)
            }
            None => self.infer(&ctx_ret, return_clause, sigma)?,
        };
        // `C` must live at `ctx.len()` (it may not mention the bound `x`); quote it there and
        // re-evaluate in the ambient env so it is reusable under the op clauses' binders.
        let c_term = quote(self.sig, ctx.lvl, ctx.dlvl, &c_ty);
        let c_val = eval(self.sig, &ctx.env, &c_term);
        let (_demand_x, ret_usage) = ret_usage.pop();
        let mut total_usage = body_usage.add(&ret_usage);
        let mut result_row = ret_row;
        let mut handled: Vec<blight_kernel::EffName> = Vec::new();

        // 3. Operation clauses: each binds `x:Aᵢ` (the op parameter) then `k:Π(_:Bᵢ).C`.
        for (op, clause) in op_clauses.iter() {
            let (eff, opsig) = self
                .sig
                .op_of(op)
                .ok_or_else(|| reject(format!("handler clause for unknown operation {op:?}")))?;
            // Wave 7/E2 scope gate, lockstep with the kernel's identical restriction (see
            // `check.rs`'s `Handle` rule): handling an operation of a *parameterized* effect is an
            // intentionally unmodeled shape here, so it is rejected rather than mistyped against
            // the parameter-open signature.
            if !eff.params.is_empty() {
                return Err(reject(format!(
                    "handling operation {op:?} of the parameterized effect {:?} is not yet \
                     supported (Wave 7/E2 scope: perform + typecheck only)",
                    eff.name
                )));
            }
            handled.push(eff.name.clone());
            let param_rt = crate::term::from_kernel(&opsig.param_ty)?;
            let result_rt = crate::term::from_kernel(&opsig.result_ty)?;
            let cont_grade: RGrade = opsig.cont_grade.into();
            // `Aᵢ` is closed over the ambient context.
            let param_val = eval(self.sig, &Env::new(), &param_rt);
            let ctx_x = ctx.extend(self.sig, param_val, sigma);
            // `Bᵢ = result_ty[x]` lives in `x:Aᵢ`'s scope (de Bruijn 0 = x). Build the
            // continuation type `k : Π(_:Bᵢ). C` (where `C` is weakened past the `x` binder by 1,
            // becoming weakened by 2 inside the Pi's codomain), evaluate it in `ctx_x`'s env. The
            // binder grade is the operation's continuation multiplicity, so the usage discipline
            // (`demand(k) ≤ cont_grade`) is checked just like an ordinary λ-binder.
            let k_dom_val = eval(self.sig, &ctx_x.env, &result_rt);
            // The continuation's codomain ignores its own binder: it is `C` shifted past `x`+`_`.
            let cod_closure_body = shift_free(&c_term, 2);
            let k_ty = RValue::Pi(
                RGrade::Omega,
                Rc::new(k_dom_val),
                crate::value::Closure {
                    env: ctx_x.env.clone(),
                    body: std::rc::Rc::new(cod_closure_body),
                },
            );
            let ctx_xk = ctx_x.extend(self.sig, k_ty, cont_grade);
            // Check the clause body against `C` (under the two binders `x`, `k`). `C` is closed at
            // `ctx.len()`, so it is invariant under the extra binders when evaluated in `ctx`'s env.
            let c_val_xk = c_val.clone();
            let (clause_row, clause_usage) = self.check(&ctx_xk, clause, &c_val_xk, sigma)?;
            // Pop the two binders (`k` then `x`); enforce `k`'s continuation multiplicity grade.
            let (demand_k, clause_usage) = clause_usage.pop();
            if !demand_k.leq(cont_grade) {
                return Err(reject(format!(
                    "handler clause for {op:?} resumes its continuation at grade {demand_k:?}, but \
                     the operation's continuation multiplicity is {cont_grade:?}"
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

        Ok((c_val, result_row, total_usage))
    }

    /// Check `term` against expected value-type `expected` at ambient demand `sigma`, returning the
    /// independently-derived effect row and usage vector. A `λ`/path binder propagates its body's
    /// row (effects are *not* suspended by a binder in this calculus — the kernel's `check_g` returns
    /// `body_row` likewise); intro forms union their components' rows.
    fn check(
        &self,
        ctx: &Ctx,
        term: &RTerm,
        expected: &RValue,
        sigma: RGrade,
    ) -> RResult<(RRow, Usage)> {
        match (term, expected) {
            (RTerm::Lam(body), RValue::Pi(grade, dom, cod)) => {
                let ctx2 = ctx.extend(self.sig, (**dom).clone(), *grade);
                // The bound variable's value in the extended env is the fresh var at ctx.lvl.
                let fresh = fresh_var(self.sig, ctx.lvl, dom);
                let cod_inst = cod.apply(self.sig, fresh);
                let (body_row, body_usage) = self.check(&ctx2, body, &cod_inst, sigma)?;
                let (demand_x, rest) = body_usage.pop();
                if !demand_x.leq(*grade) {
                    return Err(reject(format!(
                        "λ-binder at grade {grade:?} but body demands it at {demand_x:?}"
                    )));
                }
                Ok((body_row, rest))
            }
            (RTerm::Pair(a, b), RValue::Sigma(dom, cod)) => {
                let (row_a, usage_a) = self.check(ctx, a, dom, sigma)?;
                let a_val = eval(self.sig, &ctx.env, a);
                let cod_inst = cod.apply(self.sig, a_val);
                let (row_b, usage_b) = self.check(ctx, b, &cod_inst, sigma)?;
                Ok((row_a.union(&row_b), usage_a.add(&usage_b)))
            }
            (RTerm::Con(name, args), RValue::Data(d_name, params, exp_indices)) => {
                self.check_con(ctx, name, args, d_name, params, exp_indices, sigma)
            }
            // `now a : Delay A` — check the payload against `A` (so a bare-constructor payload is
            // accepted, mirroring `Con`/`Pair` checking); `now` is *total* (row = `a`'s row).
            // `later d : Delay A` — check `d` against the same `Delay A`, then add the `Partial`
            // label at the ambient demand (a guarded step may diverge).
            (RTerm::Now(a), RValue::Delay(inner)) => self.check(ctx, a, inner, sigma),
            (RTerm::Later(d), RValue::Delay(_)) => {
                let (d_row, usage) = self.check(ctx, d, expected, sigma)?;
                Ok((d_row.union(&RRow::single(partial_label(), sigma)), usage))
            }
            (RTerm::PLam(body), RValue::PathP { family, lhs, rhs }) => {
                let ctx_dim = ctx.extend_dim();
                let fam_at_i = family.apply_dim(self.sig, RInterval::Dim(ctx.dlvl));
                let (body_row, body_usage) = self.check(&ctx_dim, body, &fam_at_i, sigma)?;
                // Boundary: body[0/i] ≡ lhs, body[1/i] ≡ rhs.
                let b0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, body)
                };
                let b1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, body)
                };
                if !conv(self.sig, ctx.lvl, ctx.dlvl, &b0, lhs) {
                    // If either side is stuck on an un-run effect handler, the re-checker cannot
                    // decide the boundary (it does not run effect semantics) — abstain, never reject.
                    if is_stuck_on_effect(&b0) || is_stuck_on_effect(lhs) {
                        return Err(decline(
                            "path lhs boundary depends on an un-run effect handler",
                        ));
                    }
                    return Err(reject("path lhs boundary mismatch"));
                }
                if !conv(self.sig, ctx.lvl, ctx.dlvl, &b1, rhs) {
                    if is_stuck_on_effect(&b1) || is_stuck_on_effect(rhs) {
                        return Err(decline(
                            "path rhs boundary depends on an un-run effect handler",
                        ));
                    }
                    return Err(reject("path rhs boundary mismatch"));
                }
                Ok((body_row, body_usage))
            }
            // Check-mode `handle`: the expected type *is* the result type `C` (mirrors the kernel's
            // check-mode `Handle`, `check.rs`), so the clauses — including a bare return-clause
            // lambda in a state-passing handler — are checked against it rather than inferred (which
            // would decline). Sound: this is the same rule the kernel uses; it discharges the body's
            // handled labels and enforces each clause's continuation-grade exactly as infer mode does.
            (
                RTerm::Handle {
                    body,
                    return_clause,
                    op_clauses,
                },
                _,
            ) => {
                let (_c, row, usage) = self.infer_handle(
                    ctx,
                    body,
                    return_clause,
                    op_clauses,
                    Some(expected),
                    sigma,
                )?;
                Ok((row, usage))
            }
            // `if-zero` in checking mode (T1a): check both branches against the *expected* type
            // directly, so a branch that needs it — e.g. the prelude's `int-eq?` branching to the
            // bare `Bool` constructors `true`/`false` — checks without an ascription. Mirrors the
            // kernel's `check_g` `IfZero` arm (usage = scrutinee + branch-sum, row = union).
            (RTerm::IfZero { scrut, then_, else_ }, _) => {
                let (rs, us) = self.check(ctx, scrut, &RValue::IntTy, sigma)?;
                let (rt, ut) = self.check(ctx, then_, expected, sigma)?;
                let (re, ue) = self.check(ctx, else_, expected, sigma)?;
                Ok((rs.union(&rt).union(&re), us.add(&ut).add(&ue)))
            }
            _ => {
                let (actual, row, usage) = self.infer(ctx, term, sigma)?;
                if subtype(self.sig, ctx.lvl, ctx.dlvl, &actual, expected) {
                    Ok((row, usage))
                } else {
                    Err(reject(format!(
                        "type mismatch: inferred {actual:?} but expected {expected:?}"
                    )))
                }
            }
        }
    }

    /// Infer the type of a *bare* constructor application `Con name args` (no ascription).
    ///
    /// This mirrors the kernel's [`Term::Con`] inference rule (`blight-kernel` `check.rs`): a
    /// constructor of a **non-parameterized** family is inferable — its arguments are checked
    /// against the constructor's argument shapes, and the family's result indices are recovered by
    /// evaluating the constructor's `result_indices` against the argument values. A constructor of
    /// a **parameterized** family is *not* inferable (the parameters cannot be recovered from the
    /// arguments alone), so it still needs an ascription — exactly the kernel's `CannotInfer` case.
    ///
    /// Having this rule keeps the two checkers **symmetric**: previously a bare-`Con` scrutinee of
    /// a non-parameterized family (e.g. `Bool`/`Nat`) — which the kernel infers fine inside `Elim`
    /// — was `Rejected` here, a spurious disagreement (caught by the C1 differential harness).
    fn infer_con(
        &self,
        ctx: &Ctx,
        name: &blight_kernel::ConName,
        args: &[RTerm],
        sigma: RGrade,
    ) -> RResult<(RValue, RRow, Usage)> {
        let (decl, _idx, ctor) = self
            .sig
            .data_of_con(name)
            .ok_or_else(|| reject(format!("unknown constructor {name:?}")))?;
        let decl = decl.clone();
        let ctor = ctor.clone();
        if !decl.params.is_empty() {
            // Parameterized: parameters are not recoverable from the arguments — needs an
            // ascription, just like the kernel's `CannotInfer`. A limitation, not a type error, so
            // we *decline* (abstain) rather than reject a kernel-valid program.
            return Err(decline(format!(
                "constructor {name:?} of a parameterized family needs a type annotation to be inferred"
            )));
        }
        if args.len() != ctor.args.len() {
            return Err(reject(format!(
                "constructor {name:?} expects {} args, got {}",
                ctor.args.len(),
                args.len()
            )));
        }
        // Non-parameterized family: recursive arguments share the (param-free) family head.
        let rec_ty = RValue::Data(decl.name.clone(), Rc::new(vec![]), Rc::new(vec![]));
        let mut usage = Usage::zero(ctx.len());
        let mut row = RRow::empty();
        // `env` evaluates the constructor's result-index terms; for a non-parameterized family it
        // binds only the (innermost-last) argument values.
        let mut env = Env::new();
        for (arg, shape) in args.iter().zip(ctor.args.iter()) {
            match shape {
                Arg::Rec(_) => {
                    let (r, u) = self.check(ctx, arg, &rec_ty, sigma)?;
                    row = row.union(&r);
                    usage = usage.add(&u);
                }
                Arg::NonRec(ty) => {
                    let ty_t = crate::term::from_kernel(ty)?;
                    // Match the kernel's `Term::Con` *inference* rule: NonRec argument types are
                    // evaluated in the ambient context env (the family is non-parameterized, so
                    // there are no params to thread; this keeps kernel<->recheck symmetric).
                    let ty_val = eval(self.sig, &ctx.env, &ty_t);
                    let (r, u) = self.check(ctx, arg, &ty_val, sigma)?;
                    row = row.union(&r);
                    usage = usage.add(&u);
                }
            }
            let arg_val = eval(self.sig, &ctx.env, arg);
            env = env.extend(arg_val);
        }
        let result_indices: Vec<RValue> = ctor
            .result_indices
            .iter()
            .map(|t| {
                let rt = crate::term::from_kernel(t)?;
                Ok::<RValue, RecheckError>(eval(self.sig, &env, &rt))
            })
            .collect::<RResult<_>>()?;
        Ok((RValue::Data(decl.name, Rc::new(vec![]), Rc::new(result_indices)), row, usage))
    }

    /// Check a constructor application against an expected `Data` family (spec §2.7).
    #[allow(clippy::too_many_arguments)]
    fn check_con(
        &self,
        ctx: &Ctx,
        name: &blight_kernel::ConName,
        args: &[RTerm],
        d_name: &DataName,
        params: &[RValue],
        exp_indices: &[RValue],
        sigma: RGrade,
    ) -> RResult<(RRow, Usage)> {
        let (decl, _idx, ctor) = self
            .sig
            .data_of_con(name)
            .ok_or_else(|| reject(format!("unknown constructor {name:?}")))?;
        let decl = decl.clone();
        let ctor = ctor.clone();
        if &decl.name != d_name {
            return Err(reject(format!(
                "constructor {name:?} belongs to {:?}, not {d_name:?}",
                decl.name
            )));
        }
        if args.len() != ctor.args.len() {
            return Err(reject(format!(
                "constructor {name:?} expects {} args, got {}",
                ctor.args.len(),
                args.len()
            )));
        }
        // Local value env for arg/index types: params bound outermost, then each checked arg value.
        let mut env = Env::new();
        for p in params {
            env = env.extend(p.clone());
        }
        let mut usage = Usage::zero(ctx.len());
        let mut row = RRow::empty();
        for (arg, shape) in args.iter().zip(ctor.args.iter()) {
            match shape {
                Arg::Rec(rec_indices) => {
                    let rec_index_vals: Vec<RValue> = rec_indices
                        .iter()
                        .map(|t| {
                            let rt = crate::term::from_kernel(t)?;
                            Ok::<RValue, RecheckError>(eval(self.sig, &env, &rt))
                        })
                        .collect::<RResult<_>>()?;
                    let rec_ty = RValue::Data(decl.name.clone(), Rc::new(params.to_vec()), Rc::new(rec_index_vals));
                    let (r, u) = self.check(ctx, arg, &rec_ty, sigma)?;
                    row = row.union(&r);
                    usage = usage.add(&u);
                }
                Arg::NonRec(ty) => {
                    let ty_t = crate::term::from_kernel(ty)?;
                    let ty_val = eval(self.sig, &env, &ty_t);
                    let (r, u) = self.check(ctx, arg, &ty_val, sigma)?;
                    row = row.union(&r);
                    usage = usage.add(&u);
                }
            }
            let arg_val = eval(self.sig, &ctx.env, arg);
            env = env.extend(arg_val);
        }
        // Result indices must match the expected family indices.
        for (rix, exp) in ctor.result_indices.iter().zip(exp_indices.iter()) {
            let rix_t = crate::term::from_kernel(rix)?;
            let got = eval(self.sig, &env, &rix_t);
            if !conv(self.sig, ctx.lvl, ctx.dlvl, &got, exp) {
                return Err(reject("constructor result index mismatch"));
            }
        }
        Ok((row, usage))
    }

    /// Re-check a dependent eliminator (spec §2.7): an independent port of the kernel's
    /// `infer_elim` over full N-parameter / M-index families (the earlier ≤1/≤1 cap is lifted). The
    /// indexed case threads all indices through the motive (`λ i… . λ (_:D ps i…). T`) and concludes
    /// `P idx… scrut`; the non-indexed case is `λ (_:D ps). T` concluding `P scrut`.
    #[allow(clippy::too_many_arguments)]
    fn infer_elim(
        &self,
        ctx: &Ctx,
        data: &DataName,
        motive: &RTerm,
        methods: &[RTerm],
        scrutinee: &RTerm,
        sigma: RGrade,
    ) -> RResult<(RValue, RRow, Usage)> {
        let decl = self
            .sig
            .get(data)
            .ok_or_else(|| reject(format!("unknown inductive type {data:?}")))?
            .clone();
        let nindices = decl.indices.len();
        let indexed = nindices != 0;

        // Infer the scrutinee's type, row, and usage; recover the family's params and index values.
        let (scrut_ty, scrut_row, scrut_usage) = self.infer(ctx, scrutinee, sigma)?;
        let (eparams, scrut_indices) = match &scrut_ty {
            RValue::Data(d, ps, is) if d == data => (ps.clone(), is.clone()),
            other => {
                return Err(reject(format!(
                    "Elim scrutinee not of type {data:?}: {other:?}"
                )))
            }
        };

        // Type-check the motive in its expected shape (it arrives as a bare `Lam`, not inferable on
        // its own): non-indexed `λ (_:D ps). T : Univ ℓ`, indexed `λ i1..im. λ (_:D ps i1..im). T`.
        match motive {
            RTerm::Lam(_) if indexed => {
                // Peel `nindices` index binders, threading each index type (which may reference the
                // params and earlier indices) through the context and env.
                let mut ctx_acc = ctx.clone();
                let mut idx_vars: Vec<RValue> = Vec::with_capacity(nindices);
                for idx_ty_term in decl.indices.iter() {
                    let kt = crate::term::from_kernel(idx_ty_term)?;
                    let mut env = Env::new();
                    for p in eparams.iter() {
                        env = env.extend(p.clone());
                    }
                    for v in &idx_vars {
                        env = env.extend(v.clone());
                    }
                    let index_ty = eval(self.sig, &env, &kt);
                    idx_vars.push(RValue::Neutral(crate::value::Neutral::Var(ctx_acc.lvl)));
                    ctx_acc = ctx_acc.extend(self.sig, index_ty, RGrade::Omega);
                }
                let mut body = motive;
                for _ in 0..nindices {
                    match body {
                        RTerm::Lam(inner) => body = inner,
                        other => {
                            return Err(reject(format!(
                            "indexed Elim motive needs {nindices} index binder(s), got {other:?}"
                        )))
                        }
                    }
                }
                let dty = RValue::Data(decl.name.clone(), eparams.clone(), Rc::new(idx_vars.clone()));
                let ctx_id = ctx_acc.extend(self.sig, dty, RGrade::Omega);
                match body {
                    RTerm::Lam(inner) => {
                        // The motive's conclusion may itself be a Π — i.e. the result type is a
                        // *function* — when a binder still in scope at the `match` (e.g. a second
                        // vector matched in a nested `match`) is lifted into the motive by the
                        // elaborator (`λ i. λ (_:D ps i). Π(w:…). T`). This is still an ordinary
                        // motive type: `infer_universe` checks it lives in a universe, and the
                        // per-branch method check below applies the motive to the scrutinee indices
                        // exactly as the kernel does, so a Π conclusion needs no special handling —
                        // the method's type is simply itself a Π. (We previously *declined* this
                        // shape conservatively; the elaborator now emits a faithfully checkable
                        // motive, so we re-verify it fully.)
                        self.infer_universe(&ctx_id, inner)?;
                    }
                    other => {
                        return Err(reject(format!(
                            "indexed Elim motive must be `λ i1..im. λ (_:D ps i1..im). T`, got {other:?}"
                        )))
                    }
                }
            }
            RTerm::Lam(body) => {
                let dty = RValue::Data(decl.name.clone(), eparams.clone(), Rc::new(vec![]));
                let ctx2 = ctx.extend(self.sig, dty, RGrade::Omega);
                self.infer_universe(&ctx2, body)?;
            }
            other => {
                return Err(reject(format!(
                    "Elim motive must be a lambda (`λ … . T`), got {other:?}"
                )))
            }
        }
        // Motive strengthening (dependent-motive recovery). The elaborator sometimes hands us a
        // motive whose body mentions the *ambient* scrutinee-index variable directly (e.g.
        // `λ i. λ s. Vec B n`) instead of the bound index `i` (`λ i. λ s. Vec B i`). Both yield the
        // SAME eliminator result `motive scrut_indices scrut` when a scrutinee index is exactly that
        // ambient variable `n` (since `i` is instantiated to `n`), but only the bound-index form lets
        // the per-branch refinement specialize the conclusion. So, soundly, for each scrutinee index
        // that is a bare ambient variable `Var(L)`, rewrite occurrences of `L` inside the motive body
        // to the corresponding index binder. This recovers the dependent motive a stronger elaborator
        // would have produced, without changing the eliminator's overall type.
        let strengthened = self.strengthen_motive(ctx, motive, nindices, &scrut_indices);
        let motive = &strengthened;
        let motive_v = eval(self.sig, &ctx.env, motive);

        if methods.len() != decl.constructors.len() {
            return Err(reject(format!(
                "Elim expects {} method(s), got {}",
                decl.constructors.len(),
                methods.len()
            )));
        }
        let mut usage = scrut_usage;
        // The eliminator's row unions the scrutinee's row with every (reachable) method's row.
        let mut row = scrut_row;
        for (ctor, method) in decl.constructors.iter().zip(methods.iter()) {
            // Dependent pattern matching (spec §2.7): refine the branch against the scrutinee's
            // indices. Unifying the constructor's result indices with the scrutinee indices either
            // (a) reveals a head-constructor CLASH — the branch is unreachable for this scrutinee
            // and is vacuously well-typed (we skip it), or (b) SOLVES some constructor arguments,
            // letting us check the body under the refined (specialized) context. When unification is
            // stuck (e.g. a bare-variable scrutinee index that constrains nothing), we fall back to
            // the plain `method_type` check, matching the kernel's behavior exactly on that fragment.
            match self.refine_method(ctx, ctor, &eparams, &scrut_indices)? {
                Refinement::Unreachable => {
                    // Vacuous branch: nothing to check, contributes no usage.
                }
                Refinement::Solved { args, ambient } => {
                    let (r, u) = self.check_refined_method(
                        ctx,
                        &decl,
                        ctor,
                        method,
                        motive,
                        &eparams,
                        &scrut_indices,
                        &args,
                        &ambient,
                        sigma,
                    )?;
                    row = row.union(&r);
                    usage = usage.add(&u);
                }
                Refinement::Stuck => {
                    let method_ty = self.method_type(ctx, &decl, ctor, &motive_v, &eparams)?;
                    let (r, u) = self.check(ctx, method, &method_ty, sigma)?;
                    row = row.union(&r);
                    usage = usage.add(&u);
                }
            }
        }

        // Result: non-indexed `P scrutinee`; indexed `P idx1..idxm scrutinee`.
        let scrut_v = eval(self.sig, &ctx.env, scrutinee);
        let result = if indexed {
            if scrut_indices.len() != nindices {
                return Err(reject(format!(
                    "indexed Elim scrutinee has {} index value(s), expected {nindices}",
                    scrut_indices.len()
                )));
            }
            let mut acc = motive_v;
            for idx in crate::value::unshare_rargs(scrut_indices).into_iter() {
                acc = apply(self.sig, acc, idx);
            }
            apply(self.sig, acc, scrut_v)
        } else {
            apply(self.sig, motive_v, scrut_v)
        };
        Ok((result, row, usage))
    }

    /// Recover a dependent motive from an index-ignoring one (see the call site in `infer_elim`).
    /// For each scrutinee index that is a bare ambient variable `Var(L)`, rewrite occurrences of that
    /// ambient variable inside the motive body to the corresponding index binder. Sound because it
    /// preserves `motive scrut_indices scrut` while making the per-branch conclusion index-dependent.
    fn strengthen_motive(
        &self,
        ctx: &Ctx,
        motive: &RTerm,
        nindices: usize,
        scrut_indices: &[RValue],
    ) -> RTerm {
        // Collect (ambient level L → index-binder position j) for bare-variable scrutinee indices.
        let mut remap: Vec<(usize, usize)> = Vec::new();
        for (j, ix) in scrut_indices.iter().enumerate().take(nindices) {
            if let RValue::Neutral(crate::value::Neutral::Var(l)) = ix {
                if *l < ctx.lvl {
                    remap.push((*l, j));
                }
            }
        }
        if remap.is_empty() {
            return motive.clone();
        }
        // Peel the `nindices` index binders and the scrutinee binder, rewriting the body underneath.
        fn rebuild(
            t: &RTerm,
            peel: usize,
            ctx_lvl: usize,
            depth: usize,
            remap: &[(usize, usize)],
        ) -> RTerm {
            if peel > 0 {
                if let RTerm::Lam(inner) = t {
                    return RTerm::Lam(Box::new(rebuild(
                        inner,
                        peel - 1,
                        ctx_lvl,
                        depth + 1,
                        remap,
                    )));
                }
                return t.clone();
            }
            subst_ambient_to_binder(t, ctx_lvl, depth, remap)
        }
        // Rewrite, tracking `depth` = binders entered since the motive root. A `Var(i)` with
        // `i >= depth` is free of the motive's binders and refers to ambient level
        // `ctx_lvl - 1 - (i - depth)`; if that level is a remapped scrutinee index, replace it with the
        // de Bruijn index of the corresponding (locally bound) motive index binder `Var(depth-1-j)`.
        fn subst_ambient_to_binder(
            t: &RTerm,
            ctx_lvl: usize,
            depth: usize,
            remap: &[(usize, usize)],
        ) -> RTerm {
            match t {
                RTerm::Var(i) => {
                    if *i >= depth {
                        // Ambient level this index refers to: (ctx_lvl - 1) - (i - depth).
                        let amb = (ctx_lvl)
                            .checked_sub(1)
                            .and_then(|x| x.checked_sub(*i - depth));
                        if let Some(amb) = amb {
                            for (l, j) in remap {
                                if *l == amb {
                                    return RTerm::Var(depth - 1 - j);
                                }
                            }
                        }
                    }
                    t.clone()
                }
                RTerm::Pi(g, a, b) => RTerm::Pi(
                    *g,
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(b, ctx_lvl, depth + 1, remap)),
                ),
                RTerm::Sigma(a, b) => RTerm::Sigma(
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(b, ctx_lvl, depth + 1, remap)),
                ),
                RTerm::Lam(b) => RTerm::Lam(Box::new(subst_ambient_to_binder(
                    b,
                    ctx_lvl,
                    depth + 1,
                    remap,
                ))),
                RTerm::App(f, a) => RTerm::App(
                    Box::new(subst_ambient_to_binder(f, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                ),
                RTerm::Pair(a, b) => RTerm::Pair(
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(b, ctx_lvl, depth, remap)),
                ),
                RTerm::Fst(p) => {
                    RTerm::Fst(Box::new(subst_ambient_to_binder(p, ctx_lvl, depth, remap)))
                }
                RTerm::Snd(p) => {
                    RTerm::Snd(Box::new(subst_ambient_to_binder(p, ctx_lvl, depth, remap)))
                }
                RTerm::Ann(e, ty) => RTerm::Ann(
                    Box::new(subst_ambient_to_binder(e, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(ty, ctx_lvl, depth, remap)),
                ),
                RTerm::Data(d, ps, is) => RTerm::Data(
                    d.clone(),
                    ps.iter()
                        .map(|x| subst_ambient_to_binder(x, ctx_lvl, depth, remap))
                        .collect(),
                    is.iter()
                        .map(|x| subst_ambient_to_binder(x, ctx_lvl, depth, remap))
                        .collect(),
                ),
                RTerm::Con(c, xs) => RTerm::Con(
                    c.clone(),
                    xs.iter()
                        .map(|x| subst_ambient_to_binder(x, ctx_lvl, depth, remap))
                        .collect(),
                ),
                // The supported motive bodies are built from Π/Σ/App/Data/Con/projections over the
                // params and indices; anything else is left structurally unchanged (it cannot mention
                // the ambient index variable in the fragment the kernel supports).
                other => other.clone(),
            }
        }
        rebuild(motive, nindices + 1, ctx.lvl, 0, &remap)
    }

    /// Build the expected method-type *value* for one constructor — a faithful, independent port of
    /// the kernel's `method_type` (spec §2.7): a Π-telescope over the constructor's argument shapes
    /// (with an induction-hypothesis binder after each recursive argument) concluding
    /// `motive (con args)`, handling the one-parameter inductive families the prelude uses. Built as
    /// a closed `RTerm` then `eval`'d once.
    fn method_type(
        &self,
        ctx: &Ctx,
        decl: &DataDecl,
        ctor: &Constructor,
        motive: &RValue,
        params: &[RValue],
    ) -> RResult<RValue> {
        let data_name = decl.name.clone();
        let indexed = !decl.indices.is_empty();
        let nparams = params.len();
        let motive_term = quote(self.sig, ctx.lvl, ctx.dlvl, motive);
        let param_terms: Vec<RTerm> = params
            .iter()
            .map(|p| quote(self.sig, ctx.lvl, ctx.dlvl, p))
            .collect();

        // Binder layout: each arg is one binder; each recursive arg is followed by an IH binder.
        // `arg_pos[k]` is the telescope position of constructor arg `k`. For an indexed family the
        // recursive argument's index expressions are carried on both the RecArg and its IH binder.
        #[derive(Clone)]
        enum B {
            Arg,
            RecArg(Vec<RTerm>),
            Ih(Vec<RTerm>),
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
                    let ix: Vec<RTerm> = rec_indices
                        .iter()
                        .map(crate::term::from_kernel)
                        .collect::<RResult<_>>()?;
                    arg_pos.push(binders.len());
                    binders.push(B::RecArg(ix.clone()));
                    binders.push(B::Ih(ix));
                }
            }
        }
        let total = binders.len();

        // Translate a constructor-scope term (sees `[args.. , params..]` innermost-first) into the
        // method telescope at `depth` binders, via a simultaneous substitution — a direct port of
        // the kernel's `translate`.
        let translate = |t: &RTerm, args_before: usize, depth: usize| -> RTerm {
            let m = args_before + nparams;
            let mut repls: Vec<RTerm> = Vec::with_capacity(m);
            for i in 0..args_before {
                let ctor_arg_index = args_before - 1 - i;
                let method_binder_pos = arg_pos[ctor_arg_index];
                repls.push(RTerm::Var(depth - 1 - method_binder_pos));
            }
            for pj in 0..nparams {
                let param_index = nparams - 1 - pj;
                repls.push(shift_free(&param_terms[param_index], depth));
            }
            translate_go(t, 0, m, &repls)
        };

        // Conclusion: non-indexed `motive (con args)`; indexed `motive rix (con args)` where `rix`
        // is the constructor's result index translated into the method telescope.
        let con_args: Vec<RTerm> = (0..ctor.args.len())
            .map(|k| RTerm::Var(total - 1 - arg_pos[k]))
            .collect();
        let con_term = RTerm::Con(ctor.name.clone(), con_args);
        let mut body = if indexed {
            // Apply the motive to every result index (translated into the method telescope), then
            // the constructor term: `motive rix_1 .. rix_m (con args)`.
            let mut acc = shift_free(&motive_term, total);
            for rix_k in ctor.result_indices.iter() {
                let rix_k = crate::term::from_kernel(rix_k)?;
                let rix = translate(&rix_k, ctor.args.len(), total);
                acc = RTerm::App(Box::new(acc), Box::new(rix));
            }
            RTerm::App(Box::new(acc), Box::new(con_term))
        } else {
            RTerm::App(
                Box::new(shift_free(&motive_term, total)),
                Box::new(con_term),
            )
        };

        // `args_before` at each binder position.
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
        let nonrec_tys: Vec<Option<RTerm>> = ctor
            .args
            .iter()
            .map(|a| match a {
                Arg::NonRec(ty) => Some(crate::term::from_kernel(ty)),
                Arg::Rec(_) => None,
            })
            .map(|o| o.transpose())
            .collect::<RResult<_>>()?;

        for (pos, b) in binders.iter().enumerate().rev() {
            let depth = pos;
            let args_before = args_before_at[pos];
            let dom = match b {
                B::Arg => {
                    let k = arg_pos.iter().position(|&p| p == pos).unwrap();
                    let ty = nonrec_tys[k].clone().unwrap();
                    translate(&ty, args_before, depth)
                }
                B::RecArg(rec_indices) => {
                    let ps: Vec<RTerm> = param_terms.iter().map(|t| shift_free(t, depth)).collect();
                    let ix: Vec<RTerm> = rec_indices
                        .iter()
                        .map(|t| translate(t, args_before, depth))
                        .collect();
                    RTerm::Data(data_name.clone(), ps, ix)
                }
                B::Ih(rec_indices) => {
                    let p_motive = shift_free(&motive_term, depth);
                    let rec_pos = pos - 1;
                    let xs_var = RTerm::Var(depth - 1 - rec_pos);
                    if indexed {
                        // The rec index references constructor args preceding the RecArg; the
                        // args-before count at the IH includes the RecArg itself, so subtract one.
                        let mut acc = p_motive;
                        for ix_k in rec_indices.iter() {
                            let ix = translate(ix_k, args_before - 1, depth);
                            acc = RTerm::App(Box::new(acc), Box::new(ix));
                        }
                        RTerm::App(Box::new(acc), Box::new(xs_var))
                    } else {
                        RTerm::App(Box::new(p_motive), Box::new(xs_var))
                    }
                }
            };
            body = RTerm::Pi(RGrade::Omega, Box::new(dom), Box::new(body));
        }

        let result_mty = eval(self.sig, &ctx.env, &body);
        Ok(result_mty)
    }

    /// Decide how to check one constructor's method under dependent pattern matching, by unifying
    /// the constructor's *result indices* (as functions of fresh argument placeholders) with the
    /// scrutinee's actual indices. Two kinds of unknown are solvable: the constructor's argument
    /// *placeholders* (de Bruijn levels `≥ ctx.lvl`) and the scrutinee's own index *variables*
    /// (ambient levels `< ctx.lvl`), which get *specialized* per branch — this is the substitution
    /// that dependent pattern matching performs. A head-constructor clash means the branch is
    /// unreachable for this scrutinee (vacuously well-typed); no progress means the plain
    /// `method_type` check is already exact (kernel-faithful fallback).
    fn refine_method(
        &self,
        ctx: &Ctx,
        ctor: &Constructor,
        params: &[RValue],
        scrut_indices: &[RValue],
    ) -> RResult<Refinement> {
        // Build placeholder values for the constructor arguments and the env that types/evaluates
        // the (param + preceding-arg) scope, exactly as `check_con` does — but with fresh neutral
        // *levels* (≥ ctx.lvl) so unification can recognize them as the solvable unknowns.
        let nargs = ctor.args.len();
        let mut env = Env::new();
        for p in params {
            env = env.extend(p.clone());
        }
        for k in 0..nargs {
            env = env.extend(RValue::Neutral(crate::value::Neutral::Var(ctx.lvl + k)));
        }
        let mut sol = Solution {
            args: vec![None; nargs],
            ambient: Vec::new(),
        };
        let mut any = false;
        for (rix_t, scrut_ix) in ctor.result_indices.iter().zip(scrut_indices.iter()) {
            let rt = crate::term::from_kernel(rix_t)?;
            let got = eval(self.sig, &env, &rt);
            match self.unify_index(ctx, &got, scrut_ix, &mut sol)? {
                Unify::Clash => return Ok(Refinement::Unreachable),
                Unify::Progress => any = true,
                Unify::Trivial => {}
                Unify::Stuck => return Ok(Refinement::Stuck),
            }
        }
        if any {
            Ok(Refinement::Solved {
                args: sol.args,
                ambient: sol.ambient,
            })
        } else {
            Ok(Refinement::Stuck)
        }
    }

    /// First-order unification of a constructor result-index value `got` (which may mention argument
    /// placeholders at levels `≥ ctx.lvl`) against the scrutinee index value `want` (which may
    /// mention ambient context variables at levels `< ctx.lvl`). Solves placeholders (the branch's
    /// constructor arguments) and ambient index variables (the per-branch specialization).
    fn unify_index(
        &self,
        ctx: &Ctx,
        got: &RValue,
        want: &RValue,
        sol: &mut Solution,
    ) -> RResult<Unify> {
        // Flexible placeholder on the `got` side ⇒ solve the constructor argument.
        if let RValue::Neutral(crate::value::Neutral::Var(l)) = got {
            if *l >= ctx.lvl {
                let k = *l - ctx.lvl;
                if k < sol.args.len() {
                    return Ok(match &sol.args[k] {
                        None => {
                            sol.args[k] = Some(want.clone());
                            Unify::Progress
                        }
                        Some(prev) => {
                            if conv(self.sig, ctx.lvl, ctx.dlvl, prev, want) {
                                Unify::Trivial
                            } else {
                                Unify::Stuck
                            }
                        }
                    });
                }
            }
        }
        // Flexible ambient index variable on the `want` side ⇒ specialize it to `got`. `got` may
        // mention the constructor's argument placeholders (they become this branch's bound
        // variables); it must not contain a *stuck* neutral (an application/eliminator), which we
        // cannot soundly turn into an equation.
        if let RValue::Neutral(crate::value::Neutral::Var(l)) = want {
            if *l < ctx.lvl && self.solvable_index(got) {
                for (lvl, v) in sol.ambient.iter() {
                    if lvl == l {
                        return Ok(if conv(self.sig, ctx.lvl, ctx.dlvl, v, got) {
                            Unify::Trivial
                        } else {
                            Unify::Stuck
                        });
                    }
                }
                sol.ambient.push((*l, got.clone()));
                return Ok(Unify::Progress);
            }
        }
        match (got, want) {
            // Same data head: decompose parameters and indices.
            (RValue::Data(n1, p1, i1), RValue::Data(n2, p2, i2)) => {
                if n1 != n2 || p1.len() != p2.len() || i1.len() != i2.len() {
                    return Ok(Unify::Clash);
                }
                self.unify_seq(ctx, p1.iter().zip(p2.iter()).chain(i1.iter().zip(i2.iter())), sol)
            }
            // Same constructor head: decompose arguments. Different heads are a genuine CLASH — the
            // branch is unreachable for this scrutinee.
            (RValue::Con(c1, a1), RValue::Con(c2, a2)) => {
                if c1 != c2 || a1.len() != a2.len() {
                    return Ok(Unify::Clash);
                }
                self.unify_seq(ctx, a1.iter().zip(a2.iter()), sol)
            }
            (RValue::IntLit(a), RValue::IntLit(b)) => {
                Ok(if a == b { Unify::Trivial } else { Unify::Clash })
            }
            // Otherwise: rigidly equal ⇒ trivial; not provably so ⇒ stuck (fall back to the plain
            // method type rather than risk an unsound accept).
            _ => Ok(if conv(self.sig, ctx.lvl, ctx.dlvl, got, want) {
                Unify::Trivial
            } else {
                Unify::Stuck
            }),
        }
    }

    /// Unify a sequence of value pairs, combining their outcomes (clash/stuck short-circuit).
    fn unify_seq<'b>(
        &self,
        ctx: &Ctx,
        pairs: impl Iterator<Item = (&'b RValue, &'b RValue)>,
        sol: &mut Solution,
    ) -> RResult<Unify> {
        let mut progressed = false;
        for (a, b) in pairs {
            match self.unify_index(ctx, a, b, sol)? {
                Unify::Clash => return Ok(Unify::Clash),
                Unify::Progress => progressed = true,
                Unify::Trivial => {}
                Unify::Stuck => return Ok(Unify::Stuck),
            }
        }
        Ok(if progressed {
            Unify::Progress
        } else {
            Unify::Trivial
        })
    }

    /// May `v` be used as the right-hand side of an index equation (ambient specialization)? It must
    /// be a value built only from variables (ambient context vars or constructor-argument
    /// placeholders), data/constructor heads, and literals — never a *stuck* neutral such as an
    /// application or eliminator, which we cannot soundly equate.
    fn solvable_index(&self, v: &RValue) -> bool {
        match v {
            RValue::Neutral(crate::value::Neutral::Var(_)) => true,
            RValue::Neutral(_) => false,
            RValue::Data(_, ps, is) => {
                ps.iter().all(|x| self.solvable_index(x))
                    && is.iter().all(|x| self.solvable_index(x))
            }
            RValue::Con(_, xs) => xs.iter().all(|x| self.solvable_index(x)),
            RValue::Univ(_) | RValue::IntTy | RValue::IntLit(_) => true,
            _ => false,
        }
    }

    /// Check a constructor's method body under the refinement solved by [`Self::refine_method`]. The
    /// ambient index variables are *specialized* (re-bound in the environment), the motive is
    /// re-evaluated under that specialization, each constructor argument is bound either to its
    /// *solved* value or a fresh variable (recursive arguments also get an induction-hypothesis
    /// binder), and the body is checked against the dependent conclusion
    /// `motive (specialized scrut_indices) (con args)`.
    #[allow(clippy::too_many_arguments)]
    fn check_refined_method(
        &self,
        ctx: &Ctx,
        decl: &DataDecl,
        ctor: &Constructor,
        method: &RTerm,
        motive_term: &RTerm,
        params: &[RValue],
        scrut_indices: &[RValue],
        solved: &[Option<RValue>],
        ambient: &[(usize, RValue)],
        sigma: RGrade,
    ) -> RResult<(RRow, Usage)> {
        let mut cur = ctx.clone();
        let mut body = method;
        // `arg_env` evaluates the constructor's arg/index types (param scope, then bound args), in
        // the same convention as `check_con`.
        let mut arg_env = Env::new();
        for p in params {
            arg_env = arg_env.extend(p.clone());
        }
        let mut arg_vals: Vec<RValue> = Vec::with_capacity(ctor.args.len());
        // Map each constructor-argument placeholder (used during unification as `Var(ctx.lvl + k)`)
        // to the actual value bound for that argument here, so ambient index equations expressed
        // over placeholders can be re-expressed over the branch's real binders.
        let mut placeholder_map: Vec<(usize, RValue)> = Vec::with_capacity(ctor.args.len());
        for (k, shape) in ctor.args.iter().enumerate() {
            // Domain type of this argument, in the current refined context. For a recursive arg we
            // also remember its index *values* (computed against the args bound *before* this one)
            // to build the induction-hypothesis binder below.
            let mut rec_ix: Option<Vec<RValue>> = None;
            let dom = match shape {
                Arg::NonRec(ty) => {
                    let ty_t = crate::term::from_kernel(ty)?;
                    eval(self.sig, &arg_env, &ty_t)
                }
                Arg::Rec(rec_indices) => {
                    let ix: Vec<RValue> = rec_indices
                        .iter()
                        .map(|t| {
                            let rt = crate::term::from_kernel(t)?;
                            Ok::<RValue, RecheckError>(eval(self.sig, &arg_env, &rt))
                        })
                        .collect::<RResult<_>>()?;
                    rec_ix = Some(ix.clone());
                    RValue::Data(decl.name.clone(), Rc::new(params.to_vec()), Rc::new(ix))
                }
            };
            // Open the method's lambda for this argument.
            let inner = match body {
                RTerm::Lam(inner) => inner.as_ref(),
                other => {
                    return Err(reject(format!(
                        "indexed Elim method for {:?} expected a lambda, got {other:?}",
                        ctor.name
                    )))
                }
            };
            // Bind the argument to its solved value if forced, else to a fresh variable of `dom`.
            let arg_val = match &solved[k] {
                Some(v) => v.clone(),
                None => fresh_var(self.sig, cur.lvl, &dom),
            };
            placeholder_map.push((ctx.lvl + k, arg_val.clone()));
            // The body's binder still ranges over `dom`; record the entry at that type and bind the
            // (possibly forced) value in the environment so later types/the conclusion see it.
            cur = cur.extend_with(self.sig, dom, RGrade::Omega, arg_val.clone());
            arg_vals.push(arg_val.clone());
            arg_env = arg_env.extend(arg_val.clone());
            body = inner;

            // After a recursive argument, the method also binds an induction hypothesis
            // `P (rec indices) xs`, using the recursive argument's indices computed above. The IH's
            // motive must be re-evaluated under the ambient refinement so its index types line up.
            if let Some(ix) = rec_ix {
                let ix: Vec<RValue> = ix
                    .iter()
                    .map(|v| self.subst_levels(v, &placeholder_map))
                    .collect();
                // The induction hypothesis is the recursive result on the *shorter* structure, so it
                // is typed at the recursive argument's *own* indices, not the conclusion's. Refine the
                // ambient scrutinee-index variables by unifying them against this recursive argument's
                // indices (e.g. for `vec-map`, the scrutinee index `n` becomes the tail's length `m`),
                // then evaluate the motive under that refinement. This recovers `P (rec ix) xs` even
                // when the elaborator handed us an index-ignoring motive `λ i. λ s. Vec B n`.
                let ih_ambient = {
                    let mut sol = Solution {
                        args: vec![None; 0],
                        ambient: Vec::new(),
                    };
                    for (sx, rx) in scrut_indices.iter().zip(ix.iter()) {
                        let _ = self.unify_index(ctx, rx, sx, &mut sol)?;
                    }
                    sol.ambient
                };
                let motive_here = {
                    let env_here = ctx.refine_ambient(&ih_ambient).env;
                    eval(self.sig, &env_here, motive_term)
                };
                let mut ih_ty = motive_here;
                for v in ix {
                    let v = self.subst_levels(&v, &ih_ambient);
                    ih_ty = apply(self.sig, ih_ty, v);
                }
                ih_ty = apply(self.sig, ih_ty, arg_val);
                let inner2 = match body {
                    RTerm::Lam(inner) => inner.as_ref(),
                    other => {
                        return Err(reject(format!(
                            "indexed Elim method for {:?} expected an IH lambda, got {other:?}",
                            ctor.name
                        )))
                    }
                };
                let ih_val = fresh_var(self.sig, cur.lvl, &ih_ty);
                cur = cur.extend_with(self.sig, ih_ty, RGrade::Omega, ih_val);
                body = inner2;
            }
        }
        // Apply the per-branch refinement now that the constructor's arguments are in scope: the
        // ambient index variables are specialized to their solutions (re-expressed over the bound
        // arguments), the context environment is updated, and the motive/scrutinee indices are
        // re-evaluated so the conclusion `motive (refined indices) (con args)` reflects the branch's
        // index equations. This is exactly the substitution dependent pattern matching performs.
        let refined_ambient = self.resolve_ambient(ambient, &placeholder_map);
        cur = cur.refine_ambient(&refined_ambient);
        // Evaluate the motive against the *ambient* environment (refined), not `cur.env`: the motive
        // term's free variables are de Bruijn indices into the ambient context, and `cur.env` has the
        // method binders appended (which would shift those indices). Applying the resulting closure
        // to the indices/scrutinee is level-agnostic, so the conclusion comes out correct.
        let motive = eval(
            self.sig,
            &ctx.refine_ambient(&refined_ambient).env,
            motive_term,
        );
        let con_val = RValue::Con(ctor.name.clone(), Rc::new(arg_vals));
        let mut concl = motive;
        for ix in scrut_indices {
            let ix = self.subst_levels(ix, &refined_ambient);
            concl = apply(self.sig, concl, ix);
        }
        concl = apply(self.sig, concl, con_val);
        let (row, u) = self.check(&cur, body, &concl, sigma)?;
        // The method binders are not part of the ambient usage vector; truncate to ambient length.
        Ok((row, u.truncate(ctx.len())))
    }

    /// Re-express the ambient index solutions (computed over constructor-argument placeholders) in
    /// terms of the branch's actually-bound argument values.
    fn resolve_ambient(
        &self,
        ambient: &[(usize, RValue)],
        placeholder_map: &[(usize, RValue)],
    ) -> Vec<(usize, RValue)> {
        ambient
            .iter()
            .map(|(lvl, v)| (*lvl, self.subst_levels(v, placeholder_map)))
            .collect()
    }

    /// Substitute neutral variables at the given levels by the mapped values throughout `v`.
    fn subst_levels(&self, v: &RValue, map: &[(usize, RValue)]) -> RValue {
        match v {
            RValue::Neutral(crate::value::Neutral::Var(l)) => {
                for (lvl, val) in map {
                    if lvl == l {
                        return val.clone();
                    }
                }
                v.clone()
            }
            RValue::Data(n, ps, is) => RValue::Data(
                n.clone(),
                Rc::new(ps.iter().map(|x| self.subst_levels(x, map)).collect()),
                Rc::new(is.iter().map(|x| self.subst_levels(x, map)).collect()),
            ),
            RValue::Con(c, xs) => RValue::Con(
                c.clone(),
                Rc::new(xs.iter().map(|x| self.subst_levels(x, map)).collect()),
            ),
            other => other.clone(),
        }
    }
}

/// How a constructor's branch relates to the scrutinee's indices under dependent pattern matching.
enum Refinement {
    /// The constructor can never produce the scrutinee's indices: the branch is vacuous.
    Unreachable,
    /// The branch is reachable; some constructor arguments are forced (`args`) and some ambient
    /// scrutinee-index variables are specialized (`ambient`: `(level, value)`).
    Solved {
        args: Vec<Option<RValue>>,
        ambient: Vec<(usize, RValue)>,
    },
    /// Unification made no progress; check with the plain method type (kernel-faithful default).
    Stuck,
}

/// Accumulated unification solution: per-argument placeholder solutions and ambient index-variable
/// specializations (`(level, value)`).
struct Solution {
    args: Vec<Option<RValue>>,
    ambient: Vec<(usize, RValue)>,
}

/// The result of unifying one index pair.
enum Unify {
    /// Head-constructor clash ⇒ the branch is unreachable.
    Clash,
    /// A placeholder was solved (or a sub-unification solved something).
    Progress,
    /// Already definitionally equal; no new information.
    Trivial,
    /// Cannot decide ⇒ fall back to the plain method-type check.
    Stuck,
}

/// The recursive worker of the constructor-scope→method-scope translation (port of the kernel's
/// `go`): replace the lowest `m` de Bruijn indices `>= depth_in` by `repls` (shifted into scope),
/// and shift everything above down by `m`.
fn translate_go(t: &RTerm, depth_in: usize, m: usize, repls: &[RTerm]) -> RTerm {
    match t {
        RTerm::Var(i) => {
            if *i < depth_in {
                RTerm::Var(*i)
            } else if *i < depth_in + m {
                shift_free(&repls[*i - depth_in], depth_in)
            } else {
                RTerm::Var(*i - m)
            }
        }
        RTerm::Univ(_) | RTerm::Interval(_) => t.clone(),
        RTerm::Pi(g, a, b) => RTerm::Pi(
            *g,
            Box::new(translate_go(a, depth_in, m, repls)),
            Box::new(translate_go(b, depth_in + 1, m, repls)),
        ),
        RTerm::Sigma(a, b) => RTerm::Sigma(
            Box::new(translate_go(a, depth_in, m, repls)),
            Box::new(translate_go(b, depth_in + 1, m, repls)),
        ),
        RTerm::Lam(b) => RTerm::Lam(Box::new(translate_go(b, depth_in + 1, m, repls))),
        RTerm::App(f, a) => RTerm::App(
            Box::new(translate_go(f, depth_in, m, repls)),
            Box::new(translate_go(a, depth_in, m, repls)),
        ),
        RTerm::Pair(a, b) => RTerm::Pair(
            Box::new(translate_go(a, depth_in, m, repls)),
            Box::new(translate_go(b, depth_in, m, repls)),
        ),
        RTerm::Fst(p) => RTerm::Fst(Box::new(translate_go(p, depth_in, m, repls))),
        RTerm::Snd(p) => RTerm::Snd(Box::new(translate_go(p, depth_in, m, repls))),
        RTerm::Ann(e, ty) => RTerm::Ann(
            Box::new(translate_go(e, depth_in, m, repls)),
            Box::new(translate_go(ty, depth_in, m, repls)),
        ),
        RTerm::Data(d, ps, ix) => RTerm::Data(
            d.clone(),
            ps.iter()
                .map(|x| translate_go(x, depth_in, m, repls))
                .collect(),
            ix.iter()
                .map(|x| translate_go(x, depth_in, m, repls))
                .collect(),
        ),
        RTerm::Con(c, xs) => RTerm::Con(
            c.clone(),
            xs.iter()
                .map(|x| translate_go(x, depth_in, m, repls))
                .collect(),
        ),
        // Constructor argument/index types in the supported fragment never carry eliminators,
        // paths, or Kan operations; leave anything else structurally untouched.
        RTerm::Elim { .. }
        | RTerm::PathP { .. }
        | RTerm::PLam(_)
        | RTerm::PApp(_, _)
        | RTerm::Transp { .. }
        | RTerm::HComp { .. }
        | RTerm::Comp { .. }
        | RTerm::Delay(_)
        | RTerm::Now(_)
        | RTerm::Later(_)
        | RTerm::Force(_) => t.clone(),
        // Effects/handlers: recurse over term children, honoring the handler clause binders
        // (return clause: +1; each op clause: +2).
        RTerm::EffTy(a) => RTerm::EffTy(Box::new(translate_go(a, depth_in, m, repls))),
        RTerm::Op {
            effect,
            op,
            type_args,
            arg,
        } => RTerm::Op {
            effect: effect.clone(),
            op: op.clone(),
            type_args: type_args
                .iter()
                .map(|t| translate_go(t, depth_in, m, repls))
                .collect(),
            arg: Box::new(translate_go(arg, depth_in, m, repls)),
        },
        RTerm::Handle {
            body,
            return_clause,
            op_clauses,
        } => RTerm::Handle {
            body: Box::new(translate_go(body, depth_in, m, repls)),
            return_clause: Box::new(translate_go(return_clause, depth_in + 1, m, repls)),
            op_clauses: op_clauses
                .iter()
                .map(|(op, clause)| {
                    (
                        op.clone(),
                        Box::new(translate_go(clause, depth_in + 2, m, repls)),
                    )
                })
                .collect(),
        },
        // Int type/literal carry no de Bruijn content; an IntPrim's operands must be translated.
        RTerm::IntTy | RTerm::IntLit(_) => t.clone(),
        RTerm::IntPrim { op, lhs, rhs } => RTerm::IntPrim {
            op: *op,
            lhs: Box::new(translate_go(lhs, depth_in, m, repls)),
            rhs: Box::new(translate_go(rhs, depth_in, m, repls)),
        },
        // `if-zero` binds no term variable — all three subterms at the same depth.
        RTerm::IfZero { scrut, then_, else_ } => RTerm::IfZero {
            scrut: Box::new(translate_go(scrut, depth_in, m, repls)),
            then_: Box::new(translate_go(then_, depth_in, m, repls)),
            else_: Box::new(translate_go(else_, depth_in, m, repls)),
        },
    }
}

/// Shift free de Bruijn indices `>= 0` upward by `d` (closed-term weakening helper for building
/// method-type telescopes as terms).
fn shift_free(t: &RTerm, d: usize) -> RTerm {
    shift_free_cut(t, d, 0)
}

fn shift_free_cut(t: &RTerm, d: usize, cut: usize) -> RTerm {
    match t {
        RTerm::Var(i) => {
            if *i >= cut {
                RTerm::Var(i + d)
            } else {
                RTerm::Var(*i)
            }
        }
        RTerm::Univ(_) | RTerm::Interval(_) => t.clone(),
        RTerm::Pi(g, a, b) => RTerm::Pi(
            *g,
            Box::new(shift_free_cut(a, d, cut)),
            Box::new(shift_free_cut(b, d, cut + 1)),
        ),
        RTerm::Lam(b) => RTerm::Lam(Box::new(shift_free_cut(b, d, cut + 1))),
        RTerm::App(f, a) => RTerm::App(
            Box::new(shift_free_cut(f, d, cut)),
            Box::new(shift_free_cut(a, d, cut)),
        ),
        RTerm::Sigma(a, b) => RTerm::Sigma(
            Box::new(shift_free_cut(a, d, cut)),
            Box::new(shift_free_cut(b, d, cut + 1)),
        ),
        RTerm::Pair(a, b) => RTerm::Pair(
            Box::new(shift_free_cut(a, d, cut)),
            Box::new(shift_free_cut(b, d, cut)),
        ),
        RTerm::Fst(p) => RTerm::Fst(Box::new(shift_free_cut(p, d, cut))),
        RTerm::Snd(p) => RTerm::Snd(Box::new(shift_free_cut(p, d, cut))),
        RTerm::Ann(e, ty) => RTerm::Ann(
            Box::new(shift_free_cut(e, d, cut)),
            Box::new(shift_free_cut(ty, d, cut)),
        ),
        RTerm::Data(n, ps, is) => RTerm::Data(
            n.clone(),
            ps.iter().map(|x| shift_free_cut(x, d, cut)).collect(),
            is.iter().map(|x| shift_free_cut(x, d, cut)).collect(),
        ),
        RTerm::Con(n, args) => RTerm::Con(
            n.clone(),
            args.iter().map(|x| shift_free_cut(x, d, cut)).collect(),
        ),
        RTerm::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => RTerm::Elim {
            data: data.clone(),
            motive: Box::new(shift_free_cut(motive, d, cut)),
            methods: methods.iter().map(|m| shift_free_cut(m, d, cut)).collect(),
            scrutinee: Box::new(shift_free_cut(scrutinee, d, cut)),
        },
        RTerm::PathP { family, lhs, rhs } => RTerm::PathP {
            family: Box::new(shift_free_cut(family, d, cut)),
            lhs: Box::new(shift_free_cut(lhs, d, cut)),
            rhs: Box::new(shift_free_cut(rhs, d, cut)),
        },
        RTerm::PLam(b) => RTerm::PLam(Box::new(shift_free_cut(b, d, cut))),
        RTerm::PApp(p, r) => RTerm::PApp(Box::new(shift_free_cut(p, d, cut)), r.clone()),
        RTerm::Transp {
            family,
            cofib,
            base,
        } => RTerm::Transp {
            family: Box::new(shift_free_cut(family, d, cut)),
            cofib: cofib.clone(),
            base: Box::new(shift_free_cut(base, d, cut)),
        },
        RTerm::HComp {
            ty,
            cofib,
            tube,
            base,
        } => RTerm::HComp {
            ty: Box::new(shift_free_cut(ty, d, cut)),
            cofib: cofib.clone(),
            tube: Box::new(shift_free_cut(tube, d, cut)),
            base: Box::new(shift_free_cut(base, d, cut)),
        },
        RTerm::Comp {
            family,
            cofib,
            tube,
            base,
        } => RTerm::Comp {
            family: Box::new(shift_free_cut(family, d, cut)),
            cofib: cofib.clone(),
            tube: Box::new(shift_free_cut(tube, d, cut)),
            base: Box::new(shift_free_cut(base, d, cut)),
        },
        RTerm::Delay(a) => RTerm::Delay(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Now(a) => RTerm::Now(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Later(a) => RTerm::Later(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Force(a) => RTerm::Force(Box::new(shift_free_cut(a, d, cut))),
        RTerm::EffTy(a) => RTerm::EffTy(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Op {
            effect,
            op,
            type_args,
            arg,
        } => RTerm::Op {
            effect: effect.clone(),
            op: op.clone(),
            type_args: type_args
                .iter()
                .map(|t| shift_free_cut(t, d, cut))
                .collect(),
            arg: Box::new(shift_free_cut(arg, d, cut)),
        },
        RTerm::Handle {
            body,
            return_clause,
            op_clauses,
        } => RTerm::Handle {
            body: Box::new(shift_free_cut(body, d, cut)),
            return_clause: Box::new(shift_free_cut(return_clause, d, cut + 1)),
            op_clauses: op_clauses
                .iter()
                .map(|(op, clause)| (op.clone(), Box::new(shift_free_cut(clause, d, cut + 2))))
                .collect(),
        },
        RTerm::IntTy | RTerm::IntLit(_) => t.clone(),
        RTerm::IntPrim { op, lhs, rhs } => RTerm::IntPrim {
            op: *op,
            lhs: Box::new(shift_free_cut(lhs, d, cut)),
            rhs: Box::new(shift_free_cut(rhs, d, cut)),
        },
        RTerm::IfZero { scrut, then_, else_ } => RTerm::IfZero {
            scrut: Box::new(shift_free_cut(scrut, d, cut)),
            then_: Box::new(shift_free_cut(then_, d, cut)),
            else_: Box::new(shift_free_cut(else_, d, cut)),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::signature::{EffDecl, OpSig};
    use blight_kernel::{ConName, Constructor, DataDecl, EffName, Grade, Term};

    /// Wave 7/E2 recheck twin of the kernel's `check::tests::ref_eff_sig`: the same `Unit`/`Flag`
    /// data plus a parameterized `Ref A` effect (`get : Unit -> A`, `put : A -> Unit`), built from
    /// kernel `Term`s (the signature format the re-checker shares with the kernel).
    fn ref_eff_sig() -> Signature {
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
        sig.declare(DataDecl {
            name: DataName("Flag".into()),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("mk".into()),
                args: vec![],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        });
        let decl = EffDecl {
            name: EffName::new("Ref"),
            params: vec![Term::Univ(blight_kernel::Level::Zero)], // A : Type 0
            ops: vec![
                OpSig {
                    name: "get".into(),
                    param_ty: Term::Data(DataName("Unit".into()), vec![], vec![]),
                    // scope `[A, x:Unit]` (x innermost = index 0), so `A` itself is index 1.
                    result_ty: Term::Var(1),
                    cont_grade: Grade::Omega,
                },
                OpSig {
                    name: "put".into(),
                    param_ty: Term::Var(0), // scope `[A]`: A is index 0
                    result_ty: Term::Data(DataName("Unit".into()), vec![], vec![]),
                    cont_grade: Grade::Omega,
                },
            ],
        };
        sig.check_effect(&decl).expect("Ref is well-formed");
        sig.declare_effect(decl);
        sig
    }

    fn flag_ty() -> RTerm {
        RTerm::Data(DataName("Flag".into()), vec![], vec![])
    }
    fn mk_flag() -> RTerm {
        RTerm::Con(ConName("mk".into()), vec![])
    }
    fn tt() -> RTerm {
        RTerm::Con(ConName("tt".into()), vec![])
    }

    /// Wave 7/E2 — recheck twin of `blight_kernel::check::tests::parameterized_op_instantiates_type_arg`:
    /// the re-checker independently re-derives `perform (get @ Flag) tt : Flag` (not `Unit`), the
    /// type argument (not the value argument's type) driving the instantiated result — and agrees
    /// with the kernel.
    #[test]
    fn parameterized_effect_roundtrips() {
        let sig = ref_eff_sig();
        let checker = Recheck::new(&sig);
        let ctx = Ctx::empty();

        let get_flag = RTerm::Op {
            effect: EffName::new("Ref"),
            op: "get".into(),
            type_args: vec![flag_ty()],
            arg: Box::new(tt()),
        };
        let (ty, row, _u) = checker
            .infer(&ctx, &get_flag, RGrade::One)
            .expect("get @ Flag infers");
        assert!(
            matches!(ty, RValue::Data(ref d, ..) if d.0 == "Flag"),
            "re-checker instantiates the result to the type argument Flag, got {ty:?}"
        );
        assert_eq!(row.grade_of(&EffName::new("Ref")), RGrade::One);

        // `put` is contravariant in the same parameter: `perform (put @ Flag) mk_flag : Unit`.
        let put_flag = RTerm::Op {
            effect: EffName::new("Ref"),
            op: "put".into(),
            type_args: vec![flag_ty()],
            arg: Box::new(mk_flag()),
        };
        let (ty2, _row2, _u2) = checker
            .infer(&ctx, &put_flag, RGrade::One)
            .expect("put @ Flag infers");
        assert!(matches!(ty2, RValue::Data(ref d, ..) if d.0 == "Unit"));
    }

    /// A `perform` site with the wrong type-argument arity is Rejected, matching the kernel's
    /// `perform_at_wrong_type_arg_rejected`.
    #[test]
    fn parameterized_effect_wrong_arity_rejected() {
        let sig = ref_eff_sig();
        let checker = Recheck::new(&sig);
        let ctx = Ctx::empty();

        let missing = RTerm::Op {
            effect: EffName::new("Ref"),
            op: "get".into(),
            type_args: vec![],
            arg: Box::new(tt()),
        };
        assert!(
            checker.infer(&ctx, &missing, RGrade::One).is_err(),
            "missing type argument is rejected"
        );

        let extra = RTerm::Op {
            effect: EffName::new("Ref"),
            op: "get".into(),
            type_args: vec![flag_ty(), flag_ty()],
            arg: Box::new(tt()),
        };
        assert!(
            checker.infer(&ctx, &extra, RGrade::One).is_err(),
            "extra type argument is rejected"
        );
    }

    /// Wave 7/E2 — recheck twin of the kernel's `check::tests::handling_parameterized_effect_op_rejected`:
    /// handling an operation of a parameterized effect is an intentionally unmodeled shape here too
    /// (the `infer_handle` scope gate), so it must be Rejected, not silently mistyped against the
    /// parameter-open signature and not merely Declined.
    #[test]
    fn handling_parameterized_effect_op_rejected() {
        let sig = ref_eff_sig();
        let checker = Recheck::new(&sig);
        let ctx = Ctx::empty();
        let body = RTerm::Op {
            effect: EffName::new("Ref"),
            op: "get".into(),
            type_args: vec![flag_ty()],
            arg: Box::new(tt()),
        };
        let term = RTerm::Handle {
            body: Box::new(body),
            return_clause: Box::new(RTerm::Var(0)),
            op_clauses: vec![(
                "get".into(),
                Box::new(RTerm::App(Box::new(RTerm::Var(0)), Box::new(RTerm::Var(1)))),
            )],
        };
        assert!(
            matches!(
                checker.infer(&ctx, &term, RGrade::One),
                Err(RecheckError::Rejected(_))
            ),
            "handling a parameterized effect's operation is Rejected, not Declined or silently accepted"
        );
    }

    /// Mutation pin (N6 gate ladder): cargo-mutants found that deleting the `(Data, Data)`
    /// decomposition arm of [`Recheck::unify_index`] survived the suite — the corpus gates that
    /// exercise indexed-family refinement are `#[ignore]`d, so the arm needs a direct probe.
    /// Two behaviors only the arm provides (the catch-all below it can answer at most
    /// `Trivial`/`Stuck` via `conv`): same-head decomposition recurses into the indices and
    /// solves a constructor-argument placeholder (`Progress`), and different heads are a
    /// definite `Clash` (unreachable branch), not merely `Stuck`.
    #[test]
    fn unify_index_data_arm_decomposes_and_clashes() {
        let sig = Signature::empty();
        let rc = Recheck::new(&sig);
        let ctx = Ctx::empty();
        let a = || DataName("A".into());
        let zero = || RValue::Con(ConName("z".into()), std::rc::Rc::new(vec![]));
        let indices = |v: RValue| std::rc::Rc::new(vec![v]);
        let no_params = || std::rc::Rc::new(vec![]);

        // Same head, a placeholder (a Var at/above `ctx.lvl`, slot k = 0) as the got-side
        // index: the arm decomposes and the index sub-unification binds the slot.
        let got = RValue::Data(
            a(),
            no_params(),
            indices(RValue::Neutral(crate::value::Neutral::Var(0))),
        );
        let want = RValue::Data(a(), no_params(), indices(zero()));
        let mut sol = Solution {
            args: vec![None],
            ambient: vec![],
        };
        let r = rc
            .unify_index(&ctx, &got, &want, &mut sol)
            .expect("unify_index runs");
        assert!(
            matches!(r, Unify::Progress),
            "same-head decomposition must solve the index placeholder (Progress)"
        );
        assert!(
            sol.args[0].is_some(),
            "the placeholder slot is bound by the decomposition"
        );

        // Different heads at equal arity: the arm answers Clash (branch unreachable); the
        // catch-all could only say Stuck.
        let got = RValue::Data(a(), no_params(), indices(zero()));
        let want = RValue::Data(DataName("B".into()), no_params(), indices(zero()));
        let mut sol = Solution {
            args: vec![],
            ambient: vec![],
        };
        let r = rc
            .unify_index(&ctx, &got, &want, &mut sol)
            .expect("unify_index runs");
        assert!(
            matches!(r, Unify::Clash),
            "different data heads are a definite Clash"
        );
    }

    // R-P2 (soundness audit 2026-07-03): the `RTerm::Data` inference arm must check parameter/index
    // arity and each param/index's type in the 0-fragment, mirroring the kernel's `Term::Data`
    // rule — else recheck returns `Ok` on a malformed `Data` the kernel rejects (false-`Ok`).

    /// `Nat : Type 0` (with a `zero`) and a parameterized/indexed `Vec : (A:Type 0) → Nat → Type 0`.
    fn nat_vec_sig() -> Signature {
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: DataName("Nat".into()),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("zero".into()),
                args: vec![],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        });
        sig.declare(DataDecl {
            name: DataName("Vec".into()),
            params: vec![Term::Univ(blight_kernel::Level::Zero)], // A : Type 0
            indices: vec![Term::Data(DataName("Nat".into()), vec![], vec![])], // n : Nat
            level: 0,
            constructors: vec![],
            path_constructors: vec![],
        });
        sig
    }

    fn nat_ty_rt() -> RTerm {
        RTerm::Data(DataName("Nat".into()), vec![], vec![])
    }
    fn zero_rt() -> RTerm {
        RTerm::Con(ConName("zero".into()), vec![])
    }

    #[test]
    fn data_wrong_param_arity_rejected() {
        let sig = nat_vec_sig();
        let rc = Recheck::new(&sig);
        // Nat takes 0 params; supplying one is an arity error.
        let bad = RTerm::Data(DataName("Nat".into()), vec![RTerm::Univ(crate::term::rlevel_of_nat(0))], vec![]);
        assert!(rc.infer(&Ctx::empty(), &bad, RGrade::Zero).is_err());
        // Vec needs 1 param + 1 index; supplying none is an arity error.
        let bad2 = RTerm::Data(DataName("Vec".into()), vec![], vec![]);
        assert!(rc.infer(&Ctx::empty(), &bad2, RGrade::Zero).is_err());
    }

    #[test]
    fn data_param_not_a_type_rejected() {
        let sig = nat_vec_sig();
        let rc = Recheck::new(&sig);
        // Vec's parameter must be a `Type 0`; an `Int` literal is not a type.
        let bad = RTerm::Data(
            DataName("Vec".into()),
            vec![RTerm::IntLit(5)],
            vec![zero_rt()],
        );
        assert!(rc.infer(&Ctx::empty(), &bad, RGrade::Zero).is_err());
    }

    #[test]
    fn data_well_formed_still_accepted() {
        let sig = nat_vec_sig();
        let rc = Recheck::new(&sig);
        // `Vec Nat zero` is well-formed: param `Nat : Type 0`, index `zero : Nat`.
        let ok = RTerm::Data(DataName("Vec".into()), vec![nat_ty_rt()], vec![zero_rt()]);
        assert!(rc.infer(&Ctx::empty(), &ok, RGrade::Zero).is_ok());
    }
}
