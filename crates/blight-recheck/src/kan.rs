//! The re-checker's **independent** model of the cubical Kan table (spec §2.6/§8.3).
//!
//! This mirrors `blight_kernel::kan` but over this crate's own [`RValue`] domain, so the two
//! checkers decide the same Kan reductions by *separate* code. `Comp` is implemented as
//! `HComp` + `Transp` (CCHM). The reductions cover the sound cases the kernel implements:
//! constant lines (identity), the boundary faces of `hcomp`, the constant-tube face, and the
//! structural former dispatch for genuinely heterogeneous `transp` (Π/Σ/PathP) and varying-face
//! `hcomp` (Π/Σ/PathP). A closed-inductive varying-face composite is the documented irreducible
//! base case (the kernel does not produce it for the corpus either).

use crate::normalize::{apply, eval, nf_interval, papp, quote, vfst, vsnd};
use crate::term::{RCofib, RInterval, RTerm};
use crate::value::{Closure, DimClosure, Env, Neutral, RValue};
use blight_kernel::signature::Signature;
use std::rc::Rc;

/// Whether a cofibration is the total face `⊤` after folding.
pub fn is_total(c: &RCofib) -> bool {
    match c {
        RCofib::Top => true,
        RCofib::Bot | RCofib::Eq0(_) | RCofib::Eq1(_) => false,
        RCofib::And(a, b) => is_total(a) && is_total(b),
        RCofib::Or(a, b) => is_total(a) || is_total(b),
    }
}

/// Whether a cofibration is the empty face `⊥` after folding.
pub fn is_empty_face(c: &RCofib) -> bool {
    match c {
        RCofib::Bot => true,
        RCofib::Top | RCofib::Eq0(_) | RCofib::Eq1(_) => false,
        RCofib::And(a, b) => is_empty_face(a) || is_empty_face(b),
        RCofib::Or(a, b) => is_empty_face(a) && is_empty_face(b),
    }
}

/// Whether a dimension line is constant (its endpoints are convertible).
fn family_is_constant(sig: &Signature, family: &DimClosure) -> bool {
    let a0 = family.apply_dim(sig, RInterval::I0);
    let a1 = family.apply_dim(sig, RInterval::I1);
    crate::conv::conv(sig, 0, 0, &a0, &a1)
}

/// Build a dimension line `i. project(A i)` from a family, quoting the projection under one dim.
fn line_closure(
    sig: &Signature,
    family: &DimClosure,
    project: impl Fn(RValue) -> RValue,
) -> DimClosure {
    let projected = project(family.apply_dim(sig, RInterval::Dim(0)));
    let body = quote(sig, 0, 1, &projected);
    DimClosure {
        env: Env::new(),
        body: Rc::new(body),
    }
}

/// `transp (i. A) φ a0`. Mirrors `blight_kernel::kan::transp`.
pub fn transp(sig: &Signature, family: &DimClosure, cofib: &RCofib, base: &RValue) -> RValue {
    if is_total(cofib) || family_is_constant(sig, family) {
        return base.clone();
    }
    let a_open = family.apply_dim(sig, RInterval::Dim(0));
    match a_open {
        RValue::Univ(_) => base.clone(),
        RValue::Data(_, ps, is) if ps.is_empty() && is.is_empty() => base.clone(),
        RValue::Pi(..) => transp_pi(sig, family, base),
        RValue::Sigma(..) => transp_sigma(sig, family, base),
        RValue::PathP { .. } => transp_path(sig, family, base),
        // No `Glue` arm by design: the re-checker *declines* any judgement mentioning `Glue` during
        // `from_kernel` (see `term.rs`), so a Glue line can never reach here — the trusted kernel
        // owns the univalence Kan-Glue reduction, and the independent checker deliberately does not
        // duplicate it. The residual heads (non-constant indexed-`Data`/`Int`/`Eff` lines) are
        // unreachable from the corpus (all constant ⟹ caught by `family_is_constant` above); we
        // *fail safe* (panic) rather than risk a silent mis-reduction, mirroring `blight_kernel`.
        _ => unimplemented!(
            "recheck transp: unsupported heterogeneous former (Pi/Sigma/PathP/Data/Univ implemented; \
             Glue is declined upstream; a non-constant indexed/Int/Eff line is unreachable from the \
             corpus and fail-safe, never an acceptance)"
        ),
    }
}

fn line_reverse(sig: &Signature, family: &DimClosure) -> DimClosure {
    let projected = family.apply_dim(sig, RInterval::Neg(Box::new(RInterval::Dim(0))));
    let body = quote(sig, 0, 1, &projected);
    DimClosure {
        env: Env::new(),
        body: Rc::new(body),
    }
}

/// The *partial transport line* `j. transpFill^i A φ a0` — mirrors the kernel's `transp_fill_line`
/// (`kernel/kan.rs`). At `j = i0` it is `a0`; at `j = i1` it is the full `transp`. Realized as the
/// closure `j. transp (i. A(i ∧ j)) ⊥ a0`, quoting the `Transp` *term* (not its forced value) so
/// the `j`-dependence is preserved structurally.
fn transp_fill_line(
    sig: &Signature,
    family: &DimClosure,
    _cofib: &RCofib,
    base: &RValue,
) -> DimClosure {
    let inner_line_body = {
        // Project `A` at the conjunction of the inner bound dim (0) and the outer fill dim (1).
        let projected = family.apply_dim(
            sig,
            RInterval::Min(Box::new(RInterval::Dim(0)), Box::new(RInterval::Dim(1))),
        );
        // Quote under two dimension binders (inner `i` = 0, outer `j` = 1).
        quote(sig, 0, 2, &projected)
    };
    let base_body = quote(sig, 0, 1, base);
    let transp_term = RTerm::Transp {
        family: Box::new(inner_line_body),
        cofib: RCofib::Bot,
        base: Box::new(base_body),
    };
    DimClosure {
        env: Env::new(),
        body: Rc::new(transp_term),
    }
}

fn transp_pi(sig: &Signature, family: &DimClosure, f: &RValue) -> RValue {
    let dom_line = line_closure(sig, family, |a| match a {
        RValue::Pi(_, d, _) => (*d).clone(),
        other => other,
    });
    let x1 = RValue::Neutral(Neutral::Var(0));
    let x0 = if family_is_constant(sig, &dom_line) {
        x1.clone()
    } else {
        let rev = line_reverse(sig, &dom_line);
        transp(sig, &rev, &RCofib::Bot, &x1)
    };
    let cod_line = {
        let projected = match family.apply_dim(sig, RInterval::Dim(0)) {
            RValue::Pi(_, _, cod) => cod.apply(sig, x1.clone()),
            other => other,
        };
        let body = quote(sig, 1, 1, &projected);
        DimClosure {
            env: Env::new(),
            body: Rc::new(body),
        }
    };
    let fx0 = apply(sig, f.clone(), x0);
    let transported = transp(sig, &cod_line, &RCofib::Bot, &fx0);
    let body = quote(sig, 1, 0, &transported);
    RValue::Lam(Closure {
        env: Env::new(),
        body: Rc::new(body),
    })
}

fn transp_sigma(sig: &Signature, family: &DimClosure, pair: &RValue) -> RValue {
    let (a0, b0) = match pair {
        RValue::Pair(a, b) => ((**a).clone(), (**b).clone()),
        other => (vfst(other.clone()), vsnd(sig, other.clone())),
    };
    let fst_line = line_closure(sig, family, |a| match a {
        RValue::Sigma(d, _) => (*d).clone(),
        other => other,
    });
    let a1 = transp(sig, &fst_line, &RCofib::Bot, &a0);
    // Second-component line at the FILL of the first component: `i. B i (afill i)` (soundness
    // audit 2026-07-03, R-P5, mirroring the kernel's `transp_sigma`). With a constant
    // first-component line the fill is constant `= a0`, recovering `i. B i a0`; with a genuinely
    // varying one, instantiating `B` at the source `a0` (the previous behavior) diverged from the
    // kernel. (Reachability: a varying first-component *type* line requires a path between distinct
    // types, i.e. a `ua`/`Glue`, which the re-checker *declines* — so this branch is defensive.)
    let snd_line = if family_is_constant(sig, &fst_line) {
        let a0c = a0.clone();
        line_closure(sig, family, move |a| match a {
            RValue::Sigma(_, cod) => cod.apply(sig, a0c.clone()),
            other => other,
        })
    } else {
        let fill = transp_fill_line(sig, &fst_line, &RCofib::Bot, &a0);
        let projected = match family.apply_dim(sig, RInterval::Dim(0)) {
            RValue::Sigma(_, cod) => {
                let a_here = fill.apply_dim(sig, RInterval::Dim(0));
                cod.apply(sig, a_here)
            }
            other => other,
        };
        let body = quote(sig, 0, 1, &projected);
        DimClosure {
            env: Env::new(),
            body: Rc::new(body),
        }
    };
    let b1 = transp(sig, &snd_line, &RCofib::Bot, &b0);
    RValue::Pair(Rc::new(a1), Rc::new(b1))
}

fn transp_path(sig: &Signature, family: &DimClosure, path: &RValue) -> RValue {
    let inner_family_body = {
        let projected = match family.apply_dim(sig, RInterval::Dim(0)) {
            RValue::PathP { family: inner, .. } => inner.apply_dim(sig, RInterval::Dim(1)),
            other => other,
        };
        quote(sig, 0, 2, &projected)
    };
    let base_body = {
        let pj = papp(sig, path.clone(), RInterval::Dim(0));
        quote(sig, 0, 1, &pj)
    };
    let comp_term = RTerm::Comp {
        family: Box::new(inner_family_body),
        cofib: RCofib::Bot,
        tube: Box::new(base_body.clone()),
        base: Box::new(base_body),
    };
    RValue::PLam(DimClosure {
        env: Env::new(),
        body: Rc::new(comp_term),
    })
}

/// `hcomp A φ (i. u) a0`. Mirrors `blight_kernel::kan::hcomp`.
pub fn hcomp(
    sig: &Signature,
    ty: &RValue,
    cofib: &RCofib,
    tube: &DimClosure,
    base: &RValue,
) -> RValue {
    if is_empty_face(cofib) {
        return base.clone();
    }
    if is_total(cofib) {
        return tube.apply_dim(sig, RInterval::I1);
    }
    if family_is_constant(sig, tube) {
        return base.clone();
    }
    match ty {
        RValue::Sigma(dom, cod) => {
            let fst_tube = project_line(sig, tube, vfst);
            let fst_base = vfst(base.clone());
            let a1 = hcomp(sig, dom, cofib, &fst_tube, &fst_base);
            let snd_tube = project_line(sig, tube, |v| vsnd(sig, v));
            let snd_base = vsnd(sig, base.clone());
            let snd_ty = cod.apply(sig, a1.clone());
            let b1 = hcomp(sig, &snd_ty, cofib, &snd_tube, &snd_base);
            RValue::Pair(Rc::new(a1), Rc::new(b1))
        }
        RValue::Pi(_, _, cod) => {
            let x = RValue::Neutral(Neutral::Var(0));
            let cod_ty = cod.apply(sig, x.clone());
            let applied_tube = apply_line(sig, tube, x.clone());
            let fx = apply(sig, base.clone(), x);
            let body_val = hcomp(sig, &cod_ty, cofib, &applied_tube, &fx);
            let body = quote(sig, 1, 0, &body_val);
            RValue::Lam(Closure {
                env: Env::new(),
                body: Rc::new(body),
            })
        }
        RValue::PathP { family, .. } => {
            let inner_ty = family.apply_dim(sig, RInterval::Dim(0));
            let papp_tube = papp_line(sig, tube, RInterval::Dim(0));
            let base_papp = papp(sig, base.clone(), RInterval::Dim(0));
            let inner_ty_q = quote(sig, 0, 1, &inner_ty);
            let tube_q = quote(sig, 0, 2, &papp_tube.apply_dim(sig, RInterval::Dim(0)));
            let hc = RTerm::HComp {
                ty: Box::new(inner_ty_q),
                cofib: cofib.clone(),
                tube: Box::new(tube_q),
                base: Box::new(quote(sig, 0, 1, &base_papp)),
            };
            RValue::PLam(DimClosure {
                env: Env::new(),
                body: Rc::new(hc),
            })
        }
        // Mirrors `blight_kernel::kan::hcomp`: Π/Σ/PathP compose structurally above; a varying face
        // in a closed inductive/universe/Glue needs the system machinery the value domain does not
        // represent and is unreachable from the corpus (Glue is declined upstream). Fail-safe panic,
        // never a silent acceptance.
        _ => unimplemented!(
            "recheck hcomp: varying face in a closed inductive/universe/Glue (unreachable from the \
             corpus; fail-safe, never an acceptance)"
        ),
    }
}

fn project_line(
    sig: &Signature,
    tube: &DimClosure,
    project: impl Fn(RValue) -> RValue,
) -> DimClosure {
    let projected = project(tube.apply_dim(sig, RInterval::Dim(0)));
    DimClosure {
        env: Env::new(),
        body: Rc::new(quote(sig, 0, 1, &projected)),
    }
}

fn apply_line(sig: &Signature, tube: &DimClosure, x: RValue) -> DimClosure {
    let applied = apply(sig, tube.apply_dim(sig, RInterval::Dim(0)), x);
    DimClosure {
        env: Env::new(),
        body: Rc::new(quote(sig, 1, 1, &applied)),
    }
}

fn papp_line(sig: &Signature, tube: &DimClosure, r: RInterval) -> DimClosure {
    let applied = papp(sig, tube.apply_dim(sig, RInterval::Dim(0)), r);
    DimClosure {
        env: Env::new(),
        body: Rc::new(quote(sig, 0, 2, &applied)),
    }
}

/// `comp (i. A) φ (i. u) a0` — derived as `hcomp` over the transported base (CCHM).
pub fn comp(
    sig: &Signature,
    family: &DimClosure,
    cofib: &RCofib,
    tube: &DimClosure,
    base: &RValue,
) -> RValue {
    let transported = transp(sig, family, &RCofib::Bot, base);
    let target_ty = family.apply_dim(sig, RInterval::I1);
    hcomp(sig, &target_ty, cofib, tube, &transported)
}

/// Resolve a cofibration's free dimensions against the environment (mirrors interval resolution),
/// then fold endpoints. Used by `eval` so a Kan op's face is decided in the current dim context.
pub fn resolve_cofib(env: &Env, c: &RCofib) -> RCofib {
    match c {
        RCofib::Top => RCofib::Top,
        RCofib::Bot => RCofib::Bot,
        RCofib::Eq0(r) => fold_eq(crate::normalize::eval_interval(env, r), true),
        RCofib::Eq1(r) => fold_eq(crate::normalize::eval_interval(env, r), false),
        RCofib::And(a, b) => RCofib::And(
            Box::new(resolve_cofib(env, a)),
            Box::new(resolve_cofib(env, b)),
        ),
        RCofib::Or(a, b) => RCofib::Or(
            Box::new(resolve_cofib(env, a)),
            Box::new(resolve_cofib(env, b)),
        ),
    }
}

/// Fold a resolved `r = 0` (or `r = 1`) face to `⊤`/`⊥` when `r` is a constant endpoint.
fn fold_eq(r: RInterval, is_zero: bool) -> RCofib {
    match (nf_interval(&r), is_zero) {
        (RInterval::I0, true) | (RInterval::I1, false) => RCofib::Top,
        (RInterval::I1, true) | (RInterval::I0, false) => RCofib::Bot,
        (other, true) => RCofib::Eq0(other),
        (other, false) => RCofib::Eq1(other),
    }
}

/// Evaluate the three Kan terms (called from `eval`). Builds the dimension closures and dispatches.
pub fn eval_transp(
    sig: &Signature,
    env: &Env,
    family: &RTerm,
    cofib: &RCofib,
    base: &RTerm,
) -> RValue {
    let fam = DimClosure {
        env: env.clone(),
        body: Rc::new(family.clone()),
    };
    let cof = resolve_cofib(env, cofib);
    let b = eval(sig, env, base);
    transp(sig, &fam, &cof, &b)
}

pub fn eval_hcomp(
    sig: &Signature,
    env: &Env,
    ty: &RTerm,
    cofib: &RCofib,
    tube: &RTerm,
    base: &RTerm,
) -> RValue {
    let t = eval(sig, env, ty);
    let cof = resolve_cofib(env, cofib);
    let tube_clos = DimClosure {
        env: env.clone(),
        body: Rc::new(tube.clone()),
    };
    let b = eval(sig, env, base);
    hcomp(sig, &t, &cof, &tube_clos, &b)
}

pub fn eval_comp(
    sig: &Signature,
    env: &Env,
    family: &RTerm,
    cofib: &RCofib,
    tube: &RTerm,
    base: &RTerm,
) -> RValue {
    let fam = DimClosure {
        env: env.clone(),
        body: Rc::new(family.clone()),
    };
    let cof = resolve_cofib(env, cofib);
    let tube_clos = DimClosure {
        env: env.clone(),
        body: Rc::new(tube.clone()),
    };
    let b = eval(sig, env, base);
    comp(sig, &fam, &cof, &tube_clos, &b)
}

// =================================================================================================
// White-box conformance tests (Track M1: this file was at 0% coverage). These pin down the
// dispatch table directly on hand-built [`RValue`]/[`RTerm`]s, mirroring `blight_kernel::kan`'s own
// white-box suite: boundary faces first, then the genuinely heterogeneous Π/Σ/PathP structural
// branches, then the two documented fail-safe `unimplemented!` arms as negative goldens.
//
// A key technique used throughout: [`RTerm::Var`] at a deliberately huge, always-out-of-range index
// (`FREE`) always evaluates to the `usize::MAX` "unbound sentinel" neutral (see `eval`'s `Var` arm
// and `quote_neutral`'s special-case for it), *regardless of the ambient env's depth or the current
// quoting `lvl`*. Applying it via `PApp` at the line's own bound dimension (`dim_dep`) then gives a
// value that is *genuinely* non-constant across `i` — `PApp(Var(MAX), I0)` vs `PApp(Var(MAX), I1)`
// are different neutrals by `conv`'s structural-quote comparison — without needing any indexed
// `Data`/`Glue` type variance (which this crate's value domain cannot represent; `Glue` is declined
// upstream). This is what lets these tests force the real Π/Σ/PathP structural dispatch rather than
// only ever hitting `family_is_constant`'s early-return fast path.
// =================================================================================================
#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::RGrade;
    use blight_kernel::{ConName, DataName};

    fn sig() -> Signature {
        Signature::new()
    }

    /// `RValue` has no `PartialEq` (its neutrals need level-aware quoting to compare); use the
    /// crate's own `conv` for value equality throughout, exactly as the checker itself would.
    fn veq(s: &Signature, a: &RValue, b: &RValue) -> bool {
        crate::conv::conv(s, 0, 0, a, b)
    }

    /// Always out of range for any env this file's tests build, so `eval`'s `Var` arm falls back to
    /// the `usize::MAX` unbound sentinel every time (see module doc above).
    const FREE: usize = 9999;

    fn nat_t() -> RTerm {
        RTerm::Data(DataName("Nat".into()), vec![], vec![])
    }
    fn zero_t() -> RTerm {
        RTerm::Con(ConName("Zero".into()), vec![])
    }
    fn zero_v() -> RValue {
        RValue::Con(ConName("Zero".into()), Rc::new(vec![]))
    }
    fn succ_v(v: RValue) -> RValue {
        RValue::Con(ConName("Succ".into()), Rc::new(vec![v]))
    }
    fn univ(n: u32) -> RValue {
        RValue::Univ(crate::term::rlevel_of_nat(n))
    }
    fn const_line(body: RTerm) -> DimClosure {
        DimClosure {
            env: Env::new(),
            body: Rc::new(body),
        }
    }
    /// `Var(FREE) @ i` — a term that, evaluated under any env, is `PApp(Var(MAX), <current dim>)`:
    /// genuinely different at `i=0` vs `i=1` (see module doc).
    fn dim_dep() -> RTerm {
        RTerm::PApp(Box::new(RTerm::Var(FREE)), RInterval::Dim(0))
    }

    // ---- boundary goldens (mirrors blight_kernel::kan's own suite) ----

    #[test]
    fn transp_constant_family_is_identity() {
        let s = sig();
        let out = transp(&s, &const_line(RTerm::Univ(crate::term::rlevel_of_nat(0))), &RCofib::Top, &univ(0));
        assert!(veq(&s, &out, &univ(0)));
    }

    #[test]
    fn transp_const_nat_is_identity() {
        let s = sig();
        let line = const_line(nat_t());
        let out = transp(&s, &line, &RCofib::Bot, &zero_v());
        assert!(veq(&s, &out, &zero_v()));
    }

    #[test]
    fn transp_const_pi_is_identity() {
        let s = sig();
        let pi = RTerm::Pi(RGrade::Omega, Box::new(nat_t()), Box::new(nat_t()));
        let line = const_line(pi);
        let f = RValue::Lam(Closure {
            env: Env::new(),
            body: Rc::new(RTerm::Var(0)),
        });
        let out = transp(&s, &line, &RCofib::Bot, &f);
        assert!(veq(&s, &out, &f));
    }

    #[test]
    fn transp_const_sigma_is_identity() {
        let s = sig();
        let sigma = RTerm::Sigma(Box::new(nat_t()), Box::new(nat_t()));
        let line = const_line(sigma);
        let pair = RValue::Pair(Rc::new(zero_v()), Rc::new(zero_v()));
        let out = transp(&s, &line, &RCofib::Bot, &pair);
        assert!(veq(&s, &out, &pair));
    }

    #[test]
    fn transp_const_path_is_identity() {
        let s = sig();
        let path = RTerm::PathP {
            family: Box::new(nat_t()),
            lhs: Box::new(zero_t()),
            rhs: Box::new(zero_t()),
        };
        let line = const_line(path);
        let p = RValue::PLam(const_line(zero_t()));
        let out = transp(&s, &line, &RCofib::Bot, &p);
        assert!(veq(&s, &out, &p));
    }

    #[test]
    fn hcomp_total_cofib_picks_tube_at_i1() {
        let s = sig();
        let out = hcomp(
            &s,
            &univ(0),
            &RCofib::Top,
            &const_line(RTerm::Univ(crate::term::rlevel_of_nat(0))),
            &univ(1),
        );
        assert!(veq(&s, &out, &univ(0)), "total face: composite is tube@1");
    }

    #[test]
    fn hcomp_empty_cofib_picks_base() {
        let s = sig();
        let out = hcomp(
            &s,
            &univ(0),
            &RCofib::Bot,
            &const_line(RTerm::Univ(crate::term::rlevel_of_nat(0))),
            &univ(1),
        );
        assert!(veq(&s, &out, &univ(1)));
    }

    #[test]
    fn hcomp_partial_constant_tube_picks_base() {
        let s = sig();
        let partial = RCofib::Eq0(RInterval::Dim(0));
        assert!(!is_total(&partial) && !is_empty_face(&partial));
        let out = hcomp(
            &s,
            &univ(0),
            &partial,
            &const_line(RTerm::Univ(crate::term::rlevel_of_nat(1))),
            &univ(1),
        );
        assert!(
            veq(&s, &out, &univ(1)),
            "constant tube: degenerate box is the floor"
        );
    }

    #[test]
    fn comp_agrees_with_hcomp_transp() {
        let s = sig();
        let family = const_line(RTerm::Univ(crate::term::rlevel_of_nat(0)));
        let tube = const_line(RTerm::Univ(crate::term::rlevel_of_nat(0)));
        let base = univ(0);
        let out = comp(&s, &family, &RCofib::Top, &tube, &base);
        let manual = hcomp(
            &s,
            &family.apply_dim(&s, RInterval::I1),
            &RCofib::Top,
            &tube,
            &transp(&s, &family, &RCofib::Bot, &base),
        );
        assert!(veq(&s, &out, &manual));
    }

    // ---- heterogeneous `transp` (Track M1: the previously-untested bulk of this file) ----

    /// A genuinely non-constant `PathP` line (`family_is_constant` must independently agree it's
    /// non-constant — asserted directly, not just inferred from the output shape). `transp_path`
    /// never recurses into `transp`/`hcomp` (it defers to a lazily-built `Comp` term), so this is
    /// safe to force regardless of what the varying endpoint "means".
    #[test]
    fn transp_path_heterogeneous_line_is_plam() {
        let s = sig();
        let path = RTerm::PathP {
            family: Box::new(nat_t()),
            lhs: Box::new(dim_dep()),
            rhs: Box::new(zero_t()),
        };
        let family = const_line(path);
        assert!(
            !family_is_constant(&s, &family),
            "the line's lhs genuinely varies (PApp(Var(MAX), i)), so the line must be non-constant"
        );
        let base = RValue::PLam(const_line(zero_t()));
        let out = transp(&s, &family, &RCofib::Bot, &base);
        assert!(
            matches!(out, RValue::PLam(_)),
            "transp over a heterogeneous PathP line is a path value, got {out:?}"
        );
    }

    /// A genuinely non-constant `Pi` line whose codomain is `PathP`-shaped (so the recursive
    /// `transp` call inside `transp_pi` safely lands in the non-panicking `transp_path` arm). Forces
    /// `transp_pi`'s real body: the constant-domain `x0 = x1` branch and the codomain-line recursion.
    #[test]
    fn transp_pi_heterogeneous_line_is_lambda() {
        let s = sig();
        // i. Π (_ : Nat). PathP (j. Nat) (Var(FREE) @ i) Zero — non-constant via the codomain.
        let cod = RTerm::PathP {
            family: Box::new(nat_t()),
            lhs: Box::new(dim_dep()),
            rhs: Box::new(zero_t()),
        };
        let pi = RTerm::Pi(RGrade::Omega, Box::new(nat_t()), Box::new(cod));
        let family = const_line(pi);
        assert!(
            !family_is_constant(&s, &family),
            "the codomain's path endpoint varies with i, so the Pi line must be non-constant"
        );
        // base: λ_. λj. Zero — ignores its argument, always the constant path.
        let f = RValue::Lam(Closure {
            env: Env::new(),
            body: Rc::new(RTerm::PLam(Box::new(zero_t()))),
        });
        let out = transp(&s, &family, &RCofib::Bot, &f);
        assert!(
            matches!(out, RValue::Lam(_)),
            "transp over a heterogeneous Pi line is a function value, got {out:?}"
        );
    }

    /// A genuinely non-constant `Sigma` line (constant `Nat` first component, `PathP`-shaped second
    /// component that varies). Forces `transp_sigma`'s real body: the constant-domain identity on
    /// the first component and the codomain-line recursion (safely landing in `transp_path`) on the
    /// second.
    #[test]
    fn transp_sigma_heterogeneous_line_is_pair() {
        let s = sig();
        let cod = RTerm::PathP {
            family: Box::new(nat_t()),
            lhs: Box::new(dim_dep()),
            rhs: Box::new(zero_t()),
        };
        let sigma = RTerm::Sigma(Box::new(nat_t()), Box::new(cod));
        let family = const_line(sigma);
        assert!(!family_is_constant(&s, &family));
        let pair = RValue::Pair(
            Rc::new(zero_v()),
            Rc::new(RValue::PLam(const_line(zero_t()))),
        );
        let out = transp(&s, &family, &RCofib::Bot, &pair);
        match &out {
            RValue::Pair(a1, b1) => {
                assert!(
                    veq(&s, a1, &zero_v()),
                    "constant Nat first component transports as identity"
                );
                assert!(
                    matches!(**b1, RValue::PLam(_)),
                    "the varying second component transports to a path value, got {b1:?}"
                );
            }
            other => panic!("transp over a heterogeneous Sigma line is a pair, got {other:?}"),
        }
    }

    /// R-P5 (soundness audit 2026-07-03): `transp_fill_line` (ported to keep `transp_sigma`'s
    /// second-component line at the *fill* of the first component, mirroring the kernel) is the
    /// identity on a constant type line — `base` at both endpoints. This is the only reachable
    /// input: a genuinely *varying* first-component type line needs a path between distinct types
    /// (a `ua`/`Glue`), which the re-checker declines, so the divergent branch is unreachable and
    /// the fix is defensive parity with the mechanized kernel.
    #[test]
    fn transp_fill_line_is_identity_on_a_constant_family() {
        let s = sig();
        let family = const_line(nat_t()); // i. Nat — constant
        let base = succ_v(zero_v());
        let fill = transp_fill_line(&s, &family, &RCofib::Bot, &base);
        assert!(
            veq(&s, &fill.apply_dim(&s, RInterval::I0), &base),
            "fill at j=i0 is base"
        );
        assert!(
            veq(&s, &fill.apply_dim(&s, RInterval::I1), &base),
            "fill at j=i1 is base (constant line ⇒ identity transport)"
        );
    }

    // ---- varying-face `hcomp` (Track M1) ----

    /// A genuinely non-constant tube whose second component (fixed `PathP`-typed) varies, forcing
    /// the Σ structural branch: the first (`Nat`-typed) component's tube is constant (identity), the
    /// second recurses into the safe, non-panicking PathP `hcomp` arm.
    #[test]
    fn hcomp_sigma_varying_face_is_componentwise() {
        let s = sig();
        let partial = RCofib::Eq0(RInterval::Dim(3));
        assert!(!is_total(&partial) && !is_empty_face(&partial));
        let sigma_ty = RValue::Sigma(
            Rc::new(RValue::Data(DataName("Nat".into()), Rc::new(vec![]), Rc::new(vec![]))),
            Closure {
                env: Env::new(),
                body: Rc::new(RTerm::PathP {
                    family: Box::new(nat_t()),
                    lhs: Box::new(zero_t()),
                    rhs: Box::new(zero_t()),
                }),
            },
        );
        let tube = DimClosure {
            env: Env::new(),
            body: Rc::new(RTerm::Pair(Box::new(zero_t()), Box::new(dim_dep()))),
        };
        assert!(
            !family_is_constant(&s, &tube),
            "the tube's second component genuinely varies"
        );
        let base = RValue::Pair(
            Rc::new(zero_v()),
            Rc::new(RValue::PLam(const_line(zero_t()))),
        );
        let out = hcomp(&s, &sigma_ty, &partial, &tube, &base);
        match &out {
            RValue::Pair(a1, b1) => {
                assert!(
                    veq(&s, a1, &zero_v()),
                    "the constant-tube first component picks the floor"
                );
                assert!(
                    matches!(**b1, RValue::PLam(_)),
                    "the varying second component composes to a path value, got {b1:?}"
                );
            }
            other => panic!("Σ hcomp composes to a pair, got {other:?}"),
        }
    }

    /// Mirrors `blight_kernel::kan::hcomp_pi_varying_face_is_lambda` exactly (same tube shape, same
    /// `Nat` codomain): a tube whose body syntactically mentions the transport dimension `i` via a
    /// `PLam`/`PApp` redex that beta-reduces to the same closed value regardless of `i`. Both
    /// checkers therefore fold this to the constant-tube fast path (`family_is_constant`) rather
    /// than forcing the Π structural recursion — a `PathP`/`Pi`-shaped codomain would instead force
    /// `hcomp` to eventually re-derive `hcomp` at the closed `Nat` type with a *still-varying* tube,
    /// which is the documented fail-safe case (see `hcomp_pi_deep_varying_codomain_fails_safe`
    /// below). The Π branch's live structural code is exercised transitively via `hcomp_sigma_...`.
    #[test]
    fn hcomp_pi_varying_face_is_lambda() {
        let s = sig();
        let partial = RCofib::Eq0(RInterval::Dim(1));
        let pi_ty = RValue::Pi(
            RGrade::Omega,
            Rc::new(RValue::Data(DataName("Nat".into()), Rc::new(vec![]), Rc::new(vec![]))),
            Closure {
                env: Env::new(),
                body: Rc::new(nat_t()),
            },
        );
        // i. λ_. ((λj. zero) @ i) — mentions `i` syntactically but beta-reduces to a constant `zero`.
        let tube = DimClosure {
            env: Env::new(),
            body: Rc::new(RTerm::Lam(Box::new(RTerm::PApp(
                Box::new(RTerm::PLam(Box::new(zero_t()))),
                RInterval::Dim(0),
            )))),
        };
        let base = RValue::Lam(Closure {
            env: Env::new(),
            body: Rc::new(RTerm::Var(0)),
        });
        let out = hcomp(&s, &pi_ty, &partial, &tube, &base);
        assert!(
            matches!(out, RValue::Lam(_)),
            "Π hcomp composes to a λ, got {out:?}"
        );
    }

    /// The fail-safe counterpart: a Π codomain that is itself `PathP`-over-`Nat`, with a tube that
    /// remains *genuinely* non-constant after applying the codomain's bound variable. Forcing the
    /// outer Lam's body (via `quote`) drives the lazily-built inner `HComp` term (from the PathP
    /// branch) to actually re-evaluate `hcomp` at the closed `Nat` type with a varying tube — exactly
    /// the documented-unreachable case at line 229. Pins that the Π branch's recursion, when it
    /// *does* bottom out at a closed inductive with real variance, still fails safe rather than
    /// silently mis-composing.
    #[test]
    #[should_panic(expected = "varying face in a closed inductive/universe/Glue")]
    fn hcomp_pi_deep_varying_codomain_fails_safe() {
        let s = sig();
        let partial = RCofib::Eq0(RInterval::Dim(3));
        let pi_ty = RValue::Pi(
            RGrade::Omega,
            Rc::new(RValue::Data(DataName("Nat".into()), Rc::new(vec![]), Rc::new(vec![]))),
            Closure {
                env: Env::new(),
                body: Rc::new(RTerm::PathP {
                    family: Box::new(nat_t()),
                    lhs: Box::new(zero_t()),
                    rhs: Box::new(zero_t()),
                }),
            },
        );
        let tube = DimClosure {
            env: Env::new(),
            body: Rc::new(RTerm::Lam(Box::new(dim_dep()))),
        };
        let base = RValue::Lam(Closure {
            env: Env::new(),
            body: Rc::new(RTerm::PLam(Box::new(zero_t()))),
        });
        let _ = hcomp(&s, &pi_ty, &partial, &tube, &base);
    }

    // ---- fail-safe goldens: the two `unimplemented!` arms must panic, never silently mis-reduce ----

    /// `transp` over a genuinely non-constant line whose head former is an indexed `Data` (params
    /// non-empty) is out of the implemented fragment (§1.3 obligation 2, Track M3) and must fail
    /// safe rather than silently fall through to the paramless-`Data` identity rule.
    #[test]
    #[should_panic(expected = "unsupported heterogeneous former")]
    fn transp_indexed_data_line_fails_safe() {
        let s = sig();
        // i. Vec (Var(FREE) @ i) — a "Data" line whose one param genuinely varies with i.
        let line = const_line(RTerm::Data(DataName("Vec".into()), vec![dim_dep()], vec![]));
        let _ = transp(&s, &line, &RCofib::Bot, &zero_v());
    }

    /// `hcomp` over a varying face whose type is not Π/Σ/PathP (here a bare universe) is out of the
    /// implemented fragment and must fail safe.
    #[test]
    #[should_panic(expected = "varying face in a closed inductive/universe/Glue")]
    fn hcomp_non_structural_type_fails_safe() {
        let s = sig();
        let partial = RCofib::Eq0(RInterval::Dim(3));
        let tube = DimClosure {
            env: Env::new(),
            body: Rc::new(dim_dep()),
        };
        let _ = hcomp(&s, &univ(0), &partial, &tube, &univ(1));
    }

    #[test]
    fn resolve_cofib_folds_constant_endpoints() {
        let env = Env::new().extend_dim(RInterval::I0);
        assert_eq!(
            resolve_cofib(&env, &RCofib::Eq0(RInterval::Dim(0))),
            RCofib::Top
        );
        assert_eq!(
            resolve_cofib(&env, &RCofib::Eq1(RInterval::Dim(0))),
            RCofib::Bot
        );
    }

    #[test]
    fn succ_v_helper_builds_a_con() {
        // Sanity for the `succ_v` test helper itself (kept for potential future Nat-shaped goldens).
        let s = sig();
        assert!(veq(
            &s,
            &succ_v(zero_v()),
            &RValue::Con(ConName("Succ".into()), Rc::new(vec![zero_v()]))
        ));
    }
}
