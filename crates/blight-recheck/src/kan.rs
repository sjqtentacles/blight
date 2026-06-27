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
        _ => unimplemented!("recheck transp: unsupported heterogeneous former"),
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
    let a0c = a0.clone();
    let snd_line = line_closure(sig, family, move |a| match a {
        RValue::Sigma(_, cod) => cod.apply(sig, a0c.clone()),
        other => other,
    });
    let b1 = transp(sig, &snd_line, &RCofib::Bot, &b0);
    RValue::Pair(Box::new(a1), Box::new(b1))
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
            RValue::Pair(Box::new(a1), Box::new(b1))
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
        _ => unimplemented!("recheck hcomp: varying face in a closed inductive/universe"),
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
