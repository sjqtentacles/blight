//! Definitional equality (`conv`) on values, with η for functions, pairs, and paths — mirroring
//! the kernel's `conv`. Operates over this crate's [`RValue`], comparing neutrals by quoting.

use crate::normalize::{apply, papp, quote, reflect, vfst, vsnd};
use crate::term::RInterval;
use crate::value::{Neutral, RValue};
use blight_kernel::signature::Signature;

/// Are two values definitionally equal at term-level `lvl`, dimension-level `dlvl`?
pub fn conv(sig: &Signature, lvl: usize, dlvl: usize, a: &RValue, b: &RValue) -> bool {
    // η for functions.
    if is_fun(a) || is_fun(b) {
        let fresh = RValue::Neutral(Neutral::Var(lvl));
        return conv(
            sig,
            lvl + 1,
            dlvl,
            &apply(sig, a.clone(), fresh.clone()),
            &apply(sig, b.clone(), fresh),
        );
    }
    // η for pairs.
    if matches!(a, RValue::Pair(..)) || matches!(b, RValue::Pair(..)) {
        return conv(sig, lvl, dlvl, &vfst(a.clone()), &vfst(b.clone()))
            && conv(sig, lvl, dlvl, &vsnd(sig, a.clone()), &vsnd(sig, b.clone()));
    }
    // η for paths.
    if is_path(a) || is_path(b) {
        let fresh = RInterval::Dim(dlvl);
        return conv(
            sig,
            lvl,
            dlvl + 1,
            &papp(sig, a.clone(), fresh.clone()),
            &papp(sig, b.clone(), fresh),
        );
    }

    match (a, b) {
        (RValue::Univ(l1), RValue::Univ(l2)) => l1 == l2,
        (RValue::Pi(g1, d1, c1), RValue::Pi(g2, d2, c2)) => {
            g1 == g2 && conv(sig, lvl, dlvl, d1, d2) && {
                let fresh = RValue::Neutral(Neutral::Var(lvl));
                conv(
                    sig,
                    lvl + 1,
                    dlvl,
                    &c1.apply(sig, fresh.clone()),
                    &c2.apply(sig, fresh),
                )
            }
        }
        (RValue::Sigma(d1, c1), RValue::Sigma(d2, c2)) => {
            conv(sig, lvl, dlvl, d1, d2) && {
                let fresh = RValue::Neutral(Neutral::Var(lvl));
                conv(
                    sig,
                    lvl + 1,
                    dlvl,
                    &c1.apply(sig, fresh.clone()),
                    &c2.apply(sig, fresh),
                )
            }
        }
        (
            RValue::PathP {
                family: f1,
                lhs: l1,
                rhs: r1,
            },
            RValue::PathP {
                family: f2,
                lhs: l2,
                rhs: r2,
            },
        ) => {
            let fresh = RInterval::Dim(dlvl);
            conv(
                sig,
                lvl,
                dlvl + 1,
                &f1.apply_dim(sig, fresh.clone()),
                &f2.apply_dim(sig, fresh),
            ) && conv(sig, lvl, dlvl, l1, l2)
                && conv(sig, lvl, dlvl, r1, r2)
        }
        (RValue::Data(n1, p1, i1), RValue::Data(n2, p2, i2)) => {
            n1 == n2
                && p1.len() == p2.len()
                && i1.len() == i2.len()
                && p1
                    .iter()
                    .zip(p2.iter())
                    .all(|(x, y)| conv(sig, lvl, dlvl, x, y))
                && i1
                    .iter()
                    .zip(i2.iter())
                    .all(|(x, y)| conv(sig, lvl, dlvl, x, y))
        }
        (RValue::Con(n1, a1), RValue::Con(n2, a2)) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(x, y)| conv(sig, lvl, dlvl, x, y))
        }
        (RValue::Neutral(n1), RValue::Neutral(n2)) => {
            quote(sig, lvl, dlvl, &RValue::Neutral(n1.clone()))
                == quote(sig, lvl, dlvl, &RValue::Neutral(n2.clone()))
        }
        (RValue::Interval(r1), RValue::Interval(r2)) => {
            crate::normalize::nf_interval(r1) == crate::normalize::nf_interval(r2)
        }
        (RValue::Delay(a), RValue::Delay(b)) => conv(sig, lvl, dlvl, a, b),
        (RValue::Now(a), RValue::Now(b)) => conv(sig, lvl, dlvl, a, b),
        (RValue::Later(a), RValue::Later(b)) => conv(sig, lvl, dlvl, a, b),
        (RValue::Force(a), RValue::Force(b)) => conv(sig, lvl, dlvl, a, b),
        (RValue::IntTy, RValue::IntTy) => true,
        (RValue::IntLit(a), RValue::IntLit(b)) => a == b,
        // Glue (spec §2.6): structural. `eval` has already applied the ⊤/⊥ boundary reductions and
        // stored a *resolved* cofib, so a `Glue` value here is always a proper face — compare the
        // folded cofib syntactically and the three type components up to conversion. (Plan F1 step 3
        // specifies this structural arm. The trusted kernel's `conv_at` has no `Value::Glue` case, so
        // two Glue values fall through to `false` there; this arm is thus strictly *more* complete
        // than the kernel. It is now *exercised* by `kan::family_is_constant`, which conv-compares a
        // Glue line at two fresh dims (always distinct cofibs ⟹ `false`, correctly non-constant); a
        // genuine structural Glue≡Glue never arises on kernel-accepted terms, so no differential
        // divergence.)
        (
            RValue::Glue {
                base: b1,
                cofib: c1,
                ty: t1,
                equiv: e1,
            },
            RValue::Glue {
                base: b2,
                cofib: c2,
                ty: t2,
                equiv: e2,
            },
        ) => {
            c1 == c2
                && conv(sig, lvl, dlvl, b1, b2)
                && conv(sig, lvl, dlvl, t1, t2)
                && conv(sig, lvl, dlvl, e1, e2)
        }
        _ => false,
    }
}

fn is_fun(v: &RValue) -> bool {
    matches!(v, RValue::Lam(_) | RValue::ReflectedFun { .. })
}

fn is_path(v: &RValue) -> bool {
    matches!(v, RValue::PLam(_) | RValue::ReflectedPath { .. })
}

/// Subtyping: definitional equality plus universe cumulativity.
/// Subtyping: definitional equality plus universe cumulativity, lifted structurally through `Π`/`Σ`
/// codomains (T3.1). Mirrors `blight_kernel::check`'s `subtype` **exactly** so the re-checker accepts
/// the same coercions the kernel does (never fewer — a false-Reject would be a spurious `Rejected`;
/// never more — that would be a false-Ok). `Π`: grade **exact** (no laundering), domain **invariant**
/// (a covariant domain is unsound), codomain **covariant**. `Σ`: first component invariant, second
/// covariant. Everything else is plain `conv`. Strictly ⊇ `conv`, so nothing regresses.
pub fn subtype(
    sig: &Signature,
    lvl: usize,
    dlvl: usize,
    actual: &RValue,
    expected: &RValue,
) -> bool {
    match (actual, expected) {
        // U-Cumul via the re-checker's own sound symbolic order (T2.3) — concrete levels decide
        // exactly as the old `na <= ne`, and level variables decide only when the order holds for
        // every assignment.
        (RValue::Univ(na), RValue::Univ(ne)) => crate::term::rlevel_leq(na, ne),
        (RValue::Pi(g0, d0, c0), RValue::Pi(g1, d1, c1)) => {
            g0 == g1 && conv(sig, lvl, dlvl, d0, d1) && {
                let fresh = RValue::Neutral(Neutral::Var(lvl));
                subtype(
                    sig,
                    lvl + 1,
                    dlvl,
                    &c0.apply(sig, fresh.clone()),
                    &c1.apply(sig, fresh),
                )
            }
        }
        (RValue::Sigma(d0, c0), RValue::Sigma(d1, c1)) => {
            conv(sig, lvl, dlvl, d0, d1) && {
                let fresh = RValue::Neutral(Neutral::Var(lvl));
                subtype(
                    sig,
                    lvl + 1,
                    dlvl,
                    &c0.apply(sig, fresh.clone()),
                    &c1.apply(sig, fresh),
                )
            }
        }
        _ => conv(sig, lvl, dlvl, actual, expected),
    }
}

/// Reflect a fresh free variable of the given type at level `lvl` (used when going under a binder
/// in the checker).
pub fn fresh_var(sig: &Signature, lvl: usize, ty: &RValue) -> RValue {
    reflect(sig, Neutral::Var(lvl), ty)
}

/// Obligation 1.3.2 (`docs/metatheory.md` §1.3): mirrors `blight_kernel::check`'s
/// `kan_line_grade_skeleton_eq`. A Kan line's two endpoints may genuinely differ as *types* (the
/// whole point of `transp`/`ua`), but `Transp`/`Comp` check their base once, against the *source*
/// endpoint, then hand back the *target* endpoint as the result type with no re-verification. If
/// both endpoints are `Pi`-formers disagreeing in grade, this launders the checked value's usage
/// discipline. Note: since `conv` above already treats differing Pi-grades as non-convertible,
/// this only needs to run on the `!conv(a0, a1)` branch — it independently re-derives that any
/// `Pi`/`Sigma` skeleton shared between the (otherwise non-convertible) endpoints still agrees in
/// grade, as a second line of defense alongside the kernel's own identical check.
///
/// **Mechanized (Wave 8 / M10):** `mechanization/BlightMeta/GradeSkeleton.lean`'s
/// `grade_skeleton_preserved_by_transp` proves this check's soundness content once, independently
/// of which of the two (kernel/re-checker) copies calls it — see `docs/metatheory.md` §1.3's
/// Track M7 section and `docs/metatheory-mechanized.md`.
pub fn kan_line_grade_skeleton_eq(sig: &Signature, lvl: usize, a: &RValue, b: &RValue) -> bool {
    match (a, b) {
        (RValue::Pi(g1, d1, c1), RValue::Pi(g2, d2, c2)) => {
            if g1 != g2 || !kan_line_grade_skeleton_eq(sig, lvl, d1, d2) {
                return false;
            }
            let fresh = RValue::Neutral(Neutral::Var(lvl));
            kan_line_grade_skeleton_eq(
                sig,
                lvl + 1,
                &c1.apply(sig, fresh.clone()),
                &c2.apply(sig, fresh),
            )
        }
        (RValue::Sigma(d1, c1), RValue::Sigma(d2, c2)) => {
            if !kan_line_grade_skeleton_eq(sig, lvl, d1, d2) {
                return false;
            }
            let fresh = RValue::Neutral(Neutral::Var(lvl));
            kan_line_grade_skeleton_eq(
                sig,
                lvl + 1,
                &c1.apply(sig, fresh.clone()),
                &c2.apply(sig, fresh),
            )
        }
        _ => true,
    }
}

// =================================================================================================
// White-box unit tests for definitional equality (Track D — mutation hardening). These pin down
// *every* arm of `conv`/`subtype` directly on hand-built [`RValue`]s, including the negative cases
// (where conv must return `false`): this is what discriminates a healthy checker from a mutant that
// e.g. flips a `==` to `!=`, deletes a match arm, or turns η's `||` guard into `&&`.
// =================================================================================================
#[cfg(test)]
mod tests {
    use super::*;
    use crate::normalize::{eval, reflect};
    use crate::term::{RGrade, RTerm};
    use crate::value::{Env, RValue};
    use blight_kernel::{ConName, DataName, Signature};
    use std::rc::Rc;

    fn sig() -> Signature {
        Signature::new()
    }
    fn ev(s: &Signature, t: RTerm) -> RValue {
        eval(s, &Env::new(), &t)
    }
    fn nat_t() -> RTerm {
        RTerm::Data(DataName("Nat".into()), vec![], vec![])
    }
    fn bool_t() -> RTerm {
        RTerm::Data(DataName("Bool".into()), vec![], vec![])
    }
    fn zero_t() -> RTerm {
        RTerm::Con(ConName("Zero".into()), vec![])
    }
    fn succ_t(t: RTerm) -> RTerm {
        RTerm::Con(ConName("Succ".into()), vec![t])
    }

    #[test]
    fn univ_conv_is_level_exact() {
        let s = sig();
        assert!(conv(
            &s,
            0,
            0,
            &RValue::Univ(crate::term::rlevel_of_nat(0)),
            &RValue::Univ(crate::term::rlevel_of_nat(0))
        ));
        assert!(!conv(
            &s,
            0,
            0,
            &RValue::Univ(crate::term::rlevel_of_nat(0)),
            &RValue::Univ(crate::term::rlevel_of_nat(1))
        ));
    }

    #[test]
    fn int_conv_distinguishes_type_and_literals() {
        let s = sig();
        assert!(conv(&s, 0, 0, &RValue::IntTy, &RValue::IntTy));
        assert!(!conv(&s, 0, 0, &RValue::IntTy, &RValue::IntLit(0)));
        assert!(conv(&s, 0, 0, &RValue::IntLit(5), &RValue::IntLit(5)));
        assert!(!conv(&s, 0, 0, &RValue::IntLit(5), &RValue::IntLit(6)));
    }

    #[test]
    fn delay_family_conv_recurses_and_separates_variants() {
        let s = sig();
        let il = RValue::IntLit;
        let now = |n| RValue::Now(Rc::new(il(n)));
        let delay = |n| RValue::Delay(Rc::new(il(n)));
        let later = |n| RValue::Later(Rc::new(il(n)));
        let force = |n| RValue::Force(Rc::new(il(n)));
        // Each arm recurses into its payload …
        assert!(conv(&s, 0, 0, &now(1), &now(1)));
        assert!(!conv(&s, 0, 0, &now(1), &now(2)));
        assert!(conv(&s, 0, 0, &delay(1), &delay(1)));
        assert!(!conv(&s, 0, 0, &delay(1), &delay(2)));
        assert!(conv(&s, 0, 0, &later(1), &later(1)));
        assert!(!conv(&s, 0, 0, &later(1), &later(2)));
        assert!(conv(&s, 0, 0, &force(1), &force(1)));
        assert!(!conv(&s, 0, 0, &force(1), &force(2)));
        // … and distinct variants are never conv.
        assert!(!conv(&s, 0, 0, &now(1), &later(1)));
        assert!(!conv(&s, 0, 0, &delay(1), &now(1)));
    }

    #[test]
    fn interval_conv_uses_normal_form() {
        let s = sig();
        let iv = RValue::Interval;
        assert!(conv(&s, 0, 0, &iv(RInterval::I0), &iv(RInterval::I0)));
        assert!(!conv(&s, 0, 0, &iv(RInterval::I0), &iv(RInterval::I1)));
        // De Morgan: ¬¬0 ≡ 0.
        let dneg0 = RInterval::Neg(Box::new(RInterval::Neg(Box::new(RInterval::I0))));
        assert!(conv(&s, 0, 0, &iv(dneg0), &iv(RInterval::I0)));
    }

    #[test]
    fn data_conv_checks_name_params_and_indices() {
        let s = sig();
        let nat = || RValue::Data(DataName("Nat".into()), Rc::new(vec![]), Rc::new(vec![]));
        let boolean = RValue::Data(DataName("Bool".into()), Rc::new(vec![]), Rc::new(vec![]));
        assert!(conv(&s, 0, 0, &nat(), &nat()));
        assert!(!conv(&s, 0, 0, &nat(), &boolean)); // name
        let vec_of = |ps, is| RValue::Data(DataName("Vec".into()), Rc::new(ps), Rc::new(is));
        let a = vec_of(vec![nat()], vec![RValue::IntLit(0)]);
        assert!(conv(
            &s,
            0,
            0,
            &a,
            &vec_of(vec![nat()], vec![RValue::IntLit(0)])
        ));
        assert!(!conv(
            &s,
            0,
            0,
            &a,
            &vec_of(vec![nat()], vec![RValue::IntLit(1)])
        )); // index content
        assert!(!conv(
            &s,
            0,
            0,
            &a,
            &vec_of(vec![boolean.clone()], vec![RValue::IntLit(0)])
        )); // param content
        assert!(!conv(
            &s,
            0,
            0,
            &a,
            &vec_of(vec![], vec![RValue::IntLit(0)])
        )); // param arity
        assert!(!conv(&s, 0, 0, &a, &vec_of(vec![nat()], vec![]))); // index arity
    }

    #[test]
    fn con_conv_checks_name_arity_and_args() {
        let s = sig();
        let zero = || RValue::Con(ConName("Zero".into()), Rc::new(vec![]));
        let succ = |v| RValue::Con(ConName("Succ".into()), Rc::new(vec![v]));
        assert!(conv(&s, 0, 0, &zero(), &zero()));
        assert!(!conv(&s, 0, 0, &zero(), &succ(zero()))); // name + arity
        assert!(conv(&s, 0, 0, &succ(zero()), &succ(zero())));
        assert!(!conv(&s, 0, 0, &succ(zero()), &succ(succ(zero())))); // arg content
    }

    #[test]
    fn neutral_conv_compares_by_quote() {
        let s = sig();
        let v0 = RValue::Neutral(Neutral::Var(0));
        let v1 = RValue::Neutral(Neutral::Var(1));
        assert!(conv(&s, 2, 0, &v0, &v0));
        assert!(!conv(&s, 2, 0, &v0, &v1));
    }

    #[test]
    fn pi_conv_checks_grade_domain_and_codomain() {
        let s = sig();
        let pi = |g, a: RTerm, b: RTerm| ev(&s, RTerm::Pi(g, Box::new(a), Box::new(b)));
        let base = pi(RGrade::Omega, nat_t(), nat_t());
        assert!(conv(&s, 0, 0, &base, &pi(RGrade::Omega, nat_t(), nat_t())));
        assert!(!conv(&s, 0, 0, &base, &pi(RGrade::One, nat_t(), nat_t()))); // grade
        assert!(!conv(
            &s,
            0,
            0,
            &base,
            &pi(RGrade::Omega, bool_t(), nat_t())
        )); // domain
        assert!(!conv(
            &s,
            0,
            0,
            &base,
            &pi(RGrade::Omega, nat_t(), bool_t())
        )); // codomain
    }

    #[test]
    fn sigma_conv_checks_domain_and_codomain() {
        let s = sig();
        let sg = |a: RTerm, b: RTerm| ev(&s, RTerm::Sigma(Box::new(a), Box::new(b)));
        let base = sg(nat_t(), nat_t());
        assert!(conv(&s, 0, 0, &base, &sg(nat_t(), nat_t())));
        assert!(!conv(&s, 0, 0, &base, &sg(bool_t(), nat_t()))); // domain
        assert!(!conv(&s, 0, 0, &base, &sg(nat_t(), bool_t()))); // codomain
    }

    #[test]
    fn pathp_conv_checks_endpoints() {
        let s = sig();
        let path = |lhs: RTerm, rhs: RTerm| {
            ev(
                &s,
                RTerm::PathP {
                    family: Box::new(nat_t()),
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            )
        };
        let base = path(zero_t(), zero_t());
        assert!(conv(&s, 0, 0, &base, &path(zero_t(), zero_t())));
        assert!(!conv(&s, 0, 0, &base, &path(succ_t(zero_t()), zero_t()))); // lhs
        assert!(!conv(&s, 0, 0, &base, &path(zero_t(), succ_t(zero_t())))); // rhs
    }

    #[test]
    fn eta_for_functions_against_bare_neutral() {
        let s = sig();
        let pi_val = ev(
            &s,
            RTerm::Pi(RGrade::Omega, Box::new(nat_t()), Box::new(nat_t())),
        );
        let reflected = reflect(&s, Neutral::Var(0), &pi_val); // a ReflectedFun
        let bare = RValue::Neutral(Neutral::Var(0));
        // η must fire when *either* side is function-shaped (so the `||` guard, not `&&`, is right),
        // and `is_fun` must report `true`.
        assert!(conv(&s, 1, 0, &reflected, &bare));
        assert!(conv(&s, 1, 0, &bare, &reflected));
    }

    #[test]
    fn eta_for_pairs() {
        let s = sig();
        let pair = |a, b| RValue::Pair(Rc::new(RValue::IntLit(a)), Rc::new(RValue::IntLit(b)));
        assert!(conv(&s, 0, 0, &pair(1, 2), &pair(1, 2)));
        assert!(!conv(&s, 0, 0, &pair(1, 2), &pair(1, 3))); // second components differ
        assert!(!conv(&s, 0, 0, &pair(1, 2), &pair(9, 2))); // first components differ
    }

    #[test]
    fn eta_for_pairs_against_bare_neutral() {
        let s = sig();
        // A neutral of Σ type reflects to `(fst v, snd v)`, a *Pair*; the bare neutral is *not* a
        // Pair, so η must fire when *either* side is a pair (the `||` guard, not `&&`).
        let sigma_val = ev(&s, RTerm::Sigma(Box::new(nat_t()), Box::new(nat_t())));
        let reflected = reflect(&s, Neutral::Var(0), &sigma_val); // a Pair of Fst/Snd neutrals
        let bare = RValue::Neutral(Neutral::Var(0));
        assert!(conv(&s, 1, 0, &reflected, &bare));
        assert!(conv(&s, 1, 0, &bare, &reflected));
    }

    #[test]
    fn eta_for_paths_against_bare_neutral() {
        let s = sig();
        let path_val = ev(
            &s,
            RTerm::PathP {
                family: Box::new(nat_t()),
                lhs: Box::new(zero_t()),
                rhs: Box::new(zero_t()),
            },
        );
        let reflected = reflect(&s, Neutral::Var(0), &path_val); // a ReflectedPath
        let bare = RValue::Neutral(Neutral::Var(0));
        assert!(conv(&s, 1, 0, &reflected, &bare));
        assert!(conv(&s, 1, 0, &bare, &reflected));
    }

    #[test]
    fn subtype_adds_universe_cumulativity() {
        let s = sig();
        assert!(subtype(
            &s,
            0,
            0,
            &RValue::Univ(crate::term::rlevel_of_nat(0)),
            &RValue::Univ(crate::term::rlevel_of_nat(1))
        )); // 0 ≤ 1
        assert!(!subtype(
            &s,
            0,
            0,
            &RValue::Univ(crate::term::rlevel_of_nat(1)),
            &RValue::Univ(crate::term::rlevel_of_nat(0))
        )); // 1 ≰ 0
            // Otherwise it falls back to conv.
        assert!(subtype(&s, 0, 0, &RValue::IntTy, &RValue::IntTy));
        assert!(!subtype(
            &s,
            0,
            0,
            &RValue::IntTy,
            &RValue::Univ(crate::term::rlevel_of_nat(0))
        ));
    }

    /// T3.1 parity: the re-checker's `subtype` lifts cumulativity through `Π`/`Σ` codomains exactly
    /// like the kernel — codomain covariant, `Π` grade exact (no laundering), domain invariant.
    #[test]
    fn subtype_cumulativity_through_pi_and_sigma() {
        let s = sig();
        let pi = |g, a: RTerm, b: RTerm| ev(&s, RTerm::Pi(g, Box::new(a), Box::new(b)));
        // Π codomain covariant: Π(ω, Int, Univ 0) ≤ Π(ω, Int, Univ 1), not the reverse.
        let lo = pi(
            RGrade::Omega,
            RTerm::IntTy,
            RTerm::Univ(crate::term::rlevel_of_nat(0)),
        );
        let hi = pi(
            RGrade::Omega,
            RTerm::IntTy,
            RTerm::Univ(crate::term::rlevel_of_nat(1)),
        );
        assert!(subtype(&s, 0, 0, &lo, &hi));
        assert!(!subtype(&s, 0, 0, &hi, &lo));
        // Grade laundering rejected: Π(ω,Int,Univ 0) ⊄ Π(1,Int,Univ 1) despite codomain lift.
        let one_hi = pi(
            RGrade::One,
            RTerm::IntTy,
            RTerm::Univ(crate::term::rlevel_of_nat(1)),
        );
        assert!(!subtype(&s, 0, 0, &lo, &one_hi));
        // Domain invariant: Π(ω,Univ 0,Int) vs Π(ω,Univ 1,Int) rejected both ways.
        let da = pi(
            RGrade::Omega,
            RTerm::Univ(crate::term::rlevel_of_nat(0)),
            RTerm::IntTy,
        );
        let db = pi(
            RGrade::Omega,
            RTerm::Univ(crate::term::rlevel_of_nat(1)),
            RTerm::IntTy,
        );
        assert!(!subtype(&s, 0, 0, &da, &db));
        assert!(!subtype(&s, 0, 0, &db, &da));
        // Σ second component covariant.
        let slo = ev(
            &s,
            RTerm::Sigma(
                Box::new(RTerm::IntTy),
                Box::new(RTerm::Univ(crate::term::rlevel_of_nat(0))),
            ),
        );
        let shi = ev(
            &s,
            RTerm::Sigma(
                Box::new(RTerm::IntTy),
                Box::new(RTerm::Univ(crate::term::rlevel_of_nat(1))),
            ),
        );
        assert!(subtype(&s, 0, 0, &slo, &shi));
        assert!(!subtype(&s, 0, 0, &shi, &slo));
    }
}
