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
                && p1.iter().zip(p2).all(|(x, y)| conv(sig, lvl, dlvl, x, y))
                && i1.iter().zip(i2).all(|(x, y)| conv(sig, lvl, dlvl, x, y))
        }
        (RValue::Con(n1, a1), RValue::Con(n2, a2)) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1.iter().zip(a2).all(|(x, y)| conv(sig, lvl, dlvl, x, y))
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
        // `! E A` and `! E' A` are convertible whenever their payloads are: the re-checker ignores
        // rows (the kernel separately verified them).
        (RValue::EffTy(a), RValue::EffTy(b)) => conv(sig, lvl, dlvl, a, b),
        (RValue::IntTy, RValue::IntTy) => true,
        (RValue::IntLit(a), RValue::IntLit(b)) => a == b,
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
pub fn subtype(
    sig: &Signature,
    lvl: usize,
    dlvl: usize,
    actual: &RValue,
    expected: &RValue,
) -> bool {
    if let (RValue::Univ(na), RValue::Univ(ne)) = (actual, expected) {
        return na <= ne;
    }
    conv(sig, lvl, dlvl, actual, expected)
}

/// Reflect a fresh free variable of the given type at level `lvl` (used when going under a binder
/// in the checker).
pub fn fresh_var(sig: &Signature, lvl: usize, ty: &RValue) -> RValue {
    reflect(sig, Neutral::Var(lvl), ty)
}
