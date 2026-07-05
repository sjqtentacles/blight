//! Property-based **kernel ↔ re-checker** parity on symbolic universe levels (T2.3).
//!
//! The two checkers implement the sound symbolic level order *independently* (kernel
//! `check.rs::level_leq`, recheck `term.rs::rlevel_leq` — distinct types, distinct code). Their
//! DECISIONS must coincide: a level pair the kernel's cumulativity accepts must re-verify (`Ok`),
//! and one it rejects must be rejected by the re-checker too — in BOTH directions, so neither
//! checker silently becomes more or less permissive than the other on this fragment.
//!
//! The order is observed through the real doors, not by calling the (private) order functions:
//! `λA.A : Π^ω(A : Univ ℓa). Univ ℓb` is kernel-accepted **iff** `ℓa ≤ ℓb` (the codomain check is
//! exactly `subtype (Univ ℓa) (Univ ℓb)` = U-Cumul), and re-checked through
//! [`recheck_judgement_leveled`] under the same two prenex level variables. Every generated level
//! is well-formed under `n_levels = 2` by construction, so the well-formedness gate never masks an
//! order disagreement (the gate itself is pinned separately in the crate's white-box tests).

use blight_kernel::{check_top_leveled, Grade, Judgement, Level, Signature, Term};
use blight_recheck::{recheck_judgement_leveled, RecheckError};
use proptest::prelude::*;
use std::rc::Rc;

/// A random symbolic [`Level`] of bounded depth over `Var(0)`/`Var(1)` (well-formed under
/// `n_levels = 2`).
fn arb_level() -> impl Strategy<Value = Level> {
    let leaf = prop_oneof![
        Just(Level::Zero),
        Just(Level::Var(0)),
        Just(Level::Var(1)),
    ];
    leaf.prop_recursive(3, 24, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(|l| Level::Suc(Box::new(l))),
            (inner.clone(), inner)
                .prop_map(|(a, b)| Level::Max(Box::new(a), Box::new(b))),
        ]
    })
}

/// `λA. A : Π^ω(A : Univ ℓa). Univ ℓb` — the coercion probe whose acceptance is exactly
/// `ℓa ≤ ℓb` under each checker's own symbolic order.
fn coercion_judgement(la: &Level, lb: &Level) -> (Term, Term) {
    let term = Term::Lam(Rc::new(Term::Var(0)));
    let ty = Term::Pi(
        Grade::Omega,
        Rc::new(Term::Univ(la.clone())),
        Rc::new(Term::Univ(lb.clone())),
    );
    (term, ty)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// Kernel and re-checker agree — both directions — on the cumulativity coercion for random
    /// symbolic level pairs. (A `Declined` would also be a failure: levels are modeled now.)
    #[test]
    fn prop_kernel_recheck_agree_on_level_leq(la in arb_level(), lb in arb_level()) {
        let (term, ty) = coercion_judgement(&la, &lb);
        let kernel_ok =
            check_top_leveled(Signature::empty(), term.clone(), ty.clone(), 2).is_ok();
        let j = Judgement::HasType { term, ty };
        let sig = Signature::empty();
        match recheck_judgement_leveled(&sig, &j, 2) {
            Ok(()) => prop_assert!(
                kernel_ok,
                "recheck accepted a coercion the kernel rejects: {la:?} ≤ {lb:?}"
            ),
            Err(RecheckError::Rejected(m)) => prop_assert!(
                !kernel_ok,
                "recheck REJECTED a kernel-accepted coercion (soundness alarm): \
                 {la:?} ≤ {lb:?}: {m}"
            ),
            Err(RecheckError::Declined(m)) => prop_assert!(
                false,
                "levels are modeled (T2.3) — a Declined here is a coverage regression: {m}"
            ),
        }
    }

    /// The level-polymorphic identity family re-verifies at every random well-formed level:
    /// `λA.λx.x : Π^ω(A : Univ ℓ). Π^ω(x : A). A` is kernel-accepted for ALL `ℓ` (reflexivity of
    /// the order), and the re-checker must agree on each instance.
    #[test]
    fn prop_level_poly_identity_reverifies(l in arb_level()) {
        let ty = Term::Pi(
            Grade::Omega,
            Rc::new(Term::Univ(l.clone())),
            Rc::new(Term::Pi(
                Grade::Omega,
                Rc::new(Term::Var(0)),
                Rc::new(Term::Var(1)),
            )),
        );
        let id = Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Var(0)))));
        prop_assert!(
            check_top_leveled(Signature::empty(), id.clone(), ty.clone(), 2).is_ok(),
            "kernel accepts the identity at any well-formed level: {l:?}"
        );
        let j = Judgement::HasType { term: id, ty };
        let sig = Signature::empty();
        prop_assert_eq!(
            recheck_judgement_leveled(&sig, &j, 2),
            Ok(()),
            "re-checker agrees at level {:?}", l
        );
    }
}
