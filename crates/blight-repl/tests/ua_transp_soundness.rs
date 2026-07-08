//! Soundness regression: `transp (ua e)` must apply the equivalence, never launder to the identity.
//!
//! Root cause (fixed): `blight_kernel::kan::family_is_constant` compared a Kan line only at its
//! ENDPOINTS via `conv`. The univalence loop `i. Glue B (i=0) A e` with `A ≡ B` collapses to `B` at
//! both endpoints, so the line was wrongly judged constant and `transp` short-circuited to the
//! identity — laundering `transp (ua e) a` to `a` instead of `equiv-fun e a`, which proves
//! model-false lemmas for any non-identity self-equivalence (e.g. Bool negation, where the truth is
//! `false`). The fix probes the interior (two distinct fresh dimensions), so the loop dispatches to
//! `transp_glue`. This test pins the rejection so the fast path cannot silently regress.

use blight_elab::{ElabEnv, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Type-check `body` (with `std/bool.bl` + `std/path.bl` loaded) through the public `Program`
/// driver, i.e. through the real kernel. `Ok` = accepted, `Err` = rejected.
fn checks(body: &str) -> Result<(), String> {
    let src = format!("(load \"std/bool.bl\")\n(load \"std/path.bl\")\n{body}");
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    prog.run(&src).map(|_| ()).map_err(|e| format!("{e:?}"))
}

#[test]
fn transp_ua_does_not_launder_to_identity() {
    // Controls: the harness genuinely type-checks path boundaries through the kernel.
    assert!(
        checks("(define ok (Path Bool true true) (plam (i) true))").is_ok(),
        "control: a valid `Path Bool true true` must be accepted",
    );
    assert!(
        checks("(define bad (Path Bool true false) (plam (i) true))").is_err(),
        "control: a false `Path Bool true false` must be rejected",
    );

    // The regression: `∀ e:Equiv Bool Bool. transp (ua e) true ≡ true` is false in the univalent
    // model (for Bool negation the transport is `false`). It is provable ONLY if `transp (ua e)`
    // wrongly reduces to the identity for the abstract `e`. With the sound interior-constancy probe
    // the kernel reduces it to `equiv-fun e true` (a neutral distinct from `true`), so it is REJECTED.
    let false_lemma = "(define ua-transp-is-identity \
         (Pi ((e (Equiv Bool Bool))) \
             (Path Bool (transp (plam (i) ((ua Bool Bool e) @ i)) cbot true) true)) \
         (lam (e) (plam (i) true)))";
    assert!(
        checks(false_lemma).is_err(),
        "SOUNDNESS REGRESSION: the kernel accepted `∀ e. transp (ua e) true = true` (φ=⊥). The transp \
         fast path is laundering the ua transport to the identity again — see family_is_constant in \
         crates/blight-kernel/src/kan.rs.",
    );

    // Sibling via `φ = ⊤` (the fast-path bypass): the reducer's `is_total(cofib)` short-circuit and
    // the checker's `φ=⊤` gate both used the endpoint proxy. Both now verify the interior.
    let false_lemma_ctop =
        "(define l (Pi ((e (Equiv Bool Bool))) \
              (Path Bool (transp (plam (i) ((ua Bool Bool e) @ i)) ctop true) true)) \
          (lam (e) (plam (i) true)))";
    assert!(
        checks(false_lemma_ctop).is_err(),
        "SOUNDNESS REGRESSION (φ=⊤): the kernel accepted the ua-transport-is-identity lemma via the \
         `is_total`/`φ=⊤` endpoint-proxy bypass.",
    );

    // Sibling via a De Morgan-synthesized ⊤: the DNF folds `j ∧ ¬j = 0` to ⊤, feeding the same φ=⊤
    // path. Rejected by the interior-constancy gate even though the (separate) DNF fold is unchanged.
    let false_lemma_demorgan =
        "(define l (Pi ((e (Equiv Bool Bool))) \
              (Path (Path Bool true true) \
                    (plam (j) (transp (plam (i) ((ua Bool Bool e) @ i)) (ieq0 (imin j (~ j))) true)) \
                    (plam (j) true))) \
          (lam (e) (plam (j) (plam (i) true))))";
    assert!(
        checks(false_lemma_demorgan).is_err(),
        "SOUNDNESS REGRESSION (De Morgan ⊤): the kernel accepted the ua-transport lemma via a \
         `j ∧ ¬j`-folds-to-⊤ face feeding the φ=⊤ bypass.",
    );
}
