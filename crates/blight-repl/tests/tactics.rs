//! Proof-by-tactics acceptance (spec §9 M3 headline): `plus-zero` is proved *by tactics* — a
//! `(define-by …)` script discharges `Π n. Path Nat (plus n Zero) n` with `induction` + `refl`/
//! `cong`, and the spore mints the resulting [`Proof`]. Black-box: the `blight-elab` `Program`
//! driver only. A buggy tactic could at most fail to produce a proof (LCF), never a false one.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// The headline test: load the tactic substrate + the `plus-zero` proof script, and confirm the
/// `(define-by plus-zero …)` form produced a kernel `Proof` concluding the `plus-zero` Path type.
#[test]
fn plus_zero_by_tactics() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run("(load \"tactics.bl\")\n(load \"plus_zero_tac.bl\")")
            .expect("the tactic prelude + proof load and the proof checks")
    };

    // Exactly one form (the `define-by`) yields a checked proof.
    let proofs: Vec<_> = outcomes
        .iter()
        .filter_map(|o| match o {
            Outcome::Checked(p) => Some(p),
            _ => None,
        })
        .collect();
    assert_eq!(
        proofs.len(),
        1,
        "the tactic proof produced exactly one Proof"
    );

    // The proof concludes the intended `plus-zero` judgement, and the global is bound.
    let proof = proofs[0];
    match proof.concl() {
        blight_kernel::Judgement::HasType { ty, .. } => {
            // The declared goal type is a `Pi` into a `Path` — sanity-check it elaborated as such.
            assert!(
                matches!(ty, blight_kernel::Term::Pi(_, _, _)),
                "goal is a Pi type"
            );
        }
    }
    assert!(env.global_term("plus-zero").is_some(), "plus-zero is bound");
}

/// A deliberately wrong tactic (closing the `Succ` case with `refl` instead of `cong Succ k#ih`)
/// must *not* produce a proof — the LCF guarantee, end-to-end through the driver.
#[test]
fn wrong_tactic_is_not_a_proof() {
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    let r = prog.run(
        "(load \"tactics.bl\")\n\
         (define-by plus-zero \
            (Pi ((n Nat)) (Path Nat (plus n Zero) n)) \
            (intro n (induction n [(Zero) refl] [(Succ k) refl])))",
    );
    assert!(
        r.is_err(),
        "a wrong tactic proof must be rejected by the spore, got: {r:?}"
    );
}
