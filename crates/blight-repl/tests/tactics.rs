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

    // At least one checked proof is produced. `tactics.bl` transitively loads `std/nat.bl`, whose
    // own Wave 5/N4 `compute`/`decide` dogfood lemmas (ground, closed goals, *not* `Pi`-quantified)
    // are also `Outcome::Checked` here — so this no longer counts exactly one Proof; instead it
    // finds *the* `Pi`-quantified one, `plus-zero`'s unmistakable shape (`Π n. Path Nat …`).
    let pi_proofs: Vec<_> = outcomes
        .iter()
        .filter_map(|o| match o {
            Outcome::Checked(p) => Some(p),
            _ => None,
        })
        .filter(|p| match p.concl() {
            blight_kernel::Judgement::HasType { ty, .. } => {
                matches!(ty, blight_kernel::Term::Pi(_, _, _))
            }
        })
        .collect();
    assert_eq!(
        pi_proofs.len(),
        1,
        "exactly one Pi-quantified tactic proof (plus-zero) among the checked outcomes"
    );
    assert!(env.global_term("plus-zero").is_some(), "plus-zero is bound");
}

/// Track M2a: the `trans` combinator, freshly implemented as a genuine `hcomp`-backed path
/// composition (§2.6, CCHM). A `(trans p q)` script closes a two-step goal `Path A x z` from
/// hypotheses `p : Path A x y` and `q : Path A y z` — this is the same script that failed to load
/// before `trans` existed (the red half of this track's red→green pair; see git history / the
/// metatheory-gold-track plan for the pre-`trans` red).
#[test]
fn trans_closes_two_step_path() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(
            "(load \"tactics.bl\")\n\
             (define-by two-step\n\
               (Pi ((x Nat) (y Nat) (z Nat) (p (Path Nat x y)) (q (Path Nat y z)))\n\
                   (Path Nat x z))\n\
               (intro x (intro y (intro z (intro p (intro q (trans p q)))))))",
        )
        .expect("trans closes the two-step transitivity goal and the kernel re-checks it")
    };
    assert!(
        outcomes.iter().any(|o| matches!(o, Outcome::Checked(_))),
        "the trans-built proof is a kernel-checked Proof"
    );
    assert!(env.global_term("two-step").is_some(), "two-step is bound");
}

/// SOUNDNESS PROBE: can `trans refl refl` prove the *false* proposition `Path Nat Zero (Succ
/// Zero)` by picking unrelated midpoints (`refl : Path Nat Zero Zero`, `refl : Path Nat (Succ Zero)
/// (Succ Zero)`)? `trans`'s one-sided formula only ever forces `p`'s *floor* (`p@0`) and `q`'s *lid*
/// (`q@1`) — never a shared-midpoint compatibility condition — so this must still be *rejected*: the
/// composed term's own declared endpoints (`Zero`, `Succ Zero`) are exactly `p`'s lhs / `q`'s rhs,
/// so if this typechecked it would be a genuine false proof (`Zero` and `Succ Zero` are distinct
/// `Nat` constructors). Guards against a soundness hole in the new `hcomp` surface form.
#[test]
fn trans_cannot_prove_zero_equals_succ_zero() {
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    // `p`/`q` are explicit, raw `refl` surface terms (not the `refl` *tactic* keyword, which is not
    // itself a term `trans`'s parser would accept — this exercises the genuine construction).
    let r = prog.run(
        "(load \"tactics.bl\")\n\
         (define-by bogus\n\
           (Path Nat Zero (Succ Zero))\n\
           (trans (the (Path Nat Zero Zero) (plam (i) Zero))\n\
                  (the (Path Nat (Succ Zero) (Succ Zero)) (plam (i) (Succ Zero)))))",
    );
    assert!(
        r.is_err(),
        "trans must not be able to prove Zero ≡ Succ Zero, got: {r:?}"
    );
}

/// The LCF safety net: `trans`'s composed term is only well-typed when the *outer goal's own*
/// endpoints are `p`'s lhs and `q`'s rhs. A `p` unrelated to the goal's claimed left endpoint (`x`
/// vs. an independently-bound `y`) must be *rejected* by the kernel's `PathP` boundary check, never
/// silently accepted as a false proof.
#[test]
fn trans_rejects_a_proof_unrelated_to_the_goal() {
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    let r = prog.run(
        "(load \"tactics.bl\")\n\
         (define-by bogus-two-step\n\
           (Pi ((x Nat) (y Nat) (w Nat) (z Nat) (p (Path Nat y w)) (q (Path Nat w z)))\n\
               (Path Nat x z))\n\
           (intro x (intro y (intro w (intro z (intro p (intro q (trans p q))))))))",
    );
    assert!(
        r.is_err(),
        "a proof unrelated to the goal's own left endpoint must not produce a proof, got: {r:?}"
    );
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
