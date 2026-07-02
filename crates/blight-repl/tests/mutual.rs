//! Mutual recursion (MR milestone): the `(mutual …)` surface form desugars — entirely in the
//! untrusted tower, zero kernel growth — into a generated tag datatype + ONE merged recursive
//! function + per-member projections. A structurally-decreasing group becomes a single kernel
//! `Elim` (total, re-checked `Ok`); a non-structural group takes the partial `Delay` path
//! (re-checker honestly *declines*, never *rejects*).

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(f)
        .expect("spawn mutual test thread")
        .join()
        .expect("mutual test thread panicked");
}

const EVEN_ODD: &str = r#"
(load "std/nat.bl")
(mutual
  (deftotal even? (Pi ((n Nat)) Bool) (lam (n) (match n [(Zero) true]  [(Succ m) (odd? m)])))
  (deftotal odd?  (Pi ((n Nat)) Bool) (lam (n) (match n [(Zero) false] [(Succ m) (even? m)]))))
(define two   Nat (Succ (Succ Zero)))
(define three Nat (Succ two))
(define-by ev2-true  (Path Bool (even? two)   true)  refl)
(define-by ev3-false (Path Bool (even? three) false) refl)
(define-by od3-true  (Path Bool (odd?  three) true)  refl)
"#;

#[test]
fn mutual_total_even_odd_is_one_elim_rechecked_ok() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(EVEN_ODD)
                .expect("mutual even?/odd? group loads and kernel-checks")
        };
        for (i, o) in outcomes.iter().enumerate() {
            assert!(
                matches!(o, Outcome::Declared | Outcome::Checked(_)),
                "form {i} accepted: {o:?}"
            );
        }
        // Projections are present, and the desugaring generated the tag type + merged function.
        for sym in ["even?", "odd?", "mtl_merged_even_"] {
            assert!(env.global_term(sym).is_some(), "defines `{sym}`");
        }
        assert!(
            env.data_constructors("MtlTag_even_").is_some(),
            "generated the tag datatype"
        );
        // The merged total function re-verifies Ok through the independent re-checker (single Elim,
        // in the structural fragment). Nothing may be Rejected.
        let sig = env.signature();
        let mut merged_ok = false;
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            match blight_recheck::recheck_judgement(sig, &j) {
                Ok(()) => {
                    if name == "mtl_merged_even_" {
                        merged_ok = true;
                    }
                }
                Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("re-checker REJECTED `{name}`: {m}")
                }
            }
        }
        assert!(
            merged_ok,
            "merged mutual function re-verifies Ok (single Elim)"
        );
    });
}

const PING_PONG_DELAY: &str = r#"
(load "std/nat.bl")
(mutual
  (define-rec ping (Pi ((n Nat) (t Nat)) (Delay Nat))
    (lam (n t) (match n [(Zero) (now t)] [(Succ m) (later (pong m (Succ t)))])))
  (define-rec pong (Pi ((n Nat) (t Nat)) (Delay Nat))
    (lam (n t) (match n [(Zero) (now t)] [(Succ m) (later (ping m (Succ t)))]))))
"#;

#[test]
fn mutual_partial_delay_group_loads_and_declines() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(PING_PONG_DELAY)
                .expect("non-structural mutual Delay group loads (gate-skipped)")
        };
        for (i, o) in outcomes.iter().enumerate() {
            assert!(
                matches!(o, Outcome::Declared | Outcome::Checked(_)),
                "form {i} accepted: {o:?}"
            );
        }
        for sym in ["ping", "pong", "mtl_merged_ping"] {
            assert!(env.global_term(sym).is_some(), "defines `{sym}`");
        }
        // The partial merged function may honestly Decline; it must never be Rejected.
        let sig = env.signature();
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            if let Err(blight_recheck::RecheckError::Rejected(m)) =
                blight_recheck::recheck_judgement(sig, &j)
            {
                panic!("re-checker REJECTED partial mutual global `{name}`: {m}");
            }
        }
    });
}
