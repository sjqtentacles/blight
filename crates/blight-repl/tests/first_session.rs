//! First-session bundle (E9, v0.1 roadmap): the four verified first-ten-minutes bounce points.
//! `(do …)` sequencing, value-printing evaluation, typed holes, and (via the suite staying
//! green) the stdlib self-consistency sweep.

use blight_elab::{ElabEnv, Outcome, Program};

fn run_with<R: Send + 'static>(
    src: String,
    check: impl FnOnce(Result<Vec<Outcome>, blight_elab::ElabError>) -> R + Send + 'static,
) -> R {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let mut env = ElabEnv::new();
            let mut prog = Program::new(&mut env);
            let result = prog.run(&src);
            check(result)
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
    (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n\
      (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))\n";

/// `(do (<- x e) … e_last)` sequences: binds flow into later steps, the last form is the result,
/// and the whole desugaring is meaning-preserving (pinned by refl).
#[test]
fn do_sugar_sequences_and_computes() {
    run_with(
        format!(
            "{NAT}\
             (define five Nat (do (<- x 2) (<- y 3) (plus x y)))\n\
             (the (Path Nat five 5) (plam (i) 5))"
        ),
        |r| {
            let outcomes = r.expect("do-sugar elaborates and computes");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "every form accepted: {outcomes:?}"
            );
        },
    );
}

/// A `(do …)` step without a binder is sequenced for effect (bound to nothing): the effectful
/// let-chain soup `(let ((_ e1)) e2)` becomes `(do e1 e2)`.
#[test]
fn do_sugar_allows_unbound_steps() {
    run_with(
        format!(
            "{NAT}\
             (defdata Unit () (tt))\n\
             (effect Console (print Nat Unit))\n\
             (deftotal shout (Pi ((n Nat)) (! Console Unit))\n\
               (lam (n) (do (perform print n) (perform print n) (perform print 0))))"
        ),
        |r| {
            let outcomes = r.expect("effectful do-sequencing type-checks");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "every form accepted: {outcomes:?}"
            );
        },
    );
}

/// `blight_elab::eval_value_str` — the REPL's bare-expression path: elaborate, infer, evaluate
/// (metered), and print the re-sugared value. `(plus 2 3)` is `5`, not an `Elim` tree.
#[test]
fn bare_expression_evaluates_to_resugared_value() {
    let out = std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let mut env = ElabEnv::new();
            {
                let mut prog = Program::new(&mut env);
                prog.run(NAT).expect("prelude loads");
            }
            blight_elab::eval_value_str(&env, "(plus 2 3)")
        })
        .expect("spawn")
        .join()
        .expect("thread panicked");
    assert_eq!(out.as_deref(), Ok("5"), "the value prints re-sugared");
}

/// A typed hole `?goal` reports the expected type and the local context — a goal display, not a
/// bare unbound-name error.
#[test]
fn hole_reports_expected_type_and_context() {
    run_with(
        format!("{NAT}(define f (Pi ((n Nat)) Nat) (lam (n) (plus n ?goal)))"),
        |r| {
            let err = r.expect_err("a hole is not a completed program");
            let m = err.to_string();
            assert!(m.contains("hole `?goal`"), "names the hole: {m}");
            assert!(m.contains("expected type: `Nat`"), "shows the goal type: {m}");
            assert!(m.contains("n : Nat"), "shows the local context: {m}");
        },
    );
}

/// Unguarded boundary pins: single-character `?x` stays the char literal (65 = 'A'), and a
/// multi-character `?name` errors today (it becomes the hole namespace).
#[test]
fn char_literal_boundary_is_preserved() {
    run_with(
        format!("{NAT}(define a Nat ?A)\n(the (Path Nat a 65) (plam (i) 65))"),
        |r| {
            let outcomes = r.expect("?A is the char literal for 65");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "char literal computes: {outcomes:?}"
            );
        },
    );
    run_with(format!("{NAT}(define x Nat ?goal)"), |r| {
        assert!(r.is_err(), "multi-char ?goal is not a value today");
    });
}
