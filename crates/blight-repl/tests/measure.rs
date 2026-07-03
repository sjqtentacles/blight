//! Measure-based total definitions (`(measure …)`/`(default …)` on `deftotal`) — v0.1 roadmap arc
//! E, milestone E6. The sugar auto-synthesizes the fuel plumbing that quicksort/mergesort/gcd
//! hand-write, so the kernel still sees a plain structural `Elim` over the fuel `Nat`. These tests
//! pin: (a) a measured definition is TOTAL (no `Later`/`Delay` — it compiled to `Elim`), (b) it
//! *computes* the right answer when the measure is adequate, and (c) the honest contract — a wrong
//! measure yields "total but returns the default", never unsoundness.

use blight_elab::{ElabError, Outcome, Program};

/// Run `src` in a fresh env on a large stack and hand the result to `check` on the worker
/// thread (post-S3, `Term` holds `Rc`s, so `Outcome`/`ElabError` cannot cross `join`).
fn run_with<R: Send + 'static>(
    src: String,
    check: impl FnOnce(Result<Vec<Outcome>, ElabError>) -> R + Send + 'static,
) -> R {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let mut env = blight_elab::ElabEnv::new();
            let mut prog = Program::new(&mut env);
            let result = prog.run(&src);
            check(result)
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

/// Whether a measured definition compiled to a structural `Elim` (its helper term has no `Later`).
fn helper_is_total(src: &str, helper: &str) -> bool {
    let src = src.to_string();
    let helper = helper.to_string();
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let mut env = blight_elab::ElabEnv::new();
            {
                let mut prog = Program::new(&mut env);
                prog.run(&src).ok();
            }
            env.global_term(&helper)
                .map(|t| !term_has_later(t))
                .unwrap_or(false)
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

fn term_has_later(t: &blight_kernel::Term) -> bool {
    use blight_kernel::Term::*;
    match t {
        Later(_) => true,
        Lam(b) | PLam(b) | Delay(b) | Now(b) | Force(b) | Fst(b) | Snd(b) => term_has_later(b),
        Pi(_, a, b) | Sigma(a, b) | App(a, b) | Pair(a, b) | Ann(a, b) => {
            term_has_later(a) || term_has_later(b)
        }
        Con(_, args) => args.iter().any(term_has_later),
        Data(_, ps, is) => ps.iter().chain(is).any(term_has_later),
        Elim {
            motive,
            methods,
            scrutinee,
            ..
        } => {
            term_has_later(motive)
                || term_has_later(scrutinee)
                || methods.iter().any(term_has_later)
        }
        _ => false,
    }
}

const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n";
const LIST: &str = "(defdata List ((a (Type 0))) (nil) (cons (x a) (xs (List a))))\n";
// A minimal length + append, hand-written, for the quicksort-shaped measured test.
const LEN_APPEND: &str = "(define-rec length (Pi ((A (Type 0)) (xs (List A))) Nat)\n\
      (lam (A xs) (match xs [(nil) Zero] [(cons x rest) (Succ (length A rest))])))\n\
    (define-rec append (Pi ((A (Type 0)) (xs (List A)) (ys (List A))) (List A))\n\
      (lam (A xs ys) (match xs [(nil) ys] [(cons x rest) (cons x (append A rest ys))])))\n";

/// A measured, non-structurally-recursive definition compiles to a structural `Elim` (no `Later`)
/// — i.e. the kernel certifies it TOTAL. The classic shape: recurse on a `filter`-ed sublist, made
/// total by a `(measure (length …))` fuel bound.
#[test]
fn measured_definition_is_total_no_later() {
    let src = format!(
        "{NAT}{LIST}{LEN_APPEND}\
         (define-rec keep-tail (Pi ((A (Type 0)) (xs (List A))) (List A))\n\
           (lam (A xs) (match xs [(nil) nil] [(cons x rest) rest])))\n\
         (deftotal qsort (Pi ((xs (List Nat))) (List Nat))\n\
           (measure (length Nat xs))\n\
           (default xs)\n\
           (lam (xs)\n\
             (match xs [(nil) nil]\n\
               [(cons p rest) (append Nat (qsort (keep-tail Nat rest)) (cons p nil))])))"
    );
    assert!(
        helper_is_total(&src, "msr_fueled_qsort"),
        "the measured qsort helper must compile to a structural Elim (no Later)"
    );
}

/// A measured definition with an adequate measure *computes* the right answer. `count-down n` peels
/// a `Nat` to `Zero` recursing on a non-structural `(pred n)`; the measure `n` bounds it, and
/// `count-down 2 = Zero` holds definitionally (a constant path type-checks).
#[test]
fn measured_definition_computes_when_measure_adequate() {
    let src = format!(
        "{NAT}\
         (define-rec pred (Pi ((n Nat)) Nat) (lam (n) (match n [(Zero) Zero] [(Succ k) k])))\n\
         (deftotal count-down (Pi ((n Nat)) Nat)\n\
           (measure n)\n\
           (default Zero)\n\
           (lam (n) (match n [(Zero) Zero] [(Succ k) (count-down (pred (Succ k)))])))\n\
         (the (Path Nat (count-down (Succ (Succ Zero))) Zero) (plam (i) Zero))"
    );
    run_with(src, |r| {
        let outcomes = r.expect("measured count-down computes to Zero");
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    });
}

/// The honest contract, pinned: a *wrong* measure (seeding zero fuel) still yields a TOTAL function
/// — it just returns the `(default …)` instead of the intended value. `(measure Zero)` gives fuel
/// `(Succ Zero) = 1`, so one unfolding then the default. Here `count-down 1` with the default `7`
/// returns `7` (fuel runs out before reaching `Zero`)... actually one Succ step suffices, so it
/// reaches Zero. Use a two-step input so the single unfolding is not enough and the default shows.
#[test]
fn wrong_measure_is_total_but_returns_default() {
    let src = format!(
        "{NAT}\
         (define-rec pred (Pi ((n Nat)) Nat) (lam (n) (match n [(Zero) Zero] [(Succ k) k])))\n\
         (deftotal cd (Pi ((n Nat)) Nat)\n\
           (measure Zero)\n\
           (default (Succ (Succ (Succ Zero))))\n\
           (lam (n) (match n [(Zero) Zero] [(Succ k) (cd (pred (Succ k)))])))\n\
         (the (Path Nat (cd (Succ (Succ Zero))) (Succ (Succ (Succ Zero)))) (plam (i) (Succ (Succ (Succ Zero)))))"
    );
    // Fuel seed = (Succ Zero) = 1. cd 2 → one Succ-arm unfolding: cd (pred 2) = cd 1, but the inner
    // call is at fuel Zero → returns the default 3. So `cd 2 = 3` (the default), definitionally.
    run_with(src, |r| {
        let outcomes = r.expect(
            "a wrong measure still type-checks (total) and returns the default, definitionally",
        );
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    });
}

/// `(measure …)` without a following `(default …)` is not recognized as the measured shape (it
/// falls through to the ordinary `deftotal` path, which rejects the 5-item form) — pinning that the
/// default is mandatory.
#[test]
fn measure_without_default_is_rejected() {
    run_with(
        format!("{NAT}(deftotal f (Pi ((n Nat)) Nat) (measure n) (lam (n) (f n)))"),
        |r| {
            let err = r.expect_err("measure without default is rejected");
            // The ordinary deftotal path errors on the unexpected arity.
            let (ElabError::BadForm(_) | ElabError::BadMatch(_)) = err else {
                panic!("expected a form error, got {err:?}")
            };
        },
    );
}

/// A measured definition whose body never recurses is rejected (the clauses are pointless).
#[test]
fn measure_on_non_recursive_body_is_error() {
    run_with(
        format!("{NAT}(deftotal f (Pi ((n Nat)) Nat) (measure n) (default Zero) (lam (n) Zero))"),
        |r| {
            let err = r.expect_err("non-recursive measured def rejected");
            let ElabError::BadForm(m) = err else {
                panic!("expected BadForm, got {err:?}")
            };
            assert!(
                m.contains("never calls"),
                "message explains the body doesn't recurse: {m}"
            );
        },
    );
}
