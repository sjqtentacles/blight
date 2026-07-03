//! Equation-style definitions (`defn`) — v0.1 roadmap arc E, milestone E5. Top-level pattern-
//! equation sugar desugaring to `define-rec` + a single-scrutinee `match` on the pattern-matched
//! argument column. Exhaustiveness and first-match semantics come from the existing match path
//! (including the E3 coverage pre-pass); these tests pin the end-to-end behavior — that a `defn`
//! elaborates, kernel-checks, and *computes* the same as the hand-written recursion.

use blight_elab::{ElabError, Outcome, Program};

fn run(src: String) -> Result<Vec<Outcome>, ElabError> {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let mut env = blight_elab::ElabEnv::new();
            let mut prog = Program::new(&mut env);
            prog.run(&src)
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n";

/// A two-clause `defn` over `List` elaborates and its final `(the …)` kernel-checks — the sugar
/// produces a well-typed definition.
#[test]
fn defn_equations_desugar_and_check() {
    let outcomes = run(format!(
        "{NAT}\
         (defdata List ((a (Type 0))) (nil) (cons (x a) (xs (List a))))\n\
         (defn len (Pi ((A (Type 0)) (xs (List A))) Nat)\n\
           [(A (nil)) Zero]\n\
           [(A (cons x rest)) (Succ (len A rest))])\n\
         (the Nat (len Nat (cons Zero (cons Zero nil))))"
    ))
    .expect("defn `len` desugars, checks, and applies");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// A `defn` computes identically to the hand-written `define-rec` + `match` it abbreviates: the
/// kernel accepts the constant path `(plam (i) 3) : Path Nat (add 2 1) 3`, which type-checks only
/// because `add 2 1` reduces definitionally to `3`. So the two-argument equation set really does
/// evaluate `add` correctly (definitional equality is behavioral equality here).
#[test]
fn defn_computes_by_refl() {
    let outcomes = run(format!(
        "{NAT}\
         (defn add (Pi ((a Nat) (b Nat)) Nat)\n\
           [((Zero) b) b]\n\
           [((Succ n) b) (Succ (add n b))])\n\
         (the (Path Nat (add (Succ (Succ Zero)) (Succ Zero)) (Succ (Succ (Succ Zero))))\n\
           (plam (i) (Succ (Succ (Succ Zero)))))"
    ))
    .expect("defn `add` computes 2+1=3 definitionally");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// Nested constructor patterns in a `defn` clause work (the same nested-pattern lowering `match`
/// uses): unwrap a `(just (just x))` two levels deep.
#[test]
fn defn_nested_constructor_patterns_check() {
    let outcomes = run(format!(
        "{NAT}\
         (defdata Maybe ((a (Type 0))) (nothing) (just (x a)))\n\
         (defn unwrap2 (Pi ((m (Maybe (Maybe Nat)))) Nat)\n\
           [((nothing)) Zero]\n\
           [((just (nothing))) Zero]\n\
           [((just (just x))) x])\n\
         (the Nat (unwrap2 (just (just (Succ Zero)))))"
    ))
    .expect("nested-pattern defn checks");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// A clause with the wrong number of patterns is a clear, clause-numbered error.
#[test]
fn defn_wrong_arity_clause_is_clear_error() {
    let err = run(format!(
        "{NAT}(defn f (Pi ((a Nat) (b Nat)) Nat) [((Zero)) Zero])"
    ))
    .err()
    .expect("wrong pattern count rejected");
    let ElabError::BadForm(m) = err else {
        panic!("expected BadForm, got {err:?}")
    };
    assert!(
        m.contains("pattern") && m.contains("argument"),
        "clause-arity message: {m}"
    );
}

/// E5×E6 composition: a `defn` with leading `(measure e)`/`(default e)` clauses routes through the
/// E6 measure lowering (auto-fuel), so a non-structural equation set is made total. `count-down`
/// recurses on `(pred (Succ k))` (non-structural), measured by `n`; `count-down 2 = Zero` holds
/// definitionally because the measure is adequate.
#[test]
fn defn_with_measure_clause_composes() {
    let outcomes = run(format!(
        "{NAT}\
         (define-rec pred (Pi ((n Nat)) Nat) (lam (n) (match n [(Zero) Zero] [(Succ k) k])))\n\
         (defn count-down (Pi ((n Nat)) Nat)\n\
           (measure n)\n\
           (default Zero)\n\
           [((Zero)) Zero]\n\
           [((Succ k)) (count-down (pred (Succ k)))])\n\
         (the (Path Nat (count-down (Succ (Succ Zero))) Zero) (plam (i) Zero))"
    ))
    .expect("a measured `defn` is made total and computes correctly");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// A non-exhaustive `defn` is caught by the E3 coverage pass on the generated `match`.
#[test]
fn defn_non_exhaustive_reports_missing_case() {
    let err = run(format!("{NAT}(defn f (Pi ((n Nat)) Nat) [((Zero)) Zero])"))
        .err()
        .expect("non-exhaustive defn rejected");
    let (ElabError::BadMatch(m) | ElabError::BadForm(m)) = err else {
        panic!("expected a match error, got {err:?}")
    };
    assert!(
        m.contains("non-exhaustive"),
        "coverage message on the generated match: {m}"
    );
    assert!(m.contains("`Succ`"), "names the missing constructor: {m}");
}
