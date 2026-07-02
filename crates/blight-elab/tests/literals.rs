//! Numeric literal sugar (v0.1 roadmap arc E, milestone E1): a bare decimal atom like `3` in term
//! position is `Nat` sugar for `(Succ (Succ (Succ Zero)))`. Reader-unchanged, elaborator-only
//! (`Surface::NatLit`), zero TCB: the kernel only ever sees the expanded `Succ`/`Zero` chain.
//!
//! Includes the verified hazard test: binder grades (`0`/`1`/`omega`) are parsed through the same
//! `parse_surface` used for ordinary terms, so a naive digit-literal desugaring would silently
//! turn every graded binder `(x A 0)` into nonsense. `graded_binders_still_parse_with_literal_grades`
//! pins that this does not happen.

use blight_elab::{parse_surface, read_one, ElabEnv, Outcome, Program, Surface};

fn sexpr(src: &str) -> blight_elab::Sexpr {
    let (s, _rest) = read_one(src).unwrap_or_else(|e| panic!("`{src}` should read cleanly: {e:?}"));
    s
}

const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n";

/// A bare decimal atom parses to `Surface::NatLit`, not `Surface::Var`.
#[test]
#[ignore = "E1 red: bare-decimal detection in parse_surface lands in the next commit"]
fn bare_decimal_parses_as_nat_literal() {
    let s = parse_surface(&sexpr("3")).expect("`3` parses");
    assert_eq!(s, Surface::NatLit(3));
    let z = parse_surface(&sexpr("0")).expect("`0` parses");
    assert_eq!(z, Surface::NatLit(0));
}

/// A decimal literal elaborates and kernel-checks as the `Succ`-chain it abbreviates.
#[test]
#[ignore = "E1 red: bare-decimal detection in parse_surface lands in the next commit"]
fn decimal_elaborates_and_checks_against_nat() {
    let mut env = ElabEnv::new();
    let mut prog = Program::new(&mut env);
    let outcomes = prog
        .run(&format!("{NAT}(the Nat 3)"))
        .expect("decimal literal checks against Nat");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// A decimal in an *index* position (not just a bare term) checks — e.g. `Vec Nat 3` — exercising
/// literal sugar inside a dependent type, not only at the top level.
#[test]
#[ignore = "E1 red: bare-decimal detection in parse_surface lands in the next commit"]
fn decimal_in_defdata_index_position_checks() {
    let mut env = ElabEnv::new();
    let mut prog = Program::new(&mut env);
    let src = format!(
        "{NAT}\
         (defdata Vec ((a (Type 0))) ((n Nat)) (vnil (=> Zero))\n\
           (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))\n\
         (the (Vec Nat 1) (vcons 0 Zero (vnil)))"
    );
    let outcomes = prog.run(&src).expect("Vec Nat 3-shaped index checks");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// A decimal literal and its hand-written `Succ`-chain equivalent elaborate to the identical core
/// term — the sugar is exact, not merely "also happens to check".
#[test]
fn decimal_matches_hand_written_succ_chain() {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::new(&mut env);
        prog.run(NAT).expect("Nat declares");
    }
    let two_literal = blight_elab::elaborate_against(
        &env,
        &Surface::NatLit(2),
        &blight_kernel::Term::Data(blight_kernel::DataName("Nat".into()), vec![], vec![]),
    )
    .expect("literal 2 checks");
    let two_written = parse_surface(&sexpr("(Succ (Succ Zero))")).expect("parses");
    let two_written = blight_elab::elaborate_against(
        &env,
        &two_written,
        &blight_kernel::Term::Data(blight_kernel::DataName("Nat".into()), vec![], vec![]),
    )
    .expect("hand-written chain checks");
    assert_eq!(two_literal, two_written);
}

/// A negative decimal is not special-cased: `-5` stays an ordinary (unbound) symbol and fails
/// elaboration cleanly, rather than panicking or silently parsing as a numeral.
#[test]
fn negative_decimal_rejected_cleanly() {
    let mut env = ElabEnv::new();
    let mut prog = Program::new(&mut env);
    let result = prog.run(&format!("{NAT}(the Nat -5)"));
    assert!(
        result.is_err(),
        "-5 is not a Nat literal; it must fail as an unbound variable, not panic"
    );
}

/// An atom that merely starts or ends with digits, but is not purely digits, stays an ordinary
/// symbol (current behavior, pinned unguarded).
#[test]
fn non_numeric_atom_still_symbol() {
    assert_eq!(
        parse_surface(&sexpr("x2")).unwrap(),
        Surface::Var("x2".to_string())
    );
    assert_eq!(
        parse_surface(&sexpr("2x")).unwrap(),
        Surface::Var("2x".to_string())
    );
}

/// The hazard test: a binder grade slot's `0`/`1`/`omega` literal must still mean the grade, not a
/// `Nat` value, even though the grade position now also parses through the decimal-literal path.
#[test]
fn graded_binders_still_parse_with_literal_grades() {
    let mut env = ElabEnv::new();
    let mut prog = Program::new(&mut env);
    let src = format!(
        "{NAT}\
         (define erase-me (Pi ((n Nat 0)) Nat) (lam (n) Zero))\n\
         (define lin-id (Pi ((n Nat 1)) Nat) (lam (n) n))"
    );
    let outcomes = prog
        .run(&src)
        .expect("grade-0 and grade-1 binders still parse and check as grades, not Nat literals");
    assert!(outcomes.iter().all(|o| matches!(o, Outcome::Declared)));
}
