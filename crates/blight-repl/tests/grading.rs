//! M1 acceptance tests (spec §3, §7.2): the grading spine must be enforced *through the public
//! pipeline*, and grade-`0` content must vanish under erasure.
//!
//! Two of these tests exercise the surface→elaborate→kernel path (linear misuse). The indexed
//! `Vec a n` family is not yet expressible in surface `defdata` (its elaborator support lands with
//! the M3 tower), so the `Vec`/erasure cases drive the *kernel* public API directly — still a
//! black-box test of the trusted base, just one layer in from the parser.

use std::rc::Rc;
use blight_kernel::{
    check_top_with, erase::erase, Arg, ConName, Constructor, DataDecl, DataName, Grade, Level,
    Signature, Term, TypeError,
};

// ----------------------------------------------------------------------------------------------
// Shared kernel fixtures (a `Nat` and an indexed `Vec a n`), mirroring the kernel unit fixtures.
// ----------------------------------------------------------------------------------------------

fn u(n: u32) -> Term {
    let mut l = Level::Zero;
    for _ in 0..n {
        l = Level::Suc(Box::new(l));
    }
    Term::Univ(l)
}
fn nat_name() -> DataName {
    DataName("Nat".into())
}
fn nat_ty() -> Term {
    Term::Data(nat_name(), vec![], vec![])
}
fn zero() -> Term {
    Term::Con(ConName("zero".into()), vec![])
}
fn succ(n: Term) -> Term {
    Term::Con(ConName("succ".into()), vec![n])
}

fn nat_sig() -> Signature {
    let mut sig = Signature::new();
    sig.declare(DataDecl {
        name: nat_name(),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("succ".into()),
                args: vec![Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    sig
}

fn vec_name() -> DataName {
    DataName("Vec".into())
}

/// `Vec : (A : Univ 0) → (n : Nat) → Univ 0` with `vnil : Vec A zero` and
/// `vcons : (n : Nat) → A → Vec A n → Vec A (succ n)`. Single parameter `A`, single index `n`.
fn vec_sig() -> Signature {
    let mut sig = nat_sig();
    sig.declare(DataDecl {
        name: vec_name(),
        params: vec![u(0)],
        indices: vec![nat_ty()],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("vnil".into()),
                args: vec![],
                result_indices: vec![zero()],
            },
            Constructor {
                name: ConName("vcons".into()),
                args: vec![
                    Arg::NonRec(nat_ty()),
                    Arg::NonRec(Term::Var(1)),
                    Arg::Rec(vec![Term::Var(1)]),
                ],
                result_indices: vec![succ(Term::Var(2))],
            },
        ],
        path_constructors: vec![],
    });
    sig
}

fn vec_ty(elem: Term, len: Term) -> Term {
    Term::Data(vec_name(), vec![elem], vec![len])
}

// ----------------------------------------------------------------------------------------------
// 1. Linear misuse is rejected through the surface → elaborate → kernel pipeline.
// ----------------------------------------------------------------------------------------------

/// `λ x. (x, x)` checked against `(x : Nat) →¹ Nat × Nat` must be rejected: the linear binder is
/// used twice. We build the *type* with an explicit grade-`1` binder via the surface syntax, then
/// hand the kernel the offending body, so this is a genuine end-to-end grading rejection.
#[test]
fn repl_rejects_linear_use_twice() {
    use blight_elab::{elaborate, ElabEnv};

    let mut env = ElabEnv::new();
    // Make `Nat` available to the elaborator so the surface type resolves.
    declare_nat_surface(&mut env);

    // Elaborate `(Pi ((x Nat 1)) Nat)` from the surface to obtain a *linear* binder (grade 1)
    // straight from the grade-annotation syntax, then swap its codomain for `Nat × Nat` so the
    // body can use `x` twice. This keeps the grade itself coming through the real pipeline.
    let ty_surface = read_surface("(Pi ((x Nat 1)) Nat)");
    let ty_core = elaborate(&env, &ty_surface).expect("type elaborates");
    let ty_core = match ty_core {
        Term::Pi(grade, dom, _cod) => {
            assert_eq!(grade, Grade::One, "surface grade `1` ⟹ linear binder");
            // (x : Nat) →¹ (Nat × Nat), the codomain not depending on x.
            Term::Pi(
                grade,
                dom,
                Rc::new(Term::Sigma(Rc::new(nat_ty()), Rc::new(nat_ty()))),
            )
        }
        other => panic!("expected a Pi type, got {other:?}"),
    };

    // body = λ x. (x, x)  — uses the linear `x` twice.
    let body = Term::Lam(Rc::new(Term::Pair(
        Rc::new(Term::Var(0)),
        Rc::new(Term::Var(0)),
    )));

    match check_top_with(env.signature().clone(), body, ty_core) {
        Err(TypeError::GradeViolation(_)) => {}
        other => panic!("linear `x` used twice must be a GradeViolation, got {other:?}"),
    }
}

/// The single-use companion: `λ x. x` against `(x : Nat) →¹ Nat` is accepted.
#[test]
fn repl_accepts_linear_use_once() {
    use blight_elab::{elaborate, ElabEnv};

    let mut env = ElabEnv::new();
    declare_nat_surface(&mut env);

    let ty_surface = read_surface("(Pi ((x Nat 1)) Nat)");
    let ty_core = elaborate(&env, &ty_surface).expect("type elaborates");
    let body = Term::Lam(Rc::new(Term::Var(0)));

    check_top_with(env.signature().clone(), body, ty_core)
        .expect("a linear binder used exactly once must be accepted");
}

// ----------------------------------------------------------------------------------------------
// 2. An indexed `Vec a n` with an *erased* index typechecks (kernel API).
// ----------------------------------------------------------------------------------------------

/// `vcons zero zero vnil : Vec Nat (succ zero)` checks: the index `n` is supplied and reconciled,
/// and `vnil : Vec Nat zero` checks as well. The whole point is that the index lives only in the
/// *type*; erasure (below) confirms it costs nothing at runtime.
#[test]
fn repl_accepts_vec_with_erased_index() {
    // vnil : Vec Nat zero
    let vnil = Term::Con(ConName("vnil".into()), vec![]);
    check_top_with(vec_sig(), vnil.clone(), vec_ty(nat_ty(), zero())).expect("vnil : Vec Nat zero");

    // vcons zero zero vnil : Vec Nat (succ zero)
    let vcons = Term::Con(ConName("vcons".into()), vec![zero(), zero(), vnil]);
    check_top_with(vec_sig(), vcons, vec_ty(nat_ty(), succ(zero())))
        .expect("vcons zero zero vnil : Vec Nat (succ zero)");
}

// ----------------------------------------------------------------------------------------------
// 3. After erasure, a grade-`0` index binder is *absent* from the residual term.
// ----------------------------------------------------------------------------------------------

/// A length-indexed identity-ish function `λ (n :⁰ Nat). λ (x :¹ Nat). x`, whose type marks the
/// length `n` as erased (`grade 0`). The kernel accepts it (n is used only in the 0-fragment of
/// the type), and `erase` drops the `n`-binder entirely: the residual is just `λ x. x`, with no
/// reference to the erased index remaining.
#[test]
fn erased_index_absent_after_erasure() {
    // ty = (n : Nat) →⁰ (x : Nat) →¹ Nat
    let ty = Term::Pi(
        Grade::Zero,
        Rc::new(nat_ty()),
        Rc::new(Term::Pi(Grade::One, Rc::new(nat_ty()), Rc::new(nat_ty()))),
    );
    // term = λ n. λ x. x
    let term = Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Var(0)))));

    // The kernel accepts it: `n` is never used at runtime (grade 0), `x` exactly once.
    check_top_with(nat_sig(), term.clone(), ty.clone())
        .expect("erased index binder + linear value must check");

    // Erasure drops the grade-0 `n`-binder. The residual is `λ x. x` — a single lambda whose body
    // is `Var(0)`, with no surviving reference to the erased index.
    let erased = erase(&term, &ty);
    match &erased {
        Term::Lam(body) => match body.as_ref() {
            Term::Var(0) => {}
            other => panic!("erased body should be `Var(0)` (the kept `x`), got {other:?}"),
        },
        other => panic!("erasure should leave a single `λ x. x`, got {other:?}"),
    }
    assert!(
        !mentions_erased_index(&erased),
        "the erased index must not appear in the residual term: {erased:?}"
    );
    // Erasure is idempotent on the residual.
    assert_eq!(erase(&erased, &erased_ty_after_drop()), erased);
}

/// The type of the residual `λ x. x` after the grade-0 binder is removed: `(x : Nat) →¹ Nat`.
fn erased_ty_after_drop() -> Term {
    Term::Pi(Grade::One, Rc::new(nat_ty()), Rc::new(nat_ty()))
}

/// True if the term references what *was* the erased index — i.e. the `Erased` sentinel appears,
/// or (defensively) a stray free variable pointing past the residual scope.
fn mentions_erased_index(term: &Term) -> bool {
    matches!(term, Term::Erased)
        || match term {
            Term::Lam(b) | Term::PLam(b) => mentions_erased_index(b),
            Term::App(f, a) => mentions_erased_index(f) || mentions_erased_index(a),
            Term::Pair(a, b) => mentions_erased_index(a) || mentions_erased_index(b),
            _ => false,
        }
}

// ----------------------------------------------------------------------------------------------
// Helpers.
// ----------------------------------------------------------------------------------------------

fn read_surface(src: &str) -> blight_elab::Surface {
    let (sexpr, _) = blight_elab::read_one(src).expect("reads one s-expr");
    blight_elab::parse_surface(&sexpr).expect("parses surface")
}

/// Declare a minimal surface `Nat` so the elaborator can resolve it inside surface types.
fn declare_nat_surface(env: &mut blight_elab::ElabEnv) {
    use blight_elab::{parse_decl, read_one, Decl};
    let (form, _) = read_one("(defdata Nat () (zero) (succ (n Nat)))").expect("reads defdata");
    let decl: Decl = parse_decl(&form).expect("parses defdata");
    env.declare(&decl, None).expect("declares Nat");
}
