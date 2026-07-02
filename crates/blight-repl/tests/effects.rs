//! M2 acceptance tests (spec §4, §9 M2): "the `State` counter runs under its handler" — the
//! flagship end-to-end example. We drive the *kernel* public API directly (surface `effect`/
//! `handle`/`perform` syntax lands with the `surface-effects` step / M3 tower), so this is a
//! black-box test of the trusted base: a `State` effect, a state-threading handler, type-checked
//! through `check_top_with` (the handler discharges `State`, so the program is *pure*), and then
//! *evaluated* through NbE to a concrete value.

use blight_kernel::normalize::{conv, eval, quote};
use blight_kernel::value::Env;
use blight_kernel::{
    check_top_with, ConName, Constructor, DataDecl, DataName, EffDecl, EffName, Grade, OpSig,
    Signature, Term,
};
use std::rc::Rc;

// ---- fixtures -------------------------------------------------------------------------------

fn nat_name() -> DataName {
    DataName("Nat".into())
}
fn nat_ty() -> Term {
    Term::Data(nat_name(), vec![], vec![])
}
fn unit_name() -> DataName {
    DataName("Unit".into())
}
fn unit_ty() -> Term {
    Term::Data(unit_name(), vec![], vec![])
}
fn tt() -> Term {
    Term::Con(ConName("tt".into()), vec![])
}
fn zero() -> Term {
    Term::Con(ConName("zero".into()), vec![])
}
fn succ(n: Term) -> Term {
    Term::Con(ConName("succ".into()), vec![n])
}

/// A signature with `Nat`, `Unit`, and the `State` effect: `get : Unit → Nat`, `put : Nat → Unit`.
fn state_sig() -> Signature {
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
                args: vec![blight_kernel::Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    sig.declare(DataDecl {
        name: unit_name(),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![Constructor {
            name: ConName("tt".into()),
            args: vec![],
            result_indices: vec![],
        }],
        path_constructors: vec![],
    });
    let state = EffDecl {
        name: EffName::new("State"),
        params: vec![],
        ops: vec![
            OpSig {
                name: "get".into(),
                param_ty: unit_ty(),
                result_ty: nat_ty(),
                cont_grade: Grade::One,
            },
            OpSig {
                name: "put".into(),
                param_ty: nat_ty(),
                result_ty: unit_ty(),
                cont_grade: Grade::One,
            },
        ],
    };
    sig.check_effect(&state).expect("State well-formed");
    sig.declare_effect(state);
    sig
}

fn perform(op: &str, arg: Term) -> Term {
    Term::Op {
        effect: EffName::new("State"),
        op: op.into(),
        type_args: vec![],
        arg: Box::new(arg),
    }
}

/// The counter computation `get; put (succ n); return n`, written so each operation sits in an
/// *argument* position (call-by-value sequencing bubbles the effectful-neutral there):
///
/// `(λ n. (λ _. n) (perform put (succ n))) (perform get tt)`
///
/// It reads the state into `n`, writes `succ n`, and returns the original `n`. Its type is `Nat`
/// (in row `State`).
fn counter() -> Term {
    // inner: (λ _:Unit. n) (perform put (succ n))   — `_:Unit` because `put` returns `Unit`.
    let inner = Term::App(
        Box::new(Term::Ann(
            Box::new(Term::Lam(Box::new(Term::Var(1)))), // λ _. n
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(unit_ty()),
                Box::new(nat_ty()),
            )),
        )),
        Box::new(perform("put", succ(Term::Var(0)))), // perform put (succ n)
    );
    Term::App(
        Box::new(Term::Ann(
            Box::new(Term::Lam(Box::new(inner))), // λ n. inner
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(nat_ty()),
                Box::new(nat_ty()),
            )),
        )),
        Box::new(perform("get", tt())), // perform get tt
    )
}

/// The state-threading handler with result type `C = Nat → (Nat × Nat)` (state ↦ (result, state')).
///
/// - `return x. λ s. (x, s)`                  — deliver the result with the current state.
/// - `get _ k. λ s. (k s) s`                  — resume with the current state `s`, then run at `s`.
/// - `put s' k. λ _. (k tt) s'`               — resume with `tt`, then run at the new state `s'`.
fn handled(body: Term) -> Term {
    Term::Handle {
        body: Box::new(body),
        // return x. λ s. (x, s)   (after `λ s`: s = idx 0, x = idx 1)
        return_clause: Box::new(Term::Lam(Box::new(Term::Pair(
            Box::new(Term::Var(1)),
            Box::new(Term::Var(0)),
        )))),
        op_clauses: vec![
            (
                // get _ k. λ s. (k s) s   (after `λ s`: s=0, k=1, x=2)
                "get".into(),
                Box::new(Term::Lam(Box::new(Term::App(
                    Box::new(Term::App(Box::new(Term::Var(1)), Box::new(Term::Var(0)))),
                    Box::new(Term::Var(0)),
                )))),
            ),
            (
                // put s' k. λ _. (k tt) s'   (after `λ _`: _=0, k=1, s'=2)
                "put".into(),
                Box::new(Term::Lam(Box::new(Term::App(
                    Box::new(Term::App(Box::new(Term::Var(1)), Box::new(tt()))),
                    Box::new(Term::Var(2)),
                )))),
            ),
        ],
    }
}

/// `C = Nat → (Nat × Nat)`.
fn state_transformer_ty() -> Term {
    Term::Pi(
        Grade::Omega,
        Box::new(nat_ty()),
        Box::new(Term::Sigma(Box::new(nat_ty()), Box::new(nat_ty()))),
    )
}

// ---- the acceptance test --------------------------------------------------------------------

/// The flagship M2 example (spec §4.3, §9 M2): a `State` counter, run under a state-threading
/// handler, type-checks (the handler discharges `State`, so the whole program is a *pure proof*)
/// and *computes* to the expected `(result, final-state)` pair.
#[test]
fn state_counter_runs_under_handler() {
    let sig = state_sig();

    // The handled program has type `Nat → (Nat × Nat)` and is **pure** (State is discharged):
    // `check_top_with` demands the empty effect row, so this passing *is* the typing half of the
    // acceptance.
    let program = handled(counter());
    check_top_with(sig.clone(), program.clone(), state_transformer_ty())
        .expect("the handled State counter must type-check as a pure (State-discharged) program");

    // Run it at initial state 0: `(handle counter {…}) zero`.
    let run = Term::App(Box::new(program), Box::new(zero()));
    let env = Env::with_sig(Rc::new(sig));
    let result = eval(&env, &run);

    // Expected `(0, 1)`: the counter returns the original state `0`, and the final state is `succ 0`.
    let expected = Term::Pair(Box::new(zero()), Box::new(succ(zero())));
    let expected_v = eval(&env, &expected);
    assert!(
        conv(0, &result, &expected_v),
        "State counter computed {:?}, expected (0, succ 0)",
        quote(0, &result)
    );
}

/// Sanity: the *unhandled* counter carries the `State` effect, so it is rejected as a top-level
/// proof (the proof boundary demands purity).
#[test]
fn unhandled_counter_is_not_a_proof() {
    let sig = state_sig();
    let r = check_top_with(sig, counter(), nat_ty());
    assert!(
        r.is_err(),
        "an unhandled effectful computation cannot be a complete proof"
    );
}
