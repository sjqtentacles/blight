//! Property-based tests for normalization-by-evaluation (Track D hardening).
//!
//! `proptest` (with shrinking) generates well-typed *closed* core terms over a small fixed signature
//! (`Nat`/`Bool`/`Int`, with eliminators and β-redexes) and asserts the two defining properties of an
//! NbE normalizer:
//!
//!   1. **Idempotence.** Normalizing a term and normalizing its normal form yield the *same* term:
//!      `nf (nf t) ≡ nf t` syntactically. A normalizer that did not reach a fixed point would expose
//!      a missed reduction here.
//!   2. **Convertibility with the normal form.** A term is definitionally equal to its own normal
//!      form: `conv t (nf t)`. This is the soundness side — `nf` must preserve meaning under `conv`,
//!      the relation the kernel's type-checker relies on.
//!
//! The generator builds terms that are well-typed by construction, so `eval` is always defined; a
//! failing case shrinks to a minimal term and is replayable from the saved regression seed.

use blight_kernel::normalize::{conv, eval, quote};
use blight_kernel::value::Env;
use blight_kernel::{
    Arg, ConName, Constructor, DataDecl, DataName, Grade, IntPrimOp, Signature, Term,
};
use proptest::prelude::*;
use std::rc::Rc;

// ---------------------------------------------------------------------------------------------
// The fixed signature the generator types against: Nat and Bool (closed, no params/indices).
// ---------------------------------------------------------------------------------------------

fn gen_signature() -> Signature {
    let mut sig = Signature::new();
    sig.declare(DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("Zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("Succ".into()),
                args: vec![Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    sig.declare(DataDecl {
        name: DataName("Bool".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("true".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("false".into()),
                args: vec![],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    sig
}

fn nat() -> Term {
    Term::Data(DataName("Nat".into()), vec![], vec![])
}
fn boolean() -> Term {
    Term::Data(DataName("Bool".into()), vec![], vec![])
}

/// A closed base type the generator targets.
#[derive(Clone, Copy, Debug)]
enum Ty {
    Nat,
    Bool,
    Int,
}

impl Ty {
    fn term(self) -> Term {
        match self {
            Ty::Nat => nat(),
            Ty::Bool => boolean(),
            Ty::Int => Term::IntTy,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// A typed term: a value plus the base type it inhabits, so the property can normalize at the right
// type. We build the strategy directly (recursive, fuel-bounded) so every term is closed + typed.
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Typed {
    term: Term,
    ty: Ty,
}

/// `(the (T -> T) (λx. x)) arg` — an identity redex at base type `T` (a β-redex the normalizer
/// must reduce away).
fn app_id(ty: Term, arg: Term) -> Term {
    let id = Term::Ann(
        Rc::new(Term::Lam(Rc::new(Term::Var(0)))),
        Rc::new(Term::Pi(Grade::Omega, Rc::new(ty.clone()), Rc::new(ty))),
    );
    Term::App(Rc::new(id), Rc::new(arg))
}

/// `if scrut then a else b` via the `Bool` eliminator, both branches at result type `res`.
fn elim_bool(res: Term, scrut: Term, a: Term, b: Term) -> Term {
    Term::Elim {
        data: DataName("Bool".into()),
        motive: Rc::new(Term::Lam(Rc::new(res))),
        methods: vec![a, b],
        scrutinee: Rc::new(scrut),
    }
}

fn arb_typed(fuel: u32) -> BoxedStrategy<Typed> {
    // Leaves: a literal of each base type.
    let leaf = prop_oneof![
        Just(Typed {
            term: Term::Con(ConName("Zero".into()), vec![]),
            ty: Ty::Nat
        }),
        any::<bool>().prop_map(|b| Typed {
            term: Term::Con(ConName(if b { "true" } else { "false" }.into()), vec![]),
            ty: Ty::Bool,
        }),
        (0i64..1000).prop_map(|n| Typed {
            term: Term::IntLit(n),
            ty: Ty::Int
        }),
    ];
    if fuel == 0 {
        return leaf.boxed();
    }
    let sub = arb_typed(fuel - 1);
    let sub2 = arb_typed(fuel - 1);
    let sub3 = arb_typed(fuel - 1);

    // Recursive shapes: Succ on a Nat, an identity β-redex, a Bool eliminator, and Int prim ops.
    prop_oneof![
        2 => leaf,
        // Succ : Nat -> Nat
        1 => sub.clone().prop_map(|t| {
            let n = coerce(t, Ty::Nat);
            Typed { term: Term::Con(ConName("Succ".into()), vec![n]), ty: Ty::Nat }
        }),
        // identity redex at the subterm's own type
        1 => sub.clone().prop_map(|t| {
            let ty = t.ty;
            Typed { term: app_id(ty.term(), t.term), ty }
        }),
        // if-then-else with a Bool scrutinee; both branches share the (chosen) result type
        1 => (sub.clone(), sub2.clone(), sub3.clone()).prop_map(|(s, a, b)| {
            let scrut = coerce(s, Ty::Bool);
            // pick the result type from branch `a`, coercing `b` to match
            let res = a.ty;
            let bt = coerce(b, res);
            let at = a.term;
            Typed { term: elim_bool(res.term(), scrut, at, bt), ty: res }
        }),
        // Int primitive op
        1 => (sub, sub2, 0u32..6).prop_map(|(l, r, opi)| {
            let op = match opi {
                0 => IntPrimOp::Add,
                1 => IntPrimOp::Sub,
                2 => IntPrimOp::Mul,
                3 => IntPrimOp::Div,
                4 => IntPrimOp::Eq,
                _ => IntPrimOp::Lt,
            };
            Typed {
                term: Term::IntPrim {
                    op,
                    lhs: Rc::new(coerce(l, Ty::Int)),
                    rhs: Rc::new(coerce(r, Ty::Int)),
                },
                // Eq/Lt return a Bool-coded Int in the kernel's IntPrim semantics; treat as Int.
                ty: Ty::Int,
            }
        }),
    ]
    .boxed()
}

/// Coerce a generated `Typed` to a *required* base type. If it already matches, keep it; otherwise
/// replace it with a canonical literal of the required type (so the result stays well-typed). This
/// keeps the strategy total without a full bidirectional generator.
fn coerce(t: Typed, want: Ty) -> Term {
    match (t.ty, want) {
        (Ty::Nat, Ty::Nat) | (Ty::Bool, Ty::Bool) | (Ty::Int, Ty::Int) => t.term,
        (_, Ty::Nat) => Term::Con(ConName("Zero".into()), vec![]),
        (_, Ty::Bool) => Term::Con(ConName("true".into()), vec![]),
        (_, Ty::Int) => Term::IntLit(0),
    }
}

/// Normalize a closed term against the signature: `nf t = quote(0, eval(t))`.
fn nf(sig: &Rc<Signature>, t: &Term) -> Term {
    let env = Env::with_sig(sig.clone());
    quote(0, &eval(&env, t))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    /// NbE is idempotent: normalizing the normal form changes nothing.
    #[test]
    fn nbe_is_idempotent(t in arb_typed(5)) {
        let sig = Rc::new(gen_signature());
        let n1 = nf(&sig, &t.term);
        let n2 = nf(&sig, &n1);
        prop_assert_eq!(&n1, &n2, "nf not idempotent for {:?}", t.term);
    }

    /// A term is convertible to its own normal form (NbE preserves meaning under `conv`).
    #[test]
    fn term_is_conv_with_its_normal_form(t in arb_typed(5)) {
        let sig = Rc::new(gen_signature());
        let env = Env::with_sig(sig.clone());
        let v_term = eval(&env, &t.term);
        let n = nf(&sig, &t.term);
        let v_nf = eval(&env, &n);
        prop_assert!(conv(0, &v_term, &v_nf), "term not conv with its nf: {:?}", t.term);
    }
}
