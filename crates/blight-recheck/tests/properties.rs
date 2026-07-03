//! Generative **soundness** and **fragment-completeness** properties for the re-checker (Track D).
//!
//! Two complementary `proptest` properties over the fully-supported core fragment (Nat/Bool/Int,
//! eliminators, β-redexes — no Kan/Glue, so nothing is ever legitimately *declined*):
//!
//!   * **Fragment-completeness.** For every generated well-typed-by-construction term the *kernel*
//!     accepts, the re-checker returns `Ok` — it neither rejects (soundness alarm) nor declines
//!     (a completeness gap on a fragment it claims to support). This is stronger than the
//!     differential property in `proptest_differential.rs`, which permits `Declined`.
//!   * **Soundness (contrapositive).** For every generated judgement, *if* the kernel rejects it,
//!     the re-checker must **never** return `Ok`. We deliberately generate many type-mismatched
//!     judgements (a term of one base type claimed at another) so the kernel rejects most of them,
//!     and assert the re-checker does not certify what the kernel refused.
//!
//! Both shrink to a minimal witness and replay from the saved regression seed.

use blight_kernel::{
    check_top_with, Arg, ConName, Constructor, DataDecl, DataName, Grade, IntPrimOp, Judgement,
    Signature, Term,
};
use blight_recheck::{recheck_judgement, RecheckError};
use proptest::prelude::*;
use std::rc::Rc;

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
fn zero() -> Term {
    Term::Con(ConName("Zero".into()), vec![])
}
fn succ(n: Term) -> Term {
    Term::Con(ConName("Succ".into()), vec![n])
}

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
    /// A *different* base type, for building deliberate mismatches.
    fn other(self) -> Ty {
        match self {
            Ty::Nat => Ty::Bool,
            Ty::Bool => Ty::Int,
            Ty::Int => Ty::Nat,
        }
    }
}

#[derive(Clone, Debug)]
struct Typed {
    term: Term,
    ty: Ty,
}

fn app_id(ty: Term, arg: Term) -> Term {
    let id = Term::Ann(
        Rc::new(Term::Lam(Rc::new(Term::Var(0)))),
        Rc::new(Term::Pi(Grade::Omega, Rc::new(ty.clone()), Rc::new(ty))),
    );
    Term::App(Rc::new(id), Rc::new(arg))
}

fn elim_bool(res: Term, scrut: Term, a: Term, b: Term) -> Term {
    Term::Elim {
        data: DataName("Bool".into()),
        motive: Rc::new(Term::Lam(Rc::new(res))),
        methods: vec![a, b],
        scrutinee: Rc::new(scrut),
    }
}

fn coerce(t: Typed, want: Ty) -> Term {
    match (t.ty, want) {
        (Ty::Nat, Ty::Nat) | (Ty::Bool, Ty::Bool) | (Ty::Int, Ty::Int) => t.term,
        (_, Ty::Nat) => zero(),
        (_, Ty::Bool) => Term::Con(ConName("true".into()), vec![]),
        (_, Ty::Int) => Term::IntLit(0),
    }
}

fn arb_typed(fuel: u32) -> BoxedStrategy<Typed> {
    let leaf = prop_oneof![
        Just(Typed {
            term: zero(),
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
    prop_oneof![
        2 => leaf,
        1 => sub.clone().prop_map(|t| Typed { term: succ(coerce(t, Ty::Nat)), ty: Ty::Nat }),
        1 => sub.clone().prop_map(|t| {
            let ty = t.ty;
            Typed { term: app_id(ty.term(), t.term), ty }
        }),
        1 => (sub.clone(), sub2.clone(), sub3).prop_map(|(s, a, b)| {
            let scrut = coerce(s, Ty::Bool);
            let res = a.ty;
            let bt = coerce(b, res);
            Typed { term: elim_bool(res.term(), scrut, a.term, bt), ty: res }
        }),
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
                term: Term::IntPrim { op, lhs: Rc::new(coerce(l, Ty::Int)), rhs: Rc::new(coerce(r, Ty::Int)) },
                ty: Ty::Int,
            }
        }),
    ]
    .boxed()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(3000))]

    /// Fragment-completeness: kernel-accepted in-fragment terms are re-checked to `Ok` (never
    /// declined on the fragment the re-checker claims to fully support, never rejected).
    #[test]
    fn fragment_completeness_kernel_accept_implies_recheck_ok(t in arb_typed(5)) {
        let sig = gen_signature();
        let ty = t.ty.term();
        if check_top_with(sig.clone(), t.term.clone(), ty.clone()).is_ok() {
            let j = Judgement::HasType { term: t.term.clone(), ty };
            match recheck_judgement(&sig, &j) {
                Ok(()) => {}
                Err(RecheckError::Declined(m)) => prop_assert!(
                    false,
                    "completeness gap: re-checker DECLINED an in-fragment kernel-accepted term: {m}\n  term = {:?}",
                    t.term
                ),
                Err(RecheckError::Rejected(m)) => prop_assert!(
                    false,
                    "SOUNDNESS ALARM: re-checker REJECTED a kernel-accepted term: {m}\n  term = {:?}",
                    t.term
                ),
            }
        }
    }

    /// Soundness (contrapositive): for a deliberately type-mismatched judgement, whenever the kernel
    /// rejects, the re-checker must NEVER return `Ok`.
    #[test]
    fn soundness_kernel_reject_implies_recheck_not_ok(t in arb_typed(4)) {
        let sig = gen_signature();
        let wrong = t.ty.other().term();
        if check_top_with(sig.clone(), t.term.clone(), wrong.clone()).is_err() {
            let j = Judgement::HasType { term: t.term.clone(), ty: wrong.clone() };
            prop_assert!(
                recheck_judgement(&sig, &j).is_err(),
                "SOUNDNESS ALARM: re-checker ACCEPTED a kernel-rejected mismatch\n  term = {:?}\n  ty = {:?}",
                t.term, wrong
            );
        }
    }
}
