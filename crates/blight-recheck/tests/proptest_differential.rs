//! Property-based **kernel ↔ re-checker** differential testing (Track D hardening).
//!
//! This is the `proptest` (shrinking, reproducible) sibling of the hand-rolled-PRNG harness in
//! `differential.rs`. It generates well-typed-by-construction closed core [`Term`]s, submits each to
//! the **kernel** door ([`check_top_with`]), and for every term the kernel *accepts* asserts the
//! **re-checker** either AGREES (`Ok`) or honestly DECLINES (`Declined`) — but **never** `Rejected`.
//! A `Rejected` on a kernel-certified term is the soundness alarm the whole effort guards against.
//!
//! proptest's shrinker means any future regression collapses to a *minimal* disagreeing term and is
//! replayable from the saved `proptest-regressions` seed — strictly stronger triage than the raw PRNG
//! harness, which only prints the failing seed.

use blight_kernel::{
    check_top_with, Arg, ConName, Constructor, DataDecl, DataName, Grade, IntPrimOp, Signature,
    Term,
};
use blight_kernel::{Judgement, Level};
use blight_recheck::{recheck_judgement, RecheckError};
use proptest::prelude::*;
use std::rc::Rc;

// ---------------------------------------------------------------------------------------------
// The fixed signature: Nat, Bool, and an indexed Vec — the dependent + inductive + indexed fragment
// both checkers implement (mirrors differential.rs::gen_signature).
// ---------------------------------------------------------------------------------------------

fn u(n: u32) -> Term {
    let mut l = Level::Zero;
    for _ in 0..n {
        l = Level::Suc(Box::new(l));
    }
    Term::Univ(l)
}

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
    sig.declare(DataDecl {
        name: DataName("Vec".into()),
        params: vec![u(0)],
        indices: vec![Term::Data(DataName("Nat".into()), vec![], vec![])],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("vnil".into()),
                args: vec![],
                result_indices: vec![Term::Con(ConName("Zero".into()), vec![])],
            },
            Constructor {
                name: ConName("vcons".into()),
                args: vec![
                    Arg::NonRec(Term::Data(DataName("Nat".into()), vec![], vec![])),
                    Arg::NonRec(Term::Var(1)),
                    Arg::Rec(vec![Term::Var(1)]),
                ],
                result_indices: vec![Term::Con(ConName("Succ".into()), vec![Term::Var(2)])],
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
fn vec_of(elem: Term, len: Term) -> Term {
    Term::Data(DataName("Vec".into()), vec![elem], vec![len])
}
fn zero() -> Term {
    Term::Con(ConName("Zero".into()), vec![])
}
fn succ(n: Term) -> Term {
    Term::Con(ConName("Succ".into()), vec![n])
}

// ---------------------------------------------------------------------------------------------
// A typed term: value + the base type it inhabits.
// ---------------------------------------------------------------------------------------------

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
        1 => sub.clone().prop_map(|t| {
            Typed { term: succ(coerce(t, Ty::Nat)), ty: Ty::Nat }
        }),
        1 => sub.clone().prop_map(|t| {
            let ty = t.ty;
            Typed { term: app_id(ty.term(), t.term), ty }
        }),
        1 => (sub.clone(), sub2.clone(), sub3.clone()).prop_map(|(s, a, b)| {
            let scrut = coerce(s, Ty::Bool);
            let res = a.ty;
            let bt = coerce(b, res);
            Typed { term: elim_bool(res.term(), scrut, a.term, bt), ty: res }
        }),
        // `if-zero` (T1a): an Int scrutinee, two branches of a common type. Emitting it here is what
        // makes the differential harness actually exercise the new fragment (coverage untested =
        // coverage absent) — the kernel and re-checker must never disagree on it.
        1 => (sub.clone(), sub2.clone(), sub3).prop_map(|(s, a, b)| {
            let scrut = coerce(s, Ty::Int);
            let res = a.ty;
            let bt = coerce(b, res);
            Typed {
                term: Term::IfZero {
                    scrut: Rc::new(scrut),
                    then_: Rc::new(a.term),
                    else_: Rc::new(bt),
                },
                ty: res,
            }
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
                term: Term::IntPrim {
                    op,
                    lhs: Rc::new(coerce(l, Ty::Int)),
                    rhs: Rc::new(coerce(r, Ty::Int)),
                },
                ty: Ty::Int,
            }
        }),
    ]
    .boxed()
}

/// The differential invariant: kernel-accept ⇒ re-checker AGREES or DECLINES, never REJECTS.
fn assert_no_disagreement(sig: &Signature, term: &Term, ty: &Term) -> Result<(), TestCaseError> {
    if check_top_with(sig.clone(), term.clone(), ty.clone()).is_ok() {
        let j = Judgement::HasType {
            term: term.clone(),
            ty: ty.clone(),
        };
        if let Err(RecheckError::Rejected(m)) = recheck_judgement(sig, &j) {
            return Err(TestCaseError::fail(format!(
                "DIFFERENTIAL SOUNDNESS ALARM: kernel ACCEPTED but re-checker REJECTED.\n  \
                 reason = {m}\n  term = {term:?}\n  ty = {ty:?}"
            )));
        }
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// Generated well-typed closed terms: the kernel and re-checker never disagree.
    #[test]
    fn generated_terms_never_disagree(t in arb_typed(5)) {
        let sig = gen_signature();
        let ty = t.ty.term();
        assert_no_disagreement(&sig, &t.term, &ty)?;
    }

    /// Mutation stress: wrap in an identity redex (preserves typing where it applies). Exercises the
    /// conv/η agreement edge where a mutation accidentally stays well-typed.
    #[test]
    fn mutated_terms_never_disagree(t in arb_typed(4), wrap in any::<bool>()) {
        let sig = gen_signature();
        let ty = t.ty.term();
        let term = if wrap { app_id(ty.clone(), t.term) } else { t.term };
        assert_no_disagreement(&sig, &term, &ty)?;
    }
}

// Indexed `Vec` eliminators (the historical `safe-tail` asymmetry site): build `vcons…vnil : Vec
// Nat k` for a generated `k`, run the length eliminator, and require kernel ↔ re-checker agreement.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn indexed_vec_length_eliminator_agrees(k in 0usize..6) {
        let sig = gen_signature();
        let mut acc = Term::Ann(
            Rc::new(Term::Con(ConName("vnil".into()), vec![])),
            Rc::new(vec_of(nat(), zero())),
        );
        for i in 0..k {
            let mut len_here = zero();
            for _ in 0..i {
                len_here = succ(len_here);
            }
            acc = Term::Ann(
                Rc::new(Term::Con(
                    ConName("vcons".into()),
                    vec![len_here.clone(), zero(), acc],
                )),
                Rc::new(vec_of(nat(), succ(len_here))),
            );
        }
        let motive = Term::Lam(Rc::new(Term::Lam(Rc::new(nat()))));
        let m_vnil = zero();
        let m_vcons = Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Lam(Rc::new(
            Term::Lam(Rc::new(succ(Term::Var(0)))),
        ))))));
        let elim = Term::Elim {
            data: DataName("Vec".into()),
            motive: Rc::new(motive),
            methods: vec![m_vnil, m_vcons],
            scrutinee: Rc::new(acc),
        };
        assert_no_disagreement(&sig, &elim, &nat())?;
    }
}
