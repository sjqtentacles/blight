//! Soundness **negative corpus** (Track D hardening): a hand-curated set of *truly ill-typed* core
//! terms. The contract for every entry is twofold:
//!
//!   1. the **kernel** door ([`check_top_with`]) must **reject** it (`Err`), and
//!   2. the independent **re-checker** must **never accept** it — for the in-fragment cases it must
//!      actively `Rejected` it (the strong property the plan calls "recheck Rejects truly-ill-typed");
//!      a small set of out-of-fragment shapes may instead honestly `Declined`, but *never* `Ok`.
//!
//! This is the dual of the positive corpus in `recheck.rs` (which asserts kernel-accept ⇒ re-check
//! agree/decline) and of the generative differential harnesses: here we pin down that *false*
//! judgements are caught by both checkers, so a regression that makes either door start accepting
//! garbage is caught immediately.

use blight_kernel::{
    check_top_with, Arg, ConName, Constructor, DataDecl, DataName, Grade, IntPrimOp, Judgement,
    Level, Signature, Term,
};
use blight_recheck::{recheck_judgement, RecheckError};

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
fn zero() -> Term {
    Term::Con(ConName("Zero".into()), vec![])
}
fn tru() -> Term {
    Term::Con(ConName("true".into()), vec![])
}
fn pi(a: Term, b: Term) -> Term {
    Term::Pi(Grade::Omega, Box::new(a), Box::new(b))
}

/// What the *re-checker* must do with an ill-typed term (the kernel must always reject).
#[derive(Clone, Copy)]
enum Expect {
    /// The strong soundness property: the re-checker actively `Rejected`s it.
    Reject,
    /// An out-of-(inference-)fragment shape the re-checker honestly `Declined`s — it never accepts,
    /// but cannot pin the contradiction without an annotation (e.g. an unannotated introduction form
    /// checked against a non-matching type, which the re-checker reaches by *inference*).
    RejectOrDecline,
}

/// An ill-typed core judgement plus a human label for diagnostics.
struct Bad {
    label: &'static str,
    term: Term,
    ty: Term,
    expect: Expect,
}

/// The in-fragment negative corpus: every entry is well within the fragment **both** checkers fully
/// implement, so the soundness contract is the strong one — kernel `Err` *and* re-checker `Rejected`.
fn must_reject_corpus() -> Vec<Bad> {
    vec![
        Bad {
            label: "Zero : Bool (constructor of the wrong datatype)",
            term: zero(),
            ty: boolean(),
            expect: Expect::Reject,
        },
        Bad {
            label: "true : Nat (constructor of the wrong datatype)",
            term: tru(),
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "Succ true : Nat (Succ applied to a Bool)",
            term: Term::Con(ConName("Succ".into()), vec![tru()]),
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "Succ : Nat (constructor under-applied; needs one arg)",
            term: Term::Con(ConName("Succ".into()), vec![]),
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "5 : Nat (an Int literal claimed at Nat)",
            term: Term::IntLit(5),
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "Zero : Int (a Nat constructor claimed at Int)",
            term: zero(),
            ty: Term::IntTy,
            expect: Expect::Reject,
        },
        Bad {
            // An unannotated λ reaches the re-checker via *inference*, which needs an annotation;
            // it never accepts, but honestly declines rather than pinning the Nat≠Π contradiction.
            label: "(λx. x) : Nat (a lambda claimed at a non-Π type)",
            term: Term::Lam(Box::new(Term::Var(0))),
            ty: nat(),
            expect: Expect::RejectOrDecline,
        },
        Bad {
            label: "Zero Zero : Nat (applying a non-function)",
            term: Term::App(
                Box::new(Term::Ann(Box::new(zero()), Box::new(nat()))),
                Box::new(zero()),
            ),
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "(the (Nat->Nat) (λx. true)) Zero : Nat (body returns the wrong type)",
            term: Term::App(
                Box::new(Term::Ann(
                    Box::new(Term::Lam(Box::new(tru()))),
                    Box::new(pi(nat(), nat())),
                )),
                Box::new(zero()),
            ),
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "int-add Zero Zero : Int (IntPrim on Nat operands)",
            term: Term::IntPrim {
                op: IntPrimOp::Add,
                lhs: Box::new(zero()),
                rhs: Box::new(zero()),
            },
            ty: Term::IntTy,
            expect: Expect::Reject,
        },
        Bad {
            label: "Bool-elim with a single method (wrong method count)",
            term: Term::Elim {
                data: DataName("Bool".into()),
                motive: Box::new(Term::Lam(Box::new(nat()))),
                methods: vec![zero()],
                scrutinee: Box::new(tru()),
            },
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "Bool-elim whose methods inhabit the wrong type",
            term: Term::Elim {
                data: DataName("Bool".into()),
                motive: Box::new(Term::Lam(Box::new(nat()))),
                methods: vec![tru(), tru()],
                scrutinee: Box::new(tru()),
            },
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "Nat-elim over a Bool scrutinee (data/scrutinee mismatch)",
            term: Term::Elim {
                data: DataName("Nat".into()),
                motive: Box::new(Term::Lam(Box::new(nat()))),
                methods: vec![zero(), Term::Lam(Box::new(Term::Lam(Box::new(zero()))))],
                scrutinee: Box::new(tru()),
            },
            ty: nat(),
            expect: Expect::Reject,
        },
        Bad {
            label: "Univ 0 : Univ 0 (universe inconsistency; should be Univ 1)",
            term: u(0),
            ty: u(0),
            expect: Expect::Reject,
        },
        Bad {
            label: "unbound Var(0) : Nat (free variable at top level)",
            term: Term::Var(0),
            ty: nat(),
            expect: Expect::RejectOrDecline,
        },
        Bad {
            label: "Nat : (Nat -> Nat) (a type claimed at a function type)",
            term: nat(),
            ty: pi(nat(), nat()),
            expect: Expect::Reject,
        },
        Bad {
            label: "(the Nat Zero) : Bool (a well-typed Nat ascription claimed at Bool)",
            term: Term::Ann(Box::new(zero()), Box::new(nat())),
            ty: boolean(),
            expect: Expect::Reject,
        },
    ]
}

/// The headline: every curated ill-typed term is rejected by the kernel AND actively rejected by the
/// re-checker — neither door accepts garbage, and the re-checker does not merely shrug (decline).
#[test]
fn negative_corpus_rejected_by_both_checkers() {
    let sig = gen_signature();
    let corpus = must_reject_corpus();
    let total = corpus.len();
    let mut rejected = 0usize;
    let mut declined = 0usize;
    for Bad {
        label,
        term,
        ty,
        expect,
    } in corpus
    {
        // 1. The kernel must reject.
        let kernel = check_top_with(sig.clone(), term.clone(), ty.clone());
        assert!(
            kernel.is_err(),
            "[{label}] KERNEL SOUNDNESS ALARM: kernel ACCEPTED an ill-typed term\n  term = {term:?}\n  ty = {ty:?}"
        );

        // 2. The re-checker must never accept; per the entry's expectation it actively rejects or
        //    (for inference-only shapes) honestly declines.
        let j = Judgement::HasType {
            term: term.clone(),
            ty: ty.clone(),
        };
        match (recheck_judgement(&sig, &j), expect) {
            (Err(RecheckError::Rejected(_)), _) => rejected += 1,
            (Err(RecheckError::Declined(_)), Expect::RejectOrDecline) => declined += 1,
            (Ok(()), _) => panic!(
                "[{label}] RE-CHECKER SOUNDNESS ALARM: re-checker ACCEPTED an ill-typed term\n  \
                 term = {term:?}\n  ty = {ty:?}"
            ),
            (Err(RecheckError::Declined(m)), Expect::Reject) => panic!(
                "[{label}] re-checker DECLINED an in-fragment ill-typed term (expected Rejected): {m}\n  \
                 term = {term:?}\n  ty = {ty:?}"
            ),
        }
    }
    eprintln!(
        "[negative] {total} ill-typed terms: kernel rejected ALL; re-checker {rejected} rejected, \
         {declined} declined (0 accepted)"
    );
    // The vast majority must be *actively* rejected (the strong property); only the curated
    // inference-only shapes are allowed to decline.
    assert!(
        rejected >= total - 2,
        "expected at most 2 inference-only declines, saw {declined}"
    );
}
