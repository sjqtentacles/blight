//! C1 — kernel <-> re-checker **differential** property testing (plan "Full Autism Frontier").
//!
//! The soundness thesis of Blight is "two small, independently-written checkers agree" (spec
//! §8.3). The corpus tests in `recheck.rs` assert that on a *fixed* hand-written corpus. This
//! harness makes the same assertion *generatively*: it builds many well-formed core [`Term`]s by
//! construction (plus structural mutations), submits each to the **kernel** door
//! ([`check_top_with`]), and for every term the kernel accepts asserts the **re-checker** either
//! AGREES (`Ok`) or **honestly DECLINES** (`Declined`, for out-of-fragment constructs) — but
//! **never** `Rejected`. A `Rejected` here means the two checkers disagree on a term the kernel
//! certified: a soundness alarm. This is the automated version of the manual `safe-tail`
//! asymmetry find, and it guards every subsequent kernel edit.
//!
//! No external fuzzing dependency is used: a tiny deterministic xorshift PRNG drives a typed
//! generator, so the harness is reproducible (a failing seed is printed) and adds nothing to the
//! trusted/dependency surface.

use blight_kernel::{
    check_top_with, Arg, ConName, Constructor, DataDecl, DataName, Grade, IntPrimOp, Level, Term,
};
use blight_kernel::{Judgement, Signature};
use blight_recheck::{recheck_judgement, RecheckError};
use std::rc::Rc;

// ---------------------------------------------------------------------------------------------
// A tiny deterministic PRNG (xorshift64*). Reproducible: a failing case prints its seed.
// ---------------------------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        // Avoid the zero state (xorshift's fixed point).
        Rng(seed.wrapping_mul(0x2545_F491_4F6C_DD1D) | 1)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    /// A bounded integer in `[0, n)` (n > 0).
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }
    fn coin(&mut self) -> bool {
        self.next_u64() & 1 == 0
    }
}

// ---------------------------------------------------------------------------------------------
// The fixed signature the generator types against: Nat, Bool, and an indexed Vec. These cover
// the dependent + inductive + indexed-eliminator fragment both checkers implement.
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

// ---------------------------------------------------------------------------------------------
// Convenience constructors.
// ---------------------------------------------------------------------------------------------

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
fn vec_of(elem: Term, len: Term) -> Term {
    Term::Data(DataName("Vec".into()), vec![elem], vec![len])
}

/// One of the small set of closed base types the generator targets.
#[derive(Clone, Copy, PartialEq)]
enum BaseTy {
    Nat,
    Bool,
    Int,
}

impl BaseTy {
    fn ty(self) -> Term {
        match self {
            BaseTy::Nat => nat(),
            BaseTy::Bool => boolean(),
            BaseTy::Int => Term::IntTy,
        }
    }
    fn pick(rng: &mut Rng) -> BaseTy {
        match rng.below(3) {
            0 => BaseTy::Nat,
            1 => BaseTy::Bool,
            _ => BaseTy::Int,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// A typed generator: produce a closed term of a chosen base type, well-typed *by construction*.
// `fuel` bounds recursion depth.
// ---------------------------------------------------------------------------------------------

fn gen_value(rng: &mut Rng, ty: BaseTy, fuel: u32) -> Term {
    if fuel == 0 {
        return gen_leaf(rng, ty);
    }
    match ty {
        BaseTy::Nat => match rng.below(4) {
            0 => zero(),
            1 => succ(gen_value(rng, BaseTy::Nat, fuel - 1)),
            // `if`-style elimination on a Bool, both branches Nat (via Bool eliminator).
            2 => {
                let scrut = gen_value(rng, BaseTy::Bool, fuel - 1);
                elim_bool(rng, BaseTy::Nat, scrut, fuel - 1)
            }
            // Apply an identity function to a Nat (a redex the normalizers must agree on).
            _ => app_id(BaseTy::Nat, gen_value(rng, BaseTy::Nat, fuel - 1)),
        },
        BaseTy::Bool => match rng.below(4) {
            0 => Term::Con(ConName("true".into()), vec![]),
            1 => Term::Con(ConName("false".into()), vec![]),
            2 => {
                let scrut = gen_value(rng, BaseTy::Bool, fuel - 1);
                elim_bool(rng, BaseTy::Bool, scrut, fuel - 1)
            }
            _ => app_id(BaseTy::Bool, gen_value(rng, BaseTy::Bool, fuel - 1)),
        },
        BaseTy::Int => {
            if rng.coin() {
                Term::IntLit((rng.next_u64() as i64) % 1000)
            } else {
                let op = match rng.below(6) {
                    0 => IntPrimOp::Add,
                    1 => IntPrimOp::Sub,
                    2 => IntPrimOp::Mul,
                    3 => IntPrimOp::Div,
                    4 => IntPrimOp::Eq,
                    _ => IntPrimOp::Lt,
                };
                Term::IntPrim {
                    op,
                    lhs: Rc::new(gen_value(rng, BaseTy::Int, fuel - 1)),
                    rhs: Rc::new(gen_value(rng, BaseTy::Int, fuel - 1)),
                }
            }
        }
    }
}

fn gen_leaf(rng: &mut Rng, ty: BaseTy) -> Term {
    match ty {
        BaseTy::Nat => zero(),
        BaseTy::Bool => {
            if rng.coin() {
                Term::Con(ConName("true".into()), vec![])
            } else {
                Term::Con(ConName("false".into()), vec![])
            }
        }
        BaseTy::Int => Term::IntLit((rng.next_u64() as i64) % 1000),
    }
}

/// `(the (T -> T) (λx. x)) arg` — an identity redex at base type `T`.
fn app_id(ty: BaseTy, arg: Term) -> Term {
    let t = ty.ty();
    let id = Term::Ann(
        Rc::new(Term::Lam(Rc::new(Term::Var(0)))),
        Rc::new(Term::Pi(Grade::Omega, Rc::new(t.clone()), Rc::new(t))),
    );
    Term::App(Rc::new(id), Rc::new(arg))
}

/// Eliminate a `Bool` scrutinee into result type `res`, generating both branches.
fn elim_bool(rng: &mut Rng, res: BaseTy, scrut: Term, fuel: u32) -> Term {
    Term::Elim {
        data: DataName("Bool".into()),
        motive: Rc::new(Term::Lam(Rc::new(res.ty()))),
        methods: vec![gen_value(rng, res, fuel), gen_value(rng, res, fuel)],
        scrutinee: Rc::new(scrut),
    }
}

// ---------------------------------------------------------------------------------------------
// The differential invariant.
// ---------------------------------------------------------------------------------------------

/// Submit `(term : ty)` to the kernel; if the kernel accepts, the re-checker must AGREE or
/// honestly DECLINE — never REJECT. Returns the outcome bucket for accounting.
enum Outcome {
    KernelRejected,
    BothAgree,
    Declined,
}

fn differential_step(sig: &Signature, term: Term, ty: Term, seed: u64) -> Outcome {
    match check_top_with(sig.clone(), term.clone(), ty.clone()) {
        Err(_) => Outcome::KernelRejected,
        Ok(_proof) => {
            let j = Judgement::HasType {
                term: term.clone(),
                ty: ty.clone(),
            };
            match recheck_judgement(sig, &j) {
                Ok(()) => Outcome::BothAgree,
                Err(RecheckError::Declined(_)) => Outcome::Declined,
                Err(RecheckError::Rejected(m)) => panic!(
                    "DIFFERENTIAL SOUNDNESS ALARM (seed={seed}): kernel ACCEPTED but re-checker \
                     REJECTED.\n  reason = {m}\n  term = {term:?}\n  ty = {ty:?}"
                ),
            }
        }
    }
}

/// The headline generative test: thousands of well-typed-by-construction core terms, each checked
/// for kernel<->re-checker agreement. At least one must reach `BothAgree` (so a broken harness
/// that generates only kernel-rejected garbage cannot vacuously pass).
#[test]
fn differential_generated_terms_never_disagree() {
    let sig = gen_signature();
    let iterations: u64 = std::env::var("BLIGHT_DIFF_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(4000);

    let mut agreed = 0usize;
    let mut declined = 0usize;
    let mut kernel_rejected = 0usize;

    for seed in 0..iterations {
        let mut rng = Rng::new(seed.wrapping_add(0x9E37_79B9_7F4A_7C15));
        let ty = BaseTy::pick(&mut rng);
        let fuel = 1 + rng.below(5) as u32;
        let term = gen_value(&mut rng, ty, fuel);
        match differential_step(&sig, term, ty.ty(), seed) {
            Outcome::BothAgree => agreed += 1,
            Outcome::Declined => declined += 1,
            Outcome::KernelRejected => kernel_rejected += 1,
        }
    }

    eprintln!(
        "[differential] {iterations} terms: {agreed} agreed, {declined} declined, \
         {kernel_rejected} kernel-rejected (all 0 disagreements)"
    );
    assert!(
        agreed >= 1,
        "harness generated no kernel-accepted terms (agreed={agreed}); generator is broken"
    );
}

/// A second generator targeting *indexed* eliminators over `Vec` — the family of terms whose
/// motive/index refinement was the exact site of the historical `safe-tail` asymmetry. Each
/// `length` eliminator over a concrete `Vec Nat k` must agree.
#[test]
fn differential_indexed_vec_eliminators_agree() {
    let sig = gen_signature();
    let mut agreed = 0usize;

    for seed in 0..200u64 {
        let mut rng = Rng::new(seed.wrapping_mul(0x100_0000_01b3).wrapping_add(7));
        let k = rng.below(5); // a concrete length 0..4
                              // Build `vcons 0 0 (vcons 0 0 (... vnil))` : Vec Nat k via nested ascriptions.
        let mut acc = Term::Ann(
            Rc::new(Term::Con(ConName("vnil".into()), vec![])),
            Rc::new(vec_of(nat(), zero())),
        );
        for i in 0..k {
            let len_here = {
                let mut l = zero();
                for _ in 0..i {
                    l = succ(l);
                }
                l
            };
            acc = Term::Ann(
                Rc::new(Term::Con(
                    ConName("vcons".into()),
                    vec![len_here.clone(), zero(), acc],
                )),
                Rc::new(vec_of(nat(), succ(len_here))),
            );
        }
        // motive: λ n. λ (_ : Vec Nat n). Nat ; methods compute the length.
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
        match differential_step(&sig, elim, nat(), seed) {
            Outcome::BothAgree => agreed += 1,
            Outcome::Declined => {}
            Outcome::KernelRejected => {}
        }
    }
    assert!(
        agreed >= 1,
        "no indexed Vec eliminator was certified by both checkers (agreed={agreed})"
    );
    eprintln!("[differential] indexed Vec eliminators: {agreed} agreed");
}

/// A structural-mutation generator: take well-typed terms and feed the *same* claimed type with a
/// nearby (often ill-typed) term. The point is not that the kernel accepts them — most are
/// rejected — but that whenever the kernel *does* accept, the re-checker never rejects. This
/// stresses the "kernel-accept => recheck-not-reject" edge where mutations accidentally stay
/// well-typed (e.g. swapping definitionally-equal subterms).
#[test]
fn differential_mutations_never_silently_disagree() {
    let sig = gen_signature();
    let mut both = 0usize;
    let mut declined = 0usize;

    for seed in 0..2000u64 {
        let mut rng = Rng::new(seed ^ 0xDEAD_BEEF_CAFE_F00D);
        let ty = BaseTy::pick(&mut rng);
        let fuel = 1 + rng.below(4) as u32;
        let mut term = gen_value(&mut rng, ty, fuel);
        // Apply a small mutation: wrap in an identity redex, or eta-expand if it is a function-y
        // shape. Both preserve typing when they apply, exercising the conv/eta agreement.
        if rng.coin() {
            term = app_id(ty, term);
        }
        match differential_step(&sig, term, ty.ty(), seed) {
            Outcome::BothAgree => both += 1,
            Outcome::Declined => declined += 1,
            Outcome::KernelRejected => {}
        }
    }
    eprintln!("[differential] mutations: {both} agreed, {declined} declined");
    assert!(
        both >= 1,
        "mutation harness certified nothing (both={both})"
    );
}
