//! Acceptance: **grade-0 content is provably absent from the emitted code** (spec §7.2, §9).
//!
//! A length-indexed `Vec a n` carries its length `n` only in its *type*; `n` is grade-0, so it is
//! computationally irrelevant and must leave **no trace** in the native artifact. We model the
//! canonical situation: a `main` whose value is `Succ Zero`, supplied through a function with a
//! grade-0 (erased) index argument whose would-be value is a *distinctive* constructor
//! (`PhantomIdx`). We then compile and assert:
//!
//!   1. the `PhantomIdx` constructor's runtime tag never appears in the emitted LLVM IR, and
//!   2. the IR is byte-for-byte identical to compiling the same `main` **without** the phantom
//!      index — i.e. the grade-0 argument changed nothing in the generated code.
//!
//! Gated on the `llvm` feature (needs the inkwell emitter); pure-Rust passes are tested in-crate.
#![cfg(feature = "llvm")]

use blight_kernel::semiring::Grade;
use blight_kernel::signature::{Arg, Constructor, DataDecl};
use blight_kernel::term::{Level, Term};
use std::rc::Rc;
use blight_kernel::{ConName, DataName, Signature};

fn nat_sig() -> Signature {
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
            // A distinctive constructor that only ever appears inside the (grade-0) phantom index.
            Constructor {
                name: ConName("PhantomIdx".into()),
                args: vec![],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    sig
}

fn u0() -> Term {
    Term::Univ(Level::Zero)
}

fn succ_zero() -> Term {
    Term::Con(
        ConName("Succ".into()),
        vec![Term::Con(ConName("Zero".into()), vec![])],
    )
}

/// `main` *without* any phantom index: just the bare value `Succ Zero`.
fn main_plain() -> (Term, Term) {
    (
        succ_zero(),
        Term::Data(DataName("Nat".into()), vec![], vec![]),
    )
}

/// `main` *with* a grade-0 phantom index. Type: `(idx :^0 Nat) -> Nat`; body: `λ idx. Succ Zero`,
/// applied to the distinctive `PhantomIdx` value. Erasure drops the grade-0 binder; the supplying
/// application is dead and removed by the backend, so `PhantomIdx` must vanish entirely.
fn main_with_phantom() -> (Term, Term) {
    // outer : (idx :^0 Nat) -> Nat   =   λ idx. (λ ignore. Succ Zero) idx
    let inner = Term::App(
        Rc::new(Term::Lam(Rc::new(succ_zero()))), // λ ignore. Succ Zero  (ignores its arg)
        Rc::new(Term::Var(0)),                     // applied to idx (the grade-0 binder)
    );
    let term = Term::App(
        Rc::new(Term::Lam(Rc::new(inner))),
        // The phantom index value: a distinctive constructor that, if not erased, would emit a
        // `bl_con` for its tag.
        Rc::new(Term::Con(ConName("PhantomIdx".into()), vec![])),
    );
    let ty = Term::Pi(
        Grade::Zero,
        Rc::new(Term::Data(DataName("Nat".into()), vec![], vec![])),
        Rc::new(Term::Data(DataName("Nat".into()), vec![], vec![])),
    );
    let _ = u0();
    (term, ty)
}

/// The runtime constructor index the emitter assigns to `PhantomIdx` (see `llvm::con_index`): a
/// stable small id derived from the first byte of the name, here `'P' = 0x50 = 80`. A surviving
/// phantom would appear as a `bl_con(i64 80, …)` call in the IR.
const PHANTOM_TAG: &str = "i64 80";

#[test]
fn grade0_absent_from_binary() {
    let sig = nat_sig();

    let (plain, plain_ty) = main_plain();
    let (phantom, phantom_ty) = main_with_phantom();

    let ir_plain = blight_codegen::driver::emit_ir(&plain, &plain_ty, &sig).expect("plain ir");
    let ir_phantom =
        blight_codegen::driver::emit_ir(&phantom, &phantom_ty, &sig).expect("phantom ir");

    // The phantom index's constructor tag must not appear in the emitted code at all.
    assert!(
        !ir_phantom.contains(PHANTOM_TAG),
        "grade-0 PhantomIdx tag leaked into the emitted IR:\n{ir_phantom}"
    );

    // Stronger: the grade-0 argument changed *nothing*. With the inlined-away shell pruned, the
    // entire emitted module — every function, not just the entry — is byte-for-byte identical to
    // the no-index version. The erased index is provably absent from the binary.
    assert_eq!(
        ir_plain, ir_phantom,
        "the erased index left a trace in the emitted module"
    );
}
