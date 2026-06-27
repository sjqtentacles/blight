//! # blight-codegen — the Blight native backend (untrusted)
//!
//! This crate compiles **checked** Blight core terms to native code (spec §7). It is entirely
//! **untrusted** (spec §7.1): every term it receives has already been validated by the spore, so a
//! miscompilation here is an ordinary bug — it can produce a wrong answer or crash, but it can
//! never manufacture a false [`blight_kernel::Proof`]. No kernel trust is added.
//!
//! ## Pipeline (spec §7)
//! ```text
//!   ElabEnv.globals (closed, inlined core Term + type)
//!     → erase            grade-0 content removed (kernel) + dead-arg pass
//!     → lower            Term → Cir  (Elim→Case, Later→Fix, drop type/cubical layer)
//!     → closure_conv     lambda lifting to top-level functions w/ env records
//!     → mono             whole-program monomorphization (intra-term; spec §7.5)
//!     → anf              ANF + tail-call→jump + delay-trampoline loop (spec §7.4 tier 1)
//!     → llvm             inkwell codegen, tailcc/musttail (spec §7.4 tier 2)  [feature = "llvm"]
//!     → object → clang link → native binary
//! ```
//! The C runtime (copying GC, segmented stack, delay + effect trampolines) lives under
//! `runtime/` and is linked in by the driver.
//!
//! Everything up to and including ANF is pure Rust and unit-testable without a system LLVM; the
//! LLVM emission and the linked-binary integration tests are gated behind the `llvm` feature.

pub mod anf;
pub mod closure;
pub mod ir;
pub mod lower;
pub mod mono;
pub mod region;

#[cfg(feature = "llvm")]
pub mod driver;
#[cfg(feature = "llvm")]
pub mod llvm;
#[cfg(feature = "llvm")]
pub mod runtime;

pub use anf::{AnfFunc, AnfProgram, Atom, Comp, Tail, TailArm};
pub use ir::{Alloc, Arm, Cir, Func, Program};

#[cfg(feature = "llvm")]
pub use llvm::Target;
