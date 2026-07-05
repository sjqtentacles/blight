//! # blight-kernel — the spore (trusted base)
//!
//! This crate is the entire trusted computing base of Blight (spec §8.3). It contains the core
//! term representation, the NbE normalizer, the typing rules, the grading spine, and the
//! cubical Kan table. Everything outside this crate is untrusted: a bug elsewhere can only fail
//! to produce a [`Proof`], never manufacture a false one (spec §1.2).
//!
//! The one door (spec §2.1): obtain a [`Proof`] only by calling [`check::check_top`]; observe it
//! only via [`Proof::concl`].

pub mod check;
pub mod context;
pub mod erase;
pub mod kan;
pub mod normalize;
pub mod proof;
pub mod row;
pub mod semiring;
pub mod signature;
pub mod term;
pub mod usage;
pub mod value;

pub use check::{
    check_top, check_top_leveled, check_top_metered, check_top_with, Checker, TypeError,
};
pub use context::Context;
pub use proof::{Judgement, Proof};
pub use row::{EffName, Row, RowVar};
pub use semiring::{Grade, Semiring};
pub use signature::{
    Arg, Constructor, DataDecl, EffDecl, OpName, OpSig, PathConstructor, Signature,
};
pub use term::{unshare, Cofib, ConName, DataName, IntPrimOp, Interval, Level, SystemBranch, Term};
