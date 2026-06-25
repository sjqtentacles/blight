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
pub mod kan;
pub mod normalize;
pub mod proof;
pub mod semiring;
pub mod signature;
pub mod term;
pub mod value;

pub use check::{check_top, check_top_with, TypeError};
pub use proof::{Judgement, Proof};
pub use semiring::{Grade, Semiring};
pub use signature::{Arg, Constructor, DataDecl, PathConstructor, Signature};
pub use term::{Cofib, ConName, DataName, Interval, Level, Term};
