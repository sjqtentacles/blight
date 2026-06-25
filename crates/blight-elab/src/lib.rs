//! # blight-elab — the surface frontend (untrusted)
//!
//! Reader, surface AST, and bidirectional elaborator (spec §5, §6.1). None of this is trusted:
//! its only job is to produce core terms for the spore ([`blight_kernel`]) to re-check.

pub mod elab;
pub mod sexpr;
pub mod surface;

pub use elab::{elaborate, elaborate_against, parse_decl, parse_surface, ElabEnv, ElabError};
pub use sexpr::{read_all, read_one, ReadError, Sexpr};
pub use surface::{Binder, Clause, Decl, Surface};
