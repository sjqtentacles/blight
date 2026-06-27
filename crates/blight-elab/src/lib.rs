//! # blight-elab — the surface frontend (untrusted)
//!
//! Reader, surface AST, and bidirectional elaborator (spec §5, §6.1). None of this is trusted:
//! its only job is to produce core terms for the spore ([`blight_kernel`]) to re-check.

pub mod diagnostic;
pub mod elab;
pub mod macros;
pub mod meta;
pub mod pretty;
pub mod program;
pub mod sexpr;
pub mod spores;
pub mod surface;
pub mod tactic;

pub use diagnostic::{render as render_diagnostic, Diagnostic};
pub use elab::{elaborate, elaborate_against, parse_decl, parse_surface, ElabEnv, ElabError};
pub use macros::{MacroDef, MacroEnv};
pub use pretty::{pretty_concl, pretty_term};
pub use program::{Outcome, Program};
pub use sexpr::{
    read_all, read_all_spanned, read_one, ReadError, Sexpr, Span, Spanned, SpannedSexpr,
};
pub use spores::PackageManifest;
pub use surface::{Binder, Clause, Decl, Surface};
pub use tactic::{check_core, parse_tactic, run as run_tactic, Goal, Tactic, TacticError};
