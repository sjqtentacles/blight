//! # blight-elab — the surface frontend (untrusted)
//!
//! Reader, surface AST, and bidirectional elaborator (spec §5, §6.1). None of this is trusted:
//! its only job is to produce core terms for the spore ([`blight_kernel`]) to re-check.

pub mod diagnostic;
pub mod docs;
pub mod elab;
pub mod fmt;
pub mod infer;
pub mod macros;
pub mod meta;
pub mod mutual;
pub mod pretty;
pub mod program;
pub mod registry;
pub mod scope;
pub mod sexpr;
pub mod spores;
pub mod stepper;
pub mod surface;
pub mod tactic;

pub use diagnostic::{render as render_diagnostic, Diagnostic};
pub use docs::{extract_docs, render_markdown, DocEntry};
pub use elab::{elaborate, elaborate_against, parse_decl, parse_surface, ElabEnv, ElabError};
pub use fmt::{format_source, FormatError};
pub use infer::infer_type_str;
pub use macros::{MacroDef, MacroEnv};
pub use pretty::{pretty_concl, pretty_term};
pub use program::{Outcome, Program};
pub use registry::{fetch_and_vendor, load_index, RegistryEntry, RegistryIndex};
pub use scope::{
    find_unbound_span, narrow_span, rename_local_binder, resolve_let_rhs_at, RenameError,
};
pub use sexpr::{
    read_all, read_all_spanned, read_one, ReadError, Sexpr, Span, Spanned, SpannedSexpr,
};
pub use spores::{
    add_dependency, add_git_dependency, add_registry_dependency, fetch_git_dependency,
    git_cache_dir, GitDep, LockEntry, PackageManifest,
};
pub use stepper::{trace as step_trace, Step, StepOutcome, StepTrace, DEFAULT_STEP_BUDGET};
pub use surface::{Binder, Clause, Decl, Surface};
pub use tactic::{check_core, parse_tactic, run as run_tactic, Goal, Tactic, TacticError};
