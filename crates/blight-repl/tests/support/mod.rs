//! Shared test support for the `blight-repl` integration tests. Included by each test binary via
//! `#[path = "support/mod.rs"] mod support;` (a file under `tests/` is not itself compiled as a
//! test binary, so this is the canonical place for helpers shared across test files).

#![allow(dead_code)]

use blight_elab::ElabError;

/// Resolve a prelude module name to its on-disk source under `crates/blight-prelude/`, so that a
/// `(load "std/nat.bl")` resolves to `crates/blight-prelude/std/nat.bl`. This is the single shared
/// definition that previously lived (duplicated) in each integration-test file.
pub fn prelude_resolver(name: &str) -> Result<String, ElabError> {
    let path = format!("{}/../blight-prelude/{}", env!("CARGO_MANIFEST_DIR"), name);
    std::fs::read_to_string(&path)
        .map_err(|e| ElabError::BadForm(format!("cannot load {path:?}: {e}")))
}
