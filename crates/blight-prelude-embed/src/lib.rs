//! The standard library / tower sources, embedded into binaries at compile time. UNTRUSTED.
//!
//! Both the `blight` CLI/REPL (`blight-repl`) and the LSP server (`blight-lsp`) must resolve
//! `(load "std/nat.bl")` and friends without depending on the caller's working directory or a
//! source checkout. We therefore bake the prelude tree (under `crates/blight-prelude/`) into the
//! binary with `include_str!`, keyed by the path used in `(load …)` forms (relative to the
//! prelude root). A filesystem-first resolver tries the real filesystem before falling back to
//! these embedded sources, so a user's own files and overrides always win.
//!
//! This lives in its own tiny crate (rather than inside `blight-repl`) so the LSP server can share
//! the exact same embedded table instead of re-deriving it — one module list, two consumers.

/// One macro invocation is the single source of truth for the module list: it expands to both the
/// `embedded` lookup and the `MODULE_NAMES` enumeration (E8 — LSP `(load "` completion), so the
/// two can never drift apart.
macro_rules! embedded_modules {
    ($($rel:literal),+ $(,)?) => {
        /// `(load name)` → embedded source, for every shipped prelude/tower module. Keys are
        /// exactly the strings that appear in `(load "…")` forms.
        pub fn embedded(name: &str) -> Option<&'static str> {
            // The prelude lives next to this crate at `../blight-prelude/`. `include_str!` is
            // resolved relative to this file at compile time, so the binary needs no runtime
            // access to the tree.
            match name {
                $($rel => Some(include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../blight-prelude/",
                    $rel
                ))),)+
                _ => None,
            }
        }

        /// Every embedded module path, in table order — the completion source for `(load "`.
        const MODULE_NAMES: &[&str] = &[$($rel),+];
    };
}

embedded_modules! {
    "std/nat.bl",
    "std/bool.bl",
    "std/order.bl",
    "std/char.bl",
    "std/list.bl",
    "std/list_extra.bl",
    "std/tree.bl",
    "std/maybe.bl",
    "std/either.bl",
    "std/function.bl",
    "std/pair.bl",
    "std/ordering.bl",
    "std/string.bl",
    "std/string_extra.bl",
    "std/io.bl",
    "std/bytes.bl",
    "std/array.bl",
    "std/graphics.bl",
    "std/time.bl",
    "std/test.bl",
    "std/map.bl",
    "std/json.bl",
    "std/regex.bl",
    "std/lexer.bl",
    "std/parser.bl",
    "std/actor.bl",
    "std/vec.bl",
    "std/int.bl",
    "std/float.bl",
    "std/f64.bl",
    "std/equiv.bl",
    "std/path.bl",
    "std/prelude.bl",
    "tactics.bl",
    "plus_zero_tac.bl",
    "traits.bl",
    "modules.bl",
    "regions.bl",
    "spore.bl",
    "spore_meta.bl",
    "spore_intrinsic.bl",
    "spore_elab.bl",
    "spore_compile.bl",
    "spore_pipeline.bl",
    "spore_codegen_meta.bl",
    "spore_reader.bl",
    "spore_print.bl",
}

/// The embedded module paths (the `(load "…")` keys), in table order.
pub fn module_names() -> &'static [&'static str] {
    MODULE_NAMES
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_module_resolves() {
        assert!(embedded("std/nat.bl").is_some());
    }

    #[test]
    fn unknown_module_is_none() {
        assert!(embedded("std/does_not_exist.bl").is_none());
    }

    /// The enumeration and the lookup are macro-generated from one list, so every enumerated
    /// name must resolve — this pins the two faces against a refactor splitting them apart.
    #[test]
    fn every_enumerated_module_resolves() {
        assert!(module_names().len() >= 40);
        for name in module_names() {
            assert!(embedded(name).is_some(), "{name} enumerated but not embedded");
        }
    }
}
