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
//! the exact same embedded table instead of re-deriving it — one `include_str!` list, two
//! consumers.

/// `(load name)` → embedded source, for every shipped prelude/tower module. Keys are exactly the
/// strings that appear in `(load "…")` forms.
pub fn embedded(name: &str) -> Option<&'static str> {
    // The prelude lives next to this crate at `../blight-prelude/`. `include_str!` is resolved
    // relative to *this* file at compile time, so the binary needs no runtime access to the tree.
    macro_rules! p {
        ($rel:literal) => {
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../blight-prelude/",
                $rel
            ))
        };
    }
    Some(match name {
        "std/nat.bl" => p!("std/nat.bl"),
        "std/bool.bl" => p!("std/bool.bl"),
        "std/order.bl" => p!("std/order.bl"),
        "std/char.bl" => p!("std/char.bl"),
        "std/list.bl" => p!("std/list.bl"),
        "std/list_extra.bl" => p!("std/list_extra.bl"),
        "std/tree.bl" => p!("std/tree.bl"),
        "std/maybe.bl" => p!("std/maybe.bl"),
        "std/either.bl" => p!("std/either.bl"),
        "std/function.bl" => p!("std/function.bl"),
        "std/pair.bl" => p!("std/pair.bl"),
        "std/ordering.bl" => p!("std/ordering.bl"),
        "std/string.bl" => p!("std/string.bl"),
        "std/string_extra.bl" => p!("std/string_extra.bl"),
        "std/io.bl" => p!("std/io.bl"),
        "std/bytes.bl" => p!("std/bytes.bl"),
        "std/array.bl" => p!("std/array.bl"),
        "std/graphics.bl" => p!("std/graphics.bl"),
        "std/time.bl" => p!("std/time.bl"),
        "std/test.bl" => p!("std/test.bl"),
        "std/map.bl" => p!("std/map.bl"),
        "std/json.bl" => p!("std/json.bl"),
        "std/regex.bl" => p!("std/regex.bl"),
        "std/lexer.bl" => p!("std/lexer.bl"),
        "std/parser.bl" => p!("std/parser.bl"),
        "std/actor.bl" => p!("std/actor.bl"),
        "std/vec.bl" => p!("std/vec.bl"),
        "std/int.bl" => p!("std/int.bl"),
        "std/float.bl" => p!("std/float.bl"),
        "std/f64.bl" => p!("std/f64.bl"),
        "std/equiv.bl" => p!("std/equiv.bl"),
        "std/path.bl" => p!("std/path.bl"),
        "std/prelude.bl" => p!("std/prelude.bl"),
        "tactics.bl" => p!("tactics.bl"),
        "plus_zero_tac.bl" => p!("plus_zero_tac.bl"),
        "traits.bl" => p!("traits.bl"),
        "modules.bl" => p!("modules.bl"),
        "regions.bl" => p!("regions.bl"),
        "spore.bl" => p!("spore.bl"),
        "spore_meta.bl" => p!("spore_meta.bl"),
        "spore_intrinsic.bl" => p!("spore_intrinsic.bl"),
        "spore_elab.bl" => p!("spore_elab.bl"),
        "spore_compile.bl" => p!("spore_compile.bl"),
        "spore_pipeline.bl" => p!("spore_pipeline.bl"),
        "spore_codegen_meta.bl" => p!("spore_codegen_meta.bl"),
        _ => return None,
    })
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
}
