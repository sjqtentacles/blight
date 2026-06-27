//! The standard library / tower sources, embedded into the `blight` binary at compile time.
//!
//! `blight build` and the REPL must resolve `(load "std/nat.bl")` and friends without depending on
//! the user's working directory or a source checkout. We therefore bake the prelude tree (under
//! `crates/blight-prelude/`) into the binary with `include_str!`, keyed by the path used in `(load
//! …)` forms (relative to the prelude root). The CLI resolver tries the real filesystem first (so a
//! user's own files and overrides win) and falls back to these embedded sources.

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
        "std/vec.bl" => p!("std/vec.bl"),
        "std/prelude.bl" => p!("std/prelude.bl"),
        "tactics.bl" => p!("tactics.bl"),
        "plus_zero_tac.bl" => p!("plus_zero_tac.bl"),
        "traits.bl" => p!("traits.bl"),
        "modules.bl" => p!("modules.bl"),
        "regions.bl" => p!("regions.bl"),
        "spore.bl" => p!("spore.bl"),
        "spore_meta.bl" => p!("spore_meta.bl"),
        _ => return None,
    })
}
