//! Corpus-wide guarantees for `blight fmt` (Wave 9 / T2). These are the tests that make the
//! formatter *trustworthy* to run over a whole tree: on every real `.bl` file in the repo it must
//!
//!   1. **succeed** (the file is lexically well-formed — matched delimiters, terminated strings),
//!   2. **preserve semantics** — re-reading the formatted text yields the exact same
//!      [`blight_elab::Sexpr`] forest the original did (no token dropped, reordered, or rewritten;
//!      no comment silently swallowed into surrounding code), and
//!   3. **be idempotent** — formatting the formatted output is a no-op.
//!
//! Mirrors the corpus-walk pattern of `blight-repl/tests/examples.rs`'s `every_example_loads`.

use blight_elab::{format_source, read_all};
use std::path::{Path, PathBuf};

/// The three roots that hold hand-written `.bl` source: the examples tree, the Blight-side prelude
/// (`std/*.bl`, `spore_*.bl`), and the benchmark games. Fuzz corpora and generated artifacts are
/// not Blight source and are excluded by only collecting the `.bl` extension under these roots.
fn corpus_roots() -> Vec<PathBuf> {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")); // .../crates/blight-elab
    let repo = manifest
        .parent()
        .and_then(Path::parent)
        .expect("repo root is two levels above the crate manifest")
        .to_path_buf();
    vec![
        repo.join("examples"),
        repo.join("crates/blight-prelude"),
        repo.join("bench/games"),
    ]
}

fn collect_bl(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return; // a root that doesn't exist on this checkout is simply skipped
    };
    for entry in entries {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            collect_bl(&path, out);
        } else if path.extension().is_some_and(|e| e == "bl") {
            out.push(path);
        }
    }
}

fn all_bl_files() -> Vec<PathBuf> {
    let mut out = Vec::new();
    for root in corpus_roots() {
        collect_bl(&root, &mut out);
    }
    out.sort();
    out
}

#[test]
fn formatter_preserves_semantics_and_is_idempotent_over_the_whole_corpus() {
    let files = all_bl_files();
    assert!(
        files.len() >= 40,
        "expected the full .bl corpus on disk, found only {}: {files:?}",
        files.len()
    );

    for path in &files {
        let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));

        // 1. Formatting succeeds on every real source file.
        let formatted =
            format_source(&src).unwrap_or_else(|e| panic!("format_source failed on {path:?}: {e}"));

        // 2. Semantics preserved: the s-expression forest is byte-for-byte identical after
        //    formatting. We compare parsed trees (not raw text) so that whitespace/comment layout
        //    — the only thing the formatter is allowed to touch — is correctly ignored, while any
        //    change to an atom, a delimiter, or the token order would surface here.
        let before = read_all(&src)
            .unwrap_or_else(|e| panic!("original {path:?} did not parse as s-expressions: {e:?}"));
        let after = read_all(&formatted).unwrap_or_else(|e| {
            panic!("formatted {path:?} no longer parses as s-expressions: {e:?}")
        });
        assert_eq!(
            before, after,
            "formatting changed the parsed s-expression forest of {path:?}"
        );

        // 3. Idempotence: the second pass is a no-op.
        let twice = format_source(&formatted)
            .unwrap_or_else(|e| panic!("re-formatting {path:?} failed: {e}"));
        assert_eq!(formatted, twice, "formatter is not idempotent on {path:?}");
    }
}
