//! Property-based tests for the surface s-expression **reader** (Track D hardening).
//!
//! `proptest` (with automatic shrinking) generates arbitrary s-expression trees over a safe atom
//! alphabet, renders them to concrete syntax, reads them back with [`read_all`], and asserts the
//! parse tree is *identical* — the reader's structural round-trip property. A failure shrinks to a
//! minimal offending tree and is reproducible from the saved `proptest-regressions` seed. This is the
//! generative complement to the fixed reader unit tests.

use blight_elab::sexpr::{read_all, Sexpr};
use proptest::prelude::*;

/// Render an [`Sexpr`] back to concrete syntax. Atoms print verbatim (the generator only produces
/// delimiter-free atoms, so they re-tokenize unchanged); lists print space-separated inside `(…)`.
fn render(s: &Sexpr) -> String {
    match s {
        Sexpr::Atom(a) => a.clone(),
        Sexpr::List(items) => {
            let inner: Vec<String> = items.iter().map(render).collect();
            format!("({})", inner.join(" "))
        }
    }
}

/// An atom over a delimiter-free alphabet: starts with a letter, continues with letters/digits and
/// the symbol characters the reader treats as ordinary atom chars (no whitespace, no `()[]{};`, no
/// `"`), so it tokenizes back to exactly itself.
fn arb_atom() -> impl Strategy<Value = String> {
    proptest::string::string_regex("[a-zA-Z][a-zA-Z0-9+*/<>=?!._-]{0,6}").unwrap()
}

/// A bounded-depth s-expression tree: atoms at the leaves, lists (arity 0..4) as the recursive node.
fn arb_sexpr() -> impl Strategy<Value = Sexpr> {
    let leaf = arb_atom().prop_map(Sexpr::Atom);
    leaf.prop_recursive(
        5,  // up to 5 levels deep
        64, // up to ~64 total nodes
        4,  // up to 4 children per list
        |inner| prop::collection::vec(inner, 0..4).prop_map(Sexpr::List),
    )
}

proptest! {
    /// Reading the rendering of any generated tree yields exactly that tree (single top-level form).
    #[test]
    fn reader_roundtrips_generated_sexprs(s in arb_sexpr()) {
        let text = render(&s);
        let parsed = read_all(&text)
            .unwrap_or_else(|e| panic!("reader rejected rendered s-expr {text:?}: {e}"));
        prop_assert_eq!(parsed.len(), 1, "one top-level form for {:?}", text);
        prop_assert_eq!(&parsed[0], &s, "round-trip mismatch for {:?}", text);
    }

    /// Rendering a *sequence* of forms and reading them back preserves the whole vector — the reader
    /// splits top-level forms exactly at the rendered boundaries (whitespace-separated).
    #[test]
    fn reader_roundtrips_form_sequences(forms in prop::collection::vec(arb_sexpr(), 0..6)) {
        let text = forms.iter().map(render).collect::<Vec<_>>().join("\n");
        let parsed = read_all(&text)
            .unwrap_or_else(|e| panic!("reader rejected rendered sequence {text:?}: {e}"));
        prop_assert_eq!(parsed, forms);
    }
}
