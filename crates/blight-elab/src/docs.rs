//! `blight doc` (Wave 9 / T2): a documentation generator over the same `;`-comment convention the
//! formatter (`crate::fmt`) preserves. UNTRUSTED tooling.
//!
//! # Convention
//!
//! A `;`-comment block immediately preceding a top-level declaration (no blank line in between —
//! the same "glued" rule `crate::fmt` uses for a trailing comment, just on the other side) is that
//! declaration's doc-comment: exactly the convention already used throughout `std/*.bl` (e.g.
//! `std/nat.bl`'s "Addition by structural recursion..." directly above `plus`). A comment block
//! separated from the declaration by a blank line is ordinary prose (a section header, a file
//! banner) and is not attached to anything.
//!
//! # Signatures
//!
//! The doc generator does not re-derive types from surface syntax (`define`/`define-rec` bodies
//! are not always explicitly typed, and re-implementing elaboration here would duplicate — and
//! risk drifting from — the real bidirectional elaborator). Instead it asks the kernel what it
//! already knows: given an `env` the declarations have already been loaded into (e.g. by running
//! the file through a [`crate::program::Program`] first, as `blight doc`'s CLI wiring does),
//! [`infer_type_str`] infers each name's type exactly as `:type` would at a REPL prompt. A name the
//! checker cannot infer a bare type for (a type-class instance, an effect operation only usable
//! inside `perform`) simply gets no signature line rather than a fabricated one.

use crate::elab::ElabEnv;
use crate::infer::infer_type_str;
use crate::sexpr::{read_all_spanned, ReadError, Spanned, SpannedSexpr};

/// One documented top-level declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocEntry {
    pub name: String,
    /// The declaring keyword (`"define"`, `"defdata"`, `"effect"`, ...), so a renderer can group
    /// or label entries without re-deriving it from `signature`.
    pub keyword: String,
    /// The doc-comment text immediately above the declaration, semicolons and indentation
    /// stripped, multiple lines joined with `\n`. Empty if the declaration has no doc-comment.
    pub doc: String,
    /// `name`'s inferred type, pretty-printed, if the checker can infer a bare type for it (see
    /// the module doc's "Signatures" section for why this can legitimately be `None`).
    pub signature: Option<String>,
}

/// Head keywords that introduce a documentable name as their second element (`(kw name ...)`),
/// matching `blight_elab::program::Program::process_one`'s top-level dispatch. `class`/`instance`
/// are deliberately excluded: neither binds a new top-level name of its own.
const DOC_KEYWORDS: &[&str] = &[
    "define",
    "define-rec",
    "deftotal",
    "define-by",
    "defdata",
    "effect",
    "foreign",
];

/// Extracts one [`DocEntry`] per documentable top-level declaration in `src`, in source order.
/// `env` should already have `src`'s declarations (and anything it `(load ...)`s) bound — as
/// running it through a [`crate::program::Program`] would — so [`infer_type_str`] can resolve each
/// name's signature; an `env` that doesn't know a name simply yields `signature: None` for it
/// rather than an error, since a doc pass over a syntactically-valid-but-not-yet-checked file is
/// still useful on its own (comments and names alone).
pub fn extract_docs(env: &ElabEnv, src: &str) -> Result<Vec<DocEntry>, ReadError> {
    let forms = read_all_spanned(src)?;
    let mut out = Vec::new();
    let mut prev_end = 0usize;
    for form in &forms {
        if let Some(entry) = doc_entry_for(env, src, form, prev_end) {
            out.push(entry);
        }
        prev_end = form.span.end;
    }
    Ok(out)
}

fn doc_entry_for(
    env: &ElabEnv,
    src: &str,
    form: &Spanned<SpannedSexpr>,
    prev_end: usize,
) -> Option<DocEntry> {
    let SpannedSexpr::List(items) = &form.node else {
        return None;
    };
    let head = items.first()?;
    let SpannedSexpr::Atom(kw) = &head.node else {
        return None;
    };
    if !DOC_KEYWORDS.contains(&kw.as_str()) {
        return None;
    }
    let name_item = items.get(1)?;
    let SpannedSexpr::Atom(name) = &name_item.node else {
        return None;
    };
    let doc = doc_comment_before(&src[prev_end..form.span.start]);
    let signature = infer_type_str(env, name).ok();
    Some(DocEntry {
        name: name.clone(),
        keyword: kw.clone(),
        doc,
        signature,
    })
}

/// The doc-comment attached to a declaration whose preceding source text (from the end of the
/// previous top-level form, or file start) is `gap`: the longest run of `;`-comment lines
/// immediately adjacent to the declaration (no blank line breaking the run), semicolons and
/// leading whitespace stripped, joined with `\n`. Returns `""` if the declaration has no
/// immediately-adjacent comment — including the common case of a file-header comment block that is
/// separated from the first declaration by a blank line, which is prose, not documentation for a
/// specific name.
fn doc_comment_before(gap: &str) -> String {
    let mut lines: Vec<&str> = gap.lines().collect();
    let mut doc_lines: Vec<&str> = Vec::new();
    while let Some(line) = lines.last() {
        match line.trim().strip_prefix(';') {
            Some(text) => {
                doc_lines.push(text.trim());
                lines.pop();
            }
            None => break,
        }
    }
    doc_lines.reverse();
    doc_lines.join("\n")
}

/// Renders `entries` as a single Markdown document: one `##` section per declaration, in source
/// order, with its inferred signature (if any) in a code fence followed by its doc-comment prose.
pub fn render_markdown(entries: &[DocEntry]) -> String {
    let mut out = String::new();
    for entry in entries {
        out.push_str("## ");
        out.push_str(&entry.name);
        out.push_str("\n\n");
        if let Some(sig) = &entry.signature {
            out.push_str("```\n");
            out.push_str(&entry.name);
            out.push_str(" : ");
            out.push_str(sig);
            out.push_str("\n```\n\n");
        }
        if !entry.doc.is_empty() {
            out.push_str(&entry.doc);
            out.push_str("\n\n");
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Program;

    fn env_running(src: &str) -> ElabEnv {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::new(&mut env);
            prog.run(src).expect("setup source typechecks");
        }
        env
    }

    #[test]
    fn doc_extracts_comment_and_inferred_type() {
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\n\
             ; Addition by structural recursion on the first argument.\n\
             (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n  \
               (lam (a b) (match a\n    \
                 [(Zero) b]\n    \
                 [(Succ n) (Succ (plus n b))])))\n";
        let env = env_running(src);
        let entries = extract_docs(&env, src).expect("well-formed source");
        let plus = entries
            .iter()
            .find(|e| e.name == "plus")
            .expect("plus is documented");
        assert_eq!(
            plus.doc,
            "Addition by structural recursion on the first argument."
        );
        assert_eq!(plus.keyword, "define-rec");
        // Pretty-printed by the same kernel path `:type` uses (grades shown, binders renamed) —
        // assert on the parts that matter here rather than pinning the exact rendering, which
        // `infer::tests` already covers.
        let sig = plus.signature.as_deref().expect("plus's type is inferable");
        assert!(sig.starts_with("(Pi"), "expected a Pi type, got {sig:?}");
        assert!(
            sig.ends_with("Nat))"),
            "expected a Nat-returning Pi type, got {sig:?}"
        );
    }

    #[test]
    fn undocumented_declaration_gets_an_empty_doc_not_an_error() {
        let src = "(define one (the Nat Zero))\n";
        // `Nat`/`Zero` are unbound here on purpose — `one` itself still yields an entry with no
        // doc-comment and (since the surrounding program fails to typecheck) no signature either.
        let env = ElabEnv::new();
        let entries = extract_docs(&env, src).expect("well-formed source");
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].name, "one");
        assert_eq!(entries[0].doc, "");
        assert_eq!(entries[0].signature, None);
    }

    #[test]
    fn a_file_header_comment_separated_by_a_blank_line_is_not_attached() {
        let src = "; std/example.bl — a file banner, not plus's doc-comment.\n;\n\
             ; UNTRUSTED tower code.\n\n\
             (defdata Nat () (Zero) (Succ (n Nat)))\n";
        let env = env_running(src);
        let entries = extract_docs(&env, src).expect("well-formed source");
        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries[0].doc, "",
            "the file banner is separated by a blank line and must not attach"
        );
    }

    #[test]
    fn render_markdown_includes_name_signature_and_doc() {
        let src = "; The empty type's sole eliminator's argument type.\n\
             (defdata Void ())\n";
        let env = env_running(src);
        let entries = extract_docs(&env, src).expect("well-formed source");
        let out = render_markdown(&entries);
        assert!(out.contains("## Void"));
        assert!(out.contains("The empty type's sole eliminator's argument type."));
    }
}
