//! `blight fmt` (Wave 9 / T2, roadmap): a canonical, comment-preserving formatter for surface
//! `.bl` source. UNTRUSTED tooling — it never touches the kernel and cannot affect what typechecks.
//!
//! # Design
//!
//! This is deliberately *not* built on [`crate::sexpr`]'s reader: that reader throws comments away
//! in `skip_ws` (by design — the kernel-facing AST has no business carrying prose), and re-sugaring
//! from a comment-free tree could never reproduce a real file's comments (§`std/regex.bl`,
//! `spore_compile.bl` and friends interleave comments *inside* `defdata` bodies, one per variant).
//! So this module has its own tiny hand-rolled tokenizer (below) that treats `;`-comments as first
//! class tokens rather than trivia to be skipped, and preserves every byte of every atom (including
//! string literals, copied verbatim rather than decoded+re-encoded) and every delimiter character
//! exactly as written — `[`, `(`, and `{` are never rewritten into one another. Formatting is a
//! *pure whitespace-and-layout* transformation: it changes nothing else. Two consequences follow
//! for free, by construction rather than by hoping the tests happen to pass:
//!
//!   1. **Semantics preservation.** [`crate::sexpr`]'s reader treats whitespace and comments purely
//!      as separators; it never inspects their content. Since the sequence of "real" tokens (opens,
//!      closes, atoms) emitted by [`format_source`] is byte-identical in *content* to the input's —
//!      only their surrounding whitespace and comment layout change — re-reading the formatted
//!      output always yields the exact same [`crate::sexpr::Sexpr`] tree the original did.
//!   2. **Idempotence.** Formatting is a deterministic function of the parsed
//!      ([`Node`]/[`Elem`]) tree, and that tree only ever records *bounded* whitespace facts (is
//!      there a blank line here? is this comment glued to the end of the previous line?) that the
//!      renderer reproduces exactly. So formatting the already-formatted output re-derives the same
//!      tree and therefore emits byte-identical text on the second pass.
//!
//! # Style
//!
//! A list is printed flat (`(a b c)`) if it fits within [`MAX_WIDTH`] columns and contains no
//! comment anywhere among its children; otherwise every child goes on its own indented line, one
//! `;`-comment per line, each trailing comment glued to the end of the line of the item it follows.
//! A bare leading atom (the common `(define foo ...)` / `(defdata Foo ...)` head) stays on the
//! opening line even when the rest of the list wraps. Closing delimiters glue onto the last child's
//! line unless that line ends in a comment (comments run to end-of-line, so nothing may follow one
//! on the same line without corrupting it) — in that case the closer gets its own line, matching the
//! "stacked parens" convention already used by hand-formatted Lisp-family code.

use std::fmt;

const MAX_WIDTH: usize = 100;
const INDENT_STEP: usize = 2;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormatError(pub String);

impl fmt::Display for FormatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "format error: {}", self.0)
    }
}

impl std::error::Error for FormatError {}

/// Formats a whole `.bl` source file. Returns the canonical text (always ending in exactly one
/// trailing newline) or an error if `src` is not lexically well-formed (unterminated string,
/// unbalanced or mismatched delimiters). A syntax error the *elaborator* would reject (e.g. an
/// unbound name, or a keyword used with the wrong arity) is not this function's concern — it only
/// needs matched delimiters and terminated atoms/strings to lay text out.
pub fn format_source(src: &str) -> Result<String, FormatError> {
    let toks = tokenize(src)?;
    let mut pos = 0usize;
    let elems = parse_elems(&toks, &mut pos, None)?;
    if pos != toks.len() {
        return Err(FormatError("unbalanced closing delimiter".to_string()));
    }
    Ok(render_top_level(&elems))
}

// ---------------------------------------------------------------------------------------------
// Tokenizer
// ---------------------------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Open(char),
    Close(char),
    /// Verbatim atom text, including quotes for string literals. Never decoded or re-encoded, so
    /// it round-trips through formatting byte-for-byte.
    Atom(String),
    /// A `;`-to-end-of-line comment, including the leading `;`, with trailing whitespace trimmed.
    Comment(String),
}

#[derive(Debug, Clone)]
struct RawTok {
    kind: Token,
    /// Newlines between this token and the previous one, saturating at 2 (2+ means "at least one
    /// blank line separates them"; the file's very first token gets 2, which is never consulted).
    newlines_before: u8,
}

fn matching_close(open: char) -> char {
    match open {
        '(' => ')',
        '[' => ']',
        '{' => '}',
        _ => unreachable!("not an opening delimiter: {open}"),
    }
}

fn is_open(c: char) -> bool {
    matches!(c, '(' | '[' | '{')
}

fn is_close(c: char) -> bool {
    matches!(c, ')' | ']' | '}')
}

fn is_delim(c: char) -> bool {
    c.is_whitespace() || is_open(c) || is_close(c) || c == ';' || c == '"'
}

fn tokenize(src: &str) -> Result<Vec<RawTok>, FormatError> {
    let mut out = Vec::new();
    let mut rest = src;
    let mut newlines_before: u8 = 2; // irrelevant for the first token, but must be initialized
    loop {
        let (after, newlines) = skip_whitespace(rest);
        newlines_before = newlines_before.max(newlines).min(2);
        rest = after;
        let Some(c) = rest.chars().next() else {
            break;
        };
        if is_open(c) {
            out.push(RawTok {
                kind: Token::Open(c),
                newlines_before,
            });
            rest = &rest[c.len_utf8()..];
        } else if is_close(c) {
            out.push(RawTok {
                kind: Token::Close(c),
                newlines_before,
            });
            rest = &rest[c.len_utf8()..];
        } else if c == ';' {
            let end = rest.find('\n').unwrap_or(rest.len());
            let text = rest[..end].trim_end().to_string();
            out.push(RawTok {
                kind: Token::Comment(text),
                newlines_before,
            });
            rest = &rest[end..]; // deliberately leave the newline for skip_whitespace to count
        } else if c == '"' {
            let (text, after) = scan_string_literal(rest)?;
            out.push(RawTok {
                kind: Token::Atom(text),
                newlines_before,
            });
            rest = after;
        } else {
            let end = rest.find(is_delim).unwrap_or(rest.len());
            debug_assert!(end > 0, "is_delim already ruled out an immediate delimiter");
            out.push(RawTok {
                kind: Token::Atom(rest[..end].to_string()),
                newlines_before,
            });
            rest = &rest[end..];
        }
        newlines_before = 0;
    }
    Ok(out)
}

/// Skips whitespace only (not comments). Returns the remaining slice and the number of newlines
/// skipped, saturating at 2.
fn skip_whitespace(s: &str) -> (&str, u8) {
    let mut idx = 0usize;
    let mut newlines = 0u8;
    for c in s.chars() {
        if c == '\n' {
            newlines = newlines.saturating_add(1).min(2);
            idx += c.len_utf8();
        } else if c.is_whitespace() {
            idx += c.len_utf8();
        } else {
            break;
        }
    }
    (&s[idx..], newlines)
}

/// Scans a `"..."` string literal starting at `s`'s first byte, returning the verbatim source text
/// (quotes included, escapes un-decoded) and the remaining slice after the closing quote. Mirrors
/// `sexpr.rs::read_string`'s escaping rule: a backslash always consumes exactly one following
/// character, whatever it is, so an escaped quote never ends the literal early.
fn scan_string_literal(s: &str) -> Result<(String, &str), FormatError> {
    let mut iter = s.char_indices();
    let (_, opening) = iter
        .next()
        .filter(|(_, c)| *c == '"')
        .ok_or_else(|| FormatError("scan_string_literal called off a `\"`".to_string()))?;
    debug_assert_eq!(opening, '"');
    loop {
        match iter.next() {
            None => return Err(FormatError("unterminated string literal".to_string())),
            Some((i, '"')) => {
                let end = i + 1;
                return Ok((s[..end].to_string(), &s[end..]));
            }
            Some((_, '\\')) => {
                if iter.next().is_none() {
                    return Err(FormatError("string literal ends mid-escape".to_string()));
                }
            }
            Some(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Tree
// ---------------------------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Node {
    Atom(String),
    List(char, Vec<Elem>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Elem {
    Item {
        node: Node,
        blank_before: bool,
        /// A comment on the same source line as this item's last token, e.g. the ` ; ...` after
        /// `(a-var (i Nat))` in a `defdata` body.
        trailing: Option<String>,
    },
    /// A comment on its own line (not glued to a preceding item).
    Comment { text: String, blank_before: bool },
}

fn parse_elems(
    toks: &[RawTok],
    pos: &mut usize,
    close: Option<char>,
) -> Result<Vec<Elem>, FormatError> {
    let mut out = Vec::new();
    while *pos < toks.len() {
        match &toks[*pos].kind {
            Token::Close(c) => {
                if Some(*c) == close {
                    return Ok(out);
                }
                return Err(FormatError(format!("unexpected closing delimiter `{c}`")));
            }
            Token::Comment(text) => {
                let blank_before = toks[*pos].newlines_before >= 2;
                out.push(Elem::Comment {
                    text: text.clone(),
                    blank_before,
                });
                *pos += 1;
            }
            Token::Open(open) => {
                let open = *open;
                let blank_before = toks[*pos].newlines_before >= 2;
                *pos += 1;
                let expect = matching_close(open);
                let children = parse_elems(toks, pos, Some(expect))?;
                // `parse_elems` above only returns `Ok` for a `Some(expect)` closing delimiter
                // once it has found a token exactly equal to `Token::Close(expect)` at `*pos`
                // (any other closing delimiter, or running out of tokens, is an `Err` it already
                // returned) — so the close here is guaranteed to be present and matching.
                debug_assert_eq!(toks[*pos].kind, Token::Close(expect));
                *pos += 1;
                let trailing = take_trailing_comment(toks, pos);
                out.push(Elem::Item {
                    node: Node::List(open, children),
                    blank_before,
                    trailing,
                });
            }
            Token::Atom(a) => {
                let a = a.clone();
                let blank_before = toks[*pos].newlines_before >= 2;
                *pos += 1;
                let trailing = take_trailing_comment(toks, pos);
                out.push(Elem::Item {
                    node: Node::Atom(a),
                    blank_before,
                    trailing,
                });
            }
        }
    }
    if close.is_some() {
        return Err(FormatError("unterminated list".to_string()));
    }
    Ok(out)
}

fn take_trailing_comment(toks: &[RawTok], pos: &mut usize) -> Option<String> {
    match toks.get(*pos) {
        Some(RawTok {
            kind: Token::Comment(text),
            newlines_before: 0,
        }) => {
            let text = text.clone();
            *pos += 1;
            Some(text)
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------------------------

fn render_top_level(elems: &[Elem]) -> String {
    let mut out = String::new();
    for (i, elem) in elems.iter().enumerate() {
        if i > 0 {
            out.push('\n');
            if elem_blank_before(elem) {
                out.push('\n');
            }
        }
        render_elem(elem, 0, &mut out);
    }
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

fn elem_blank_before(elem: &Elem) -> bool {
    match elem {
        Elem::Item { blank_before, .. } | Elem::Comment { blank_before, .. } => *blank_before,
    }
}

fn render_elem(elem: &Elem, indent: usize, out: &mut String) {
    match elem {
        Elem::Comment { text, .. } => out.push_str(text),
        Elem::Item { node, trailing, .. } => {
            render_node(node, indent, out);
            if let Some(t) = trailing {
                out.push_str("  ");
                out.push_str(t);
            }
        }
    }
}

/// Renders `node`'s one-line form if it (recursively) contains no comment; `None` forces the
/// caller to lay it out across multiple lines instead, since a `;`-comment can never be followed
/// by more tokens on the same line without silently swallowing them.
fn measure_flat(node: &Node) -> Option<String> {
    match node {
        Node::Atom(a) => Some(a.clone()),
        Node::List(open, elems) => {
            let mut parts = Vec::with_capacity(elems.len());
            for e in elems {
                match e {
                    Elem::Comment { .. } => return None,
                    Elem::Item {
                        node,
                        trailing: Some(_),
                        ..
                    } => {
                        let _ = node;
                        return None;
                    }
                    Elem::Item {
                        node,
                        trailing: None,
                        ..
                    } => parts.push(measure_flat(node)?),
                }
            }
            Some(format!(
                "{open}{}{}",
                parts.join(" "),
                matching_close(*open)
            ))
        }
    }
}

fn render_node(node: &Node, indent: usize, out: &mut String) {
    match node {
        Node::Atom(a) => out.push_str(a),
        Node::List(open, elems) => {
            if elems.is_empty() {
                out.push(*open);
                out.push(matching_close(*open));
                return;
            }
            if let Some(flat) = measure_flat(node) {
                if indent + flat.chars().count() <= MAX_WIDTH {
                    out.push_str(&flat);
                    return;
                }
            }
            render_node_multiline(*open, elems, indent, out);
        }
    }
}

fn render_node_multiline(open: char, elems: &[Elem], indent: usize, out: &mut String) {
    out.push(open);
    let child_indent = indent + INDENT_STEP;

    // Greedily glue as many leading children onto the opening line as fit within the width
    // budget (the common `(defdata Nat () ...)` / `(define foo ...)` header). Gluing always
    // takes at least the very first child unconditionally (even if it alone would overflow), so
    // a lone very-long head atom doesn't get needlessly pushed to its own line. It stops at the
    // first child that is a comment, carries its own trailing comment, contains an embedded
    // comment of its own (so has no flat rendering at all), requested a blank line before it, or
    // would overflow the width budget.
    let mut idx = 0;
    let mut header_len = indent + 1;
    let mut glued_any = false;
    while let Some(Elem::Item {
        node,
        trailing: None,
        blank_before,
    }) = elems.get(idx)
    {
        if glued_any && *blank_before {
            break;
        }
        let Some(flat) = measure_flat(node) else {
            break;
        };
        let sep = usize::from(glued_any);
        let candidate_len = header_len + sep + flat.chars().count();
        if glued_any && candidate_len > MAX_WIDTH {
            break;
        }
        if glued_any {
            out.push(' ');
        }
        out.push_str(&flat);
        header_len = candidate_len;
        glued_any = true;
        idx += 1;
    }

    let mut ends_in_comment = false;
    // Never allow a blank line as the very first thing inside a list — whether that's right
    // after the opening delimiter (`idx == 0`) or right after the glued header line.
    let mut first_line = true;
    for elem in &elems[idx..] {
        out.push('\n');
        if elem_blank_before(elem) && !first_line {
            out.push('\n');
        }
        out.push_str(&" ".repeat(child_indent));
        render_elem(elem, child_indent, out);
        ends_in_comment = matches!(
            elem,
            Elem::Comment { .. }
                | Elem::Item {
                    trailing: Some(_),
                    ..
                }
        );
        first_line = false;
    }
    if ends_in_comment {
        out.push('\n');
        out.push_str(&" ".repeat(indent));
    }
    out.push(matching_close(open));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt_ok(src: &str) -> String {
        format_source(src).unwrap_or_else(|e| panic!("format_source failed on {src:?}: {e}"))
    }

    #[test]
    fn flat_form_stays_on_one_line() {
        assert_eq!(fmt_ok("(  the   Nat    x )"), "(the Nat x)\n");
    }

    #[test]
    fn collapses_extra_blank_lines_between_top_level_forms() {
        let src = "(define a 1)\n\n\n\n(define b 2)\n";
        assert_eq!(fmt_ok(src), "(define a 1)\n\n(define b 2)\n");
    }

    #[test]
    fn preserves_single_blank_line_between_top_level_forms() {
        let src = "(define a 1)\n\n(define b 2)\n";
        assert_eq!(fmt_ok(src), src);
    }

    #[test]
    fn no_blank_line_stays_absent() {
        let src = "(define a 1)\n(define b 2)\n";
        assert_eq!(fmt_ok(src), src);
    }

    #[test]
    fn own_line_comment_inside_a_form_is_preserved() {
        let src = "(defdata Nat ()\n  ; a natural number\n  (Zero)\n  (Succ (n Nat)))\n";
        assert_eq!(fmt_ok(src), src);
    }

    #[test]
    fn trailing_comment_on_a_constructor_is_preserved_and_aligned_with_two_spaces() {
        let src = "(defdata Nat ()\n  (Zero)  ; base case\n  (Succ (n Nat)))\n";
        assert_eq!(fmt_ok(src), src);
    }

    #[test]
    fn a_form_wider_than_max_width_wraps() {
        let wide_name = "a".repeat(120);
        let src = format!("(define {wide_name} (the Nat (Succ Zero)))\n");
        // Sanity: the flat form genuinely exceeds the budget, so wrapping is forced (not incidental).
        assert!(src.trim_end().chars().count() > MAX_WIDTH);
        let out = fmt_ok(&src);
        assert!(
            out.contains('\n'),
            "expected the wide form to wrap: {out:?}"
        );
        // The head keyword stays glued to the opening delimiter even when the list wraps (greedy
        // header packing takes at least the first child unconditionally): the open paren is never
        // left bare on its own line with `define` pushed below it.
        assert!(
            out.starts_with("(define"),
            "head keyword should stay on the opening line: {out:?}"
        );
        // The final child (`(the Nat (Succ Zero))`) got pushed to its own indented line.
        assert!(
            out.contains("\n  (the Nat (Succ Zero))"),
            "the trailing child should wrap to its own two-space-indented line: {out:?}"
        );
        assert_eq!(fmt_ok(&out), out, "wrapped output must be idempotent");
    }

    #[test]
    fn short_multiline_input_is_canonicalized_onto_one_line() {
        // A short form that merely happened to be split across lines in the source collapses to
        // its canonical flat form — only width or an embedded comment force multi-line output.
        let src = "(the Nat\n  x)  ; a note\n";
        assert_eq!(fmt_ok(src), "(the Nat x)  ; a note\n");
    }

    #[test]
    fn trailing_comment_on_the_last_child_forces_close_paren_onto_its_own_line() {
        // `(bar x)`'s trailing comment runs to end-of-line, so `foo`'s closing paren cannot glue
        // onto that same line without being swallowed into the comment; it must get its own line.
        let src = "(foo\n  ; force multi-line\n  (bar x)  ; note\n)\n";
        let out = fmt_ok(src);
        let last_child_line = out
            .lines()
            .find(|l| l.contains("(bar x)"))
            .expect("the (bar x) line survived formatting");
        assert!(
            last_child_line.trim_end().ends_with("; note"),
            "trailing comment should stay glued to (bar x)'s line: {last_child_line:?}"
        );
        let closing_line = out.lines().last().unwrap();
        assert_eq!(
            closing_line.trim(),
            ")",
            "the closing paren must be alone on its own line, not appended after the comment: {out:?}"
        );
    }

    #[test]
    fn string_atoms_round_trip_verbatim_including_escapes() {
        let src = r#"(define s "hi \"there\"\n")
"#;
        assert_eq!(fmt_ok(src), src);
    }

    #[test]
    fn preserves_bracket_and_brace_delimiter_choice() {
        // Short enough to canonicalize onto one line — but `[...]` clauses and `{...}` implicit
        // binders must never be rewritten into `(...)`.
        let src = "(match x\n  [(Zero) 0]\n  [(Succ n) 1])\n";
        assert_eq!(fmt_ok(src), "(match x [(Zero) 0] [(Succ n) 1])\n");
        let src2 = "(lam {A Type} (x A) x)\n";
        assert_eq!(fmt_ok(src2), src2);
    }

    #[test]
    fn format_is_idempotent() {
        let corpus = [
            "(define a 1)\n(define b 2)\n",
            "(defdata Nat ()\n  (Zero)  ; base case\n  (Succ (n Nat)))\n",
            "(the Nat\n  x)  ; a note\n",
            "(define a 1)\n\n\n(define b 2)\n",
            "; header comment\n;\n(define a 1)\n",
        ];
        for src in corpus {
            let once = fmt_ok(src);
            let twice = fmt_ok(&once);
            assert_eq!(once, twice, "not idempotent on {src:?}");
        }
    }

    #[test]
    fn rejects_mismatched_delimiters() {
        assert!(format_source("(foo]").is_err());
    }

    #[test]
    fn rejects_unterminated_list() {
        assert!(format_source("(foo (bar)").is_err());
    }

    #[test]
    fn rejects_unbalanced_close() {
        assert!(format_source("(foo))").is_err());
    }

    #[test]
    fn rejects_unterminated_string() {
        assert!(format_source("(define s \"unterminated)").is_err());
    }

    #[test]
    fn fmt_check_flags_unformatted_source() {
        let messy = "(  define a   1 )\n";
        let tidy = fmt_ok(messy);
        assert_ne!(
            messy, tidy,
            "the messy source should not already be canonical"
        );
        assert_eq!(
            fmt_ok(&tidy),
            tidy,
            "the tidy source should already be canonical"
        );
    }
}
