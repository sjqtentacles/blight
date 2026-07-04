//! S-expression reader (spec §5): the homoiconic surface syntax. UNTRUSTED.

/// A half-open byte range `[start, end)` into the original source text. Used to point diagnostics at
/// the exact offending token/form (spec §5 surface). Spans compose: a list's span covers its open
/// paren through its close paren.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Span {
        Span { start, end }
    }

    /// The smallest span covering both `self` and `other`.
    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

/// A node paired with its source [`Span`]. The span-aware reader (`read_all_spanned`) produces a
/// `Spanned<Sexpr>` tree (whose `List` children are themselves spanned via [`SpannedSexpr`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(node: T, span: Span) -> Spanned<T> {
        Spanned { node, span }
    }
}

/// A fully span-annotated s-expression: every atom and every (sub)list carries its own span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpannedSexpr {
    Atom(String),
    List(Vec<Spanned<SpannedSexpr>>),
}

impl Spanned<SpannedSexpr> {
    /// Drop all span information, recovering the plain [`Sexpr`] the rest of the pipeline consumes.
    pub fn strip(&self) -> Sexpr {
        match &self.node {
            SpannedSexpr::Atom(a) => Sexpr::Atom(a.clone()),
            SpannedSexpr::List(items) => Sexpr::List(items.iter().map(|s| s.strip()).collect()),
        }
    }
}

/// A raw s-expression: the parse tree before it is interpreted as a surface form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexpr {
    /// An atom (symbol, keyword, or literal token), kept as text.
    Atom(String),
    /// A list `( ... )`.
    List(Vec<Sexpr>),
}

/// A reader/parser error with a human-facing message, and (when known) the source [`Span`] of the
/// offending text so a diagnostic can underline it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadError {
    pub msg: String,
    pub span: Option<Span>,
}

impl ReadError {
    pub fn new(msg: impl Into<String>) -> ReadError {
        ReadError {
            msg: msg.into(),
            span: None,
        }
    }

    pub fn at(msg: impl Into<String>, span: Span) -> ReadError {
        ReadError {
            msg: msg.into(),
            span: Some(span),
        }
    }
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.msg)
    }
}

/// The maximum s-expression nesting depth the reader accepts. Past this, recursion is refused with a
/// [`ReadError`] rather than overflowing the stack — adversarial input like `((((((…` (found by the
/// `reader`/`elab`/`kernel` fuzz targets) is rejected gracefully. Far above any plausible hand- or
/// machine-written program. Kept well below the point where the reader's own (mutually recursive)
/// descent would exhaust a small thread stack.
pub const MAX_DEPTH: usize = 256;

/// Parse a single s-expression from the front of `input`, returning it and the unconsumed rest.
pub fn read_one(input: &str) -> Result<(Sexpr, &str), ReadError> {
    let (s, rest) = read_one_spanned_at(input, 0, 0)?;
    Ok((s.strip(), rest))
}

/// Parse all s-expressions in `input` until it is exhausted.
pub fn read_all(input: &str) -> Result<Vec<Sexpr>, ReadError> {
    Ok(read_all_spanned(input)?.iter().map(|s| s.strip()).collect())
}

/// Span-aware sibling of [`read_all`]: parse every top-level form, each annotated with its source
/// span (and recursively for sublists). Byte offsets are absolute into `input`.
pub fn read_all_spanned(input: &str) -> Result<Vec<Spanned<SpannedSexpr>>, ReadError> {
    let mut out = Vec::new();
    let mut abs = skip_ws_at(input, 0);
    while abs < input.len() {
        let (s, after) = read_one_spanned_at(&input[abs..], abs, 0)?;
        out.push(s);
        abs = skip_ws_at(input, after_offset(input, abs, after));
    }
    Ok(out)
}

/// Helper: given the slice `&input[abs..]` and the returned `rest` slice from a reader, recover the
/// absolute offset of `rest` into `input`.
fn after_offset(input: &str, _abs: usize, rest: &str) -> usize {
    // `rest` is a suffix of `input`; its start offset is the difference of the pointers.
    input.len() - rest.len()
}

/// Span-aware single read at absolute base offset `base` (the offset of `input[0]` into the source).
fn read_one_spanned_at(
    input: &str,
    base: usize,
    depth: usize,
) -> Result<(Spanned<SpannedSexpr>, &str), ReadError> {
    let trimmed = skip_ws(input);
    let lead = input.len() - trimmed.len();
    let start = base + lead;
    let rest = trimmed;
    if depth > MAX_DEPTH {
        return Err(ReadError::at(
            format!("s-expression nesting too deep (limit {MAX_DEPTH})"),
            Span::new(start, start + 1),
        ));
    }
    match rest.chars().next() {
        None => Err(ReadError::new("unexpected end of input")),
        Some('(') | Some('[') => read_list_spanned(rest, start, depth),
        Some('{') => read_brace_spanned(rest, start, depth),
        Some('"') => {
            let (atom, after) = read_string(rest)?;
            let end = start + (rest.len() - after.len());
            let text = match atom {
                Sexpr::Atom(a) => a,
                _ => unreachable!("read_string yields an atom"),
            };
            Ok((
                Spanned::new(SpannedSexpr::Atom(text), Span::new(start, end)),
                after,
            ))
        }
        Some(')') | Some(']') | Some('}') => Err(ReadError::at(
            "unexpected close paren",
            Span::new(start, start + 1),
        )),
        Some(_) => {
            let (atom, after) = read_atom(rest)?;
            let end = start + (rest.len() - after.len());
            let text = match atom {
                Sexpr::Atom(a) => a,
                _ => unreachable!("read_atom yields an atom"),
            };
            Ok((
                Spanned::new(SpannedSexpr::Atom(text), Span::new(start, end)),
                after,
            ))
        }
    }
}

fn read_list_spanned(
    input: &str,
    start: usize,
    depth: usize,
) -> Result<(Spanned<SpannedSexpr>, &str), ReadError> {
    let open = input.chars().next().unwrap();
    let close = if open == '(' { ')' } else { ']' };
    let mut rest = &input[open.len_utf8()..];
    let mut cursor = start + open.len_utf8();
    let mut items = Vec::new();
    loop {
        let trimmed = skip_ws(rest);
        cursor += rest.len() - trimmed.len();
        rest = trimmed;
        match rest.chars().next() {
            None => return Err(ReadError::at("unterminated list", Span::new(start, cursor))),
            Some(c) if c == close => {
                let end = cursor + c.len_utf8();
                return Ok((
                    Spanned::new(SpannedSexpr::List(items), Span::new(start, end)),
                    &rest[c.len_utf8()..],
                ));
            }
            Some(c) if c == ')' || c == ']' => {
                return Err(ReadError::at(
                    format!("mismatched close paren '{c}'"),
                    Span::new(cursor, cursor + c.len_utf8()),
                ));
            }
            Some(_) => {
                let (item, after) = read_one_spanned_at(rest, cursor, depth + 1)?;
                let consumed = rest.len() - after.len();
                cursor += consumed;
                rest = after;
                items.push(item);
            }
        }
    }
}

fn read_brace_spanned(
    input: &str,
    start: usize,
    depth: usize,
) -> Result<(Spanned<SpannedSexpr>, &str), ReadError> {
    let mut rest = &input['{'.len_utf8()..];
    let mut cursor = start + '{'.len_utf8();
    let mut items = vec![Spanned::new(
        SpannedSexpr::Atom("brace".into()),
        Span::new(start, cursor),
    )];
    loop {
        let trimmed = skip_ws(rest);
        cursor += rest.len() - trimmed.len();
        rest = trimmed;
        match rest.chars().next() {
            None => {
                return Err(ReadError::at(
                    "unterminated brace group",
                    Span::new(start, cursor),
                ))
            }
            Some('}') => {
                let end = cursor + '}'.len_utf8();
                return Ok((
                    Spanned::new(SpannedSexpr::List(items), Span::new(start, end)),
                    &rest['}'.len_utf8()..],
                ));
            }
            Some(c) if c == ')' || c == ']' => {
                return Err(ReadError::at(
                    format!("mismatched close paren '{c}'"),
                    Span::new(cursor, cursor + c.len_utf8()),
                ));
            }
            Some(_) => {
                let (item, after) = read_one_spanned_at(rest, cursor, depth + 1)?;
                cursor += rest.len() - after.len();
                rest = after;
                items.push(item);
            }
        }
    }
}

/// Skip whitespace/comments starting from absolute offset `at` into `input`, returning the new
/// absolute offset.
fn skip_ws_at(input: &str, at: usize) -> usize {
    let trimmed = skip_ws(&input[at..]);
    input.len() - trimmed.len()
}

/// Skip whitespace and `;`-to-end-of-line comments.
fn skip_ws(input: &str) -> &str {
    let mut rest = input;
    loop {
        let trimmed = rest.trim_start();
        if let Some(after) = trimmed.strip_prefix(';') {
            // line comment: drop through end of line.
            rest = match after.find('\n') {
                Some(nl) => &after[nl + 1..],
                None => "",
            };
            continue;
        }
        return trimmed;
    }
}

fn is_delim(c: char) -> bool {
    c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ';')
}

fn read_atom(input: &str) -> Result<(Sexpr, &str), ReadError> {
    let end = input.find(is_delim).unwrap_or(input.len());
    if end == 0 {
        return Err(ReadError::new("empty atom"));
    }
    Ok((Sexpr::Atom(input[..end].to_string()), &input[end..]))
}

/// A string literal `"…"` reads as an atom whose text retains the surrounding quotes and whose
/// interior is decoded (`\"`, `\\`, `\n`, `\t`). Keeping the quotes lets downstream code recognize
/// a string atom (vs. a symbol) and recover the contents by stripping the first/last char.
fn read_string(input: &str) -> Result<(Sexpr, &str), ReadError> {
    let mut rest = &input['"'.len_utf8()..];
    let mut out = String::from("\"");
    loop {
        match rest.chars().next() {
            None => return Err(ReadError::new("unterminated string literal")),
            Some('"') => {
                out.push('"');
                return Ok((Sexpr::Atom(out), &rest['"'.len_utf8()..]));
            }
            Some('\\') => {
                rest = &rest['\\'.len_utf8()..];
                match rest.chars().next() {
                    Some('n') => out.push('\n'),
                    Some('t') => out.push('\t'),
                    Some('"') => out.push('"'),
                    Some('\\') => out.push('\\'),
                    Some(c) => return Err(ReadError::new(format!("unknown escape '\\{c}'"))),
                    None => return Err(ReadError::new("dangling escape in string")),
                }
                let c = rest.chars().next().unwrap();
                rest = &rest[c.len_utf8()..];
            }
            Some(c) => {
                out.push(c);
                rest = &rest[c.len_utf8()..];
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_atom() {
        let (s, rest) = read_one("Zero rest").unwrap();
        assert_eq!(s, Sexpr::Atom("Zero".into()));
        assert_eq!(rest.trim_start(), "rest");
    }

    #[test]
    fn reads_nested_list() {
        let (s, _) = read_one("(Succ (n Nat))").unwrap();
        assert_eq!(
            s,
            Sexpr::List(vec![
                Sexpr::Atom("Succ".into()),
                Sexpr::List(vec![Sexpr::Atom("n".into()), Sexpr::Atom("Nat".into())]),
            ])
        );
    }

    #[test]
    fn brackets_are_lists_too() {
        let (s, _) = read_one("[(Zero) b]").unwrap();
        assert_eq!(
            s,
            Sexpr::List(vec![
                Sexpr::List(vec![Sexpr::Atom("Zero".into())]),
                Sexpr::Atom("b".into()),
            ])
        );
    }

    #[test]
    fn reads_multiple_top_level() {
        let all = read_all("(a) (b)\n; comment\n(c)").unwrap();
        assert_eq!(all.len(), 3);
    }

    #[test]
    fn skips_comments() {
        let all = read_all("; lead\n(ok) ; trailing\n").unwrap();
        assert_eq!(all, vec![Sexpr::List(vec![Sexpr::Atom("ok".into())])]);
    }

    #[test]
    fn string_literal_reads() {
        // A string with spaces and an escaped quote reads as one atom retaining outer quotes.
        let (s, rest) = read_one(r#""hello world \"x\"" tail"#).unwrap();
        assert_eq!(s, Sexpr::Atom("\"hello world \"x\"\"".into()));
        assert_eq!(rest.trim_start(), "tail");
        // It is a single atom inside a list, not split on the interior whitespace.
        let (l, _) = read_one(r#"(load "a b.bl")"#).unwrap();
        assert_eq!(
            l,
            Sexpr::List(vec![
                Sexpr::Atom("load".into()),
                Sexpr::Atom("\"a b.bl\"".into()),
            ])
        );
    }

    #[test]
    fn spans_point_at_the_source() {
        // `(Succ n)` — the list spans the whole form; the atoms span their own slices.
        let src = "(Succ n)";
        let forms = read_all_spanned(src).unwrap();
        assert_eq!(forms.len(), 1);
        let top = &forms[0];
        assert_eq!(top.span, Span::new(0, 8));
        assert_eq!(&src[top.span.start..top.span.end], "(Succ n)");
        let items = match &top.node {
            SpannedSexpr::List(items) => items,
            _ => panic!("expected a list"),
        };
        assert_eq!(&src[items[0].span.start..items[0].span.end], "Succ");
        assert_eq!(&src[items[1].span.start..items[1].span.end], "n");
    }

    #[test]
    fn spans_survive_leading_whitespace_and_comments() {
        let src = "; lead\n  (a b)\n";
        let forms = read_all_spanned(src).unwrap();
        assert_eq!(forms.len(), 1);
        assert_eq!(&src[forms[0].span.start..forms[0].span.end], "(a b)");
    }

    #[test]
    fn second_form_span_is_absolute() {
        let src = "(a)\n(bb)";
        let forms = read_all_spanned(src).unwrap();
        assert_eq!(forms.len(), 2);
        assert_eq!(&src[forms[1].span.start..forms[1].span.end], "(bb)");
    }

    #[test]
    fn unterminated_list_error_carries_a_span() {
        let err = read_all_spanned("(a b").unwrap_err();
        assert!(err.span.is_some(), "reader errors should carry a span");
        assert!(err.msg.contains("unterminated"));
    }

    #[test]
    fn strip_recovers_plain_sexpr() {
        let src = "(Succ (n Nat))";
        let spanned = read_all_spanned(src).unwrap();
        assert_eq!(spanned[0].strip(), read_one(src).unwrap().0);
    }

    #[test]
    fn deeply_nested_input_is_rejected_not_overflowed() {
        // Pathologically deep nesting (found by the fuzz targets) must return a `ReadError`, not
        // overflow the stack. Use well past `MAX_DEPTH` open parens.
        let src = "(".repeat(MAX_DEPTH + 50);
        let err = read_all(&src).unwrap_err();
        assert!(
            err.msg.contains("too deep"),
            "expected a depth-limit error, got: {}",
            err.msg
        );
        // A merely-deep-but-legal nesting still parses.
        let ok_depth = 100;
        let nested = format!("{}x{}", "(".repeat(ok_depth), ")".repeat(ok_depth));
        assert!(read_all(&nested).is_ok());
    }
}
