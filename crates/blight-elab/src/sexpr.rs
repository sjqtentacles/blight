//! S-expression reader (spec §5): the homoiconic surface syntax. UNTRUSTED.

/// A raw s-expression: the parse tree before it is interpreted as a surface form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexpr {
    /// An atom (symbol, keyword, or literal token), kept as text.
    Atom(String),
    /// A list `( ... )`.
    List(Vec<Sexpr>),
}

/// A reader/parser error with a human-facing message.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadError(pub String);

/// Parse a single s-expression from the front of `input`, returning it and the unconsumed rest.
pub fn read_one(input: &str) -> Result<(Sexpr, &str), ReadError> {
    let rest = skip_ws(input);
    let mut chars = rest.char_indices();
    match chars.next() {
        None => Err(ReadError("unexpected end of input".into())),
        Some((_, '(')) | Some((_, '[')) => read_list(rest),
        Some((_, ')')) | Some((_, ']')) => Err(ReadError("unexpected close paren".into())),
        Some(_) => read_atom(rest),
    }
}

/// Parse all s-expressions in `input` until it is exhausted.
pub fn read_all(input: &str) -> Result<Vec<Sexpr>, ReadError> {
    let mut out = Vec::new();
    let mut rest = skip_ws(input);
    while !rest.is_empty() {
        let (s, after) = read_one(rest)?;
        out.push(s);
        rest = skip_ws(after);
    }
    Ok(out)
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
    c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | ';')
}

fn read_atom(input: &str) -> Result<(Sexpr, &str), ReadError> {
    let end = input.find(is_delim).unwrap_or(input.len());
    if end == 0 {
        return Err(ReadError("empty atom".into()));
    }
    Ok((Sexpr::Atom(input[..end].to_string()), &input[end..]))
}

fn read_list(input: &str) -> Result<(Sexpr, &str), ReadError> {
    // input starts with '(' or '['; record the matching close.
    let open = input.chars().next().unwrap();
    let close = if open == '(' { ')' } else { ']' };
    let mut rest = &input[open.len_utf8()..];
    let mut items = Vec::new();
    loop {
        rest = skip_ws(rest);
        match rest.chars().next() {
            None => return Err(ReadError("unterminated list".into())),
            Some(c) if c == close => {
                return Ok((Sexpr::List(items), &rest[c.len_utf8()..]));
            }
            Some(c) if c == ')' || c == ']' => {
                return Err(ReadError(format!("mismatched close paren '{c}'")));
            }
            Some(_) => {
                let (item, after) = read_one(rest)?;
                items.push(item);
                rest = after;
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
}

