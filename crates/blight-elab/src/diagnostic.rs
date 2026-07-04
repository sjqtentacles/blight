//! Source-pointing diagnostics (spec §5 surface). UNTRUSTED.
//!
//! A [`Diagnostic`] pairs a human-facing message with an optional source [`Span`]. Given the
//! original source text, [`render`] produces a multi-line string that quotes the offending line and
//! underlines the exact range with carets — the standard compiler-diagnostic shape, hand-rolled to
//! avoid a heavyweight dependency.

use crate::sexpr::Span;

/// A diagnostic: what went wrong, and (when known) where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    pub span: Option<Span>,
}

impl Diagnostic {
    pub fn new(message: impl Into<String>) -> Diagnostic {
        Diagnostic {
            message: message.into(),
            span: None,
        }
    }

    pub fn at(message: impl Into<String>, span: Span) -> Diagnostic {
        Diagnostic {
            message: message.into(),
            span: Some(span),
        }
    }

    /// Render this diagnostic against `source`, quoting the offending line with a caret underline.
    pub fn render(&self, source: &str) -> String {
        render(source, self.span, &self.message)
    }
}

/// The 1-based `(line, column)` of byte offset `off` in `source`. Public so callers outside this
/// module (e.g. an LSP server mapping a `Span` to an editor position) can reuse the exact same
/// offset accounting `render` uses, rather than re-implementing line/column arithmetic.
pub fn line_col(source: &str, off: usize) -> (usize, usize) {
    let (line, col, _range) = locate(source, off);
    (line, col)
}

/// The 1-based `(line, column)` of byte offset `off` in `source`, plus the byte range of the line
/// that contains it.
fn locate(source: &str, off: usize) -> (usize, usize, std::ops::Range<usize>) {
    let off = off.min(source.len());
    let line_start = source[..off].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = source[off..]
        .find('\n')
        .map(|i| off + i)
        .unwrap_or(source.len());
    let line_no = source[..off].bytes().filter(|&b| b == b'\n').count() + 1;
    let col = source[line_start..off].chars().count() + 1;
    (line_no, col, line_start..line_end)
}

/// Render a message with an optional span against `source`. With a span, quote the line and
/// underline `[start, end)` with carets; without one, just return the message.
pub fn render(source: &str, span: Option<Span>, message: &str) -> String {
    let Some(span) = span else {
        return format!("error: {message}");
    };
    let (line_no, col, line_range) = locate(source, span.start);
    let line = &source[line_range.clone()];
    // Column of the underline start within the displayed line (chars, for alignment).
    let underline_start = source[line_range.start..span.start.min(line_range.end)]
        .chars()
        .count();
    // Underline length: clamp the span to this line so a multi-line span still renders sanely.
    let span_end_on_line = span.end.min(line_range.end);
    let underline_len = source[span.start.min(line_range.end)..span_end_on_line]
        .chars()
        .count()
        .max(1);

    let gutter = format!("{line_no}");
    let pad = " ".repeat(gutter.len());
    let caret = format!(
        "{}{}",
        " ".repeat(underline_start),
        "^".repeat(underline_len)
    );
    format!(
        "error: {message}\n\
         {pad} --> line {line_no}:{col}\n\
         {pad} |\n\
         {gutter} | {line}\n\
         {pad} | {caret}"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_caret_under_the_span() {
        let src = "(define x\n  (bad form))";
        // Underline "bad" on line 2.
        let start = src.find("bad").unwrap();
        let span = Span::new(start, start + 3);
        let out = render(src, Some(span), "something is wrong");
        assert!(out.contains("error: something is wrong"));
        assert!(out.contains("line 2:"));
        assert!(out.contains("(bad form))"));
        assert!(out.contains("^^^"), "three carets under `bad`: {out}");
    }

    #[test]
    fn no_span_is_just_the_message() {
        assert_eq!(render("x", None, "oops"), "error: oops");
    }

    #[test]
    fn locate_reports_line_and_column() {
        let src = "ab\ncde";
        let off = src.find('d').unwrap();
        let (line, col, _range) = locate(src, off);
        assert_eq!((line, col), (2, 2));
    }
}
