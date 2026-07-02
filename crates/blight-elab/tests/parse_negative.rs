//! Parser/reader NEGATIVE corpus (Track D). The happy path (round-trip) is covered by
//! `proptest_reader.rs`; this file pins the *refusal* behaviour: malformed reader input and
//! structurally ill-formed surface/declaration forms must each return an `Err` (a `ReadError` or an
//! `ElabError`) — never a panic, never a silently-accepted garbage AST. Front-end robustness is a
//! prerequisite for trusting everything downstream of it.

use blight_elab::{parse_decl, parse_surface, read_all, read_one, Sexpr};

/// Read exactly one s-expression from `src` (the source is expected to be reader-valid here; the
/// reader-level negatives are tested separately via [`read_all`]/[`read_one`]).
fn sexpr(src: &str) -> Sexpr {
    let (s, _rest) = read_one(src).unwrap_or_else(|e| panic!("`{src}` should read cleanly: {e:?}"));
    s
}

/// Reader-level malformed input is rejected with a `ReadError`, never a panic.
#[test]
fn reader_rejects_malformed_input() {
    let bad = [
        "(",        // unterminated list
        "(a (b c)", // unbalanced nesting
        "(a b))",   // read_all sees a stray close after the form
        ")",        // a bare close paren
        "(a {b)",   // mismatched bracket kinds
        "{a b",     // unterminated brace group
    ];
    for src in bad {
        let r = read_all(src);
        assert!(
            r.is_err(),
            "reader must reject `{src}` with a ReadError, got: {r:?}"
        );
    }
}

/// `read_one` on an unterminated form errors rather than returning a partial tree.
#[test]
fn read_one_rejects_unterminated_form() {
    assert!(
        read_one("(the Nat").is_err(),
        "unterminated form is a reader error"
    );
    assert!(
        read_one("(lam (x").is_err(),
        "unterminated binder list is a reader error"
    );
}

/// Structurally ill-formed *expression* forms are rejected by `parse_surface` — the head keyword is
/// recognised but its shape is wrong (missing operands, empty special forms, …).
#[test]
fn parse_surface_rejects_malformed_special_forms() {
    let bad = [
        "()",        // the empty application
        "(lam)",     // a lambda with neither parameters nor a body
        "(lam (x))", // a lambda with parameters but no body
        "(the)",     // `the` with no type and no expression
        "(the Nat)", // `the` with a type but no expression
        "(Pi)",      // a dependent function type with no telescope/codomain
        "(match)",   // a match with no scrutinee and no arms
        "(Type)",    // a universe with no level
    ];
    for src in bad {
        let s = sexpr(src);
        let r = parse_surface(&s);
        assert!(r.is_err(), "parse_surface must reject `{src}`, got: {r:?}");
    }
}

/// Ill-formed *declaration* forms are rejected by `parse_decl`.
#[test]
fn parse_decl_rejects_malformed_declarations() {
    // `parse_decl`'s `define` is `(define name body)` (the type is inferred / carried by a `the`),
    // so the malformed cases are the wrong *arities* around that shape.
    let bad = [
        "foo",                 // a bare atom is not a declaration
        "()",                  // an empty list is not a declaration
        "(define)",            // `define` with no name and no body
        "(define x)",          // `define` with a name but no body
        "(define x Nat Zero)", // `define` with too many operands (it is `(define name body)`)
        "(defdata)",           // `defdata` with no name/params/constructors
        "(define-rec f)",      // `define-rec` missing its body
        "(deftotal g)",        // `deftotal` missing its body
    ];
    for src in bad {
        let s = sexpr(src);
        let r = parse_decl(&s);
        assert!(r.is_err(), "parse_decl must reject `{src}`, got: {r:?}");
    }
}

/// A sanity counter-weight to the negative corpus: the *well-formed* shapes the negatives perturb do
/// parse, so the tests above are rejecting on structure, not on some unrelated blanket failure.
#[test]
fn well_formed_counterparts_parse() {
    parse_surface(&sexpr("(the Nat Zero)")).expect("a complete `the` parses");
    parse_surface(&sexpr("(lam (x) x)")).expect("a complete lambda parses");
    parse_surface(&sexpr("(Type 0)")).expect("a universe with a level parses");
    parse_decl(&sexpr("(define x Zero)")).expect("a complete `define` parses");
}
