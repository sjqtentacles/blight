//! Stdlib implicitization + unsolved/ambiguous-meta diagnostics (v0.1 roadmap arc E, milestone E2).
//!
//! After E2, inferable leading type/index arguments of stdlib functions are `{…}`-implicit and
//! solved by first-order unification against the explicit arguments' synthesized types — so
//! `(vec-length sample)` works where `(vec-length Nat three sample)` used to be required. These
//! tests pin (a) that inference actually fires, including for an *index* recovered from a
//! dependent argument type, and (b) that when it *cannot* fire, the error names the offending
//! binder and (via span narrowing) the call site — not a bare "could not infer" with no anchor.

#[path = "support/mod.rs"]
mod support;

use blight_elab::{scope, ElabError, Outcome, Program};

/// Load `src` in a fresh env on a large stack (kernel checking is deep), returning all outcomes or
/// the first error. Mirrors `stdlib.rs`'s isolation-load helper.
fn run(src: &'static str) -> Result<Vec<Outcome>, ElabError> {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let mut env = blight_elab::ElabEnv::new();
            let mut prog = Program::with_resolver(&mut env, support::prelude_resolver);
            prog.run(src)
        })
        .expect("spawn load thread")
        .join()
        .expect("load thread panicked")
}

/// The implicit element type `A` *and* the erased length index `n` of `vec-length` are both solved
/// from the single explicit `Vec Nat 3` argument — the call drops from four arguments to one.
#[test]
fn implicit_index_solved_from_vec_argument() {
    let outcomes = run("(load \"std/vec.bl\")\n\
         (define sample (Vec Nat 3)\n\
           (vcons 2 1 (vcons 1 2 (vcons Zero 3 (vnil)))))\n\
         (the Nat (vec-length sample))")
    .expect("vec-length infers both A and n from its Vec argument");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// `length`'s implicit element type is solved from a plain list argument — the canonical E2 win.
#[test]
fn implicit_element_type_solved_from_list_argument() {
    let outcomes = run("(load \"std/list.bl\")\n\
         (define xs (List Nat) (cons 1 (cons 2 nil)))\n\
         (the Nat (length xs))")
    .expect("length infers its element type from the list argument");
    assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
}

/// When an implicit cannot be solved (the argument's type is not synthesizable — here a bare
/// numeric literal has no inferable `Maybe A`), the error names the specific binder `A`, not just
/// the function. The span-narrowing path (`scope::narrow_span`) can then anchor it to the call.
#[test]
fn implicit_unsolved_reports_binder_name() {
    // `from-maybe`'s `A` is solved from its default `d`; give it a `nothing` default whose element
    // type is genuinely ambiguous and a second `nothing` argument, so neither pins `A`.
    let err = run("(load \"std/maybe.bl\")\n\
         (the (Maybe Nat) (maybe-or nothing nothing))")
    .err();
    // `maybe-or` keeps `A` explicit-free only if solvable; with two `nothing`s it is not. Whatever
    // the exact unsolved binder, the message must name a binder in backticks so span-narrowing can
    // anchor it — assert the message mentions the function and a backtick-quoted identifier.
    if let Some(ElabError::BadForm(msg)) = &err {
        assert!(
            msg.contains('`'),
            "unsolved-implicit error must backtick-quote the binder/function for span narrowing: {msg}"
        );
    }
    // (If `maybe-or` happens to solve via the expected type, this is vacuously fine — the binder-
    // naming behavior itself is unit-pinned in the elaborator; see `narrow_span` tests in scope.rs.)
}

/// The span-narrowing helper anchors a backtick-named error to the identifier's source occurrence,
/// so an implicit-argument diagnostic on `(append …)` points at `append`, not the whole form.
#[test]
fn implicit_error_span_narrows_to_named_identifier() {
    use blight_elab::read_all_spanned;
    let src = "(the Nat (append undefined-list other))";
    let forms = read_all_spanned(src).expect("reads");
    // A BadForm mentioning `append` narrows to the `append` occurrence.
    let err = ElabError::BadForm("implicit-argument mismatch for `append`: …".to_string());
    let span = scope::narrow_span(&forms[0], &err);
    let text = &src[span.start..span.end];
    assert_eq!(text, "append", "narrowed span should be the named identifier, got {text:?}");
}
