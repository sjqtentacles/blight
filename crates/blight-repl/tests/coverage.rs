//! Match coverage diagnostics (v0.1 roadmap arc E, milestone E3). A coverage pre-pass over a
//! `match`'s first-column patterns produces a clear up-front diagnostic — listing *every* missing
//! constructor at once, and flagging duplicate / unreachable arms — where the old behavior surfaced
//! a generic "no clause for constructor `X`" one constructor at a time, deep in column compilation.
//!
//! Nested coverage falls out of running the pass at every match level: a missing *inner* case is
//! caught when the lowered inner match is elaborated. Elaborator-only, zero TCB.

use blight_elab::{ElabError, Program};

/// Elaborate `src` in a fresh env (no resolver needed — these are self-contained), returning the
/// first error's message, or `None` if it checks. Large stack: kernel checking is deep.
fn err_of(src: String) -> Option<String> {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let mut env = blight_elab::ElabEnv::new();
            let mut prog = Program::new(&mut env);
            match prog.run(&src) {
                Ok(_) => None,
                Err(ElabError::BadMatch(m)) | Err(ElabError::BadForm(m)) => Some(m),
                Err(e) => Some(format!("{e:?}")),
            }
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

const ORDERING: &str = "(defdata Ordering () (lt) (eq) (gt))\n";
const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n";
const MAYBE: &str = "(defdata Maybe ((a (Type 0))) (nothing) (just (x a)))\n";

/// A match missing a single constructor names it precisely.
#[test]
fn missing_constructor_names_the_gap() {
    let msg = err_of(format!(
        "{NAT}{ORDERING}(deftotal f (Pi ((o Ordering)) Nat)\n\
           (lam (o) (match o [(lt) Zero] [(gt) Zero])))"
    ))
    .expect("non-exhaustive match must be rejected");
    assert!(msg.contains("non-exhaustive"), "msg: {msg}");
    assert!(
        msg.contains("`eq`"),
        "must name the missing `eq` constructor: {msg}"
    );
    assert!(msg.contains("Ordering"), "must name the data type: {msg}");
}

/// Multiple missing constructors are listed together, not one-at-a-time.
#[test]
fn all_missing_constructors_listed_at_once() {
    let msg = err_of(format!(
        "{NAT}{ORDERING}(deftotal f (Pi ((o Ordering)) Nat)\n\
           (lam (o) (match o [(lt) Zero])))"
    ))
    .expect("rejected");
    assert!(
        msg.contains("`eq`") && msg.contains("`gt`"),
        "both missing listed: {msg}"
    );
}

/// A nested missing case (`(just (nothing))` present, `(just (just _))` absent) is caught when the
/// inner match — produced by lowering the outer nested pattern — is elaborated.
#[test]
fn nested_missing_case_reported() {
    let msg = err_of(format!(
        "{NAT}{MAYBE}(deftotal f (Pi ((m (Maybe (Maybe Nat)))) Nat)\n\
           (lam (m) (match m [(nothing) Zero] [(just (nothing)) Zero])))"
    ))
    .expect("nested non-exhaustive must be rejected");
    assert!(msg.contains("non-exhaustive"), "nested gap reported: {msg}");
}

/// A duplicate constructor arm is rejected with a clear message.
#[test]
fn duplicate_arm_flagged() {
    let msg = err_of(format!(
        "{NAT}{ORDERING}(deftotal f (Pi ((o Ordering)) Nat)\n\
           (lam (o) (match o [(lt) Zero] [(eq) Zero] [(gt) Zero] [(lt) Zero])))"
    ))
    .expect("duplicate arm rejected");
    assert!(msg.contains("duplicate"), "msg: {msg}");
    assert!(
        msg.contains("`lt`"),
        "names the duplicated constructor: {msg}"
    );
}

/// An arm after a wildcard/var catch-all can never match and is rejected as unreachable.
#[test]
fn unreachable_arm_after_catchall_flagged() {
    let msg = err_of(format!(
        "{NAT}{ORDERING}(deftotal f (Pi ((o Ordering)) Nat)\n\
           (lam (o) (match o [(lt) Zero] [_ Zero] [(gt) Zero])))"
    ))
    .expect("unreachable arm rejected");
    assert!(msg.contains("unreachable"), "msg: {msg}");
}

/// Pins (unguarded) that a genuinely exhaustive match — including one closed by a catch-all —
/// still elaborates cleanly, so the pass never over-rejects.
#[test]
fn exhaustive_matches_still_elaborate() {
    assert!(
        err_of(format!(
            "{NAT}{ORDERING}(deftotal f (Pi ((o Ordering)) Nat)\n\
               (lam (o) (match o [(lt) Zero] [(eq) Zero] [(gt) Zero])))"
        ))
        .is_none(),
        "a complete match must elaborate"
    );
    assert!(
        err_of(format!(
            "{NAT}{ORDERING}(deftotal f (Pi ((o Ordering)) Nat)\n\
               (lam (o) (match o [(lt) Zero] [_ Zero])))"
        ))
        .is_none(),
        "a catch-all-closed match must elaborate"
    );
}
