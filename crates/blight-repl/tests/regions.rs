//! M5 region-capability tests (spec §3.5): the region capability token is an ordinary value of the
//! opaque prelude type `Rgn`, bound by a grade-1 (linear) binder. There is **no** new kernel rule —
//! these tests prove the *existing* linear-binder discipline (a grade-1 binder may be demanded at
//! most once) already enforces the capability's single-use lifetime. The trusted base is unchanged.
//!
//! Black-box: only the `blight-elab` public `Program` driver + the kernel door.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// A grade-1 region token used exactly once is accepted: `(λ r. r) : Π(r :¹ Rgn). Rgn`.
#[test]
fn region_token_used_once_ok() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(
            "(load \"regions.bl\")\n\
             (the (Pi ((r Rgn 1)) Rgn) (lam (r) r))",
        )
        .expect("a linear region token used once typechecks")
    };
    assert!(
        matches!(outcomes.last(), Some(Outcome::Checked(_))),
        "the single-use region token is kernel-checked: {outcomes:?}"
    );
}

/// A grade-1 region token used *twice* is rejected by the existing linear-binder rule — using it in
/// both components of a pair demands it at grade `ω`, which does not dominate the declared `1`.
#[test]
fn region_token_linear_used_twice_rejected() {
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    let r = prog.run(
        "(load \"regions.bl\")\n\
         (the (Pi ((r Rgn 1)) (Sigma ((x Rgn)) Rgn)) (lam (r) (pair r r)))",
    );
    assert!(
        r.is_err(),
        "a linear region token used twice must be rejected (got {r:?})"
    );
}

/// `(region r body)` parses to the dedicated surface node, distinct from `let`.
#[test]
fn region_surface_parses() {
    use blight_elab::{parse_surface, read_one, Surface};
    let (sx, _rest) = read_one("(region r Zero)").expect("reads");
    let s = parse_surface(&sx).expect("parses");
    match s {
        Surface::Region(name, body) => {
            assert_eq!(name, "r");
            assert_eq!(*body, Surface::Var("Zero".into()));
        }
        other => panic!("expected Surface::Region, got {other:?}"),
    }
}

/// A region scope whose body is an ordinary value typechecks end-to-end: `(region r Zero) : Nat`.
/// The capability `r` is in scope but unused (`0 ≤ 1`), and the result type `Nat` does not mention
/// `Rgn`, so the token does not escape.
#[test]
fn region_elaborates_and_checks() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(
            "(load \"regions.bl\")\n\
             (defdata Nat () (Zero) (Succ (n Nat)))\n\
             (the Nat (region r Zero))",
        )
        .expect("a region with a pure body typechecks")
    };
    assert!(
        matches!(outcomes.last(), Some(Outcome::Checked(_))),
        "the region scope is kernel-checked: {outcomes:?}"
    );
}

/// Returning the capability out of a region — making the region's result type `Rgn` — is rejected:
/// the token must not escape its scope (spec §3.5).
#[test]
fn region_token_escape_in_type_rejected() {
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    let r = prog.run(
        "(load \"regions.bl\")\n\
         (the Rgn (region r r))",
    );
    assert!(
        matches!(r, Err(blight_elab::ElabError::BadForm(ref m)) if m.contains("escape")),
        "a region whose result type is `Rgn` (the token escaping) must be rejected: {r:?}"
    );
}
