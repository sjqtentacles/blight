//! Regression: `comp`/`transp` over an OPEN family (one capturing enclosing binders) must not crash.
//!
//! `family_is_constant` used to quote at a hardcoded term-level 0, underflowing `quote` on the ambient
//! neutrals of an open family — crashing the checker on ordinary path composition via `comp`. It now
//! derives its level from the family's captured env. Independently, `comp`'s Kan-adequacy compared
//! `tube@i0` against `base` *transported* into `A(i1)` (a cross-type comparison that also forced the
//! crash); it now compares `tube@i0 ≡ base` in `A(i0)`, exactly as `HComp` does.

use blight_elab::{ElabEnv, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

fn checks(body: &str) -> Result<(), String> {
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    prog.run(body).map(|_| ()).map_err(|e| format!("{e:?}"))
}

/// Ordinary path composition via `comp` over an open family `k. A` (`A` a context variable) must
/// type-check — before the fix it underflow-panicked the checker.
#[test]
fn comp_path_composition_over_open_family() {
    let cconcat = "(define cconcat \
        (Pi ((A (Type 0)) (x A) (y A) (z A) (p (Path A x y)) (q (Path A y z))) (Path A x z)) \
        (lam (A x y z p q) (plam (i) (comp (plam (k) A) (ieq1 i) (plam (j) (q @ j)) (p @ i)))))";
    assert!(
        checks(cconcat).is_ok(),
        "comp path composition over an open family must type-check, not underflow-crash the checker",
    );
}

/// The Kan-adequacy guard must still reject a `comp` minting a false path (the fix must not weaken it).
#[test]
fn false_comp_still_rejected_by_adequacy() {
    let bad = "(load \"std/bool.bl\")\n(define bad (Path Bool true false) \
        (plam (i) (comp (plam (k) Bool) (ieq1 i) (plam (j) false) true)))";
    assert!(
        checks(bad).is_err(),
        "a false comp must still be rejected by Kan-adequacy",
    );
}
