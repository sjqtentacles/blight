//! Diagnostics quality (E7, v0.1 roadmap): golden rendered output for the four headline error
//! shapes. Red-guarded until the pass lands; each golden is the *target* rendering, designed from
//! the measured current output (captured 2026-07-03):
//!
//!   unbound-typo:  `unbound name: Succc`                                      (no suggestion)
//!   lam-arity:     `… cannot infer a type (needs an ascription): lambda/pair …` (generic)
//!   the-mismatch:  `… expected a constructor of DataName("Nat"), found ConName("true") …` (Debug)
//!   deftotal:      `… (use \`define-rec\` …)`                                  (no measure hint)

use blight_elab::{ElabEnv, Program};

/// Run `src` and return the rendered error string (the same rendering the CLI/REPL prints).
fn err_of(src: &str) -> String {
    let src = src.to_string();
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let mut env = ElabEnv::new();
            let mut prog = Program::new(&mut env);
            match prog.run(&src) {
                Ok(_) => panic!("probe program must fail"),
                Err(e) => e.to_string(),
            }
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n";

/// An unbound name that is one edit from a constructor in scope suggests it.
#[test]
fn unbound_var_typo_suggests_nearest_name() {
    let m = err_of(&format!("{NAT}(define x Nat (Succc Zero))"));
    assert!(
        m.contains("unbound name: Succc") && m.contains("did you mean `Succ`?"),
        "suggests the nearest name in scope: {m}"
    );
}

/// A lambda binding more parameters than its declared `Pi` type has binders names both counts.
#[test]
fn lam_arity_error_names_both_counts() {
    let m = err_of(&format!("{NAT}(define f (Pi ((a Nat)) Nat) (lam (a b) a))"));
    assert!(
        m.contains("lambda binds 2 parameters") && m.contains("has 1"),
        "names the lambda's and the type's binder counts: {m}"
    );
}

/// A `the` mismatch renders both types re-sugared (surface syntax, decimals post-E1) — never
/// Debug-formatted internals like `DataName("Nat")`.
#[test]
fn the_mismatch_renders_resugared_types() {
    let m = err_of(&format!(
        "{NAT}(defdata Bool () (true) (false))\n(the Nat true)"
    ));
    assert!(
        m.contains("expected `Nat`") && m.contains("`true`") && m.contains("`Bool`"),
        "both sides re-sugared: {m}"
    );
    assert!(
        !m.contains("DataName") && !m.contains("ConName"),
        "no Debug-formatted internals: {m}"
    );
}

/// A non-structural `deftotal` suggests the E6 measure clause alongside `define-rec`.
#[test]
fn nonstructural_deftotal_suggests_measure() {
    let m = err_of(&format!(
        "{NAT}(deftotal bad (Pi ((n Nat)) Nat) (lam (n) (bad n)))"
    ));
    assert!(
        m.contains("(measure") && m.contains("define-rec"),
        "suggests both the E6 measure clause and define-rec: {m}"
    );
}

/// Unguarded boundary pins: all four probes must at least ERROR today (the pass improves the
/// rendering, never widens acceptance).
#[test]
fn all_probe_programs_error_today() {
    for src in [
        format!("{NAT}(define x Nat (Succc Zero))"),
        format!("{NAT}(define f (Pi ((a Nat)) Nat) (lam (a b) a))"),
        format!("{NAT}(defdata Bool () (true) (false))\n(the Nat true)"),
        format!("{NAT}(deftotal bad (Pi ((n Nat)) Nat) (lam (n) (bad n)))"),
    ] {
        let _ = err_of(&src); // err_of panics if the program is accepted
    }
}
