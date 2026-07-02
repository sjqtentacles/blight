//! E1 (numeric literals, v0.1 roadmap arc E): the REPL-facing round-trip. A checked `(the T e)`
//! form's conclusion is rendered with [`blight_elab::pretty_concl`] — the same renderer the REPL's
//! `:type` command and the `blight build` error path use — so this pins that a `Nat` numeral
//! prints back as a decimal, not the raw `Succ`-chain, closing the loop with the parser side
//! (`crates/blight-elab/tests/literals.rs`).

use blight_elab::{pretty_concl, ElabEnv, Outcome, Program};

const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n";

#[test]
#[ignore = "E1 red: bare-decimal detection in parse_surface lands in the next commit"]
fn repl_prints_canonical_nat_as_decimal() {
    let mut env = ElabEnv::new();
    let mut prog = Program::new(&mut env);
    let outcomes = prog
        .run(&format!("{NAT}(the Nat 3)"))
        .expect("(the Nat 3) checks");
    let Some(Outcome::Checked(proof)) = outcomes.last() else {
        panic!("expected a Checked outcome, got {outcomes:?}");
    };
    assert_eq!(pretty_concl(proof), "\u{22a2} 3 : Nat");
}
