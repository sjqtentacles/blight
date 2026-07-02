#![no_main]
//! Fuzz the **kernel** through the full program pipeline: arbitrary source is read, elaborated, and
//! every definition/`the`/`define-by` is submitted to the kernel's one door. A bad program must be
//! *rejected* (an `Err` outcome), never crash the trusted checker. `(load …)` is disabled (the
//! resolver always errors) so the fuzzer cannot touch the filesystem and stays deterministic.

use blight_elab::{ElabEnv, ElabError, Program};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, |path: &str| {
        Err(ElabError::BadForm(format!("fuzz: load disabled ({path})")))
    });
    let _ = prog.run(src);
});
