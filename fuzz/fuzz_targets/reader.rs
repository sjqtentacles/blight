#![no_main]
//! Fuzz the surface s-expression **reader**: arbitrary UTF-8 in, the tokenizer/parser must return a
//! `Result` (never panic, hang, or overflow the stack on pathological nesting).

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(src) = std::str::from_utf8(data) {
        let _ = blight_elab::read_all(src);
    }
});
