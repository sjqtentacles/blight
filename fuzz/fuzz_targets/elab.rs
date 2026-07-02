#![no_main]
//! Fuzz the **elaborator** front end: read arbitrary input, then run each form through
//! `parse_surface`/`parse_decl` and `elaborate`. Malformed or ill-typed input must surface as an
//! `Err`, never a panic.

use blight_elab::{elaborate, parse_decl, parse_surface, read_all, ElabEnv};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    let Ok(forms) = read_all(src) else {
        return;
    };
    let env = ElabEnv::new();
    for form in &forms {
        if let Ok(surface) = parse_surface(form) {
            let _ = elaborate(&env, &surface);
        }
        let _ = parse_decl(form);
    }
});
