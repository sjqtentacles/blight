//! R2 (v0.1 roadmap): the browser playground's checker, exported over a thin C ABI so a static
//! page can instantiate the raw cdylib with `WebAssembly.instantiate` — no wasm-bindgen, no
//! bundler, no npm. Protocol: the host calls [`bp_alloc`] to place UTF-8 source, [`bp_check`]
//! returns a length-prefixed (4-byte LE) UTF-8 report the host reads and then releases with
//! [`bp_free_report`].
//!
//! Scope (per the roadmap): source in → elaborate + kernel-check + independent re-check verdicts
//! out (the type of `main`, errors with carets). *Not* running compiled programs — the wasm
//! runtime has no Console/GC in v0.1.

/// Allocate `len` bytes the host can write source into. Paired with the implicit ownership
/// transfer into [`bp_check`] (which reads, never frees — the host owns the input buffer and
/// should call [`bp_free_input`]).
#[no_mangle]
pub extern "C" fn bp_alloc(len: usize) -> *mut u8 {
    let mut buf = Vec::<u8>::with_capacity(len);
    let ptr = buf.as_mut_ptr();
    std::mem::forget(buf);
    ptr
}

/// Release an input buffer previously obtained from [`bp_alloc`].
///
/// # Safety
/// `ptr`/`len` must be exactly a live `bp_alloc(len)` result, released once.
#[no_mangle]
pub unsafe extern "C" fn bp_free_input(ptr: *mut u8, len: usize) {
    drop(Vec::from_raw_parts(ptr, 0, len));
}

/// Release a report buffer previously returned by [`bp_check`].
///
/// # Safety
/// `ptr` must be exactly a live `bp_check` result, released once.
#[no_mangle]
pub unsafe extern "C" fn bp_free_report(ptr: *mut u8) {
    if ptr.is_null() {
        return;
    }
    let len = u32::from_le_bytes(*(ptr as *const [u8; 4])) as usize;
    drop(Vec::from_raw_parts(ptr, len + 4, len + 4));
}

/// Check `len` bytes of UTF-8 Blight source at `ptr`; return a length-prefixed UTF-8 report.
///
/// # Safety
/// `ptr`/`len` must describe initialized, readable memory (normally a `bp_alloc` buffer the
/// host wrote).
#[no_mangle]
pub unsafe extern "C" fn bp_check(ptr: *const u8, len: usize) -> *mut u8 {
    let src = std::slice::from_raw_parts(ptr, len);
    let report = match std::str::from_utf8(src) {
        Ok(src) => check_source(src),
        Err(e) => format!("error: source is not UTF-8: {e}"),
    };
    let bytes = report.into_bytes();
    let mut out = Vec::with_capacity(bytes.len() + 4);
    out.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    out.extend_from_slice(&bytes);
    let p = out.as_mut_ptr();
    std::mem::forget(out);
    p
}

/// The pure-Rust checking pipeline the export wraps (host-testable without wasm): elaborate
/// against the embedded prelude, kernel-check, then run the *independent re-checker* over every
/// typed global — the two-checker story, in the browser. Errors render with carets via the
/// span-aware driver. Panics (a checker bug, never expected) are caught and reported rather
/// than aborting the wasm instance.
pub fn check_source(src: &str) -> String {
    let src_owned = src.to_string();
    std::panic::catch_unwind(move || check_source_inner(&src_owned)).unwrap_or_else(|_| {
        "internal error: the checker panicked (please report this program)".into()
    })
}

fn check_source_inner(src: &str) -> String {
    let mut env = blight_elab::ElabEnv::new();
    let run = {
        let mut prog = blight_elab::Program::with_resolver(&mut env, |name: &str| {
            blight_prelude_embed::embedded(name)
                .map(str::to_string)
                .ok_or_else(|| {
                    blight_elab::ElabError::BadForm(format!(
                        "cannot load {name:?}: not in the embedded prelude"
                    ))
                })
        });
        prog.run_with_diagnostics(src)
    };
    let outcomes = match run {
        Err(diag) => return diag.render(src),
        Ok(outcomes) => outcomes,
    };

    let mut report = String::new();
    let checked = outcomes
        .iter()
        .filter(|o| matches!(o, blight_elab::Outcome::Checked(_)))
        .count();
    report.push_str(&format!(
        "ok: {} form(s) accepted ({checked} kernel-checked proof(s))\n",
        outcomes.len()
    ));
    if let Some(ty) = env.global_type("main") {
        report.push_str(&format!("main : {}\n", blight_elab::pretty_term(ty)));
    }
    // The independent re-checker's verdict over every typed global — agree or honestly decline;
    // a rejection is a soundness alarm and is surfaced first.
    let sig = env.signature();
    let (mut ok, mut declined, mut rejected) = (0usize, 0usize, Vec::new());
    for (name, term, ty) in env.typed_globals() {
        let j = blight_kernel::Judgement::HasType { term, ty };
        match blight_recheck::recheck_judgement(sig, &j) {
            Ok(()) => ok += 1,
            Err(blight_recheck::RecheckError::Declined(_)) => declined += 1,
            Err(blight_recheck::RecheckError::Rejected(m)) => rejected.push((name, m)),
        }
    }
    for (name, m) in &rejected {
        report.push_str(&format!(
            "SOUNDNESS ALARM — independent re-check REJECTED `{name}`: {m}\n"
        ));
    }
    report.push_str(&format!(
        "re-check (independent second checker): {ok} verified, {declined} honestly declined, {} rejected\n",
        rejected.len()
    ));
    report
}
