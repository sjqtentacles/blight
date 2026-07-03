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

/// The pure-Rust checking pipeline the export wraps (host-testable without wasm).
pub fn check_source(_src: &str) -> String {
    "R2: pending".to_string()
}
