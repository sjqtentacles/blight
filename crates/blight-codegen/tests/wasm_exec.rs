//! Acceptance: **the freestanding wasm target actually runs** (Wave 10 / P3).
//!
//! `driver::link_wasm` links a checked `term : ty` into a `.wasm` module against the portable
//! subset ported onto `runtime/wasm_rt.c` (bump-allocated Delay/Later trampoline, algebraic-effect
//! machinery, region arenas — see that file's header for the exact scope and its "Honest scope"
//! limitations). This is the wasmtime dev-dep exec harness the roadmap calls for: it *executes* the
//! linked module (not just asserts it links) and checks the returned `bl_main` i32 against the
//! value the same program produces on the native backend, so a divergence between the native and
//! wasm runtime ports is a hard CI failure rather than a silent miscompile.
//!
//! Needs a wasm-capable `clang` (the LLVM-bundled one, not Apple clang — override with
//! `BLIGHT_WASM_CC`) and `wasm-ld` (override with `BLIGHT_WASM_LD`); see `driver::link_wasm`'s
//! doc comment. Gated on the `llvm` feature like every other linked-binary integration test.
#![cfg(feature = "llvm")]

use blight_codegen::driver::{self, bench_support::prelude_resolver};
use blight_elab::{ElabEnv, Program};
use blight_kernel::{term::Term, Signature};

/// Elaborate `src` (which must define `main`) and return the checked `(term, ty, sig)` triple
/// `link_wasm`/`link_binary` both consume.
fn elaborate_main(src: &str) -> (Term, Term, Signature) {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(src)
            .unwrap_or_else(|e| panic!("test source elaborates: {e:?}"));
    }
    let term = env
        .global_term("main")
        .unwrap_or_else(|| panic!("no `main` global"))
        .clone();
    let ty = env
        .global_type("main")
        .cloned()
        .unwrap_or_else(|| term.clone());
    let sig = env.signature().clone();
    (term, ty, sig)
}

/// Link `src`'s `main` to a `.wasm` module under a fresh scratch dir, run it under `wasmtime`, and
/// return the `bl_main` result. `name` disambiguates the scratch directory across tests running in
/// parallel.
fn run_wasm(name: &str, src: &str) -> i32 {
    let dir = std::env::temp_dir().join(format!("blight_wasm_exec_{name}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("scratch dir");

    let (term, ty, sig) = elaborate_main(src);
    let out_wasm = dir.join("out.wasm");
    driver::link_wasm(&term, &ty, &sig, &out_wasm, &dir)
        .unwrap_or_else(|e| panic!("link_wasm({name}) failed: {e}"));

    let engine = wasmtime::Engine::default();
    let module =
        wasmtime::Module::from_file(&engine, &out_wasm).expect("wasm module parses/validates");
    let mut store = wasmtime::Store::new(&engine, ());
    let linker: wasmtime::Linker<()> = wasmtime::Linker::new(&engine);
    let instance = linker
        .instantiate(&mut store, &module)
        .unwrap_or_else(|e| panic!("instantiate({name}) failed (missing import?): {e}"));
    let bl_main = instance
        .get_typed_func::<(), i32>(&mut store, "bl_main")
        .expect("module exports `bl_main` (); i32");
    bl_main
        .call(&mut store, ())
        .unwrap_or_else(|e| panic!("bl_main trapped in `{name}`: {e}"))
}

/// Plain data + the growable bump allocator: `main` is computed at *runtime* (via the generic
/// structurally-recursive `mult`/`plus`, not a compile-time-folded literal) as `1000 * 5 = 5000`,
/// which allocates 5000 `bl_alloc`-ed `BL_CON` (`Succ`) nodes — comfortably more than wasm-ld's
/// small default initial page count once closures/env records for prelude loading are counted too.
/// This is the regression test for `bl_bump_ensure`: a stale version of this shim silently ran off
/// the end of linear memory here instead of growing it. (Built via repeated `mult`/`plus` rather
/// than 5000 nested `Succ`s in source, which would blow the reader's `MAX_DEPTH` nesting limit —
/// unrelated to this target.)
#[test]
fn wasm_plain_nat_grows_memory_and_matches_native() {
    let src = r#"
        (load "std/nat.bl")
        (define ten Nat (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))))))
        (define hundred Nat (mult ten ten))
        (define thousand Nat (mult hundred ten))
        (define five Nat (Succ (Succ (Succ (Succ (Succ Zero))))))
        (define main Nat (mult thousand five))
    "#;
    assert_eq!(run_wasm("plain_nat", src), 5000);
}

/// The Delay/Later trampoline (`bl_force`/`wasm_step_thunk`): a genuinely non-structural
/// `define-rec` (rejected by `deftotal`) compiles to a `later`-guarded step that only a working
/// force-trampoline can drive to completion. Mirrors `examples/ackermann.bl`'s `parity`.
#[test]
fn wasm_delay_force_trampoline_matches_native() {
    let src = r#"
        (load "std/nat.bl")
        (define-rec parity (Pi ((n Nat)) (Delay Nat))
          (lam (n)
            (match n [(Zero) (now Zero)]
              [(Succ m) (match m [(Zero) (now (Succ Zero))] [(Succ k) (parity k)])])))
        (define seven Nat (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))
        (define main Nat (force (parity seven)))
    "#;
    assert_eq!(run_wasm("delay_force", src), 1);
}

/// The algebraic-effect machinery in tail position (`bl_perform`/`bl_handle_clo`). Mirrors
/// `examples/state_handler.bl`.
#[test]
fn wasm_tail_effect_handler_matches_native() {
    let src = r#"
        (load "std/nat.bl")
        (defdata Unit () (tt))
        (effect State (get Unit Nat) (put Nat Unit))
        (define main Nat
          (handle (perform get tt) (return x x) (get x k (k (Succ (Succ (Succ Zero)))))))
    "#;
    assert_eq!(run_wasm("tail_effect", src), 3);
}

/// The **non-tail** algebraic-effect path (`bl_app`/`bl_con_bubble` OpNode-bubbling, not just
/// `bl_perform`/`bl_handle_clo`) — a stale wasm shim that only ported `bl_perform`/`bl_handle_clo`
/// verbatim but not the OpNode-awareness of `bl_app`/`bl_con_bubble` would still link (both symbols
/// exist) but silently mishandle the captured continuation here. Mirrors
/// `examples/effect_nontail.bl`.
#[test]
fn wasm_nontail_effect_handler_matches_native() {
    let src = r#"
        (load "std/nat.bl")
        (defdata Unit () (tt))
        (effect State (get Unit Nat) (put Nat Unit))
        (define main Nat
          (handle (plus (perform get tt) (perform get tt))
                  (return x x) (get x k (k (Succ (Succ Zero))))))
    "#;
    assert_eq!(run_wasm("nontail_effect", src), 4);
}

/// Region arenas (`bl_arena_enter`/`bl_arena_alloc`/`bl_arena_leave`): the escape analysis routes
/// `plus`'s scratch through the arena path. On this target that collapses to the general heap (see
/// the wasm_rt.c file header's "Honest scope" note) but must still produce the correct *value* —
/// this is the correctness half of that documented simplification. Mirrors
/// `examples/region_scratch.bl`.
#[test]
fn wasm_region_arena_matches_native() {
    let src = r#"
        (load "std/nat.bl")
        (load "regions.bl")
        (define one Nat (Succ Zero))
        (define main Nat (region r (plus one one)))
    "#;
    assert_eq!(run_wasm("region_arena", src), 2);
}
