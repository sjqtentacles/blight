//! Declarations of the C-runtime FFI surface the codegen emits calls to (spec §7.3/§7.4).
//!
//! These names must match `runtime/blight_rt.h`. The LLVM emitter declares each as an external
//! function in the module; the driver links the compiled runtime objects to resolve them.

/// The runtime intrinsics the emitter references, with their C signatures (documented here for the
/// emitter; the actual LLVM function types are built in [`crate::llvm`]). All Blight values are
/// opaque pointers (`BlValue`).
pub mod sym {
    /// `BlValue bl_con(uint64_t ctor_index, uint32_t nfields)` — allocate a constructor.
    pub const CON: &str = "bl_con";
    /// `BlValue bl_alloc(uint32_t tag, uint32_t nfields, uint64_t aux)` — generic allocation.
    pub const ALLOC: &str = "bl_alloc";
    /// `void bl_gc_poll(void)` — GC safepoint at back-edges / entry.
    pub const GC_POLL: &str = "bl_gc_poll";
    /// `void bl_gc_push_root(BlValue *slot)` — register a stack slot as a GC root.
    pub const GC_PUSH_ROOT: &str = "bl_gc_push_root";
    /// `void bl_gc_pop_roots(size_t n)` — pop the `n` most-recently-pushed GC roots.
    pub const GC_POP_ROOTS: &str = "bl_gc_pop_roots";
    /// `BlValue bl_force(BlValue)` — drive the delay trampoline.
    pub const FORCE: &str = "bl_force";
    /// `BlValue bl_perform(const char*, const char*, BlValue)` — perform an effect op.
    pub const PERFORM: &str = "bl_perform";
    /// `BlValue bl_handle_clo(BlValue body_clo, BlValue ret_clo, size_t n_ops, const char **op_names,
    /// BlValue *op_clos)` — install a deep handler whose clauses are Blight closure values.
    pub const HANDLE_CLO: &str = "bl_handle_clo";
    /// `BlValue bl_app(BlValue f, BlValue a)` — OpNode-aware application (delimited-continuation
    /// capture). Non-tail call sites route through this so effects bubble correctly.
    pub const APP: &str = "bl_app";
    /// `BlValue bl_con_bubble(BlValue obj)` — OpNode-aware data construction; bubbles an effectful
    /// constructor/tuple field so the surrounding build is captured into the continuation.
    pub const CON_BUBBLE: &str = "bl_con_bubble";
    /// `BlValue bl_int(int64_t)` — box an integer.
    pub const INT: &str = "bl_int";
    /// `void bl_arena_enter(void)` — open a region arena scope (spec §3.5).
    pub const ARENA_ENTER: &str = "bl_arena_enter";
    /// `BlValue bl_arena_alloc(uint32_t tag, uint32_t nfields, uint64_t aux)` — bump-allocate in the
    /// current region arena (never triggers a GC).
    pub const ARENA_ALLOC: &str = "bl_arena_alloc";
    /// `void bl_arena_leave(void)` — close the most-recent region arena scope (O(1) reclaim).
    pub const ARENA_LEAVE: &str = "bl_arena_leave";
    /// `void bl_write_barrier(BlValue obj, BlValue val)` — record an old→young store for the
    /// generational GC's remembered set (spec §7.3).
    pub const WRITE_BARRIER: &str = "bl_write_barrier";
}

/// Tag constants mirroring `BlTag` in `blight_rt.h`.
pub mod tag {
    pub const CON: u64 = 0;
    pub const TUPLE: u64 = 1;
    pub const CLOSURE: u64 = 2;
    pub const NOW: u64 = 3;
    pub const LATER: u64 = 4;
    /// A machine integer: payload in `header.aux`, no traced fields. Mirrors `BlTag::BL_INT`.
    pub const INT: u64 = 5;
    /// A bubbling effect operation (`field[0]=arg`, `field[1]=continuation closure`). Mirrors the
    /// kernel's `Value::OpNode`. Eliminators check for this tag to route through `bl_app`.
    pub const OPNODE: u64 = 6;
}

#[cfg(test)]
mod tests {
    use std::path::Path;
    use std::process::Command;

    /// Compile the runtime C sources + a C test harness (`test_src`, relative to `runtime/`) into
    /// one binary and run it.
    fn build_and_run_harness(dir: &Path, test_src: &str) -> std::process::Output {
        std::fs::create_dir_all(dir).unwrap();
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let mut objs = Vec::new();
        let srcs = [
            "gc.c",
            "stack.c",
            "delay.c",
            "effects.c",
            "arena.c",
            test_src,
        ];
        for src in srcs {
            let stem = src.replace('/', "_");
            let obj = dir.join(format!("{stem}.o"));
            let st = Command::new("clang")
                .args(["-c", "-O2", "-g", "-I"])
                .arg(&runtime)
                .arg(runtime.join(src))
                .arg("-o")
                .arg(&obj)
                .status()
                .expect("clang -c");
            assert!(st.success(), "compiling {src}");
            objs.push(obj);
        }

        let bin = dir.join("harness");
        let mut link = Command::new("clang");
        link.arg("-o").arg(&bin);
        for o in &objs {
            link.arg(o);
        }
        assert!(link.status().expect("clang link").success(), "link harness");
        Command::new(&bin).output().expect("run harness")
    }

    /// Like [`build_and_run_harness`], but also links `prelude_rt.c` compiled with `-DBL_NO_MAIN`
    /// so the harness can call its printers/constructors (`bl_print_string`, `bl_con`, …) while
    /// supplying its own `main`.
    fn build_and_run_harness_with_prelude(dir: &Path, test_src: &str) -> std::process::Output {
        std::fs::create_dir_all(dir).unwrap();
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let mut objs = Vec::new();
        // (source, extra defines)
        let srcs: [(&str, &[&str]); 6] = [
            ("gc.c", &[]),
            ("stack.c", &[]),
            ("delay.c", &[]),
            ("effects.c", &[]),
            ("arena.c", &[]),
            ("prelude_rt.c", &["-DBL_NO_MAIN"]),
        ];
        for (src, defs) in srcs {
            let stem = src.replace('/', "_");
            let obj = dir.join(format!("{stem}.o"));
            let mut cmd = Command::new("clang");
            cmd.args(["-c", "-O2", "-g", "-I"]).arg(&runtime);
            for d in defs {
                cmd.arg(d);
            }
            let st = cmd
                .arg(runtime.join(src))
                .arg("-o")
                .arg(&obj)
                .status()
                .expect("clang -c");
            assert!(st.success(), "compiling {src}");
            objs.push(obj);
        }
        // The test source itself.
        let stem = test_src.replace('/', "_");
        let test_obj = dir.join(format!("{stem}.o"));
        let st = Command::new("clang")
            .args(["-c", "-O2", "-g", "-I"])
            .arg(&runtime)
            .arg(runtime.join(test_src))
            .arg("-o")
            .arg(&test_obj)
            .status()
            .expect("clang -c");
        assert!(st.success(), "compiling {test_src}");
        objs.push(test_obj);

        let bin = dir.join("harness");
        let mut link = Command::new("clang");
        link.arg("-o").arg(&bin);
        for o in &objs {
            link.arg(o);
        }
        assert!(link.status().expect("clang link").success(), "link harness");
        Command::new(&bin).output().expect("run harness")
    }

    /// Forcing a 1,000,000-step delay chain completes without a stack overflow (spec §9 headline),
    /// and the GC runs and preserves live roots under allocation pressure.
    #[test]
    fn million_deep_via_delay_no_overflow_and_gc_collects_under_pressure() {
        let dir = std::env::temp_dir().join(format!("blight_rt_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/runtime_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "runtime harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("RUNTIME_OK"),
            "harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// A region arena: enter/alloc/leave reclaims in O(1); arena objects are traced-but-not-moved by
    /// the GC and arena allocation never triggers a collection (spec §3.5 / §7.3).
    #[test]
    fn arena_enter_alloc_leave_frees_and_objects_not_evacuated() {
        let dir = std::env::temp_dir().join(format!("blight_arena_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/arena_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "arena harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("ARENA_OK"),
            "arena harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// The generational GC: minor collections reclaim dead nursery objects while keeping long-lived
    /// rooted objects; the write barrier keeps an old→young pointer's target alive across a minor GC
    /// (spec §7.3).
    #[test]
    fn generational_minor_major_and_write_barrier() {
        let dir = std::env::temp_dir().join(format!("blight_gc_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/gc_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "gc harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("GEN_GC_OK"),
            "gc harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// A deep effect handler resumes its captured continuation (re-installing itself), and a native
    /// State `get`/`put` counter threads state to completion (spec §4.3).
    #[test]
    fn state_counter_runs_native_and_deep_handler_resumes() {
        let dir = std::env::temp_dir().join(format!("blight_eff_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/effects_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "effects harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("EFFECTS_OK"),
            "effects harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// `bl_print_string` decodes a `String` (std/string.bl `empty`/`push` cons-list of unary `Nat`
    /// codepoints) to its bytes on stdout. No kernel change — this is pure runtime tower code.
    #[test]
    fn print_string_renders_text() {
        let dir = std::env::temp_dir().join(format!("blight_str_{}", std::process::id()));
        let out = build_and_run_harness_with_prelude(&dir, "tests/string_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "string harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("STRING_OK"),
            "string harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }
}
