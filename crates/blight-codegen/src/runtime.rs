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
    /// `BlValue bl_app_global(void *fnptr, BlValue a)` — direct application of a captureless
    /// top-level function (A3 spine fusion): null env, no per-call closure allocation; an effectful
    /// argument falls back to `bl_app` so effects bubble identically.
    pub const APP_GLOBAL: &str = "bl_app_global";
    /// `BlValue bl_con_bubble(BlValue obj)` — OpNode-aware data construction; bubbles an effectful
    /// constructor/tuple field so the surrounding build is captured into the continuation.
    pub const CON_BUBBLE: &str = "bl_con_bubble";
    /// `BlValue bl_int(int64_t)` — box an integer.
    pub const INT: &str = "bl_int";
    /// `int64_t bl_int_val(BlValue)` — read an integer's payload, decoding a tagged immediate (M21).
    /// Used by `IntPrim` to read operands that may be unboxed.
    pub const INT_VAL: &str = "bl_int_val";
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
    /// `BlValue bl_nat_add(BlValue, BlValue)` — O(1) machine-word `Nat` addition (numeric.c, M20).
    pub const NAT_ADD: &str = "bl_nat_add";
    /// `BlValue bl_nat_mul(BlValue, BlValue)` — O(1) machine-word `Nat` multiplication.
    pub const NAT_MUL: &str = "bl_nat_mul";
    /// `BlValue bl_nat_sub(BlValue, BlValue)` — O(1) truncated machine-word `Nat` subtraction.
    pub const NAT_SUB: &str = "bl_nat_sub";
    /// `BlValue bl_nat_pred(BlValue)` — O(1) truncated machine-word `Nat` predecessor (unary).
    pub const NAT_PRED: &str = "bl_nat_pred";
    /// `BlValue bl_nat_min(BlValue, BlValue)` — O(1) machine-word `Nat` minimum (numeric.c, M25b).
    pub const NAT_MIN: &str = "bl_nat_min";
    /// `BlValue bl_nat_max(BlValue, BlValue)` — O(1) machine-word `Nat` maximum (numeric.c, M25b).
    pub const NAT_MAX: &str = "bl_nat_max";
    /// `BlValue bl_nat_from_u64(uint64_t)` — allocate a fast machine-word `Nat` (used for folded
    /// numeric literals, M20 P1d).
    pub const NAT_FROM_U64: &str = "bl_nat_from_u64";
    /// `BlValue bl_nat_to_con(BlValue)` — materialize ONE inductive layer (`Zero`/`Succ`) of a fast
    /// `Nat` so a generic pattern-match reader sees the chain it expects (numeric.c, M20). A value
    /// that is already a `Zero`/`Succ` Con is returned unchanged.
    pub const NAT_TO_CON: &str = "bl_nat_to_con";
    /// `uint64_t bl_nat_is_succ(BlValue)` — the inductive *tag* (1 = Succ, 0 = Zero) of a Nat-shaped
    /// value, read WITHOUT materializing a `Succ` box (numeric.c, M25). Lets `emit_case` switch a
    /// fast-`Nat` loop driver with zero allocation per step.
    pub const NAT_IS_SUCC: &str = "bl_nat_is_succ";
    /// `BlValue bl_nat_pred_value(BlValue)` — the `Succ` arm's predecessor field of a Nat-shaped
    /// value, WITHOUT materializing a `Succ` box (numeric.c, M25): a fast Nat for a BL_NAT input.
    pub const NAT_PRED_VALUE: &str = "bl_nat_pred_value";
    /// `BlValue bl_string_to_con(BlValue)` — materialize ONE inductive layer (`empty`/`push`) of a
    /// packed `String` (BL_STRING) so a generic pattern-match reader sees the cons-list it expects
    /// (numeric.c, A2). A value that is already an `empty`/`push` Con (or any non-BL_STRING) is
    /// returned unchanged, so it composes after `bl_nat_to_con` in the generic destructuring shim.
    pub const STRING_TO_CON: &str = "bl_string_to_con";
    /// `BlValue bl_string_from_codepoints(const uint64_t *, uint64_t)` — allocate a packed `String`
    /// from a contiguous codepoint run (numeric.c, A2). Used for folded `String` literals.
    pub const STRING_FROM_CODEPOINTS: &str = "bl_string_from_codepoints";
    /// `BlValue bl_float_add(BlValue, BlValue)` — O(1) fixed-point `Float` addition over the
    /// `(mkfloat (mantissa Int))` library representation (numeric.c, M23). Returns a fresh `mkfloat`.
    pub const FLOAT_ADD: &str = "bl_float_add";
    /// `BlValue bl_float_sub(BlValue, BlValue)` — O(1) fixed-point `Float` subtraction.
    pub const FLOAT_SUB: &str = "bl_float_sub";
    /// `BlValue bl_float_mul(BlValue, BlValue)` — O(1) fixed-point `Float` multiplication
    /// (`(x*y)/SCALE`).
    pub const FLOAT_MUL: &str = "bl_float_mul";
    /// `BlValue bl_float_div(BlValue, BlValue)` — O(1) fixed-point `Float` division (`(x*SCALE)/y`).
    pub const FLOAT_DIV: &str = "bl_float_div";
    /// `BlValue bl_float_neg(BlValue)` — O(1) fixed-point `Float` negation (unary; `0 - x`).
    pub const FLOAT_NEG: &str = "bl_float_neg";
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
    /// A machine-word natural number: value in `header.aux`, no traced fields (M20). Mirrors
    /// `BlTag::BL_NAT`; observationally identical to the inductive `Zero`/`Succ` chain.
    pub const NAT: u64 = 8;
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
            "serialize.c",
            "numeric.c",
            "boxed_array.c",
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

    /// Compile the runtime C sources + a C test harness into ONE standalone executable and return
    /// its path, WITHOUT running it. Unlike [`build_and_run_harness`] (which runs the binary once
    /// and returns its captured output), this is for a harness whose `main` needs `argv`/long-lived
    /// process behavior — currently only the P5 code-mobility two-process test
    /// (`tests/mobility_pingpong.c`), which the caller spawns TWICE (once per role) via
    /// `std::process::Command` so `bl_binary_id` really is identical between two independent OS
    /// processes, not merely two invocations of `build_and_run_harness`'s one-shot design.
    fn build_process_binary(dir: &Path, test_src: &str) -> std::path::PathBuf {
        std::fs::create_dir_all(dir).unwrap();
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let mut objs = Vec::new();
        let srcs = [
            "gc.c",
            "stack.c",
            "delay.c",
            "effects.c",
            "arena.c",
            "serialize.c",
            "numeric.c",
            "boxed_array.c",
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
        bin
    }

    /// P5 (roadmap Wave 10 / code mobility): a `BL_CLOSURE` crosses a REAL loopback TCP socket
    /// between two independently-spawned OS PROCESSES of the identical compiled binary
    /// (`tests/mobility_pingpong.c`) and is applied on the far side — the process-boundary analogue
    /// of `code_mobility_round_trips_closures_and_opnodes` above (which stays in one process). `pong`
    /// is spawned first and its stdout is read for the `PORT <p>` line it prints once bound (mirrors
    /// `blight-net`'s `pingpong.rs` demo's own rendezvous protocol); `ping` is then spawned with that
    /// port. Both must exit 0 and print `PINGPONG_MOBILITY_OK`.
    #[test]
    fn code_mobility_ships_a_closure_across_a_process_boundary() {
        use std::io::{BufRead, BufReader};
        use std::process::Stdio;

        let dir = std::env::temp_dir().join(format!("blight_mobility_proc_{}", std::process::id()));
        let bin = build_process_binary(&dir, "tests/mobility_pingpong.c");

        let mut pong = Command::new(&bin)
            .arg("pong")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn pong");
        let mut pong_stdout = BufReader::new(pong.stdout.take().expect("pong stdout"));
        let mut port_line = String::new();
        pong_stdout
            .read_line(&mut port_line)
            .expect("read pong PORT line");
        let port: u16 = port_line
            .trim()
            .strip_prefix("PORT ")
            .unwrap_or_else(|| panic!("pong did not print a PORT line, got: {port_line:?}"))
            .parse()
            .expect("parse pong port");

        let ping_out = Command::new(&bin)
            .arg("ping")
            .arg(port.to_string())
            .output()
            .expect("run ping");

        // Drain the rest of pong's stdout/stderr now that ping has completed its round-trip.
        let mut pong_rest = String::new();
        use std::io::Read;
        pong_stdout.read_to_string(&mut pong_rest).ok();
        let pong_status = pong.wait().expect("wait pong");
        let mut pong_stderr = String::new();
        pong.stderr
            .take()
            .expect("pong stderr")
            .read_to_string(&mut pong_stderr)
            .ok();

        let ping_stdout = String::from_utf8_lossy(&ping_out.stdout);
        let ping_stderr = String::from_utf8_lossy(&ping_out.stderr);
        assert!(
            ping_out.status.success(),
            "ping exited non-zero\nstdout: {ping_stdout}\nstderr: {ping_stderr}"
        );
        assert!(
            ping_stdout.contains("PINGPONG_MOBILITY_OK ping 42"),
            "ping reported success\nstdout: {ping_stdout}\nstderr: {ping_stderr}"
        );
        assert!(
            pong_status.success(),
            "pong exited non-zero\nstdout: {port_line}{pong_rest}\nstderr: {pong_stderr}"
        );
        assert!(
            pong_rest.contains("PINGPONG_MOBILITY_OK pong 42"),
            "pong reported success\nstdout: {port_line}{pong_rest}\nstderr: {pong_stderr}"
        );
    }

    /// SDL2 discovery for the `graphics`-feature C test harness below — mirrors `driver.rs`'s
    /// `sdl2_flags` exactly (same env-override-then-`pkg-config` convention), duplicated here rather
    /// than shared because `runtime.rs`'s test harness and `driver.rs`'s build pipeline are
    /// independent compilation entry points with no existing shared "shell out to pkg-config" module.
    #[cfg(feature = "graphics")]
    fn sdl2_flags(which: &str, env_var: &str) -> Vec<String> {
        if let Ok(v) = std::env::var(env_var) {
            return v.split_whitespace().map(String::from).collect();
        }
        let out = Command::new("pkg-config")
            .arg(which)
            .arg("sdl2")
            .output()
            .unwrap_or_else(|e| panic!("pkg-config not available to discover SDL2: {e}"));
        assert!(
            out.status.success(),
            "`pkg-config sdl2 {which}` failed (install SDL2 dev headers or set {env_var}): {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout)
            .split_whitespace()
            .map(String::from)
            .collect()
    }

    /// Compile the runtime C sources + `graphics.c` + a C test harness into one binary linked
    /// against SDL2, and run it. Only compiled under the `graphics` cargo feature (mirrors
    /// `driver.rs`'s `build_objects`/`build_lto` graphics wiring).
    #[cfg(feature = "graphics")]
    fn build_and_run_harness_graphics(dir: &Path, test_src: &str) -> std::process::Output {
        std::fs::create_dir_all(dir).unwrap();
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let cflags = sdl2_flags("--cflags", "SDL2_CFLAGS");
        let mut objs = Vec::new();
        for src in [
            "gc.c",
            "stack.c",
            "delay.c",
            "effects.c",
            "arena.c",
            "serialize.c",
            "numeric.c",
            "boxed_array.c",
            "graphics.c",
            test_src,
        ] {
            let stem = src.replace('/', "_");
            let obj = dir.join(format!("{stem}.o"));
            let st = Command::new("clang")
                .args(["-c", "-O2", "-g", "-I"])
                .arg(&runtime)
                .args(&cflags)
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
        for f in sdl2_flags("--libs", "SDL2_LIBS") {
            link.arg(f);
        }
        assert!(link.status().expect("clang link").success(), "link harness");
        Command::new(&bin)
            .env("SDL_VIDEODRIVER", "dummy")
            .output()
            .expect("run harness")
    }

    /// Layer 3-adjacent unit gate for P2 (roadmap Wave 10 / P2, docs/design-wave4-gobars.md §5 item
    /// 4): `bl_run_graphics` drives a hand-built OpNode chain through `init-window` then two
    /// `poll-input`s, with the test's own C code injecting two synthetic SDL events (`SDL_PushEvent`,
    /// under the headless `SDL_VIDEODRIVER=dummy` set by this harness) between resumes — the
    /// "deterministic sequence of polled synthetic events in a headless/test SDL driver" the go-bar
    /// requires. See `runtime/tests/graphics_test.c` for the full trampoline-driving detail.
    #[cfg(feature = "graphics")]
    #[test]
    fn graphics_handler_observes_synthetic_input_events_in_order() {
        let dir = std::env::temp_dir().join(format!("blight_graphics_{}", std::process::id()));
        let out = build_and_run_harness_graphics(&dir, "tests/graphics_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "graphics harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("GRAPHICS_OK"),
            "graphics harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// Like [`build_and_run_harness`], but with optional AddressSanitizer instrumentation and extra
    /// process environment for the run. Used by the P4.1 mark-compact tests, which exercise the
    /// single-region compacting old generation (`BL_GC_OLDGEN=compact`) and gate its object
    /// relocation for use-after-free under ASan.
    fn build_and_run_harness_cfg(
        dir: &Path,
        test_src: &str,
        asan: bool,
        env: &[(&str, &str)],
    ) -> std::process::Output {
        std::fs::create_dir_all(dir).unwrap();
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let mut objs = Vec::new();
        let srcs = [
            "gc.c",
            "stack.c",
            "delay.c",
            "effects.c",
            "arena.c",
            "serialize.c",
            "numeric.c",
            "boxed_array.c",
            test_src,
        ];
        for src in srcs {
            let stem = src.replace('/', "_");
            let obj = dir.join(format!("{stem}.o"));
            let mut cmd = Command::new("clang");
            cmd.args(["-c", "-O1", "-g", "-I"]).arg(&runtime);
            if asan {
                cmd.arg("-fsanitize=address");
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
        let bin = dir.join("harness");
        let mut link = Command::new("clang");
        if asan {
            link.arg("-fsanitize=address");
        }
        link.arg("-o").arg(&bin);
        for o in &objs {
            link.arg(o);
        }
        assert!(link.status().expect("clang link").success(), "link harness");
        let mut run = Command::new(&bin);
        for (k, v) in env {
            run.env(k, v);
        }
        run.output().expect("run harness")
    }

    /// P4.1 mark-compact old generation: under `BL_GC_OLDGEN=compact` the old generation must run as a
    /// **single region** (peak ~1x the live set) — reserving exactly its capacity, not the legacy
    /// semi-space's 2x — while a large long-lived rooted set survives the forced major compactions
    /// with every value intact. The harness prints `COMPACT_OK` only when compaction is active and the
    /// one-region footprint invariant holds.
    #[test]
    fn oldgen_compaction_is_single_region() {
        let dir = std::env::temp_dir().join(format!("blight_gccompact_{}", std::process::id()));
        let out = build_and_run_harness_cfg(
            &dir,
            "tests/gc_test.c",
            false,
            &[("BL_GC_OLDGEN", "compact")],
        );
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "compact gc harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("COMPACT_OK") && stdout.contains("GEN_GC_OK"),
            "compact gc harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// P4.1 ASan use-after-free gate: the compacting old generation relocates the entire live set into
    /// a freshly right-sized region and frees the source region each major. Built under
    /// AddressSanitizer and run in compact mode, any missed root/field (a dangling pointer into the
    /// freed region) would be a hard ASan failure. Skipped unless ASan is available on the host.
    #[test]
    fn oldgen_compaction_no_use_after_free_under_asan() {
        let dir = std::env::temp_dir().join(format!("blight_gcasan_{}", std::process::id()));
        let out = build_and_run_harness_cfg(
            &dir,
            "tests/gc_test.c",
            true,
            &[("BL_GC_OLDGEN", "compact")],
        );
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "compact gc harness under ASan exited non-zero (likely a UAF)\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            !stderr.contains("AddressSanitizer") && !stderr.contains("ERROR: "),
            "ASan reported a memory error in the compacting collector\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("COMPACT_OK"),
            "compact gc harness under ASan reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// C2 (Blight Arc II): old-gen compaction is now **on by default** — `BL_GC_OLDGEN` left unset
    /// (exactly what every ordinary compiled program sees) must compact, not fall back to the legacy
    /// semi-space. This is the RED-then-GREEN test for the flip: run the harness with *no* env
    /// override at all and require both the general GC suite and the new
    /// `oldgen_compaction_default_on_survives_stress` stress test to report the compacting mode.
    #[test]
    fn oldgen_compaction_default_on_by_default() {
        let dir = std::env::temp_dir().join(format!("blight_gcdefault_{}", std::process::id()));
        let out = build_and_run_harness_cfg(&dir, "tests/gc_test.c", false, &[]);
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "default (BL_GC_OLDGEN unset) gc harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("GEN_GC_OK"),
            "default gc harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("DEFAULT_COMPACT_ON") && stdout.contains("COMPACT_OK"),
            "BL_GC_OLDGEN unset must default to the compacting old generation\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// The reversibility half of C2: `BL_GC_OLDGEN=semispace` must still opt back into the legacy
    /// two-space collector even though it is no longer the default.
    #[test]
    fn oldgen_semispace_explicit_opt_out_still_works() {
        let dir = std::env::temp_dir().join(format!("blight_gcsemispace_{}", std::process::id()));
        let out = build_and_run_harness_cfg(
            &dir,
            "tests/gc_test.c",
            false,
            &[("BL_GC_OLDGEN", "semispace")],
        );
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "semispace gc harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("GEN_GC_OK"),
            "semispace gc harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("DEFAULT_COMPACT_OFF") && !stdout.contains("COMPACT_OK"),
            "BL_GC_OLDGEN=semispace must opt out of the compacting old generation\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// C2's differential gate: `gc_diff.c` runs the SAME deterministic alloc-heavy workload once per
    /// `BL_GC_OLDGEN` setting (unset/default, "semispace", "compact") and prints a checksum over every
    /// surviving value. The checksum must be bit-identical across all three — the old-gen strategy may
    /// change footprint and collection counts, but never an observable result. `GC_DIFF_MAJORS` also
    /// pins that the stress genuinely forced multiple majors in every leg (a vacuous "0 majors, trivial
    /// agreement" pass would not actually exercise compaction), and `GC_DIFF_COMPACTING` cross-checks
    /// the mode each leg actually ran under against what C2 flipped the default to.
    #[test]
    fn gc_diff_identical_across_oldgen_modes() {
        let dir = std::env::temp_dir().join(format!("blight_gcdiff_{}", std::process::id()));
        let run = |env: &[(&str, &str)]| -> (bool, String, String) {
            let out = build_and_run_harness_cfg(&dir, "tests/gc_diff.c", false, env);
            (
                out.status.success(),
                String::from_utf8_lossy(&out.stdout).into_owned(),
                String::from_utf8_lossy(&out.stderr).into_owned(),
            )
        };
        let field = |stdout: &str, key: &str| -> String {
            stdout
                .lines()
                .find_map(|l| l.strip_prefix(key))
                .unwrap_or_else(|| panic!("gc_diff stdout missing {key}\nstdout: {stdout}"))
                .trim()
                .to_string()
        };

        let (ok_default, out_default, err_default) = run(&[]);
        let (ok_semispace, out_semispace, err_semispace) = run(&[("BL_GC_OLDGEN", "semispace")]);
        let (ok_compact, out_compact, err_compact) = run(&[("BL_GC_OLDGEN", "compact")]);

        assert!(
            ok_default,
            "gc_diff (default) exited non-zero\nstderr: {err_default}"
        );
        assert!(
            ok_semispace,
            "gc_diff (semispace) exited non-zero\nstderr: {err_semispace}"
        );
        assert!(
            ok_compact,
            "gc_diff (compact) exited non-zero\nstderr: {err_compact}"
        );
        for (label, out) in [
            ("default", &out_default),
            ("semispace", &out_semispace),
            ("compact", &out_compact),
        ] {
            assert!(
                out.contains("GC_DIFF_OK"),
                "gc_diff ({label}) did not report success\nstdout: {out}"
            );
        }

        let checksum_default = field(&out_default, "GC_DIFF_CHECKSUM=");
        let checksum_semispace = field(&out_semispace, "GC_DIFF_CHECKSUM=");
        let checksum_compact = field(&out_compact, "GC_DIFF_CHECKSUM=");
        assert_eq!(
            checksum_default, checksum_semispace,
            "default vs semispace: observable checksum diverged"
        );
        assert_eq!(
            checksum_default, checksum_compact,
            "default vs compact: observable checksum diverged"
        );

        for (label, out) in [
            ("default", &out_default),
            ("semispace", &out_semispace),
            ("compact", &out_compact),
        ] {
            let majors: u64 = field(out, "GC_DIFF_MAJORS=")
                .parse()
                .unwrap_or_else(|e| panic!("gc_diff ({label}) GC_DIFF_MAJORS not a number: {e}"));
            assert!(
                majors > 0,
                "gc_diff ({label}) forced no major collections; the stress is not exercising the old generation"
            );
        }

        assert_eq!(
            field(&out_default, "GC_DIFF_COMPACTING="),
            "1",
            "default (BL_GC_OLDGEN unset) must be compacting"
        );
        assert_eq!(
            field(&out_semispace, "GC_DIFF_COMPACTING="),
            "0",
            "BL_GC_OLDGEN=semispace must not be compacting"
        );
        assert_eq!(
            field(&out_compact, "GC_DIFF_COMPACTING="),
            "1",
            "BL_GC_OLDGEN=compact must be compacting"
        );
    }

    /// Wave 10 / P6 (RC + in-place reuse) go-bar's committed RED test. `tests/rc_diff.c` calls
    /// `bl_gc_reused_bytes()` — an observability accessor for an in-place-reuse mechanism that does
    /// not exist yet (see the file's header comment and `docs/design-rc-reuse.md` for the full
    /// go-bar and the finding that blocked a real attempt this pass: in-place reuse is safe WITHOUT
    /// a new non-moving GC mode only for a narrow "same-arm, same-shape, C3-proven-Linear" pattern,
    /// but a sound *codegen* rewrite for that pattern — new ANF nodes, an ANF pass consuming
    /// `linearity.rs`, and the emitter support — is itself a real, correctness-critical, near-TCB-
    /// adjacent surface (a wrong reuse is a UAF, not a wrong number) that this pass chose not to rush).
    /// `#[ignore]`d so `cargo test` stays green: this is a *documented* gap, not a silently-skipped
    /// one — `cargo test -- --ignored` (or trying to build `rc_diff.c` directly) fails loudly with a
    /// clang compile error pointing at the missing accessor, which is the point.
    #[test]
    #[ignore = "P6 in-place reuse is a documented deferral (docs/design-rc-reuse.md); bl_gc_reused_bytes() \
                does not exist yet — this pins the target observational-identity + ASan-no-UAF property \
                for whoever implements it"]
    fn in_place_reuse_is_observationally_identical() {
        let dir = std::env::temp_dir().join(format!("blight_rcdiff_{}", std::process::id()));
        let out = build_and_run_harness_cfg(&dir, "tests/rc_diff.c", true, &[]);
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "rc_diff harness exited non-zero (expected once P6 lands)\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("RC_DIFF_OK"),
            "stdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// Like [`build_and_run_harness`], but also links `prelude_rt.c` compiled with `-DBL_NO_MAIN`
    /// so the harness can call its printers/constructors (`bl_print_string`, `bl_con`, …) while
    /// supplying its own `main`.
    fn build_and_run_harness_with_prelude(dir: &Path, test_src: &str) -> std::process::Output {
        std::fs::create_dir_all(dir).unwrap();
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let mut objs = Vec::new();
        // (source, extra defines)
        let srcs: [(&str, &[&str]); 8] = [
            ("gc.c", &[]),
            ("stack.c", &[]),
            ("delay.c", &[]),
            ("effects.c", &[]),
            ("arena.c", &[]),
            ("numeric.c", &[]),
            ("boxed_array.c", &[]),
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

    /// P1 (roadmap Wave 10 / A3b go-bar items 3-4): `gc_test.c`'s boxed-array tests
    /// (`test_boxed_array_survives_minor_and_major_gc_structurally`,
    /// `test_boxed_array_write_barrier_old_to_young`) run as part of the same `main()` the plain
    /// `generational_minor_major_and_write_barrier` test above already exercises (asserted there via
    /// `GEN_GC_OK`, which only prints once every test in the binary passed). This is the go-bar's
    /// explicit ASan-clean requirement: the same binary built with AddressSanitizer must report the
    /// dedicated `BOXED_ARRAY_OK` sentinel with a clean stderr (no UAF/leak in the rooted-handle-table
    /// root-scanning or write-barrier paths this go-bar added).
    #[test]
    fn boxed_array_survives_gc_and_write_barrier_under_asan() {
        let dir =
            std::env::temp_dir().join(format!("blight_boxedarray_asan_{}", std::process::id()));
        let out = build_and_run_harness_cfg(&dir, "tests/gc_test.c", true, &[]);
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "boxed-array gc harness under ASan exited non-zero (likely a UAF)\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            !stderr.contains("AddressSanitizer") && !stderr.contains("ERROR: "),
            "ASan reported a memory error in the boxed-array root-scan/write-barrier path\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("BOXED_ARRAY_OK"),
            "boxed-array gc harness under ASan reported success\nstdout: {stdout}\nstderr: {stderr}"
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

    /// M18 (structural serializer): serialize.c flattens an immutable value to a heap-independent
    /// blob and rebuilds it in the current heap. The harness checks round-trip structural equality
    /// over representative data shapes (Int, nested Con/Tuple, a deep cons-list), that the rebuilt
    /// value is a DISJOINT deep copy (share-nothing), and that data-only is enforced (a closure, or a
    /// value containing one, is rejected). This is the boundary primitive the worker pool (M17) and
    /// distributed transport (M19) use.
    #[test]
    fn structural_serializer_round_trips_and_is_data_only() {
        let dir = std::env::temp_dir().join(format!("blight_ser_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/serialize_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "serialize harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("SERIALIZE_OK"),
            "serialize harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// P5 (code mobility, roadmap Wave 10): the `bl_value_serialize_mobile`/`bl_value_deserialize_
    /// mobile` extension additionally handles BL_CLOSURE (resolved via a hand-registered
    /// `bl_code_table_register` table, standing in for a real binary's codegen-emitted one) and
    /// BL_OPNODE (resolved by (effect,op) NAME, not raw index), and rejects a mismatched binary id or
    /// an out-of-range code_id before ever touching a pointer. See `runtime/tests/mobility_test.c`.
    #[test]
    fn code_mobility_round_trips_closures_and_opnodes() {
        let dir = std::env::temp_dir().join(format!("blight_mobility_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/mobility_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "mobility harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("MOBILITY_OK"),
            "mobility harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// M18 perf proof (throughput): the structural (de)serializer is the boundary primitive the
    /// worker pool (M17) and distributed transport (M19) ride on — every cross-heap/cross-machine
    /// message is one serialize + one deserialize. This harness round-trips a representative deep
    /// message (a long cons-list) many times and reports blob size, ns/op, and MB/s. The test asserts
    /// the harness succeeds and reports a sane non-zero throughput; the `SERIALIZE_BENCH` line is
    /// surfaced by `bench/multicore.sh` for the perf docs. No threads, so it uses `build_and_run_harness`.
    #[test]
    fn serializer_throughput_reported() {
        let dir = std::env::temp_dir().join(format!("blight_serb_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/serialize_bench.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "serialize bench exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        let summary = stdout
            .lines()
            .find(|l| l.starts_with("SERIALIZE_BENCH_OK"))
            .unwrap_or_else(|| {
                panic!("serialize bench did not report success\nstdout: {stdout}\nstderr: {stderr}")
            });
        let mb_per_s = summary
            .split_whitespace()
            .find_map(|tok| tok.strip_prefix("MB_per_s="))
            .and_then(|v| v.parse::<f64>().ok())
            .unwrap_or_else(|| panic!("missing `MB_per_s=` in summary: {summary}"));
        assert!(
            mb_per_s > 0.0,
            "expected positive serializer throughput, got {mb_per_s} MB/s\nstdout: {stdout}"
        );
    }

    /// M20 (fast-`Nat` differential gate): numeric.c's machine-word `Nat` ops must be observationally
    /// identical to the inductive `Zero`/`Succ` semantics the kernel checks. The harness computes
    /// `plus`/`mult`/`sub`/`pred` over a fuzzed range BOTH as O(1) `bl_nat_*` calls on `BL_NAT` words
    /// AND on real `Succ`/`Zero` chains (the unary reference), and asserts bit-identical results; it
    /// also checks the `bl_nat_to_con` coherence shim materializes a chain that counts back exactly.
    /// A divergence fails the build — the optimization is *checked*, never *trusted*.
    #[test]
    fn fast_nat_matches_unary_semantics() {
        let dir = std::env::temp_dir().join(format!("blight_natdiff_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/numeric_diff.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "numeric diff harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("NUMERIC_DIFF_OK"),
            "numeric diff harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// A2 (packed-`String` differential gate): numeric.c's BL_STRING representation must be
    /// observationally identical to the *checked* `empty`/`push` cons-list of `Nat` codepoints
    /// (std/string.bl). The harness builds the SAME codepoint sequence both as a packed BL_STRING and
    /// as a real inductive chain, then asserts length, every codepoint, and the `bl_string_to_con`
    /// coherence shim (one materialized `empty`/`push` layer that walks back to the original
    /// sequence; identity on a real chain) all agree bit-for-bit. A divergence fails the build — the
    /// representation is *checked*, never *trusted*.
    #[test]
    fn packed_string_matches_inductive_semantics() {
        let dir = std::env::temp_dir().join(format!("blight_strdiff_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/string_diff.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "string diff harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("STRING_DIFF_OK"),
            "string diff harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// M23 (fixed-point `Float` differential gate): numeric.c's `bl_float_*` helpers must be
    /// observationally identical to the *checked* meaning of std/float.bl — exact base-10 fixed-point
    /// rational arithmetic on the scaled `Int` mantissa. The harness computes `add`/`sub`/`mul`/`div`/
    /// `neg` over a fuzzed grid BOTH as O(1) `bl_float_*` calls and via the fixed-point reference
    /// (`int64_t`/`__int128`, exactly the wrapper's `Int` arithmetic), and asserts bit-identical
    /// mantissas. A divergence fails the build — the optimization is *checked*, never *trusted*. (We
    /// deliberately avoid an IEEE-`double` helper, which could never pass this exact-rational gate.)
    #[test]
    fn fast_float_matches_fixedpoint_semantics() {
        let dir = std::env::temp_dir().join(format!("blight_floatdiff_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/float_diff.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "float diff harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("FLOAT_DIFF_OK"),
            "float diff harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// L2 (`F64` foreign hatch): numeric.c's `bl_f64_*` helpers must behave exactly like literal C
    /// `double` arithmetic (conversion, `add`/`sub`/`mul`/`div`/`neg`, ties-away-from-zero rounding,
    /// IEEE comparison including `NaN != NaN`, and division-by-zero yielding `+-Inf` rather than
    /// trapping), and the boxed representation must be a bit-for-bit `bl_int` box of the raw IEEE
    /// bit pattern for both tagged-immediate and heap-boxed payloads. Unlike
    /// `fast_float_matches_fixedpoint_semantics`, this is deliberately NOT a differential gate — `F64`
    /// is an unverified escape hatch (spec §7.6, Design B) with no independent reference to diff
    /// against; hardware `double` arithmetic IS the ground truth.
    #[test]
    fn f64_hatch_matches_hardware_double_semantics() {
        let dir = std::env::temp_dir().join(format!("blight_f64_{}", std::process::id()));
        let out = build_and_run_harness(&dir, "tests/f64_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "f64 harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("F64_OK"),
            "f64 harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// Compile the runtime C sources + a C test harness into one binary with `-pthread` (and, when
    /// `BL_TSAN` is set in the environment, ThreadSanitizer), then run it. Used by the M15
    /// share-nothing multicore test, which spawns OS threads.
    fn build_and_run_harness_threaded(dir: &Path, test_src: &str) -> std::process::Output {
        std::fs::create_dir_all(dir).unwrap();
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let tsan = std::env::var_os("BL_TSAN").is_some();
        let mut objs = Vec::new();
        for src in [
            "gc.c",
            "stack.c",
            "delay.c",
            "effects.c",
            "arena.c",
            "serialize.c",
            "worker.c",
            "numeric.c",
            "boxed_array.c",
            test_src,
        ] {
            let stem = src.replace('/', "_");
            let obj = dir.join(format!("{stem}.o"));
            let mut cmd = Command::new("clang");
            cmd.args(["-c", "-O1", "-g", "-pthread", "-I"])
                .arg(&runtime);
            if tsan {
                cmd.arg("-fsanitize=thread");
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
        let bin = dir.join("harness");
        let mut link = Command::new("clang");
        link.arg("-pthread");
        if tsan {
            link.arg("-fsanitize=thread");
        }
        link.arg("-o").arg(&bin);
        for o in &objs {
            link.arg(o);
        }
        assert!(link.status().expect("clang link").success(), "link harness");
        Command::new(&bin).output().expect("run harness")
    }

    /// M15 (share-nothing multicore): two OS-thread workers each initialize their own thread-local
    /// runtime (`bl_runtime_init`) and allocate/collect on independent heaps with no locks. The
    /// harness asserts each worker runs its own GC (thread-local collection counters), the heaps are
    /// disjoint, and each worker's live list survives its own collections intact — i.e. the
    /// `BL_THREAD_LOCAL` runtime state isolates workers with no cross-thread corruption. Run with
    /// `BL_TSAN=1` to additionally build under ThreadSanitizer.
    #[test]
    fn share_nothing_multicore_two_runtimes_isolated() {
        let dir = std::env::temp_dir().join(format!("blight_mc_{}", std::process::id()));
        let out = build_and_run_harness_threaded(&dir, "tests/multicore_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "multicore harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("MULTICORE_OK"),
            "multicore harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// M17 (share-nothing worker pool): a pool of 4 workers runs 64 independent tasks in parallel,
    /// each on its own thread-local heap (forcing its own GC under churn), with arguments/results
    /// crossing worker boundaries by structural copy of immutable values. The harness reduces the
    /// results to a deterministic sum-of-squares — proving parallel execution on isolated heaps with
    /// correct, order-independent results. Run with `BL_TSAN=1` to build under ThreadSanitizer.
    #[test]
    fn share_nothing_worker_pool_parallel_map_reduce() {
        let dir = std::env::temp_dir().join(format!("blight_wp_{}", std::process::id()));
        let out = build_and_run_harness_threaded(&dir, "tests/worker_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "worker-pool harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("WORKER_OK"),
            "worker-pool harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// P4 (roadmap Wave 10 / auto-parallelism): `bl_pool_submit_code` hands a worker a task by its P5
    /// `code_id` instead of a native `BlWorkerFn`, resolving through the SAME registered table
    /// `bl_value_*_mobile` uses. Proves both the captureless (`env = NULL`) and captured-env (env
    /// crosses the worker boundary by structural copy, like `arg`) shapes reduce correctly across a
    /// pool — the parallel-map-reduce property `share_nothing_worker_pool_parallel_map_reduce` already
    /// proves for the native API, now proven for the code-id API `code_table_source_for`-emitted call
    /// sites will actually use. Run with `BL_TSAN=1` to build under ThreadSanitizer.
    #[test]
    fn worker_pool_submits_tasks_by_p5_code_id() {
        let dir = std::env::temp_dir().join(format!("blight_wpcode_{}", std::process::id()));
        let out = build_and_run_harness_threaded(&dir, "tests/worker_code_test.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "worker code_id harness exited non-zero\nstdout: {stdout}\nstderr: {stderr}"
        );
        assert!(
            stdout.contains("WORKER_CODE_OK"),
            "worker code_id harness reported success\nstdout: {stdout}\nstderr: {stderr}"
        );
    }

    /// M17 perf proof (scaling): the share-nothing worker pool runs a fixed set of heavy independent
    /// tasks across pools of 1/2/4/8 workers and prints a `SPEEDUP` table. The HARD gate is
    /// determinism — the reduced sum-of-squares must be identical at every pool size (the C harness
    /// aborts otherwise), proving parallel execution on isolated heaps is correct and
    /// order-independent. The speedup gate is SOFT: real wall-clock speedup is only asserted on hosts
    /// reporting `>= 4` cores and not under ThreadSanitizer (tsan serializes threads and inflates
    /// timing), so the test is honest without being flaky on small/loaded/instrumented runners. The
    /// `SPEEDUP`/`WORKER_BENCH_OK` lines are surfaced by `bench/multicore.sh` for the perf docs.
    #[test]
    fn worker_pool_scales_with_cores() {
        let dir = std::env::temp_dir().join(format!("blight_wpb_{}", std::process::id()));
        let out = build_and_run_harness_threaded(&dir, "tests/worker_bench.c");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "worker-pool bench exited non-zero (determinism gate failed?)\nstdout: {stdout}\nstderr: {stderr}"
        );
        let summary = stdout
            .lines()
            .find(|l| l.starts_with("WORKER_BENCH_OK"))
            .unwrap_or_else(|| {
                panic!("worker bench did not report success\nstdout: {stdout}\nstderr: {stderr}")
            });

        // Parse `ncores=N` and `best_speedup=F` from the summary line.
        let field = |key: &str| -> f64 {
            summary
                .split_whitespace()
                .find_map(|tok| tok.strip_prefix(key))
                .and_then(|v| v.parse::<f64>().ok())
                .unwrap_or_else(|| panic!("missing `{key}` in summary: {summary}"))
        };
        let ncores = field("ncores=");
        let best_speedup = field("best_speedup=");

        // Soft speedup gate: only require real parallel speedup where it is fair to expect it.
        let tsan = std::env::var_os("BL_TSAN").is_some();
        if ncores >= 4.0 && !tsan {
            assert!(
                best_speedup > 1.0,
                "expected the worker pool to be faster than 1 worker on a >=4-core host \
                 (best_speedup={best_speedup}, ncores={ncores})\nstdout: {stdout}"
            );
        }
    }
}
