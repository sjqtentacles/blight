//! The backend driver (spec §7): orchestrates erase → lower → closure-conv → mono → ANF → LLVM
//! object emission, compiles the C runtime, and links a native binary via `clang`. Gated behind
//! the `llvm` feature.

use crate::{
    anf, autopar, capspec, closure, cse, ctnorm, defunc, elimloop, flatten, fusion, inline, layout,
    linearity, lower, mono, recognize, region, unbox,
};
use blight_kernel::{Signature, Term};
use std::path::Path;
use std::process::Command;

/// Compile a checked global `term : ty` (with the program `sig`) to a native executable at
/// `out_bin`. `work` is a scratch directory for intermediates.
pub fn build_binary(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_bin: &Path,
    work: &Path,
) -> Result<(), String> {
    build_binary_opt(
        term,
        ty,
        sig,
        out_bin,
        work,
        crate::llvm::OptLevel::default(),
    )
}

/// Like [`build_binary`] but with an explicit IR optimization level (the `--opt` flag).
pub fn build_binary_opt(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_bin: &Path,
    work: &Path,
    opt: crate::llvm::OptLevel,
) -> Result<(), String> {
    std::fs::create_dir_all(work).map_err(|e| e.to_string())?;

    // The backend pipeline (lower → recognize → unbox → region → closure → mono → ANF → LLVM) is a
    // set of structurally-recursive tree passes whose recursion depth tracks the *nesting depth* of
    // the fully-inlined program term. A self-hosting source (e.g. the C3 `std/lexer.bl` scanner, which
    // inlines `string->bytes`/`max-paren-depth`/`paren-step` and the `std` arithmetic they call) can
    // nest deep enough to overflow the default 8 MiB main-thread stack. Run the whole pipeline on a
    // dedicated thread with a generous stack — exactly what the differential test harness already does
    // (`compile_source_to_anf`) — so a deep but finite term compiles instead of aborting. `scope`
    // borrows `term`/`ty`/`sig` without `'static`, and propagates the inner `Result`/panic.
    let run = || -> Result<(), String> { build_binary_pipeline(term, ty, sig, out_bin, work, opt) };
    let res = std::thread::scope(|s| {
        std::thread::Builder::new()
            .name("blight-backend".into())
            .stack_size(512 * 1024 * 1024)
            .spawn_scoped(s, run)
            .map_err(|e| format!("spawn backend thread: {e}"))?
            .join()
            .map_err(|_| "backend pipeline panicked".to_string())?
    });
    res
}

/// The backend pipeline body (lower → … → link). Always invoked on a large-stack thread by
/// [`build_binary_opt`]; factored out only so the stack-size wrapper stays a thin shell.
fn build_binary_pipeline(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_bin: &Path,
    work: &Path,
    opt: crate::llvm::OptLevel,
) -> Result<(), String> {
    // P6.2 compile-time normalization: fold closed, effect-free sub-`Term`s to their normal form by
    // calling the kernel's *own* trusted evaluator (zero TCB growth — we reuse the existing reducer,
    // we do not author a second one), subject to a size-non-increasing cost cap (the unary-`Nat`
    // blowup guard). Runs on the elaborated `Term` *before* `lower`, where `normalize` applies
    // directly. Gated by `BL_NO_CTNORM` and wired into the B1 differential A/B matrix (DIFF_FLAGS).
    let ct_owned;
    let term: &Term = if std::env::var_os("BL_NO_CTNORM").is_some() {
        term
    } else {
        ct_owned = ctnorm::ctnorm(term, sig);
        &ct_owned
    };
    // The pure-Rust pipeline. Region escape analysis runs on the lowered `Cir` (after `lower`,
    // before `closure`): it reads the `Cir::Region` scopes and retags non-escaping allocations
    // `Arena`, which then ride through closure conversion / mono / ANF unchanged.
    let cir = lower::lower(term, ty, sig);
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[lower] {cir:#?}");
    }
    // P7 deforestation/fusion: shortcut the single-consumer build-then-fold pipeline
    // `foldr f z (map g xs)` to `foldr (λx acc. f (g x) acc) z xs`, deleting the intermediate mapped
    // list (every `cons` cell `map` would build, and the GC traffic to reclaim it). Runs FIRST on the
    // pristine lowered `Cir` (before recognize/elimloop could rewrite the `foldr`/`map` `Fix(Lam(Case))`
    // cores the fingerprint reads), so the fused `foldr` then still rides recognize/elimloop normally.
    // Pure backend representation optimization — the kernel/re-checker only see the un-fused
    // definitions — gated by `BL_NO_FUSION` for the differential A/B bit-identical safety net.
    let cir = if std::env::var_os("BL_NO_FUSION").is_some() {
        cir
    } else {
        fusion::fuse(&cir)
    };
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[fusion] {cir:#?}");
    }
    // Recognize prelude `Nat` arithmetic (`plus`/`mult`/`sub`/`pred`) and rewrite to O(1) machine-
    // word `NatPrim` ops (recognize.rs, M20). Pure backend representation optimization: the kernel
    // and re-checker still only see the inductive definition, and a differential fuzz test gates
    // correctness. Disabled by `BL_NO_NATPRIM` for differential A/B testing and as an escape hatch.
    let cir = if std::env::var_os("BL_NO_NATPRIM").is_some() {
        cir
    } else {
        recognize::recognize(&cir)
    };
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[recognize] {cir:#?}");
    }
    // P3 elim-loop (3a/3b): rewrite a structural eliminator whose induction hypothesis would
    // otherwise recurse on the C stack into a bounded-stack loop — a tail-accumulator catamorphism
    // becomes a self-`Jump` accumulator loop (3a, [`crate::lower::build_elim_loop`]); a non-tail / tree
    // fold becomes a heap-worklist loop (3b, [`crate::elimworklist`]). Runs strictly *after* recognize
    // (so the prelude `plus`/`mult` eliminators are already O(1) `NatPrim`, leaving only genuine
    // catamorphisms) and before unbox/region/closure (so the de Bruijn `Fix(Lam(Case))` shape the
    // recovery reads is intact). Pure backend rewrite — the kernel/re-checker only see the inductive
    // `Elim` — bit-identical and gated by `BL_NO_ELIMLOOP` for the differential A/B safety net.
    let cir = if std::env::var_os("BL_NO_ELIMLOOP").is_some() {
        cir
    } else {
        elimloop::elim_loop(&cir, true)
    };
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[elimloop] {cir:#?}");
    }
    // Wave 10 / P4 auto-parallelism: ANALYSIS-ONLY divide-and-conquer recognizer (crate::autopar).
    // Runs strictly after elimloop (so a linear/single-recursive-field site has already been
    // looped away by 3a/3b, leaving only genuine tree-shaped folds like `tree-sum` for this scan)
    // and before unbox/region/closure (so the de Bruijn `Fix(Lam(Case))` shape the recovery reads is
    // intact). This NEVER rewrites `cir` — see `crate::autopar` module docs for why the actual
    // parallel-rewrite half of P4 is deferred (a sharpened negative pending a work-stealing
    // `worker.c`) — so it is trivially bit-identical whether it runs or not; `BL_NO_AUTOPAR` skips
    // the scan outright (matching `BL_NO_LINEARITY`'s precedent: an inert query, not in DIFF_FLAGS)
    // and `BL_AUTOPAR_STATS=1` prints each recognized candidate to stderr.
    let autopar_candidates =
        autopar::analyze_gated(&cir, std::env::var_os("BL_NO_AUTOPAR").is_none());
    if std::env::var_os("BL_AUTOPAR_STATS").is_some() {
        for c in &autopar_candidates {
            eprintln!(
                "BL_AUTOPAR_STATS ctor={} fanout={} pure={}",
                c.ctor.0, c.fanout, c.pure
            );
        }
    }
    // M27: scalar-replacement-of-aggregates — delete small product allocations (`Pair`/records)
    // that are built only to be immediately projected/matched in place, feeding the field values
    // straight to the consumer (product β). Pure backend representation optimization (the kernel and
    // re-checker still only see the `Tuple`/`Con` + `Proj`/`Case`), bit-identical and gated by the
    // `BL_NO_UNBOX` A/B switch. Runs after recognize so a product exposed by a `NatPrim` rewrite is
    // also folded, and before region/closure so the de Bruijn `Case`/`Proj` structure is intact.
    let cir = if std::env::var_os("BL_NO_UNBOX").is_some() {
        cir
    } else {
        unbox::unbox(&cir)
    };
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[unbox] {cir:#?}");
    }
    // A1: flatten escaping products (inline a pure, never-matched child product's slots into its
    // parent → one wider all-pointer object, fewer indirections). Runs after unbox (so deletable
    // products are already gone) and before region/closure (so the de Bruijn `Con`/`Proj`/`Case`
    // structure the analysis reads is intact). Pure backend representation optimization — the kernel
    // and re-checker only ever see the inductive `Con`/`Tuple` + `Proj` — gated by `BL_NO_FLATTEN`
    // for the differential A/B bit-identical safety net (this is exactly the hazard that caught the
    // reverted M27 elim-inline, so it is differential-test-first).
    let cir = if std::env::var_os("BL_NO_FLATTEN").is_some() {
        cir
    } else {
        flatten::flatten(&cir)
    };
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[flatten] {cir:#?}");
    }
    // P6.1 CSE: share a repeated *pure* computation in a straight-line, eagerly-evaluated region
    // (`(f x) + (f x)` → `let t = f x in t + t`) so the work and any allocation it performs happen
    // once. Runs after unbox/flatten (so it sees the final lowered product/projection shape) and
    // before region/closure (de Bruijn `Cir` intact, all-`Gc` allocations). Pure backend rewrite —
    // the kernel/re-checker only see the un-shared term — gated by `BL_NO_CSE` for the differential
    // A/B bit-identical safety net.
    let cir = if std::env::var_os("BL_NO_CSE").is_some() {
        cir
    } else {
        cse::cse(&cir)
    };
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[cse] {cir:#?}");
    }
    let cir = region::analyze_gated(&cir);
    let prog = closure::convert(&cir);
    let prog = mono::monomorphize(&prog);
    // A4 cross-function inliner: splice small, non-recursive, captureless, effect-free top-level
    // functions into their call sites as β-as-`let` (call-by-value preserving), removing the per-call
    // closure alloc + indirect call. Runs after mono so it sees the final specialized function set,
    // and before ANF (it works on the closure-converted `Cir`). Pure backend representation
    // optimization — the kernel/re-checker never see this IR — gated by `BL_NO_INLINE` and wired into
    // the B1 differential A/B matrix (DIFF_FLAGS) for the bit-identity safety net.
    let prog = if std::env::var_os("BL_NO_INLINE").is_some() {
        prog
    } else {
        inline::inline(&prog)
    };
    // A1′ whole-program post-monomorphization layout pass: re-apply the proven `unbox` (SRA, deletes
    // the `Proj`-of-`Con` chains that mono + inlining expose but the pre-mono `unbox` never saw) and
    // `flatten` (escaping-product widening) across *every* post-mono/post-inline function body. Each
    // sub-pass is internally gated by its own `BL_NO_UNBOX` / `BL_NO_FLATTEN` switch (both already in
    // DIFF_FLAGS) so the B1 bit-identity harness covers it; it reuses the identical, differentially
    // gated transforms (zero new trust) and the precise GC needs no change. `BL_LAYOUT_STATS=1`
    // reports per-pass firings.
    let prog = layout::layout(&prog);
    // A3 spine fusion: fold each captureless partial-application closure (`MkClosure(f, []) + Call`)
    // a curried structural/effectful loop emits per step into a direct `CallGlobal` (null env, no
    // allocation). Pure backend representation optimization — the kernel/re-checker never see ANF —
    // bit-identical and gated by `BL_NO_SPINEFUSE` for the differential A/B safety net.
    let fuse_spine = std::env::var_os("BL_NO_SPINEFUSE").is_none();
    // P2 self-recursion arity-raise: collapse an identity-env self-rebuild tail call into a `Jump`
    // that reuses the current env (no per-step closure alloc). Bit-identical, gated by
    // `BL_NO_ARITYRAISE` for the differential A/B safety net.
    let raise_arity = std::env::var_os("BL_NO_ARITYRAISE").is_none();
    let mut anf = anf::normalize_opts_raise(&prog, fuse_spine, raise_arity);
    anf.con_tags = anf::con_tags_from_sig(sig);
    // P10 follow-on: capture-aware specialization (ANF→ANF). Runs *before* `defunc`: it clones a
    // singleton-closure-flow apply's target `L` into a captureless specialization when every one of
    // `L`'s captures is provably a single constant literal (the same whole-program 0-CFA `defunc`
    // uses, extended with closure-site + constant-literal tracking — see `crate::cfa`), substituting
    // each `EnvRef` with a `let`-bound literal and rewriting the apply to a null-env `CallGlobal`/
    // `TailCallGlobal` of the clone. This eliminates the per-call capture env-load `defunc` alone
    // leaves behind. `defunc`'s own output (`CallKnown`/`TailCallKnown`) is opaque to this CFA, so it
    // must run first; `defunc` then devirtualizes whatever indirect applies remain. Pure backend
    // representation optimization — the kernel/re-checker never see ANF — value-preserving and gated
    // by `BL_NO_CAPSPEC` for the differential A/B safety net (DIFF_FLAGS).
    let anf = if std::env::var_os("BL_NO_CAPSPEC").is_some() {
        anf
    } else {
        capspec::capspec(&anf)
    };
    // P10 defunctionalization (ANF→ANF): devirtualize each higher-order closure apply (`Comp::Call`/
    // `Tail::TailCall`) whose head provably flows from a single lifted function `L` into a direct
    // `CallKnown(L, env, arg)` — statically binding `L` (LTO-inlinable) and dropping the closure-header
    // function-pointer load; the closure object is passed unchanged as the env, so captures are
    // preserved. A whole-program 0-CFA proves the singleton-flow; any open/escaping head keeps the
    // indirect path. Pure backend representation optimization — the kernel/re-checker never see ANF —
    // value-preserving and gated by `BL_NO_DEFUNC` for the differential A/B safety net (DIFF_FLAGS).
    let anf = if std::env::var_os("BL_NO_DEFUNC").is_some() {
        anf
    } else {
        defunc::defunc(&anf)
    };
    // C3 transient-consumption (linearity) analysis substrate: classify every `let`-bound
    // allocation site's uses against the QTT-grade-inspired Linear/Shared/Dead lattice (see
    // `crate::linearity`). This is a **pure self-check + diagnostic** run over the final ANF —
    // it is the identity transform on the program (nothing is freed early yet; no consumer pass
    // exists), so it is bit-identical whether it runs or not. `BL_LINEARITY_STATS=1` reports the
    // per-function counts; `BL_NO_LINEARITY` skips the query entirely.
    let anf = linearity::analyze_gated(anf);
    if std::env::var_os("BL_DUMP_ANF").is_some() {
        eprintln!("[anf] {anf:#?}");
    }

    // Cross-object LTO (Phase 3): by default we ship the Blight program and the C runtime as LLVM
    // *bitcode* and let `clang -flto` optimize across the boundary, so the runtime's hot helpers
    // (`bl_alloc`/`bl_app`/`bl_force`/`bl_nat_*`) inline into compiled Blight code — the win that the
    // separate-object build provably can't get (the optimizer never crosses into the runtime). The
    // historical object path is kept verbatim as a fallback under `BL_NO_LTO` (and is used
    // automatically if the LTO link fails), so nothing regresses if a toolchain lacks LTO support.
    // The `graphics` cargo feature is required to build a `main : (! Graphics A)` program (it gates
    // linking `runtime/graphics.c` + SDL2, docs/design-wave4-gobars.md §5). Fail early with a clear
    // message rather than a confusing "undefined symbol: bl_run_graphics" at the final link step.
    if !cfg!(feature = "graphics")
        && matches!(ty, Term::EffTy(row, _) if row.contains(&blight_kernel::EffName::new("Graphics")))
    {
        return Err(
            "main : (! Graphics A) requires the `graphics` cargo feature (SDL2); rebuild blight \
             with `--features llvm,graphics`"
                .to_string(),
        );
    }

    let runtime_dir = runtime_src_dir();
    let use_lto = std::env::var_os("BL_NO_LTO").is_none();
    if use_lto {
        match build_lto(&anf, &runtime_dir, work, ty, out_bin, opt) {
            Ok(()) => return Ok(()),
            Err(e) => {
                // A toolchain without working `-flto` (or an LTO-link failure) must not break the
                // build: fall back to the object path. Surface the reason for diagnosis.
                eprintln!("[lto] cross-object LTO link unavailable ({e}); using object path");
            }
        }
    }
    build_objects(&anf, &runtime_dir, work, ty, out_bin, opt)
}

/// SDL2 discovery for the `graphics` cargo feature (docs/design-wave4-gobars.md §5). Prefers explicit
/// `SDL2_CFLAGS`/`SDL2_LIBS` env overrides (a nonstandard install, or a cross-compile sysroot), else
/// shells out to `pkg-config sdl2` — the standard discovery mechanism for both a Homebrew `sdl2` and
/// a Linux distro's `libsdl2-dev`. `which` is `--cflags` or `--libs`; `env_var` is the matching
/// override name. Panics with an actionable message on failure (this only runs when a program
/// actually needs linking, and only when the `graphics` feature was explicitly opted into).
#[cfg(feature = "graphics")]
fn sdl2_flags(which: &str, env_var: &str) -> Vec<String> {
    if let Ok(v) = std::env::var(env_var) {
        return v.split_whitespace().map(String::from).collect();
    }
    let out = Command::new("pkg-config")
        .arg(which)
        .arg("sdl2")
        .output()
        .unwrap_or_else(|e| {
            panic!(
                "pkg-config not available to discover SDL2 ({env_var} unset, `graphics` feature \
             requires SDL2 dev headers): {e}"
            )
        });
    if !out.status.success() {
        panic!(
            "`pkg-config sdl2 {which}` failed (install SDL2 dev headers — `libsdl2-dev` on \
             Debian/Ubuntu, `brew install sdl2` on macOS — or set {env_var} explicitly): {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .map(String::from)
        .collect()
}

/// The historical separate-object build: emit `program.o`, compile each runtime `.c` to a native
/// object, author the result-type-aware `main`, and link with plain `clang` (no `-flto`). This is
/// the fallback when LTO is disabled (`BL_NO_LTO`) or unavailable.
fn build_objects(
    anf: &crate::AnfProgram,
    runtime_dir: &Path,
    work: &Path,
    ty: &Term,
    out_bin: &Path,
    opt: crate::llvm::OptLevel,
) -> Result<(), String> {
    // Emit the program object.
    let prog_obj = work.join("program.o");
    crate::llvm::emit_object_for_target(anf, &prog_obj, crate::llvm::Target::Native, opt)?;

    // Compile the C runtime objects. We author our own `main` (below) so that printing can be
    // result-type-aware (text for a `String`, numeral otherwise), so `prelude_rt.c` is compiled
    // with `-DBL_NO_MAIN` to suppress its built-in numeric `main` while keeping its printers and
    // constructors. This stays entirely in tower code — no kernel/IR change.
    let mut runtime_objs = Vec::new();
    for src in [
        "gc.c",
        "arena.c",
        "stack.c",
        "delay.c",
        "effects.c",
        "numeric.c",
        "boxed_array.c",
        // P5 (roadmap Wave 10 / code mobility): every real binary links the mobile (de)serializer +
        // its function-index-table registration hook, not just a mobility-using program — the same
        // way `effects.c`'s intern table is always linked whether or not a program performs any
        // effect. Cheap (no external deps) and otherwise inert (an unregistered/unused table costs
        // nothing beyond a few static bytes and one constructor call at startup).
        "serialize.c",
    ] {
        let obj = work.join(format!("{src}.o"));
        compile_c(&runtime_dir.join(src), &obj, runtime_dir)?;
        runtime_objs.push(obj);
    }
    {
        let obj = work.join("prelude_rt.c.o");
        compile_c_with_defs(
            &runtime_dir.join("prelude_rt.c"),
            &obj,
            runtime_dir,
            &["-DBL_NO_MAIN"],
        )?;
        runtime_objs.push(obj);
    }
    #[cfg(feature = "graphics")]
    {
        let cflags = sdl2_flags("--cflags", "SDL2_CFLAGS");
        let cflag_refs: Vec<&str> = cflags.iter().map(String::as_str).collect();
        let obj = work.join("graphics.c.o");
        compile_c_with_defs(
            &runtime_dir.join("graphics.c"),
            &obj,
            runtime_dir,
            &cflag_refs,
        )?;
        runtime_objs.push(obj);
    }

    // P5 (roadmap Wave 10 / code mobility): the codegen-emitted function-index table, as its own
    // small translation unit (see `code_table_source_for`'s doc comment for why not LLVM IR).
    {
        let code_table_c = code_table_source_for(anf);
        let code_table_path = work.join("code_table.c");
        std::fs::write(&code_table_path, &code_table_c).map_err(|e| e.to_string())?;
        let code_table_obj = work.join("code_table.c.o");
        compile_c(&code_table_path, &code_table_obj, runtime_dir)?;
        runtime_objs.push(code_table_obj);
    }

    // Author a tiny `main.c` that selects the printer by the program's result type. A `String`
    // (std/string.bl) prints as text via `bl_print_string`; everything else uses the historical
    // numeric/constructor `bl_print`.
    let main_c = main_source_for(ty);
    let main_path = work.join("main.c");
    std::fs::write(&main_path, &main_c).map_err(|e| e.to_string())?;
    let main_obj = work.join("main.c.o");
    compile_c(&main_path, &main_obj, runtime_dir)?;
    runtime_objs.push(main_obj);

    // Link everything into the binary via clang.
    let mut cmd = Command::new("clang");
    cmd.arg("-o").arg(out_bin).arg(&prog_obj);
    for o in &runtime_objs {
        cmd.arg(o);
    }
    #[cfg(feature = "graphics")]
    for f in sdl2_flags("--libs", "SDL2_LIBS") {
        cmd.arg(f);
    }
    let status = cmd
        .status()
        .map_err(|e| format!("clang link failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("clang link failed with status {status}"));
    }
    Ok(())
}

/// The Phase 3 cross-object LTO build: emit the Blight program as bitcode, compile every runtime
/// translation unit (plus the result-type-aware `main`) to bitcode, and link the whole set with
/// `clang -flto`, so LLVM inlines runtime helpers into hot Blight code across the former
/// object-file boundary. Produces a byte-for-byte equivalent result to [`build_objects`] (LTO only
/// changes speed, never observable behavior); the caller falls back to the object path on any error.
fn build_lto(
    anf: &crate::AnfProgram,
    runtime_dir: &Path,
    work: &Path,
    ty: &Term,
    out_bin: &Path,
    opt: crate::llvm::OptLevel,
) -> Result<(), String> {
    // The Blight program as bitcode.
    let prog_bc = work.join("program.bc");
    crate::llvm::emit_bitcode_for_target(anf, &prog_bc, crate::llvm::Target::Native, opt)?;

    // Runtime translation units as bitcode (prelude_rt with -DBL_NO_MAIN, like the object path).
    let mut bcs = vec![prog_bc];
    for src in [
        "gc.c",
        "arena.c",
        "stack.c",
        "delay.c",
        "effects.c",
        "numeric.c",
        "boxed_array.c",
        // P5 (roadmap Wave 10 / code mobility): see `build_objects`'s matching comment.
        "serialize.c",
    ] {
        let bc = work.join(format!("{src}.bc"));
        compile_c_to_bitcode(&runtime_dir.join(src), &bc, runtime_dir, &[])?;
        bcs.push(bc);
    }
    {
        let bc = work.join("prelude_rt.c.bc");
        compile_c_to_bitcode(
            &runtime_dir.join("prelude_rt.c"),
            &bc,
            runtime_dir,
            &["-DBL_NO_MAIN"],
        )?;
        bcs.push(bc);
    }
    #[cfg(feature = "graphics")]
    {
        let cflags = sdl2_flags("--cflags", "SDL2_CFLAGS");
        let cflag_refs: Vec<&str> = cflags.iter().map(String::as_str).collect();
        let bc = work.join("graphics.c.bc");
        compile_c_to_bitcode(
            &runtime_dir.join("graphics.c"),
            &bc,
            runtime_dir,
            &cflag_refs,
        )?;
        bcs.push(bc);
    }

    // P5 (roadmap Wave 10 / code mobility): the codegen-emitted function-index table, as bitcode.
    {
        let code_table_c = code_table_source_for(anf);
        let code_table_path = work.join("code_table.c");
        std::fs::write(&code_table_path, &code_table_c).map_err(|e| e.to_string())?;
        let code_table_bc = work.join("code_table.c.bc");
        compile_c_to_bitcode(&code_table_path, &code_table_bc, runtime_dir, &[])?;
        bcs.push(code_table_bc);
    }

    // The result-type-aware `main`, as bitcode too.
    let main_c = main_source_for(ty);
    let main_path = work.join("main.c");
    std::fs::write(&main_path, &main_c).map_err(|e| e.to_string())?;
    let main_bc = work.join("main.c.bc");
    compile_c_to_bitcode(&main_path, &main_bc, runtime_dir, &[])?;
    bcs.push(main_bc);

    // Link with `-flto` so the optimizer runs across all modules. `-O2` drives the LTO inliner.
    // `-Wno-override-module` silences the benign triple-mismatch note when the runtime `.bc` (built
    // by `clang`, already carrying the host triple) is merged with the program `.bc`.
    let mut cmd = Command::new("clang");
    cmd.arg("-flto")
        .arg("-O2")
        .arg("-Wno-override-module")
        .arg("-o")
        .arg(out_bin);
    for bc in &bcs {
        cmd.arg(bc);
    }
    #[cfg(feature = "graphics")]
    for f in sdl2_flags("--libs", "SDL2_LIBS") {
        cmd.arg(f);
    }
    let status = cmd
        .status()
        .map_err(|e| format!("clang -flto link failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("clang -flto link failed with status {status}"));
    }
    Ok(())
}

/// Is `ty` the `String` data type (std/string.bl)? Used to pick the text printer for `main`.
fn term_is_string(ty: &Term) -> bool {
    matches!(ty, Term::Data(name, _, _) if name.0 == "String")
}

/// If `ty` is an effect type `(! E A)` whose row carries a *native top-level* effect (`Console`, the
/// C1 `FileIO`, the C2 `Bytes`, the A3a `Arrays`, the A3b (Wave 10 / P1) boxed `Array`, the Wave 2
/// `Clock`, or the Wave 10 / P2 `Graphics`), return its inner result type `A`. Such a `main` is run
/// through a native top-level handler (`bl_run_console` or, for `Graphics`, `bl_run_graphics`;
/// see [`native_handler_fn`]) instead of being treated as a pure value.
fn console_inner(ty: &Term) -> Option<&Term> {
    match ty {
        Term::EffTy(row, inner)
            if row.contains(&blight_kernel::EffName::new("Console"))
                || row.contains(&blight_kernel::EffName::new("FileIO"))
                || row.contains(&blight_kernel::EffName::new("Bytes"))
                || row.contains(&blight_kernel::EffName::new("Arrays"))
                || row.contains(&blight_kernel::EffName::new("Array"))
                || row.contains(&blight_kernel::EffName::new("Clock"))
                || row.contains(&blight_kernel::EffName::new("Graphics")) =>
        {
            Some(inner)
        }
        _ => None,
    }
}

/// Which native top-level handler function folds `ty`'s row, given [`console_inner`] already
/// returned `Some` for it: `bl_run_graphics` (P2, `runtime/graphics.c`, `graphics` cargo feature)
/// for the `Graphics` effect specifically, `bl_run_console` (`runtime/effects.c`) for every other
/// native effect (`Console`/`FileIO`/`Bytes`/`Arrays`/`Array`/`Clock` all share that one handler).
fn native_handler_fn(ty: &Term) -> &'static str {
    match ty {
        Term::EffTy(row, _) if row.contains(&blight_kernel::EffName::new("Graphics")) => {
            "bl_run_graphics"
        }
        _ => "bl_run_console",
    }
}

/// The C `main` source for a program whose result type is `ty`: a `String` result prints as text
/// (`bl_print_string`), otherwise the numeric/constructor printer (`bl_print`, via prelude_rt.c's
/// historical path replicated here). Both initialize the same 64 MiB heap + stack as the original
/// baked-in `main`, so non-String programs are byte-for-byte unchanged.
fn main_source_for(ty: &Term) -> String {
    // Opt-in GC churn signal for the bench harness: when BL_GC_STATS is set, write the collection
    // count to stderr (never stdout) just before exit. Off by default, so output is unchanged.
    let gc_stats = r#"  if (getenv("BL_GC_STATS")) { fprintf(stderr, "BL_GC_STATS collections=%zu minor=%zu major=%zu grows=%zu promoted_bytes=%zu bytes_allocated=%zu compacting=%d shrinks=%zu old_capacity=%zu old_live=%zu peak_old_reserved=%zu\n", bl_gc_collections(), bl_gc_minor(), bl_gc_major(), bl_gc_grows(), bl_gc_promoted_bytes(), bl_gc_bytes_allocated(), bl_gc_oldgen_compacting(), bl_gc_old_shrinks(), bl_gc_old_capacity(), bl_gc_old_live_bytes(), bl_gc_peak_old_reserved_bytes()); }
"#;
    // `main : (! Console A)`: run the bubbling Console computation through the native top-level
    // handler, which performs the real I/O, then print the pure result `A` (Unit/String/numeral).
    if let Some(inner) = console_inner(ty) {
        let printer = result_printer_for(inner);
        let handler_fn = native_handler_fn(ty);
        return format!(
            r#"#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init(64 * 1024 * 1024); /* 64 MiB initial heap (the collector grows it on demand) */
  bl_stack_init();
  BlValue result = {handler_fn}(bl_program_entry());
  {printer}
{gc_stats}  return 0;
}}
"#
        );
    }
    let printer = result_printer_for(ty);
    format!(
        r#"#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init(64 * 1024 * 1024); /* 64 MiB initial heap (the collector grows it on demand) */
  bl_stack_init();
  BlValue result = bl_program_entry();
  {printer}
{gc_stats}  return 0;
}}
"#
    )
}

/// FNV-1a (64-bit) over the ordered list of lifted function names, joined by a NUL separator (so
/// `["ab","c"]` and `["a","bc"]` hash differently). This is `bl_binary_id` (P5, roadmap Wave 10 /
/// code mobility): a compile-time content fingerprint of "the set of functions this program can
/// resolve a `code_id` against, in this exact order" — two processes running the SAME compiled
/// binary always agree on it, while a differently-compiled binary (even one built from a trivially
/// edited source) almost certainly does not, which is exactly the coarse guard
/// `bl_value_deserialize_mobile` needs: reject a foreign blob before ever resolving a `code_id` to a
/// pointer (`docs/design-code-mobility.md`). Not a security-grade hash (FNV-1a has no collision
/// resistance guarantees) — the security property here is "almost certainly disagrees across
/// distinct binaries", not "cannot be forged", since the whole point is a same-binary sanity check,
/// not an adversarial-input authentication tag.
fn fnv1a_binary_id<'a>(names: impl Iterator<Item = &'a str>) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;
    let mut hash = OFFSET_BASIS;
    for name in names {
        for b in name.bytes() {
            hash ^= b as u64;
            hash = hash.wrapping_mul(PRIME);
        }
        // Separator byte (NUL can never appear in a C identifier) so the boundary between two
        // adjacent names is unambiguous in the hash the same way it already is in the source text.
        hash ^= 0u64;
        hash = hash.wrapping_mul(PRIME);
    }
    hash
}

/// The codegen-emitted C source for P5's code mobility function-index table (roadmap Wave 10):
/// declares every lifted top-level function `driver.rs`'s pipeline produced (`anf.funcs`, in the
/// SAME order codegen assigned — see `blight_rt.h`'s `bl_code_table_register` doc comment), packs
/// their addresses into a table, and registers it (plus the [`fnv1a_binary_id`] fingerprint) with
/// `serialize.c` via a constructor that runs before `main` — so `bl_value_serialize_mobile`/
/// `bl_value_deserialize_mobile` have a live table the instant any Blight code could possibly run,
/// with no explicit call needed from the hand-authored `main_source_for` shell. Compiled into its
/// own translation unit (not emitted as LLVM IR alongside `program.o`) purely so the C-only runtime
/// test harnesses (`runtime.rs`'s `build_and_run_harness*`), which link `serialize.c` but never
/// build an actual Blight program, are unaffected — nothing here is referenced unless this generated
/// file is itself compiled in, which only `build_objects`/`build_lto` do.
fn code_table_source_for(anf: &crate::AnfProgram) -> String {
    let binary_id = fnv1a_binary_id(anf.funcs.iter().map(|f| f.name.as_str()));
    let mut src = String::new();
    src.push_str("#include \"blight_rt.h\"\n\n");
    for f in &anf.funcs {
        src.push_str(&format!("extern BlValue {}(BlValue, BlValue);\n", f.name));
    }
    // A trailing NULL sentinel keeps the array non-empty (a portable, warning-free array
    // initializer) even for a program that lifted zero functions; `bl_code_table_len` below is an
    // explicit count, never `sizeof(...)`-derived, so the sentinel is simply never indexed.
    src.push_str("\nstatic void *const bl_code_table_data[] = {\n");
    for f in &anf.funcs {
        src.push_str(&format!("  (void *){},\n", f.name));
    }
    src.push_str("  (void *)0\n};\n\n");
    src.push_str(&format!(
        "static const uint64_t bl_code_table_len_ = {}ULL;\n",
        anf.funcs.len()
    ));
    src.push_str(&format!(
        "static const uint64_t bl_code_table_binary_id_ = {binary_id}ULL;\n\n"
    ));
    src.push_str(
        "__attribute__((constructor))\nstatic void bl_code_table_init_(void) {\n  \
         bl_code_table_register(bl_code_table_data, bl_code_table_len_, bl_code_table_binary_id_);\n}\n",
    );
    src
}

/// Pick the result printer call for a (pure) result type `ty`. A `String` prints as text; the
/// `Unit` type prints nothing (its sole value carries no information — used by Console programs
/// whose observable output already happened via `print`); everything else uses the numeric printer.
fn result_printer_for(ty: &Term) -> &'static str {
    if term_is_string(ty) {
        "bl_print_string(result);"
    } else if matches!(ty, Term::Data(name, _, _) if name.0 == "Unit") {
        "(void) result;"
    } else {
        "bl_print_default(result);"
    }
}

/// Emit only the program object (no link) — used by the grade-0-absent acceptance test to scan
/// symbols.
pub fn emit_program_object(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_obj: &Path,
) -> Result<(), String> {
    emit_program_object_for_target(term, ty, sig, out_obj, crate::llvm::Target::Native)
}

/// Emit only the program object (no link) for the requested `target`. The `wasm32` target produces
/// a WebAssembly object (`\0asm` magic) rather than a host object; it is not linked here.
pub fn emit_program_object_for_target(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_obj: &Path,
    target: crate::llvm::Target,
) -> Result<(), String> {
    let cir = lower::lower(term, ty, sig);
    let cir = region::analyze_gated(&cir);
    let prog = closure::convert(&cir);
    let prog = mono::monomorphize(&prog);
    let mut anf = anf::normalize_opts_raise(
        &prog,
        std::env::var_os("BL_NO_SPINEFUSE").is_none(),
        std::env::var_os("BL_NO_ARITYRAISE").is_none(),
    );
    anf.con_tags = anf::con_tags_from_sig(sig);
    crate::llvm::emit_object_for_target(&anf, out_obj, target, crate::llvm::OptLevel::default())
}

/// Emit textual LLVM IR for the full pipeline (used by tests to assert on tailcc/musttail).
pub fn emit_ir(term: &Term, ty: &Term, sig: &Signature) -> Result<String, String> {
    let cir = lower::lower(term, ty, sig);
    let cir = region::analyze_gated(&cir);
    let prog = closure::convert(&cir);
    let prog = mono::monomorphize(&prog);
    let mut anf = anf::normalize_opts_raise(
        &prog,
        std::env::var_os("BL_NO_SPINEFUSE").is_none(),
        std::env::var_os("BL_NO_ARITYRAISE").is_none(),
    );
    anf.con_tags = anf::con_tags_from_sig(sig);
    crate::llvm::emit_ir(&anf)
}

/// Link a runnable WebAssembly module (`out_wasm`) for a checked `term : ty`. Emits the program as
/// a wasm object, compiles the minimal freestanding wasm ABI shim (`runtime/wasm_rt.c`) to a wasm
/// object, and links both with `wasm-ld` into a `.wasm` module exporting `bl_main`.
///
/// This needs a wasm-capable toolchain: a `clang` whose backend knows `wasm32` (the LLVM-bundled
/// clang, not Apple clang) and a `wasm-ld`. Override either via `BLIGHT_WASM_CC` / `BLIGHT_WASM_LD`;
/// otherwise we look on `PATH`. When the toolchain is absent we return a clear, actionable error so
/// callers can fall back to object-only emission.
pub fn link_wasm(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_wasm: &Path,
    work: &Path,
) -> Result<(), String> {
    let wasm_cc = which_tool("BLIGHT_WASM_CC", &["clang"]).ok_or_else(|| {
        "wasm link needs a wasm-capable clang; set BLIGHT_WASM_CC or install LLVM clang \
         (Apple clang has no wasm backend)"
            .to_string()
    })?;
    let wasm_ld = which_tool("BLIGHT_WASM_LD", &["wasm-ld", "wasm-ld-18", "wasm-ld-19"])
        .ok_or_else(|| {
            "wasm link needs `wasm-ld`; set BLIGHT_WASM_LD or install lld".to_string()
        })?;

    std::fs::create_dir_all(work).map_err(|e| e.to_string())?;

    // 1. The program object, retargeted to wasm32.
    let prog_obj = work.join("program.wasm.o");
    emit_program_object_for_target(term, ty, sig, &prog_obj, crate::llvm::Target::Wasm32)?;

    // 2. The freestanding wasm ABI shim → wasm object.
    let shim_src = runtime_src_dir().join("wasm_rt.c");
    let shim_obj = work.join("wasm_rt.o");
    let status = Command::new(&wasm_cc)
        .args(["--target=wasm32-unknown-unknown", "-O2", "-nostdlib", "-c"])
        .arg("-I")
        .arg(runtime_src_dir())
        .arg(&shim_src)
        .arg("-o")
        .arg(&shim_obj)
        .status()
        .map_err(|e| format!("wasm cc failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("compiling wasm_rt.c failed: {status}"));
    }

    // 3. Link to a runnable module exporting `bl_main` (no entry, no libc).
    let status = Command::new(&wasm_ld)
        .args(["--no-entry", "--export=bl_main", "--allow-undefined"])
        .arg(&prog_obj)
        .arg(&shim_obj)
        .arg("-o")
        .arg(out_wasm)
        .status()
        .map_err(|e| format!("wasm-ld failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("wasm-ld link failed with status {status}"));
    }
    Ok(())
}

/// Resolve a tool: an explicit `$ENV` override if set, else the first of `candidates` found on
/// `PATH`. Returns the resolved program name/path to hand to `Command::new`.
fn which_tool(env_var: &str, candidates: &[&str]) -> Option<std::ffi::OsString> {
    if let Some(p) = std::env::var_os(env_var) {
        if !p.is_empty() {
            return Some(p);
        }
    }
    let path = std::env::var_os("PATH")?;
    for cand in candidates {
        for dir in std::env::split_paths(&path) {
            let full = dir.join(cand);
            if full.is_file() {
                return Some(full.into_os_string());
            }
        }
    }
    None
}

fn compile_c(src: &Path, obj: &Path, include_dir: &Path) -> Result<(), String> {
    compile_c_with_defs(src, obj, include_dir, &[])
}

/// Like [`compile_c`] but passes extra `clang` flags (e.g. `-DBL_NO_MAIN`).
fn compile_c_with_defs(
    src: &Path,
    obj: &Path,
    include_dir: &Path,
    defs: &[&str],
) -> Result<(), String> {
    let status = Command::new("clang")
        .arg("-c")
        .arg("-O2")
        .arg("-I")
        .arg(include_dir)
        .args(defs)
        .args(if std::env::var_os("BL_EFFECTS_DEBUG").is_some() {
            &["-DBL_EFFECTS_DEBUG"][..]
        } else {
            &[][..]
        })
        .arg(src)
        .arg("-o")
        .arg(obj)
        .status()
        .map_err(|e| format!("clang -c failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("compiling {} failed: {status}", src.display()));
    }
    Ok(())
}

/// Like [`compile_c_with_defs`] but emits LLVM **bitcode** (`-c -emit-llvm`) instead of a native
/// object, for the Phase 3 cross-object LTO link. Runtime translation units shipped as `.bc` let the
/// LTO linker inline `bl_alloc`/`bl_app`/`bl_force`/`bl_nat_*` into hot Blight code — the boundary
/// the plain-object build can never cross. Same `-O2`/`-DBL_*` flags as the object path so the only
/// difference is the output format.
fn compile_c_to_bitcode(
    src: &Path,
    bc: &Path,
    include_dir: &Path,
    defs: &[&str],
) -> Result<(), String> {
    let status = Command::new("clang")
        .arg("-c")
        .arg("-emit-llvm")
        .arg("-O2")
        .arg("-I")
        .arg(include_dir)
        .args(defs)
        .args(if std::env::var_os("BL_EFFECTS_DEBUG").is_some() {
            &["-DBL_EFFECTS_DEBUG"][..]
        } else {
            &[][..]
        })
        .arg(src)
        .arg("-o")
        .arg(bc)
        .status()
        .map_err(|e| format!("clang -c -emit-llvm failed to start: {e}"))?;
    if !status.success() {
        return Err(format!(
            "compiling {} to bitcode failed: {status}",
            src.display()
        ));
    }
    Ok(())
}

/// Locate the `runtime/` directory shipped with this crate.
fn runtime_src_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime")
}

/// Support for runtime/memory benchmarks and their sanity tests: build a hand-written
/// [`crate::AnfProgram`] (exposing `bl_program_entry`) into a native binary linked against a custom
/// C `main` (which can read the runtime counters `bl_gc_collections()`, `bl_arena_live_bytes()`,
/// `bl_arena_alloc_count()`), run it, and capture stdout. This deliberately mirrors the
/// `region_workload_bypasses_gc` acceptance test so the bench harness and that test share one path.
pub mod bench_support {
    use super::{compile_c, runtime_src_dir};
    use crate::{Alloc, AnfFunc, AnfProgram, Atom, Comp, Tail, TailArm};
    use blight_kernel::ConName;
    use std::path::Path;
    use std::process::Command;

    /// Resolve `(load "std/…")` against the checked-in prelude (same convention the test/bench
    /// harnesses use). `CARGO_MANIFEST_DIR` is `crates/blight-codegen`, so the prelude is one level
    /// up under `blight-prelude/`.
    pub fn prelude_resolver(name: &str) -> Result<String, blight_elab::ElabError> {
        let path = format!("{}/../blight-prelude/{}", env!("CARGO_MANIFEST_DIR"), name);
        std::fs::read_to_string(&path)
            .map_err(|e| blight_elab::ElabError::BadForm(format!("cannot load {path:?}: {e}")))
    }

    /// Elaborate `src` (which must define a `main` global) and lower it all the way to ANF through
    /// the full pure-Rust backend (lower → region → closure → mono → anf). This is exactly what
    /// `build_binary` feeds the object emitter, so a `build_run_with_main` over the result measures
    /// the *runtime* cost of a real `.bl` program (deep recursion, list/tree algorithms, …) rather
    /// than a hand-built ANF stub. Panics with context on any elaboration failure.
    pub fn compile_source_to_anf(src: &str) -> AnfProgram {
        // Elaborating long unary-`Nat` programs recurses deeply through the term, so do the work on
        // a generous (64 MiB) stack — mirrors the CLI build thread; callers (benches/tests) need not
        // arrange their own large stack.
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner(&src))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    fn compile_source_to_anf_inner(src: &str) -> AnfProgram {
        compile_source_to_anf_inner_opt(src, true)
    }

    /// Like [`compile_source_to_anf_inner`] but with explicit control over the M20 `Nat` recognizer
    /// (`recognize.rs`). With `recognize == true` this is *exactly* the `build_binary` pipeline
    /// (lower → **recognize** → region → closure → mono → anf); with `false` it is the pre-M20
    /// baseline (the recognizer skipped, so prelude `Nat` arithmetic lowers to the generic O(n)
    /// eliminator). The two are the A/B arms of the differential/perf tests.
    fn compile_source_to_anf_inner_opt(src: &str, recognize: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = if recognize {
            crate::recognize::recognize(&cir)
        } else {
            cir
        };
        // P3 elim-loop rides with the optimized arm (after recognize, before unbox), respecting the
        // `BL_NO_ELIMLOOP` gate so this helper matches the shipped `build_binary_pipeline`.
        let cir = if recognize && std::env::var_os("BL_NO_ELIMLOOP").is_none() {
            crate::elimloop::elim_loop(&cir, true)
        } else {
            cir
        };
        // M27 SRA rides with the optimized arm (off in the pre-M20 baseline arm).
        let cir = if recognize {
            crate::unbox::unbox(&cir)
        } else {
            cir
        };
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let mut anf = crate::anf::normalize(&prog);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        anf
    }

    /// Compile `src` through the full shipped pipeline, toggling **only** the P3 elim-loop transform
    /// (`elimloop::elim_loop`). `elim == true` is the shipped build; `false` is exactly that pipeline
    /// with `BL_NO_ELIMLOOP` (every other pass identical) — the deterministic A/B for the elim-loop
    /// win test, free of racy process-wide env-var toggling.
    fn compile_source_to_anf_inner_elimloop(src: &str, elim: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = crate::recognize::recognize(&cir);
        let cir = crate::elimloop::elim_loop(&cir, elim);
        let cir = crate::unbox::unbox(&cir);
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let mut anf = crate::anf::normalize(&prog);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        anf
    }

    /// Spawning wrapper for [`compile_source_to_anf_inner_elimloop`] (generous stack).
    pub fn compile_source_to_anf_elimloop(src: &str, elim: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_elimloop(&src, elim))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// Compile `src` through the full shipped pipeline, toggling **only** the P6.1 CSE pass
    /// (`cse::cse`). `cse_on == true` is the shipped build; `false` is exactly that pipeline with
    /// `BL_NO_CSE` (every other pass identical) — the deterministic A/B for the CSE win test, free of
    /// racy process-wide env-var toggling.
    fn compile_source_to_anf_inner_cse(src: &str, cse_on: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = crate::recognize::recognize(&cir);
        let cir = crate::elimloop::elim_loop(&cir, true);
        let cir = crate::unbox::unbox(&cir);
        let cir = crate::flatten::flatten(&cir);
        let cir = if cse_on { crate::cse::cse(&cir) } else { cir };
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let mut anf = crate::anf::normalize(&prog);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        anf
    }

    /// Spawning wrapper for [`compile_source_to_anf_inner_cse`] (generous stack).
    pub fn compile_source_to_anf_cse(src: &str, cse_on: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_cse(&src, cse_on))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// Compile `src` through the full shipped pipeline, toggling **only** the P7 fusion pass
    /// (`fusion::fuse`). `fuse_on == true` is the shipped build; `false` is exactly that pipeline with
    /// `BL_NO_FUSION` (every other pass identical) — the deterministic A/B for the fusion win test,
    /// free of racy process-wide env-var toggling. Fusion runs FIRST (on the pristine lowered `Cir`),
    /// matching `build_binary_pipeline`.
    fn compile_source_to_anf_inner_fusion(src: &str, fuse_on: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = if fuse_on {
            crate::fusion::fuse(&cir)
        } else {
            cir
        };
        let cir = crate::recognize::recognize(&cir);
        let cir = crate::elimloop::elim_loop(&cir, true);
        let cir = crate::unbox::unbox(&cir);
        let cir = crate::flatten::flatten(&cir);
        let cir = crate::cse::cse(&cir);
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let mut anf = crate::anf::normalize(&prog);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        anf
    }

    /// Spawning wrapper for [`compile_source_to_anf_inner_fusion`] (generous stack).
    pub fn compile_source_to_anf_fusion(src: &str, fuse_on: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_fusion(&src, fuse_on))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// Elaborate `src` and lower it to ANF with explicit control over the M20 recognizer (see
    /// [`compile_source_to_anf_inner_opt`]). Runs on a generous stack like [`compile_source_to_anf`].
    pub fn compile_source_to_anf_opt(src: &str, recognize: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_opt(&src, recognize))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// Compile `src` through the **full** shipped optimization pipeline (recognize + unbox + region +
    /// closure + mono), toggling only the A3 spine fusion via [`crate::anf::normalize_opts`]. The two
    /// arms are the A/B for the spine-fusion perf test: `fuse == true` is the real pipeline; `false`
    /// is exactly that pipeline with `BL_NO_SPINEFUSE` (every other pass identical), so any difference
    /// in allocation/collection counts is attributable to the captureless-call fold alone.
    fn compile_source_to_anf_inner_spinefuse(src: &str, fuse: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = crate::recognize::recognize(&cir);
        let cir = crate::unbox::unbox(&cir);
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let mut anf = crate::anf::normalize_opts(&prog, fuse);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        anf
    }

    /// Spawn-on-a-big-stack wrapper for [`compile_source_to_anf_inner_spinefuse`].
    pub fn compile_source_to_anf_spinefuse(src: &str, fuse: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_spinefuse(&src, fuse))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// Compile `src` through the **full** shipped optimization pipeline (recognize, elimloop, unbox,
    /// flatten, cse, region, closure, mono, inline, layout, anf), then apply the P10
    /// defunctionalization ANF→ANF pass (`defunc::defunc`) iff `on`. `on == true` mirrors the shipped
    /// build; `on == false` is exactly that pipeline with `BL_NO_DEFUNC` (every other pass identical),
    /// so any difference in the indirect-apply (`Comp::Call`/`Tail::TailCall`) vs direct-known-apply
    /// (`Comp::CallKnown`/`Tail::TailCallKnown`) counts is attributable to defunctionalization alone.
    /// Crucially it runs the *full* path including `inline` + `layout` so the surviving indirect apply
    /// sites the pass rewrites are actually present (a reduced spine would not expose them).
    fn compile_source_to_anf_inner_defunc(src: &str, on: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = crate::recognize::recognize(&cir);
        let cir = crate::elimloop::elim_loop(&cir, true);
        let cir = crate::unbox::unbox(&cir);
        let cir = crate::flatten::flatten(&cir);
        let cir = crate::cse::cse(&cir);
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let prog = crate::inline::inline(&prog);
        let prog = crate::layout::layout(&prog);
        let mut anf = crate::anf::normalize(&prog);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        if on {
            crate::defunc::defunc(&anf)
        } else {
            anf
        }
    }

    /// Spawn-on-a-big-stack wrapper for [`compile_source_to_anf_inner_defunc`].
    pub fn compile_source_to_anf_defunc(src: &str, on: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_defunc(&src, on))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// Compile `src` through the **full** shipped optimization pipeline (recognize, elimloop, unbox,
    /// flatten, cse, region, closure, mono, inline, layout, anf), then apply the P10
    /// follow-on capture-aware specialization ANF→ANF pass (`capspec::capspec`) iff `on` — **not**
    /// followed by `defunc`, so the assertions see capspec's own rewrite in isolation (exactly the
    /// `Comp::Call`/`Tail::TailCall` shape it targets, undisturbed by `defunc`'s later
    /// `CallKnown`/`TailCallKnown` rewrite of whatever it leaves behind). `on == true` mirrors the
    /// shipped build with only `BL_NO_DEFUNC` set; `on == false` is exactly that pipeline with
    /// `BL_NO_CAPSPEC` too (every other pass identical), so any difference in `EnvRef`/`CallGlobal`
    /// counts is attributable to capture-aware specialization alone.
    fn compile_source_to_anf_inner_capspec(src: &str, on: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = crate::recognize::recognize(&cir);
        let cir = crate::elimloop::elim_loop(&cir, true);
        let cir = crate::unbox::unbox(&cir);
        let cir = crate::flatten::flatten(&cir);
        let cir = crate::cse::cse(&cir);
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let prog = crate::inline::inline(&prog);
        let prog = crate::layout::layout(&prog);
        let mut anf = crate::anf::normalize(&prog);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        if on {
            crate::capspec::capspec(&anf)
        } else {
            anf
        }
    }

    /// Spawn-on-a-big-stack wrapper for [`compile_source_to_anf_inner_capspec`].
    pub fn compile_source_to_anf_capspec(src: &str, on: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_capspec(&src, on))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// Compile `src` through the **full** shipped optimization pipeline, toggling only the P2
    /// self-recursion arity-raise via [`crate::anf::normalize_opts_raise`]. The two arms are the A/B
    /// for the arity-raise perf test: `raise == true` is the real pipeline; `false` is exactly that
    /// pipeline with `BL_NO_ARITYRAISE` (every other pass identical, spine fusion on both), so any
    /// difference in `MkClosure`/`Jump` counts is attributable to the env-reuse fold alone.
    fn compile_source_to_anf_inner_arity(src: &str, raise: bool) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = crate::recognize::recognize(&cir);
        let cir = crate::unbox::unbox(&cir);
        let cir = crate::region::analyze_gated(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let mut anf = crate::anf::normalize_opts_raise(&prog, true, raise);
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        anf
    }

    /// Spawn-on-a-big-stack wrapper for [`compile_source_to_anf_inner_arity`].
    pub fn compile_source_to_anf_arity(src: &str, raise: bool) -> AnfProgram {
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner_arity(&src, raise))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    /// A `Nat` literal `Succ^(n) Zero` as surface syntax.
    pub fn nat_lit(n: usize) -> String {
        let mut s = String::from("(Zero)");
        for _ in 0..n {
            s = format!("(Succ {s})");
        }
        s
    }

    /// `main : Nat` = `plus a b` over two numerals. With the M20 recognizer this folds to a single
    /// O(1) `NatPrim::Add` of two machine-word `NatLit`s; without it, it is the prelude's O(n)
    /// `Succ`-chain eliminator. The same source is the A/B arm for the `nat_arithmetic_is_fast` test.
    pub fn nat_plus_source(a: usize, b: usize) -> String {
        format!(
            "(load \"std/nat.bl\")\n(define main Nat (plus {} {}))\n",
            nat_lit(a),
            nat_lit(b)
        )
    }

    /// `main : Nat` = `seed · 2^doublings`, computed by a *shallow* structurally-recursive driver
    /// `double-n` that repeatedly does `(plus acc acc)`. The SOURCE stays tiny (the counter literal
    /// is only `doublings`-deep, so it elaborates instantly), but at RUNTIME the result grows
    /// exponentially: the pre-M20 baseline materializes a `Succ` chain of length `seed·2^doublings`
    /// (O(2^n) `bl_alloc`s → many GC collections), whereas the M20 recognizer turns each `plus acc
    /// acc` into one O(1) machine-word add (zero allocation, zero collections). This is the workload
    /// that exhibits the headline O(n)→O(1) win without tripping the elaborator's literal-depth guard.
    pub fn nat_doubling_source(doublings: usize, seed: usize) -> String {
        format!(
            "(load \"std/nat.bl\")\n\
             (define-rec double-n (Pi ((n Nat) (acc Nat)) Nat)\n\
               (lam (n acc) (match n\n\
                 [(Zero) acc]\n\
                 [(Succ k) (double-n k (plus acc acc))])))\n\
             (define main Nat (double-n {} {}))\n",
            nat_lit(doublings),
            nat_lit(seed)
        )
    }

    /// `main : Nat` = `sum-go fuel 1 0` — a structural recursion on `fuel` (the exact shape of
    /// `bench/games/sum/sum_nat.bl`). Each step does `match fuel [Zero → acc][Succ f → recurse]`
    /// (the `Nat` loop driver) and advances `idx`/`acc` by recognized O(1) `plus`s. With the M25
    /// no-alloc `Nat` peel, destructuring `fuel` allocates **nothing** per step, so a deep loop runs
    /// at register speed and collects zero times; without it, every step materialized a `Succ` box
    /// (one `bl_alloc` per iteration), so a deep loop forces collections on a small heap. The result
    /// is `sum 1..n = n·(n+1)/2`. `fuel` is built as a `Nat` *value* via `mult` (not an n-deep
    /// source literal), so `n` can be large without tripping the elaborator's macro-depth guard.
    pub fn nat_fold_sum_source(rows: usize, cols: usize) -> String {
        // fuel = rows · cols, each factor a small source numeral the elaborator handles instantly.
        format!(
            "(load \"std/nat.bl\")\n\
             (define one Nat (Succ Zero))\n\
             (deftotal sum-go (Pi ((fuel Nat) (idx Nat) (acc Nat)) Nat)\n\
               (lam (fuel idx acc) (match fuel\n\
                 [(Zero) acc]\n\
                 [(Succ f) (sum-go f (plus idx one) (plus acc idx))])))\n\
             (define rows Nat {})\n\
             (define cols Nat {})\n\
             (define fuel Nat (mult rows cols))\n\
             (define main Nat (sum-go fuel one Zero))\n",
            nat_lit(rows),
            nat_lit(cols)
        )
    }

    /// `main : Nat` summing an `n`-element `List Nat` with `foldr plus 0` — deep structural
    /// recursion that *actually runs* (no delay), allocating a list spine and the unary result on
    /// the GC heap. The element values cycle `0,1,2`.
    pub fn list_sum_source(n: usize) -> String {
        let mut list = String::from("nil");
        for i in 0..n {
            list = format!("(cons {} {list})", nat_lit(i % 3));
        }
        format!(
            "(load \"std/list.bl\")\n\
             (define main Nat (foldr Nat Nat (lam (x acc) (plus x acc)) Zero {list}))\n"
        )
    }

    /// `main : Nat` = `length (reverse xs)` over an `n`-element `List Nat`: an accumulator-threaded
    /// reverse (tier-1 TCO loop) followed by a structural length. Runs fully.
    pub fn list_reverse_source(n: usize) -> String {
        let mut list = String::from("nil");
        for i in 0..n {
            list = format!("(cons {} {list})", nat_lit(i % 3));
        }
        format!("(load \"std/list.bl\")\n(define main Nat (length Nat (reverse Nat {list})))\n")
    }

    /// `main : Nat` = sum of a `Tree Nat` built by inserting `n` values with `tree-insert`, folded
    /// by a structural `tree-sum`. Exercises a two-recursive-field inductive at runtime.
    pub fn tree_sum_source(n: usize) -> String {
        let mut tree = String::from("(leaf)");
        for i in 0..n {
            tree = format!("(tree-insert Nat nat-le {} {tree})", nat_lit(i % 3));
        }
        format!(
            "(load \"std/tree.bl\")\n\
             (deftotal tree-sum (Pi ((tr (Tree Nat))) Nat)\n\
               (lam (tr) (match tr\n\
                 [(leaf) Zero]\n\
                 [(node l x r) (plus (tree-sum l) (plus x (tree-sum r)))])))\n\
             (define main Nat (tree-sum {tree}))\n"
        )
    }

    /// `main : Nat` = a multi-argument structural loop (`loop fuel acc`, the `sum-go` shape) that on
    /// **every step** calls four *captureless* top-level helpers (`h0..h3`, each `λx.x` on `Nat`) on
    /// the accumulator before recursing. This is the A3 spine-fusion workload: each `(hk …)` is a
    /// `CallClosure(MkClosure(hk, []), …)` — a captureless closure built only to be called once — and
    /// the curried self-call `(loop f …)` similarly builds a captureless `MkClosure(loop, [])` for its
    /// first partial application. With fusion ON every one of these becomes a direct `CallGlobal` with
    /// **no** closure allocation; with it OFF each is a `MkClosure(_, []) + Call`. So each loop step
    /// allocates five fewer closures with fusion on. The accumulator is an immediate `Nat` (the
    /// helpers are identity), so the result is `0`. `fuel = rows·cols` is a value via `mult`.
    pub fn spine_fusion_source(rows: usize, cols: usize) -> String {
        format!(
            "(load \"std/nat.bl\")\n\
             (deftotal h0 (Pi ((x Nat)) Nat) (lam (x) x))\n\
             (deftotal h1 (Pi ((x Nat)) Nat) (lam (x) x))\n\
             (deftotal h2 (Pi ((x Nat)) Nat) (lam (x) x))\n\
             (deftotal h3 (Pi ((x Nat)) Nat) (lam (x) x))\n\
             (deftotal loop (Pi ((fuel Nat) (acc Nat)) Nat)\n\
               (lam (fuel acc) (match fuel\n\
                 [(Zero) acc]\n\
                 [(Succ f) (loop f (h0 (h1 (h2 (h3 acc)))))])))\n\
             (define rows Nat {})\n\
             (define cols Nat {})\n\
             (define fuel Nat (mult rows cols))\n\
             (define main Nat (loop fuel Zero))\n",
            nat_lit(rows),
            nat_lit(cols)
        )
    }

    /// Count the `Comp`s in an [`AnfProgram`] (every function body + the entry) matching `pred`.
    pub fn count_comps(prog: &AnfProgram, pred: &dyn Fn(&Comp) -> bool) -> usize {
        fn in_tail(t: &Tail, pred: &dyn Fn(&Comp) -> bool) -> usize {
            match t {
                Tail::Let(c, rest) => (pred(c) as usize) + in_tail(rest, pred),
                Tail::Case(_, arms) => arms.iter().map(|a| in_tail(&a.body, pred)).sum(),
                Tail::Region(b) => in_tail(b, pred),
                _ => 0,
            }
        }
        in_tail(&prog.entry, pred)
            + prog
                .funcs
                .iter()
                .map(|f| in_tail(&f.body, pred))
                .sum::<usize>()
    }

    /// Count every `Atom::EnvRef` occurrence within a single `Tail` expression, walking into every
    /// `Comp`/`Tail` operand position (not just top-level `let`-bound `Comp`s, so e.g. a capture
    /// nested in a `MkClosure`'s list or an `IntPrim`'s operand is counted too).
    pub fn count_envrefs_in_tail(t: &Tail) -> usize {
        fn atom(a: &Atom) -> usize {
            matches!(a, Atom::EnvRef(_)) as usize
        }
        fn comp(c: &Comp) -> usize {
            match c {
                Comp::Atom(a) => atom(a),
                Comp::MkClosure(_, caps, _) => caps.iter().map(atom).sum(),
                Comp::Call(f, a) => atom(f) + atom(a),
                Comp::CallGlobal(_, a) => atom(a),
                Comp::CallKnown(_, e, a) => atom(e) + atom(a),
                Comp::Con(_, args, _) | Comp::Tuple(args, _) => args.iter().map(atom).sum(),
                Comp::Proj(_, a) | Comp::Now(a, _) | Comp::Later(a, _) => atom(a),
                Comp::Op { arg, .. } => atom(arg),
                Comp::IntPrim { lhs, rhs, .. } => atom(lhs) + atom(rhs),
                Comp::NatPrim { lhs, rhs, .. } | Comp::FloatPrim { lhs, rhs, .. } => {
                    atom(lhs) + rhs.as_ref().map_or(0, atom)
                }
                Comp::Foreign(_, arg) => arg.as_ref().map_or(0, atom),
                Comp::IntLit(_) | Comp::NatLit(_) | Comp::StrLit(_) => 0,
            }
        }
        fn in_tail(t: &Tail) -> usize {
            match t {
                Tail::Ret(a) | Tail::Jump(a) | Tail::Trampoline(a) => atom(a),
                Tail::Let(c, rest) => comp(c) + in_tail(rest),
                Tail::TailCall(f, a) => atom(f) + atom(a),
                Tail::TailCallGlobal(_, a) => atom(a),
                Tail::TailCallKnown(_, e, a) => atom(e) + atom(a),
                Tail::Case(scrut, arms) => {
                    atom(scrut) + arms.iter().map(|a| in_tail(&a.body)).sum::<usize>()
                }
                Tail::Region(b) => in_tail(b),
                Tail::Handle {
                    body,
                    return_clause,
                    op_clauses,
                } => {
                    atom(body)
                        + atom(return_clause)
                        + op_clauses.iter().map(|(_, a)| atom(a)).sum::<usize>()
                }
            }
        }
        in_tail(t)
    }

    /// Count every `Atom::EnvRef` occurrence in an [`AnfProgram`] (every function body + the entry).
    pub fn count_envrefs(prog: &AnfProgram) -> usize {
        count_envrefs_in_tail(&prog.entry)
            + prog
                .funcs
                .iter()
                .map(|f| count_envrefs_in_tail(&f.body))
                .sum::<usize>()
    }

    /// A C `main` (spec §7.3 — dynamic heap) that initializes a deliberately **tiny** `heap_kib`-KiB
    /// GC heap, then builds a single linked list of `nodes` GC-allocated `BL_CON` cells **all held
    /// live at once** (each node points at the previous via `fields[0]`; the head is kept on the
    /// shadow stack across every `bl_alloc`). The live set far exceeds the initial heap, so the
    /// collector must *grow* its semi-spaces instead of aborting. Prints `RESULT collections=<n>
    /// length=<n>`, where `length` walks the final list iteratively to prove it is intact (no node
    /// was lost or corrupted across the growing collections). No Blight program drives this — it is a
    /// focused unit test of the allocator/collector growth path, immune to compiler/C-stack limits.
    pub fn grow_heap_main(heap_kib: usize, nodes: usize) -> String {
        format!(
            r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void); /* unused; linked for symmetry */
int main(void) {{
  bl_gc_init({heap_kib} * 1024);
  bl_stack_init();
  BlValue head = bl_alloc(BL_CON, 1, 0); /* sentinel: one field, initially NULL */
  bl_gc_push_root(&head);
  for (size_t i = 0; i < {nodes}; i++) {{
    BlValue node = bl_alloc(BL_CON, 1, 1); /* allocation may trigger a (growing) collection */
    node->fields[0] = head; /* keep the whole chain reachable from `head` */
    head = node;
  }}
  size_t len = 0;
  for (BlValue p = head; p != 0; p = p->fields[0]) len++;
  printf("RESULT collections=%zu length=%zu\n", bl_gc_collections(), len);
  bl_gc_pop_roots(1);
  return 0;
}}
"#
        )
    }

    /// Parse `length=<n>` out of a `grow_heap_main` stdout line.
    pub fn parse_length(stdout: &str) -> usize {
        stdout
            .split_whitespace()
            .find_map(|tok| tok.strip_prefix("length="))
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no length= field in: {stdout:?}"))
    }

    /// A counted scratch loop over a `DEPTH`-deep `Nat`: each `Succ` iteration allocates
    /// `scratch_per_iter` dead 2-tuples (region-arena'd when `arena`, GC-heap otherwise) then jumps
    /// to the predecessor. The exact shape of `region_workload_bypasses_gc`; the workload that shows
    /// region reclamation bypassing the collector.
    pub fn scratch_loop_program(arena: bool, depth: usize, scratch_per_iter: usize) -> AnfProgram {
        let alloc = if arena { Alloc::Arena } else { Alloc::Gc };
        let mut body: Tail = Tail::Jump(Atom::Var(scratch_per_iter));
        for _ in 0..scratch_per_iter {
            body = Tail::Let(
                Comp::Tuple(vec![Atom::Var(0), Atom::Var(0)], alloc),
                Box::new(body),
            );
        }
        let succ_body = if arena {
            Tail::Region(Box::new(body))
        } else {
            body
        };
        let loop_body = Tail::Case(
            Atom::Var(0),
            vec![
                TailArm {
                    con: ConName("Zero".into()),
                    binders: 0,
                    body: Tail::Ret(Atom::Var(0)),
                },
                TailArm {
                    con: ConName("Succ".into()),
                    binders: 1,
                    body: succ_body,
                },
            ],
        );
        let loopf = AnfFunc {
            name: "scratch_loop".into(),
            recursive: true,
            body: loop_body,
        };

        let mut entry: Tail = Tail::TailCall(Atom::Global("scratch_loop".into()), Atom::Var(0));
        for _ in 0..depth {
            entry = Tail::Let(
                Comp::Con(ConName("Succ".into()), vec![Atom::Var(0)], Alloc::Gc),
                Box::new(entry),
            );
        }
        entry = Tail::Let(
            Comp::Con(ConName("Zero".into()), vec![], Alloc::Gc),
            Box::new(entry),
        );
        AnfProgram {
            funcs: vec![loopf],
            entry,
            con_tags: Default::default(),
        }
    }

    /// A C `main` that initializes a `heap_mib`-MiB GC heap + stack, runs `bl_program_entry`, and
    /// prints one machine-readable line: `RESULT collections=<n> arena_allocs=<n>`.
    pub fn counters_main(heap_mib: usize) -> String {
        format!(
            r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init({heap_mib} * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  (void)r;
  printf("RESULT collections=%zu arena_allocs=%zu\n",
         bl_gc_collections(), bl_arena_alloc_count());
  return 0;
}}
"#
        )
    }

    /// A C `main` that initializes a `heap_mib`-MiB heap + stack, runs `bl_program_entry`, and prints
    /// `RESULT value=<n> collections=<n>` where `value` is the result read as a `Nat` word
    /// (`bl_nat_of_value` accepts both a fast `BL_NAT` and a real `Zero`/`Succ` chain, so this is
    /// representation-agnostic — the A and B arms print the same `value`). Used by the M20
    /// `nat_arithmetic_is_fast` test to assert both correctness (same `value`) and the O(1)-allocation
    /// win (`collections` collapses with the recognizer on).
    pub fn nat_result_counters_main(heap_mib: usize) -> String {
        format!(
            r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init({heap_mib} * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  bl_gc_push_root(&r);
  unsigned long long v = (unsigned long long)bl_nat_of_value(r);
  printf("RESULT value=%llu collections=%zu\n", v, bl_gc_collections());
  bl_gc_pop_roots(1);
  return 0;
}}
"#
        )
    }

    /// Parse `value=<n>` out of a `nat_result_counters_main` stdout line.
    pub fn parse_value(stdout: &str) -> u64 {
        stdout
            .split_whitespace()
            .find_map(|tok| tok.strip_prefix("value="))
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no value= field in: {stdout:?}"))
    }

    /// Parse `collections=<n>` out of a `counters_main` stdout line.
    pub fn parse_collections(stdout: &str) -> usize {
        stdout
            .split_whitespace()
            .find_map(|tok| tok.strip_prefix("collections="))
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no collections= field in: {stdout:?}"))
    }

    /// Build `prog` (which must expose `bl_program_entry`) plus the C source `main_c` (a full
    /// translation unit defining `int main(void)`) into a binary at `<work>/<name>`, run it, and
    /// return its captured stdout as a `String`. Panics on any build/link/run failure with context.
    pub fn build_run_with_main(prog: &AnfProgram, main_c: &str, work: &Path, name: &str) -> String {
        std::fs::create_dir_all(work).expect("create work dir");
        let runtime = runtime_src_dir();

        let prog_obj = work.join(format!("{name}_program.o"));
        crate::llvm::emit_object(prog, &prog_obj).expect("emit program object");

        let mut objs = vec![prog_obj];
        for src in [
            "gc.c",
            "arena.c",
            "stack.c",
            "delay.c",
            "effects.c",
            "numeric.c",
            "boxed_array.c",
        ] {
            let obj = work.join(format!("{name}_{src}.o"));
            compile_c(&runtime.join(src), &obj, &runtime).expect("compile runtime object");
            objs.push(obj);
        }

        let main_path = work.join(format!("{name}_main.c"));
        std::fs::write(&main_path, main_c).expect("write main.c");
        let main_obj = work.join(format!("{name}_main.o"));
        compile_c(&main_path, &main_obj, &runtime).expect("compile main.c");
        objs.push(main_obj);

        let bin = work.join(name);
        let mut link = Command::new("clang");
        link.arg("-o").arg(&bin);
        for o in &objs {
            link.arg(o);
        }
        let st = link.status().expect("clang link starts");
        assert!(st.success(), "link {name}");

        let out = Command::new(&bin).output().expect("run benchmark binary");
        assert!(
            out.status.success(),
            "benchmark binary {name} exits 0; stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).into_owned()
    }
}

#[cfg(test)]
mod bench_sanity_tests {
    use super::bench_support::*;
    use crate::{AnfProgram, Comp};

    /// M20 headline: `plus` over two numerals is O(1) with the fast-`Nat` recognizer.
    ///
    /// We compile the *same* source `main = plus a b` twice — once through the real `build_binary`
    /// pipeline (recognizer ON), once with the recognizer OFF (the pre-M20 generic `Succ`-chain
    /// eliminator) — onto a deliberately small heap, and compare:
    ///   - **correctness**: both arms print the same `value = a + b` (the optimization never changes
    ///     an observable result — that is the differential guarantee, here end-to-end);
    ///   - **the win**: the baseline must allocate ~`a + b` `Succ` cells (forcing GC collections on
    ///     the small heap), while the recognized arm folds to one machine-word add and collects
    ///     **zero** times — O(n) allocations → O(1).
    ///
    /// This is the end-to-end proof that the headline claim holds in a real compiled binary, not just
    /// in the runtime unit (`fast_nat_matches_unary_semantics`).
    #[test]
    fn nat_arithmetic_is_fast() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_nat_fast_{}", std::process::id()));
                // Large enough that the unary baseline's `Succ` chain dwarfs the small heap and
                // forces collections, but bounded so elaborating the nested numeral stays within the
                // compile thread's stack (each `Succ` recurses one frame deep).
                // 2^14 = 16384 — a runtime result several times the ~4k-cell nursery of a 2 MiB
                // heap, so the baseline's `Succ` chain forces collections, while the source (a
                // 14-deep counter) elaborates instantly. The recognizer makes each doubling O(1).
                const DOUBLINGS: usize = 14;
                const SEED: usize = 1;
                let expected = (SEED as u64) << DOUBLINGS; // seed · 2^doublings
                let src = nat_doubling_source(DOUBLINGS, SEED);
                let main_c = nat_result_counters_main(2); // small 2 MiB heap (~8k-cell nursery)

                let fast = build_run_with_main(
                    &compile_source_to_anf_opt(&src, true),
                    &main_c,
                    &dir,
                    "nat_fast",
                );
                let slow = build_run_with_main(
                    &compile_source_to_anf_opt(&src, false),
                    &main_c,
                    &dir,
                    "nat_slow",
                );

                // Correctness: identical observable result.
                assert_eq!(
                    parse_value(&fast),
                    expected,
                    "recognized doubling computes seed·2^n; got {fast:?}"
                );
                assert_eq!(
                    parse_value(&slow),
                    expected,
                    "baseline doubling computes seed·2^n; got {slow:?}"
                );
                assert_eq!(
                    parse_value(&fast),
                    parse_value(&slow),
                    "recognizer must not change the observable result"
                );

                // The win: the baseline allocates O(2^n) `Succ` cells and collects; the fast path is
                // O(1) per doubling and never collects.
                let fast_gc = parse_collections(&fast);
                let slow_gc = parse_collections(&slow);
                assert_eq!(
                    fast_gc, 0,
                    "fast doubling is O(1) per step — no allocation, no collection; got {fast:?}"
                );
                assert!(
                    slow_gc > 0,
                    "baseline doubling is O(2^n) — its `Succ` chain must force a collection on the \
                     small heap (else the test proves nothing); got {slow:?}"
                );
            })
            .expect("spawn nat_arithmetic_is_fast thread")
            .join()
            .expect("nat_arithmetic_is_fast thread");
    }

    /// M25 (default-correct path): a structural `Nat` loop driver (`match fuel [Zero][Succ f]`)
    /// computes the right fold and the M20 recognizer folds its `plus`/`mult` to O(1) machine words.
    ///
    /// `sum-go fuel 1 0` (the `bench/games/sum/sum_nat.bl` shape) recurses `fuel`-deep; every step
    /// matches `fuel` and advances `idx`/`acc` by `plus`. We compile the *same* source with the
    /// recognizer ON (the real pipeline) and OFF (the pre-M20 generic `Succ`-chain eliminator) and
    /// assert:
    ///   - **correctness (differential)**: both arms print the same `value = n·(n+1)/2`, deep enough
    ///     to exercise the curried multi-arg recursion spine end-to-end;
    ///   - **the win (deterministic)**: the recognized arm collects **0** times — every `plus`/`mult`
    ///     folds to one machine-word op, so no `Succ` chain is ever materialized on the heap. This is
    ///     a heap-size-independent invariant (unlike a brittle "fewer-than-baseline" collection race).
    ///
    /// We run both arms on a heap large enough that the *un*recognized baseline does not collect: its
    /// deep, non-TCO curried spine pins O(depth) live frames (and their temp-roots), and forcing a
    /// collection in that state is a known-fragile slow-path stress (it can SIGBUS / overflow the
    /// finite shadow-stack budget past ~n·80). The recognized path it is compared against has O(1)
    /// live state and runs the same source at n=1000; see `bench/games/sum`. The allocation-churn win
    /// where the unary baseline is *forced* to GC is proven separately by `nat_arithmetic_is_fast`.
    #[test]
    fn nat_fold_is_fast() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_nat_fold_{}", std::process::id()));
                // fuel = ROWS·COLS = 60: deep enough to exercise the curried multi-arg spine, shallow
                // enough that the unrecognized baseline survives a no-GC run (see the doc comment on
                // the slow-path GC fragility). The shipped recognized path runs the same shape at
                // n=1000 with O(1) live state.
                const ROWS: usize = 6;
                const COLS: usize = 10;
                let n = ROWS * COLS;
                let expected = (n as u64) * (n as u64 + 1) / 2; // sum 1..n
                let src = nat_fold_sum_source(ROWS, COLS);
                // 64 MiB heap (the shipped main's size): big enough that neither arm collects at this
                // depth, so the baseline's fragile deep-spine GC is never triggered.
                let main_c = nat_result_counters_main(64);

                let fast = build_run_with_main(
                    &compile_source_to_anf_opt(&src, true),
                    &main_c,
                    &dir,
                    "fold_fast",
                );
                let slow = build_run_with_main(
                    &compile_source_to_anf_opt(&src, false),
                    &main_c,
                    &dir,
                    "fold_slow",
                );

                assert_eq!(
                    parse_value(&fast),
                    expected,
                    "recognized fold computes n·(n+1)/2; got {fast:?}"
                );
                assert_eq!(
                    parse_value(&slow),
                    expected,
                    "baseline fold computes n·(n+1)/2 (differential agreement); got {slow:?}"
                );

                let fast_gc = parse_collections(&fast);
                assert_eq!(
                    fast_gc, 0,
                    "M20: recognizing the loop's `plus`/`mult` into O(1) machine-word ops must \
                     materialize no `Succ` chains — the recognized arm collects 0 times; got \
                     fast={fast:?}"
                );
            })
            .expect("spawn nat_fold_is_fast thread")
            .join()
            .expect("nat_fold_is_fast thread");
    }

    /// P3 (elim-loop, 3a): a tail-accumulator structural recursion must run in **bounded C stack**.
    ///
    /// `sum-go fuel idx acc` (the `nat_fold_sum_source` shape) recurses on `fuel` while threading the
    /// `idx`/`acc` accumulators through the eliminator's *function-typed motive*. Lowered naively the
    /// eliminator computes its induction hypothesis with an **eager, non-tail** self-call
    /// (`CallGlobal("rec_0", f)`) — so a `fuel`-deep input builds `fuel` C-stack frames and SIGSEGVs
    /// past a few hundred thousand (the documented `nat_fold_is_fast` cap of n≈60). The 3a elim-loop
    /// transform lowers this accumulator pattern to a multi-arg `Jump` loop, so it must compute the
    /// exact `n·(n+1)/2` at `n = 10^6` without overflowing.
    #[test]
    fn elim_accumulator_recursion_is_stack_safe() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_elimloop_{}", std::process::id()));
                let n: u64 = 1_000_000; // built as a Nat *value* via mult (no deep source literal)
                let expected = n * (n - 1) / 2; // sum 0..n-1 = 499999500000
                // fuel = ((10·10)·(10·10))·(10·10) = 10^6, each factor a tiny source numeral, so the
                // parser never sees a deep nesting; `sum-go` recurses `fuel`-deep at runtime.
                let src = format!(
                    "(load \"std/nat.bl\")\n\
                     (deftotal sum-go (Pi ((fuel Nat) (idx Nat) (acc Nat)) Nat)\n\
                       (lam (fuel idx acc) (match fuel\n\
                         [(Zero) acc]\n\
                         [(Succ f) (sum-go f (Succ idx) (plus acc idx))])))\n\
                     (define ten Nat {})\n\
                     (define hundred Nat (mult ten ten))\n\
                     (define n Nat (mult (mult hundred hundred) hundred))\n\
                     (define main Nat (sum-go n Zero Zero))\n",
                    nat_lit(10)
                );
                let main_c = nat_result_counters_main(64);
                let out = build_run_with_main(
                    &compile_source_to_anf(&src),
                    &main_c,
                    &dir,
                    "elimloop_deep",
                );
                assert_eq!(
                    parse_value(&out),
                    expected,
                    "deep tail-accumulator fold must loop in bounded stack and compute n·(n+1)/2 at \
                     n=10^6; got {out:?}"
                );
            })
            .expect("spawn elim_accumulator_recursion_is_stack_safe thread")
            .join()
            .expect("elim_accumulator_recursion_is_stack_safe thread");
    }

    /// P3 (elim-loop, 3a) — the deterministic, heap-independent *mechanism* A/B (sibling to
    /// `spine_fusion_reduces_allocations`). The same `sum-go` accumulator source is compiled through
    /// the full pipeline twice — elim-loop ON (shipped) vs OFF (`BL_NO_ELIMLOOP`, every other pass
    /// identical) — and we assert the transform's signature:
    ///   - **the win**: ON, the eliminator's recursive arm is a `Tail::Jump` (a bounded-stack
    ///     back-edge) — OFF there is *no* `Jump` (the eager eliminator recurses via a non-tail call);
    ///   - and the per-step closure traffic does not grow (ON emits no more captureless `MkClosure`
    ///     sites than OFF).
    ///
    /// Pinning the `Jump` mechanism is independent of heap/timing noise, exactly the discipline the
    /// plan requires for a behavior-preserving pass.
    #[test]
    fn elim_loop_emits_bounded_stack_jump() {
        let src = "(load \"std/nat.bl\")\n\
            (deftotal sum-go (Pi ((fuel Nat) (idx Nat) (acc Nat)) Nat)\n\
              (lam (fuel idx acc) (match fuel\n\
                [(Zero) acc]\n\
                [(Succ f) (sum-go f (Succ idx) (plus acc idx))])))\n\
            (define main Nat (sum-go (Succ (Succ (Succ Zero))) Zero Zero))\n";
        let on = compile_source_to_anf_elimloop(src, true);
        let off = compile_source_to_anf_elimloop(src, false);

        let any_jump = |a: &AnfProgram| {
            a.funcs.iter().any(|f| crate::anf::has_jump(&f.body)) || crate::anf::has_jump(&a.entry)
        };
        assert!(
            any_jump(&on),
            "elim-loop ON rewrites the tail-accumulator eliminator to a bounded-stack `Tail::Jump`"
        );
        assert!(
            !any_jump(&off),
            "with elim-loop OFF the eager eliminator emits no `Jump` (the bit-identical reference)"
        );

        let is_captureless_mkclo =
            |c: &Comp| matches!(c, Comp::MkClosure(_, caps, _) if caps.is_empty());
        let on_mkclo = count_comps(&on, &is_captureless_mkclo);
        let off_mkclo = count_comps(&off, &is_captureless_mkclo);
        assert!(
            on_mkclo <= off_mkclo,
            "elim-loop must not increase captureless closure traffic: on={on_mkclo} off={off_mkclo}"
        );
    }

    /// P6.1 (CSE) — the deterministic, heap-independent *mechanism* A/B. A body with a repeated
    /// **pure** computation `(x*x) + (x*x)` is compiled through the full pipeline twice — CSE ON
    /// (shipped) vs OFF (`BL_NO_CSE`, every other pass identical) — and we assert the transform's
    /// signature: ON emits strictly **fewer** `int*` operations (the repeat is shared into one
    /// `let`), and never more total ops, than OFF. The duplicated multiply lives inside a lambda
    /// (operands are the bound variable, not literals) so it is never constant-folded away, leaving a
    /// genuine repeated subterm for CSE to share. Pinning the op-count delta is independent of
    /// heap/timing noise — exactly the discipline a behavior-preserving pass requires.
    #[test]
    fn cse_shares_repeated_pure_subterm() {
        let src = "(define sq-sum (Pi ((x Int)) Int)\n\
              (lam (x) (int+ (int* x x) (int* x x))))\n\
            (define main Int (sq-sum (int 7)))\n";
        let on = compile_source_to_anf_cse(src, true);
        let off = compile_source_to_anf_cse(src, false);

        let is_mul = |c: &Comp| {
            matches!(
                c,
                Comp::IntPrim {
                    op: blight_kernel::IntPrimOp::Mul,
                    ..
                }
            )
        };
        let on_muls = count_comps(&on, &is_mul);
        let off_muls = count_comps(&off, &is_mul);
        assert_eq!(
            off_muls, 2,
            "without CSE the `(x*x) + (x*x)` body emits the multiply twice (the reference)"
        );
        assert_eq!(
            on_muls, 1,
            "CSE shares the repeated pure `x*x` into a single `let` (one multiply): \
             on={on_muls} off={off_muls}"
        );
    }

    /// P7 (deforestation/fusion) — the deterministic, heap-independent *mechanism* A/B plus an
    /// end-to-end correctness check, the sibling of `cse_shares_repeated_pure_subterm` and
    /// `spine_fusion_reduces_allocations`.
    ///
    /// The canonical build-then-fold pipeline `foldr int-add 0 (map int-double xs)` is compiled
    /// through the full pipeline twice — fusion ON (shipped) vs OFF (`BL_NO_FUSION`, every other pass
    /// identical) — and we assert the transform's signature:
    ///   - **the win**: ON emits strictly **fewer** `cons` constructor sites than OFF — the
    ///     intermediate mapped list's per-element `cons (g x) …` allocation (the body of the lifted
    ///     `map` recurrence) is gone entirely, so the intermediate list is never built;
    ///   - **multi-consumer guard**: a `let m = map g xs in …` (modeled here by a non-`map` list
    ///     argument) is left un-fused (equal `cons` sites), proven by `fusion::tests`;
    ///   - **correctness (differential, end-to-end)**: both arms build, run, and print the identical
    ///     `value = 2·(1+2+3) = 12`.
    #[test]
    fn fusion_eliminates_intermediate_list() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_fusion_{}", std::process::id()));
                let src = "(load \"std/list.bl\")\n\
                    (load \"std/int.bl\")\n\
                    (define main Int\n\
                      (foldr Int Int int-add (int 0)\n\
                        (map Int Int int-double (cons (int 1) (cons (int 2) (cons (int 3) nil))))))\n";
                let on = compile_source_to_anf_fusion(src, true);
                let off = compile_source_to_anf_fusion(src, false);

                // The mechanism: the lifted `map` recurrence's `cons (g x) (self rest)` allocation
                // site disappears with fusion on (the intermediate list is never built).
                let is_cons = |c: &Comp| matches!(c, Comp::Con(name, _, _) if name.0 == "cons");
                let on_cons = count_comps(&on, &is_cons);
                let off_cons = count_comps(&off, &is_cons);
                assert!(
                    on_cons < off_cons,
                    "fusion deletes the intermediate mapped list's `cons` site(s): \
                     on={on_cons} off={off_cons}"
                );

                // Correctness: both build + run natively and agree on 2·(1+2+3) = 12.
                let main_c = r#"#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {
  bl_gc_init(64 * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  printf("value=%lld\n", (long long) bl_int_val(r));
  return 0;
}
"#;
                let parse = |s: &str| -> i64 {
                    s.split_whitespace()
                        .find_map(|t| t.strip_prefix("value="))
                        .and_then(|n| n.parse().ok())
                        .unwrap_or_else(|| panic!("no value= in {s:?}"))
                };
                let fused = build_run_with_main(&on, main_c, &dir, "fusion_on");
                let unfused = build_run_with_main(&off, main_c, &dir, "fusion_off");
                assert_eq!(parse(&fused), 12, "fused foldr-of-map computes 12; got {fused:?}");
                assert_eq!(
                    parse(&unfused),
                    parse(&fused),
                    "fusion must not change the observable result; \
                     fused={fused:?} unfused={unfused:?}"
                );
            })
            .expect("spawn fusion_eliminates_intermediate_list thread")
            .join()
            .expect("fusion_eliminates_intermediate_list thread");
    }

    /// P3 (elim-loop, 3b) RED — a **non-tail** linear structural fold must run in bounded C stack.
    ///
    /// `count-up n = match n [Zero -> Zero] [Succ k -> Succ (count-up k)]` uses its induction
    /// hypothesis `(count-up k)` in **non-tail** position (under a `Succ`), so the 3a tail-accumulator
    /// transform correctly declines it (no accumulator). Lowered eagerly it recurses `n`-deep on the C
    /// stack and SIGSEGVs past ~5·10^4 frames (docs/benchmarks-game.md caveat 5). The P3.3 (3b)
    /// reverse-then-fold transform ([`crate::elimworklist`]) rebuilds this single-recursive-field
    /// linear fold as `λx. fold_loop (rev_loop x Zero) Zero` — two tail-accumulator catamorphisms the
    /// (3a) loop then makes O(1)-native-stack — so it must compute the exact value (`n`) at `n = 10^6`
    /// without overflowing.
    #[test]
    fn elim_nontail_linear_fold_is_stack_safe() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_elimwl_{}", std::process::id()));
                let n: u64 = 1_000_000;
                let src = format!(
                    "(load \"std/nat.bl\")\n\
                     (deftotal count-up (Pi ((n Nat)) Nat)\n\
                       (lam (n) (match n\n\
                         [(Zero) Zero]\n\
                         [(Succ k) (Succ (count-up k))])))\n\
                     (define ten Nat {})\n\
                     (define hundred Nat (mult ten ten))\n\
                     (define n Nat (mult (mult hundred hundred) hundred))\n\
                     (define main Nat (count-up n))\n",
                    nat_lit(10)
                );
                let main_c = nat_result_counters_main(64);
                let out =
                    build_run_with_main(&compile_source_to_anf(&src), &main_c, &dir, "elimwl_deep");
                assert_eq!(
                    parse_value(&out),
                    n,
                    "deep non-tail linear fold must run on a heap worklist and return n at n=10^6; \
                     got {out:?}"
                );
            })
            .expect("spawn elim_nontail_linear_fold_is_stack_safe thread")
            .join()
            .expect("elim_nontail_linear_fold_is_stack_safe thread");
    }

    /// A3 (spine fusion): the captureless-call fold removes real per-step closure allocations, and is
    /// observationally transparent. We compile the *same* curried multi-arg loop
    /// (`spine_fusion_source`, which calls four captureless `λx.x` helpers per step) through the
    /// **full** pipeline twice — once with spine fusion ON (the shipped build), once OFF
    /// (`BL_NO_SPINEFUSE`, every other pass identical) — and assert two things:
    ///
    ///   - **the win (deterministic, heap-independent)**: the fused ANF allocates **strictly fewer**
    ///     `MkClosure` objects and emits at least one `CallGlobal`, while the un-fused ANF emits *no*
    ///     `CallGlobal` and keeps every captureless `MkClosure(_, []) + Call`. Counting allocation
    ///     *sites* in the loop body (each runs once per iteration) proves the per-step heap traffic
    ///     drops without depending on a fragile GC-collection race or a deep spine that pins O(depth)
    ///     roots (the hazard `nat_fold_is_fast` documents).
    ///   - **correctness (differential, end-to-end)**: both arms *build and run* natively through the
    ///     new `bl_app_global` path and print the **identical** result (`0`), so the fold preserves
    ///     observable behavior.
    #[test]
    fn spine_fusion_reduces_allocations() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_spinefuse_{}", std::process::id()));
                let src = spine_fusion_source(20, 20); // 400 steps: runs end-to-end, no GC needed.
                let on = compile_source_to_anf_spinefuse(&src, true);
                let off = compile_source_to_anf_spinefuse(&src, false);

                // The mechanism: fused folds every captureless `MkClosure(_, [])` into a `CallGlobal`.
                let is_captureless_mkclo =
                    |c: &Comp| matches!(c, Comp::MkClosure(_, caps, _) if caps.is_empty());
                let is_callglobal = |c: &Comp| matches!(c, Comp::CallGlobal(_, _));
                let on_mkclo = count_comps(&on, &is_captureless_mkclo);
                let off_mkclo = count_comps(&off, &is_captureless_mkclo);
                let on_cg = count_comps(&on, &is_callglobal);
                let off_cg = count_comps(&off, &is_callglobal);
                assert_eq!(
                    off_cg, 0,
                    "with spine fusion off, no CallGlobal is emitted (the un-fused reference)"
                );
                assert!(
                    on_cg > 0,
                    "spine fusion emits CallGlobal for the captureless partial-application calls"
                );
                assert!(
                    on_mkclo < off_mkclo,
                    "spine fusion strictly reduces captureless MkClosure allocation sites: \
                     on={on_mkclo} off={off_mkclo}"
                );

                // Correctness: both build + run natively (exercising `bl_app_global`) and agree.
                let main_c = nat_result_counters_main(64);
                let fused_out = build_run_with_main(&on, &main_c, &dir, "spinefuse_on");
                let unfused_out = build_run_with_main(&off, &main_c, &dir, "spinefuse_off");
                assert_eq!(
                    parse_value(&fused_out),
                    0,
                    "identity helpers over acc=Zero compute 0; got {fused_out:?}"
                );
                assert_eq!(
                    parse_value(&unfused_out),
                    parse_value(&fused_out),
                    "spine fusion must not change the observable result; \
                     fused={fused_out:?} unfused={unfused_out:?}"
                );
            })
            .expect("spawn spine_fusion_reduces_allocations thread")
            .join()
            .expect("spine_fusion_reduces_allocations thread");
    }

    /// The real `bench/games/binrec/binrec_int.bl` source (the "curried self-call materializes
    /// partial-application closures" regression C1 investigated — see
    /// `docs/c1-uncurry-investigation.md`). Loaded verbatim so these tests exercise the exact program
    /// the bench harness measures, not a hand-built stand-in.
    fn binrec_source() -> &'static str {
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../bench/games/binrec/binrec_int.bl"
        ))
    }

    /// A minimal C `main` for a program whose result is a native `Int` (`binrec`'s result type):
    /// reads it with `bl_int_val` (always linked, unlike the optional `prelude_rt.c` this harness
    /// deliberately excludes — see [`build_run_with_main`]) and prints it in plain decimal, matching
    /// `binrec_int.bl`'s own `golden.txt` format.
    fn int_result_main() -> String {
        r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {
  bl_gc_init(64 * 1024 * 1024);
  bl_stack_init();
  BlValue result = bl_program_entry();
  printf("%lld\n", (long long)bl_int_val(result));
  return 0;
}
"#
        .to_string()
    }

    /// C1 (Wave 6) RED/regression — investigation target: `docs/benchmarks-game.md` historically
    /// documented `binrec` allocating ~151 MB because "each curried self-call materializes
    /// partial-application closures," which C1 was scoped to fix with a new CFA-driven uncurrying
    /// pass. Compiling the *real* `binrec_int.bl` through the same A/B harness
    /// `spine_fusion_reduces_allocations` uses (full pipeline minus `elim_loop`, so the self-recursive
    /// `Cir::CallClosure(MkClosure(binrec, []), m)` shape survives to `anf::normalize_opts` unmolested)
    /// shows the fix already exists: the pre-existing **A3 captureless-call spine fusion**
    /// (`anf.rs`, `BL_NO_SPINEFUSE`) removes every `MkClosure` at the self-call site on its own, with
    /// no new pass needed. `binrec`'s recursive function is the sole `recursive: true` `AnfFunc`
    /// (named generically, e.g. `rec_0`, by closure conversion) — the assertion is scoped to *that
    /// function's own body*, matching the plan's literal "at the self-call" wording, because a single
    /// one-time `MkClosure` may still legitimately appear at the *entry* (the one non-recursive,
    /// outermost `main = (binrec twentyone)` invocation) without indicating any per-call churn; only
    /// the recursive body runs once per one of the ~4.2 M calls, so that is where churn would show.
    /// `fuse == true` (the shipped setting) must show zero `MkClosure` and at least one
    /// `CallGlobal`/`CallKnown`/`Jump` in that body, while `fuse == false` (`BL_NO_SPINEFUSE`) recovers
    /// the historical un-fused shape — so this doubles as the differential (A3) bit-identity gate for
    /// `binrec` specifically.
    #[test]
    fn binrec_recursive_site_has_no_mkclosure() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let src = binrec_source();
                let fused = compile_source_to_anf_spinefuse(src, true);
                let unfused = compile_source_to_anf_spinefuse(src, false);

                let recursive_body = |p: &AnfProgram| -> crate::Tail {
                    p.funcs
                        .iter()
                        .find(|f| f.recursive)
                        .unwrap_or_else(|| panic!("binrec compiles to a recursive AnfFunc: {p:?}"))
                        .body
                        .clone()
                };
                let fused_body = recursive_body(&fused);
                let unfused_body = recursive_body(&unfused);

                let count_in = |t: &crate::Tail, pred: &dyn Fn(&Comp) -> bool| -> usize {
                    let p = AnfProgram {
                        funcs: vec![],
                        entry: t.clone(),
                        con_tags: Default::default(),
                    };
                    count_comps(&p, pred)
                };
                let is_mkclosure = |c: &Comp| matches!(c, Comp::MkClosure(_, _, _));
                let is_callglobal_or_known =
                    |c: &Comp| matches!(c, Comp::CallGlobal(_, _) | Comp::CallKnown(_, _, _));

                assert_eq!(
                    count_in(&fused_body, &is_mkclosure),
                    0,
                    "spine fusion on: binrec's recursive self-call site must build no closure at \
                     all (a bare CallGlobal/Jump, not a partial application): {fused_body:?}"
                );
                assert!(
                    count_in(&fused_body, &is_callglobal_or_known) > 0
                        || crate::anf::has_jump(&fused_body),
                    "spine fusion on: binrec's self-call site must be a direct CallGlobal/Jump: \
                     {fused_body:?}"
                );
                assert!(
                    count_in(&unfused_body, &is_mkclosure) > 0,
                    "spine fusion off (BL_NO_SPINEFUSE): the historical un-fused MkClosure \
                     reference must still be produced at the self-call (the differential \
                     slow-path reference): {unfused_body:?}"
                );
            })
            .expect("spawn binrec_recursive_site_has_no_mkclosure thread")
            .join()
            .expect("binrec_recursive_site_has_no_mkclosure thread");
    }

    /// C1 (Wave 6) e2e correctness twin: `binrec` must compute the same golden (`4194303`) whether or
    /// not A3 spine fusion runs — the closure elision is purely an allocation optimization, never a
    /// semantic change. Builds and runs the *real* `binrec_int.bl` natively (through `bl_app_global`
    /// for the fused arm, through the generic closure-apply path for the un-fused arm) twice and
    /// compares stdout byte-for-byte. This is the "`tests::uncurry_preserves_semantics_binrec`"
    /// Red test the original C1 plan specified, adapted to the mechanism that actually implements it
    /// (A3 spine fusion, not a new CFA-driven uncurrying pass — see `docs/c1-uncurry-investigation.md`).
    #[test]
    fn binrec_spine_fusion_preserves_semantics() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_binrec_sf_{}", std::process::id()));
                let src = binrec_source();
                let fused = compile_source_to_anf_spinefuse(src, true);
                let unfused = compile_source_to_anf_spinefuse(src, false);
                let main_c = int_result_main();
                let fused_out = build_run_with_main(&fused, &main_c, &dir, "binrec_sf_on");
                let unfused_out = build_run_with_main(&unfused, &main_c, &dir, "binrec_sf_off");
                assert_eq!(
                    fused_out.trim(),
                    "4194303",
                    "binrec's shared golden must hold with spine fusion on; got {fused_out:?}"
                );
                assert_eq!(
                    fused_out, unfused_out,
                    "A3 spine fusion must not change binrec's observable output: \
                     fused={fused_out:?} unfused={unfused_out:?}"
                );
            })
            .expect("spawn binrec_spine_fusion_preserves_semantics thread")
            .join()
            .expect("binrec_spine_fusion_preserves_semantics thread");
    }

    /// P10 (defunctionalization): a higher-order `iterate` threads one *capturing* continuation
    /// closure `step` through a structural loop and applies it indirectly at `(step acc)`. The
    /// closure `(adder one)` is the only value that ever flows to `step` (a singleton reachable set),
    /// so whole-program closure analysis can devirtualize the indirect apply to a direct call of the
    /// known lifted function — passing the closure object as its environment (captures preserved).
    ///
    /// We compile the *same* source through the **full** pipeline twice — defunc ON (the shipped
    /// build) and OFF (`BL_NO_DEFUNC`, every other pass identical) — and assert:
    ///   - **the win (deterministic, heap-independent)**: the defunctionalized ANF has **strictly
    ///     fewer** indirect `Comp::Call`s and **strictly more** direct `Comp::CallKnown`s than the
    ///     baseline (the surviving higher-order apply became a direct, LTO-inlinable call);
    ///   - **correctness (differential, end-to-end)**: both arms build, run, and print the identical
    ///     `value`.
    ///
    /// Against the identity-stub `defunc` this fails (no `CallKnown` is introduced, the `Call` count
    /// does not drop) — it is the RED test that the analysis + rewrite turn GREEN.
    #[test]
    fn defunc_eliminates_indirect_apply() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_defunc_{}", std::process::id()));
                // `iterate fuel step acc` applies the higher-order `step` to `acc` `fuel` times;
                // `(adder one)` is the single capturing closure threaded through `step`. fuel = 16
                // (result 16) runs end-to-end with no GC needed.
                let src = format!(
                    "(load \"std/nat.bl\")\n\
                     (deftotal adder (Pi ((k Nat)) (Pi ((a Nat)) Nat))\n\
                       (lam (k) (lam (a) (plus a k))))\n\
                     (deftotal iterate (Pi ((fuel Nat) (step (Pi ((a Nat)) Nat)) (acc Nat)) Nat)\n\
                       (lam (fuel step acc) (match fuel\n\
                         [(Zero) acc]\n\
                         [(Succ f) (iterate f step (step acc))])))\n\
                     (define one Nat (Succ Zero))\n\
                     (define main Nat (iterate {} (adder one) Zero))\n",
                    nat_lit(16)
                );
                let on = compile_source_to_anf_defunc(&src, true);
                let off = compile_source_to_anf_defunc(&src, false);

                let is_call = |c: &Comp| matches!(c, Comp::Call(_, _));
                let is_callknown = |c: &Comp| matches!(c, Comp::CallKnown(_, _, _));
                let on_call = count_comps(&on, &is_call);
                let off_call = count_comps(&off, &is_call);
                let on_known = count_comps(&on, &is_callknown);
                let off_known = count_comps(&off, &is_callknown);
                assert_eq!(
                    off_known, 0,
                    "with defunc off, no CallKnown is emitted (the indirect reference)"
                );
                assert!(
                    on_known > off_known,
                    "defunc devirtualizes the singleton-flow apply to a direct CallKnown: \
                     on={on_known} off={off_known}"
                );
                assert!(
                    on_call < off_call,
                    "defunc strictly reduces indirect Comp::Call sites: on={on_call} off={off_call}"
                );

                // Correctness: both build + run natively and agree (16 · 1 = 16).
                let main_c = nat_result_counters_main(64);
                let on_out = build_run_with_main(&on, &main_c, &dir, "defunc_on");
                let off_out = build_run_with_main(&off, &main_c, &dir, "defunc_off");
                assert_eq!(
                    parse_value(&on_out),
                    16,
                    "iterate (+1) 16 times over Zero computes 16; got {on_out:?}"
                );
                assert_eq!(
                    parse_value(&off_out),
                    parse_value(&on_out),
                    "defunc must not change the observable result; on={on_out:?} off={off_out:?}"
                );
            })
            .expect("spawn defunc_eliminates_indirect_apply thread")
            .join()
            .expect("defunc_eliminates_indirect_apply thread");
    }

    /// P10 follow-on (capture-aware specialization): compiles the real benchmark source
    /// `bench/games/hofold/hofold_int.bl` — `(adder (int 1))` is a singleton-flow closure over
    /// `adder`, whose only capture `k` (`int 1`, an `IntLit`) is a single constant literal reaching
    /// every flow path (via the CFA's call arg->param edge, `adder`'s only call site). capspec should
    /// clone `adder`'s lifted body into a captureless `*$cap$0` with `1` baked in as a `let`-bound
    /// literal, and rewrite the apply to a null-env `CallGlobal`/`TailCallGlobal` of it — eliminating
    /// the capture `EnvRef` entirely in the clone.
    ///
    /// We compile the *same* source through the **full** pipeline (with `defunc` off in both arms, so
    /// the assertions see capspec's own rewrite, not `defunc`'s later `CallKnown` devirtualization of
    /// whatever capspec leaves behind) twice — capspec ON and OFF (`BL_NO_CAPSPEC`) — and assert:
    ///   - **the win (deterministic, heap-independent)**: capspec ON gains a `*$cap$*` clone function
    ///     whose body contains **zero** `EnvRef` (the original `adder` — capture and all — is left in
    ///     place per the plan, so the win is visible in the *new* clone, not a whole-program count)
    ///     and the call site is rewritten to a null-env `CallGlobal`;
    ///   - **correctness (differential, end-to-end)**: both arms build, run, and print the identical
    ///     `value` (1000000 = `iterate million (adder 1) 0`, exactly the value
    ///     `bench/games/hofold/hofold_int.bl` documents at its own call site).
    #[test]
    fn capspec_eliminates_capture_env_load() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_capspec_{}", std::process::id()));
                // The exact source of `bench/games/hofold/hofold_int.bl` (the P10-follow-on benchmark
                // this pass targets) minus its header comment. `fuel` is built via `mult` (the M20
                // fast-`Nat` path folds it to a single machine word), not a raw `Succ`-chain literal,
                // so `iterate` compiles to a genuine runtime `Jump` loop rather than a compile-time
                // unrolled chain — build time is independent of the fuel value, so there is no reason
                // to shrink it below the real benchmark's `million`.
                let src = std::fs::read_to_string(
                    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                        .parent()
                        .unwrap()
                        .parent()
                        .unwrap()
                        .join("bench/games/hofold/hofold_int.bl"),
                )
                .expect("read bench/games/hofold/hofold_int.bl");
                let on = compile_source_to_anf_capspec(&src, true);
                let off = compile_source_to_anf_capspec(&src, false);

                let clone = on
                    .funcs
                    .iter()
                    .find(|f| f.name.contains("$cap$"))
                    .unwrap_or_else(|| {
                        panic!(
                            "capspec adds a specialized clone function: {:?}",
                            on.funcs.iter().map(|f| &f.name).collect::<Vec<_>>()
                        )
                    });
                let clone_envrefs = count_envrefs_in_tail(&clone.body);
                assert_eq!(
                    clone_envrefs, 0,
                    "the specialized clone's body has no capture EnvRef left: {clone:#?}"
                );
                assert!(
                    !off.funcs.iter().any(|f| f.name.contains("$cap$")),
                    "with capspec off, no clone is synthesized: {:?}",
                    off.funcs.iter().map(|f| &f.name).collect::<Vec<_>>()
                );
                let is_callglobal = |c: &Comp| matches!(c, Comp::CallGlobal(_, _));
                assert!(
                    count_comps(&on, &is_callglobal) > count_comps(&off, &is_callglobal),
                    "the specialized apply becomes a direct, null-env CallGlobal"
                );

                // Correctness: both build + run natively and agree (100 · 1 = 100).
                let main_c = r#"#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {
  bl_gc_init(64 * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  printf("value=%lld\n", (long long) bl_int_val(r));
  return 0;
}
"#;
                let parse = |s: &str| -> i64 {
                    s.split_whitespace()
                        .find_map(|t| t.strip_prefix("value="))
                        .and_then(|n| n.parse().ok())
                        .unwrap_or_else(|| panic!("no value= in {s:?}"))
                };
                let on_out = build_run_with_main(&on, main_c, &dir, "capspec_on");
                let off_out = build_run_with_main(&off, main_c, &dir, "capspec_off");
                assert_eq!(
                    parse(&on_out),
                    1_000_000,
                    "iterate (+1) a million times over 0 computes 1000000; got {on_out:?}"
                );
                assert_eq!(
                    parse(&off_out),
                    parse(&on_out),
                    "capspec must not change the observable result; on={on_out:?} off={off_out:?}"
                );
            })
            .expect("spawn capspec_eliminates_capture_env_load thread")
            .join()
            .expect("capspec_eliminates_capture_env_load thread");
    }

    /// P2 (self-recursion arity-raise): a tail-recursive structural function whose captured leading
    /// parameter rides verbatim emits, every step, a self-closure rebuild of its *own* env
    /// (`MkClosure(self, [EnvRef0]) + TailCall`). The raise folds that into a `Jump` that reuses the
    /// current env — one fewer `bl_alloc` per iteration — and is observationally transparent.
    ///
    /// `keep d n` recurses on `n` (the scrutinee) while threading `d` (a leading, loop-invariant
    /// capture) verbatim, returning `d`. We compile the *same* source through the **full** pipeline
    /// twice — raise ON (the shipped build) and OFF (`BL_NO_ARITYRAISE`, every other pass identical) —
    /// and assert:
    ///   - **the win (deterministic)**: the raised ANF has **strictly more** `Jump`s and **strictly
    ///     fewer** `MkClosure`s than the un-raised one (the per-step self-rebuild became a back-edge);
    ///   - **correctness (differential, end-to-end)**: both arms build, run, and print the identical
    ///     `value = d`.
    #[test]
    fn arity_raise_reduces_allocations() {
        use crate::{AnfProgram, Tail};
        fn count_jumps(prog: &AnfProgram) -> usize {
            fn go(t: &Tail) -> usize {
                match t {
                    Tail::Jump(_) => 1,
                    Tail::Let(_, rest) | Tail::Region(rest) => go(rest),
                    Tail::Case(_, arms) => arms.iter().map(|a| go(&a.body)).sum(),
                    _ => 0,
                }
            }
            go(&prog.entry) + prog.funcs.iter().map(|f| go(&f.body)).sum::<usize>()
        }
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_arityraise_{}", std::process::id()));
                let src = format!(
                    "(load \"std/nat.bl\")\n\
                     (deftotal keep (Pi ((d Nat) (n Nat)) Nat)\n\
                       (lam (d n) (match n\n\
                         [(Zero) d]\n\
                         [(Succ m) (keep d m)])))\n\
                     (define main Nat (keep {} {}))\n",
                    nat_lit(3),
                    nat_lit(64)
                );
                let on = compile_source_to_anf_arity(&src, true);
                let off = compile_source_to_anf_arity(&src, false);

                let is_mkclo = |c: &Comp| matches!(c, Comp::MkClosure(_, _, _));
                let on_mkclo = count_comps(&on, &is_mkclo);
                let off_mkclo = count_comps(&off, &is_mkclo);
                let on_jumps = count_jumps(&on);
                let off_jumps = count_jumps(&off);
                assert!(
                    on_jumps > off_jumps,
                    "the raise turns the per-step self-rebuild into a Jump: on={on_jumps} \
                     off={off_jumps}"
                );
                assert!(
                    on_mkclo < off_mkclo,
                    "the raise strictly reduces MkClosure allocation sites: on={on_mkclo} \
                     off={off_mkclo}"
                );

                let main_c = nat_result_counters_main(8);
                let raised = build_run_with_main(&on, &main_c, &dir, "arity_on");
                let unraised = build_run_with_main(&off, &main_c, &dir, "arity_off");
                assert_eq!(
                    parse_value(&raised),
                    3,
                    "keep d n returns the loop-invariant d; got {raised:?}"
                );
                assert_eq!(
                    parse_value(&unraised),
                    parse_value(&raised),
                    "the arity-raise must not change the observable result; \
                     raised={raised:?} unraised={unraised:?}"
                );
            })
            .expect("spawn arity_raise_reduces_allocations thread")
            .join()
            .expect("arity_raise_reduces_allocations thread");
    }

    /// Sanity guard for the runtime benchmark harness (TDD seam, mirrors
    /// `llvm::tests::region_workload_bypasses_gc`): on a small heap the GC-heap scratch loop is
    /// forced to collect (`collections > 0`), while the region/arena twin reclaims each iteration in
    /// O(1) and never collects (`collections == 0`). If this ever flips, the bench's "regions bypass
    /// the GC" measurement is meaningless, so we assert it before trusting any timing.
    #[test]
    fn bench_harness_region_bypasses_gc_and_heap_collects() {
        let dir = std::env::temp_dir().join(format!("blight_bench_sanity_{}", std::process::id()));
        let main_c = counters_main(8); // 8 MiB heap, ~1 MiB nursery
        let depth = 300;
        let scratch = 256;

        let gc = build_run_with_main(
            &scratch_loop_program(false, depth, scratch),
            &main_c,
            &dir,
            "sanity_gc",
        );
        let arena = build_run_with_main(
            &scratch_loop_program(true, depth, scratch),
            &main_c,
            &dir,
            "sanity_arena",
        );

        assert!(
            parse_collections(&gc) > 0,
            "GC-heap scratch loop forces collections; got {gc:?}"
        );
        assert_eq!(
            parse_collections(&arena),
            0,
            "region/arena scratch loop bypasses the GC; got {arena:?}"
        );
    }

    /// `compile_source_to_anf` lowers a real `.bl` program (here a `List Nat` sum) through the full
    /// backend and the produced binary runs to completion. Guards the source-driven runtime benches.
    #[test]
    fn bench_harness_source_program_builds_and_runs() {
        // Elaborating a long unary-`Nat` list recurses deeply; run on an 8 MiB stack (the default
        // test thread is ~2 MiB), matching the real CLI's main thread.
        std::thread::Builder::new()
            .stack_size(8 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_bench_src_{}", std::process::id()));
                let main_c = counters_main(64);
                let out = build_run_with_main(
                    &compile_source_to_anf(&list_sum_source(200)),
                    &main_c,
                    &dir,
                    "src_list_sum",
                );
                assert!(
                    out.contains("collections="),
                    "source-compiled list-sum runs to completion; got {out:?}"
                );
            })
            .expect("spawn")
            .join()
            .expect("source-program sanity thread");
    }

    /// Acceptance test for the **dynamic (growable) heap** (spec §7.3): a workload whose *live* set
    /// dwarfs the initial heap must run to completion by *growing* the collector's semi-spaces, not
    /// abort with "heap exhausted". We start the GC with a deliberately tiny **64 KiB** heap and then
    /// allocate a single linked list of 200 000 `BL_CON` nodes held live all at once (~5 MiB), which
    /// cannot remotely fit in 64 KiB. Before the dynamic-heap fix this aborted; now the major
    /// collector reallocates ever-larger semi-spaces and the binary exits 0 with the list fully
    /// intact (`length == 200001`, counting the sentinel) and at least one collection having run
    /// (proving the GC actually engaged — and thus grew — rather than the heap being large enough).
    #[test]
    fn growable_heap_survives_live_set_exceeding_initial_heap() {
        let dir = std::env::temp_dir().join(format!("blight_grow_heap_{}", std::process::id()));
        const NODES: usize = 200_000;
        let out = build_run_with_main(
            &scratch_loop_program(false, 0, 0), // trivial entry program (unused by this main)
            &grow_heap_main(64, NODES),         // 64 KiB initial heap
            &dir,
            "grow_heap",
        );
        assert!(
            parse_collections(&out) > 0,
            "the 5 MiB live set must force the collector (and thus heap growth); got {out:?}"
        );
        assert_eq!(
            parse_length(&out),
            NODES + 1,
            "the entire live list (plus sentinel) must survive every growing collection; got {out:?}"
        );
    }

    /// C3 (Wave 6): the transient-consumption (linearity) analysis substrate
    /// ([`crate::linearity`]), exercised end-to-end against a *real* compiled `.bl` program (not just
    /// the module's own hand-built ANF fixtures) — the differential/observational-invisibility gate
    /// the go-bar asks for.
    ///
    ///   - **the analysis fires on real code**: `foldr` over a `List Nat` compiles to ANF with at
    ///     least one allocation site the analysis proves `Linear` (this is not a vacuous "always
    ///     Shared" analysis — see `crate::linearity`'s own unit corpus for the lattice; this is proof
    ///     the lattice's non-trivial corner is actually reached by the compiler's own output).
    ///   - **identity on the IR**: `linearity::analyze_gated` returns an `AnfProgram` structurally
    ///     `==` to its input — stronger than a binary diff (immune to link-time non-determinism like
    ///     embedded temp paths) and exactly the "this pass changes nothing" contract the module doc
    ///     promises.
    ///   - **identity end-to-end**: building and running both the original ANF and the
    ///     `analyze_gated`-passed ANF (which, per the previous assertion, is the byte-identical value,
    ///     but we still build+run both independently rather than only trust `==`) prints the same
    ///     result.
    #[test]
    fn linearity_analysis_is_observationally_invisible() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_linearity_{}", std::process::id()));
                let anf = compile_source_to_anf(&list_sum_source(50));

                let stats = crate::linearity::analyze(&anf);
                assert!(
                    stats.values().any(|s| s.linear > 0),
                    "a real foldr/list program must exercise at least one Linear allocation site; \
                     stats: {stats:?}"
                );

                let gated = crate::linearity::analyze_gated(anf.clone());
                assert_eq!(
                    gated, anf,
                    "analyze_gated must be the identity transform on the ANF program"
                );

                let main_c = nat_result_counters_main(16);
                let direct = build_run_with_main(&anf, &main_c, &dir, "linearity_direct");
                let through_gate = build_run_with_main(&gated, &main_c, &dir, "linearity_gated");
                assert_eq!(
                    parse_value(&direct),
                    parse_value(&through_gate),
                    "the analysis must not change the observable result; \
                     direct={direct:?} through_gate={through_gate:?}"
                );
            })
            .expect("spawn linearity_analysis_is_observationally_invisible thread")
            .join()
            .expect("linearity_analysis_is_observationally_invisible thread");
    }

    /// C4 (Wave 6) go/no-go re-measurement, pinned as a regression: of the whole `bench/games/*`
    /// corpus, only the `hofold_int.bl`-shaped closure-indirection loop ever forces a real GC
    /// collection, and its per-iteration cost is dominated by a `bl_nat_to_con` materialization of
    /// the structural `Nat` eliminator's scrutinee (a 24-byte `Succ` cell: 16-byte header + one
    /// 8-byte field) — the *generic* fallback for the disabled-by-default M25 zero-allocation `Nat`
    /// peel (`BL_NAT_PEEL`, `llvm.rs::is_nat_eliminator_shape`). This is the evidence behind
    /// `docs/roadmap-post-m6.md`'s "P9.2 header packing — deferred" update: the one workload that
    /// looks like "header overhead binds" is actually dominated by an already-built, currently
    /// gated-off optimization, not by header *layout* — so a header repack is not the highest-leverage
    /// fix here, `BL_NAT_PEEL` is. This test pins the exact, measured mechanism so the finding cannot
    /// silently rot: compiling the *same* small `iterate`/`adder` loop (`hofold_int.bl`'s shape) with
    /// `BL_NAT_PEEL` off (default) vs on must (1) print the identical result, (2) differ in
    /// `bytes_allocated` by **exactly** `fuel * 24` bytes (the materialized `Succ` cell's header +
    /// field, eliminated one-for-one per loop iteration), and (3) never *increase* the collection
    /// count.
    #[test]
    fn nat_peel_removes_the_materialized_succ_cell_hofold_relies_on() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_c4_natpeel_{}", std::process::id()));
                let fuel: u64 = 200; // under the reader's 256 s-expression nesting limit (nat_lit)
                let src = format!(
                    "(load \"std/nat.bl\")\n\
                     (load \"std/int.bl\")\n\
                     (deftotal adder (Pi ((k Int)) (Pi ((a Int)) Int))\n\
                       (lam (k) (lam (a) (int+ a k))))\n\
                     (deftotal iterate (Pi ((fuel Nat) (step (Pi ((a Int)) Int)) (acc Int)) Int)\n\
                       (lam (fuel step acc) (match fuel\n\
                         [(Zero) acc]\n\
                         [(Succ f) (iterate f step (step acc))])))\n\
                     (define fuel Nat {})\n\
                     (define main Int (iterate fuel (adder (int 1)) (int 0)))\n",
                    nat_lit(fuel as usize)
                );
                let anf = compile_source_to_anf(&src);
                let main_c = r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {
  bl_gc_init(16 * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  printf("RESULT value=%lld bytes=%zu collections=%zu\n",
         (long long)bl_int_val(r), bl_gc_bytes_allocated(), bl_gc_collections());
  return 0;
}
"#;
                let without_peel = build_run_with_main(&anf, main_c, &dir, "c4_peel_off");
                // SAFETY (test-only): sets a process-wide env var read only by this pure, synchronous
                // compile step (`llvm::emit_object`'s `is_nat_eliminator_shape` check), immediately
                // restored after.
                unsafe {
                    std::env::set_var("BL_NAT_PEEL", "1");
                }
                let with_peel = build_run_with_main(&anf, main_c, &dir, "c4_peel_on");
                unsafe {
                    std::env::remove_var("BL_NAT_PEEL");
                }

                fn field(s: &str, key: &str) -> u64 {
                    s.split_whitespace()
                        .find_map(|t| t.strip_prefix(key))
                        .and_then(|n| n.parse().ok())
                        .unwrap_or_else(|| panic!("no {key} field in {s:?}"))
                }

                let off_value = field(&without_peel, "value=");
                let on_value = field(&with_peel, "value=");
                assert_eq!(
                    off_value, fuel,
                    "iterate (+1) fuel times from 0 == fuel; got {without_peel:?}"
                );
                assert_eq!(
                    on_value, off_value,
                    "BL_NAT_PEEL must not change the observable result; \
                     off={without_peel:?} on={with_peel:?}"
                );

                let off_bytes = field(&without_peel, "bytes=");
                let on_bytes = field(&with_peel, "bytes=");
                assert!(
                    off_bytes > on_bytes,
                    "the peel must strictly reduce bytes_allocated; off={off_bytes} on={on_bytes}"
                );
                assert_eq!(
                    (off_bytes - on_bytes) / fuel,
                    24,
                    "the peel must save exactly the materialized Succ cell's 24 bytes/iteration \
                     (16 B header + one 8 B field): off={off_bytes} on={on_bytes} fuel={fuel}"
                );

                let off_colls = field(&without_peel, "collections=");
                let on_colls = field(&with_peel, "collections=");
                assert!(
                    on_colls <= off_colls,
                    "the peel must not increase collections; off={off_colls} on={on_colls}"
                );
            })
            .expect("spawn nat_peel_removes_the_materialized_succ_cell_hofold_relies_on thread")
            .join()
            .expect("nat_peel_removes_the_materialized_succ_cell_hofold_relies_on thread");
    }
}
