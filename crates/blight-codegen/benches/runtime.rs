//! Runtime / memory benchmarks (spec §7.3/§7.4): build representative programs to native binaries
//! and measure (i) wall-clock of the produced binary and (ii) the runtime memory counters
//! (`bl_gc_collections()`, `bl_arena_alloc_count()`). Requires the `llvm` feature + a system LLVM
//! 18 and `clang`: `cargo bench -p blight-codegen --features llvm --bench runtime`.
//!
//! The headline workload is the region-vs-GC scratch loop (the same one the
//! `region_workload_bypasses_gc` acceptance test and the `bench_harness_*` sanity test use): an
//! identical loop allocates per-iteration scratch either in a region arena (reclaimed in O(1), no
//! GC) or on the GC heap (forces collections). Benching both shows the cost the collector adds and
//! the win regions buy.

use blight_codegen::driver::bench_support::compile_source_to_anf;
use blight_codegen::driver::bench_support::{
    build_run_with_main, counters_main, list_reverse_source, list_sum_source, parse_collections,
    scratch_loop_program, tree_sum_source,
};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

fn work_dir() -> std::path::PathBuf {
    let d = std::env::temp_dir().join(format!("blight_bench_runtime_{}", std::process::id()));
    std::fs::create_dir_all(&d).expect("create bench work dir");
    d
}

/// A plain `main` that runs `bl_program_entry` and exits — no counters, used for the algorithm
/// workloads where we only want wall-clock of the produced binary.
fn plain_main(heap_mib: usize) -> String {
    format!(
        r#"
#include "blight_rt.h"
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init({heap_mib} * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  (void)r;
  return 0;
}}
"#
    )
}

/// Build (and run once) a program on a 512 MiB stack: `emit_object`/codegen recurses over the
/// program's tail chain, so a deep entry needs more than the default thread stack. Returns the
/// produced binary's stdout (it is left on disk at `<work>/<name>` for re-running).
fn build_on_big_stack(
    prog: blight_codegen::AnfProgram,
    main_c: String,
    work: std::path::PathBuf,
    name: &str,
) -> String {
    let name = name.to_string();
    std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || build_run_with_main(&prog, &main_c, &work, &name))
        .expect("spawn build thread")
        .join()
        .expect("build thread")
}

fn bench_runtime(c: &mut Criterion) {
    let work = work_dir();
    let main_c = counters_main(8); // 8 MiB heap so the GC-heap variant is forced to collect

    // Report the GC/arena counters once (not a timing) so the doc can cite concrete numbers, and
    // assert the bypass invariant holds before trusting the timings.
    {
        let depth = 300usize;
        let scratch = 256usize;
        let gc = build_run_with_main(
            &scratch_loop_program(false, depth, scratch),
            &main_c,
            &work,
            "report_gc",
        );
        let arena = build_run_with_main(
            &scratch_loop_program(true, depth, scratch),
            &main_c,
            &work,
            "report_arena",
        );
        let gc_n = parse_collections(&gc);
        let arena_n = parse_collections(&arena);
        eprintln!(
            "runtime counters (depth={depth}, scratch/iter={scratch}, 8 MiB heap): \
             GC-heap collections={gc_n}, region/arena collections={arena_n}"
        );
        assert!(gc_n > 0 && arena_n == 0, "region bypass invariant holds");
    }

    // Region-vs-GC scratch loop, widened to more depths (the one workload with a clean
    // cross-strategy story). Time the produced binaries (run cost, not compile).
    let mut group = c.benchmark_group("runtime/scratch_loop_run");
    for &depth in &[200usize, 800, 3200] {
        let scratch = 128usize;
        let gc_prog = scratch_loop_program(false, depth, scratch);
        let arena_prog = scratch_loop_program(true, depth, scratch);

        let gc_name = format!("run_gc_{depth}");
        let arena_name = format!("run_arena_{depth}");
        let _ = build_run_with_main(&gc_prog, &main_c, &work, &gc_name);
        let _ = build_run_with_main(&arena_prog, &main_c, &work, &arena_name);
        let gc_bin = work.join(&gc_name);
        let arena_bin = work.join(&arena_name);

        group.bench_with_input(BenchmarkId::new("gc_heap", depth), &depth, |b, _| {
            b.iter(|| {
                std::process::Command::new(&gc_bin)
                    .output()
                    .expect("run gc binary")
            })
        });
        group.bench_with_input(BenchmarkId::new("region", depth), &depth, |b, _| {
            b.iter(|| {
                std::process::Command::new(&arena_bin)
                    .output()
                    .expect("run region binary")
            })
        });
    }
    group.finish();

    // Deep recursion via the delay trampoline is exercised authoritatively by the standalone
    // runtime test `million_deep_via_delay_no_overflow_and_gc_collects_under_pressure` (a real
    // 1,000,000-step `bl_force` in bounded C stack). It is *not* duplicated as a compiled-Blight
    // criterion bench here: a compiled countdown counts a **unary `Nat`**, so feeding the trampoline
    // a million-deep chain means first materializing a million-deep `Nat` value — the unary-cost
    // story, not the trampoline's. See docs/benchmarks-game.md for the framing and that test for the
    // bounded-stack measurement.

    // Real `.bl` algorithm workloads (list/tree), built from source through the full backend. These
    // run fully (no delay) and chart algorithmic scaling that *is* legitimately comparable. Builds
    // go through `build_on_big_stack` since codegen recurses over the (deep, unary) list/tree
    // literal; sizes are kept modest because the *produced* binary's structural recursion (e.g.
    // non-tail `foldr`/`length`) also descends the spine on the process stack.
    let mut group = c.benchmark_group("runtime/list_sum");
    let pmain = plain_main(64);
    for &n in &[100usize, 300, 800] {
        let name = format!("list_sum_{n}");
        let _ = build_on_big_stack(
            compile_source_to_anf(&list_sum_source(n)),
            pmain.clone(),
            work.clone(),
            &name,
        );
        let bin = work.join(&name);
        group.bench_with_input(BenchmarkId::new("run", n), &n, |b, _| {
            b.iter(|| std::process::Command::new(&bin).output().expect("run"))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("runtime/list_reverse");
    for &n in &[100usize, 300, 800] {
        let name = format!("list_reverse_{n}");
        let _ = build_on_big_stack(
            compile_source_to_anf(&list_reverse_source(n)),
            pmain.clone(),
            work.clone(),
            &name,
        );
        let bin = work.join(&name);
        group.bench_with_input(BenchmarkId::new("run", n), &n, |b, _| {
            b.iter(|| std::process::Command::new(&bin).output().expect("run"))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("runtime/tree_sum");
    for &n in &[50usize, 100, 200] {
        let name = format!("tree_sum_{n}");
        let _ = build_on_big_stack(
            compile_source_to_anf(&tree_sum_source(n)),
            pmain.clone(),
            work.clone(),
            &name,
        );
        let bin = work.join(&name);
        group.bench_with_input(BenchmarkId::new("run", n), &n, |b, _| {
            b.iter(|| std::process::Command::new(&bin).output().expect("run"))
        });
    }
    group.finish();
}

criterion_group!(benches, bench_runtime);
criterion_main!(benches);
