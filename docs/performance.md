# Blight performance

How fast is Blight, where does the time and memory go, and what are the honest trade-offs? This
doc gives the **cost model**, **measured numbers** from the in-tree benchmark harness, and the
**advantages / disadvantages** of the current implementation. It is descriptive of the bootstrap
implementation in this repo, not a language-design promise.

> All numbers below were measured on an **Apple M2 Pro** (macOS, arm64), `rustc 1.96`, release
> builds, LLVM 18. They are *indicative* — treat the shapes (how a stage scales, whether regions
> avoid the GC) as the durable signal and re-run the harness on your own machine for absolutes.

## 1. Cost model

### Compile pipeline (spec §7)

`blight build` runs a fixed pipeline. The pure-Rust part (everything up to and including ANF) runs
on every build with no LLVM dependency; LLVM emission + `clang` linking is the back half.

```
parse → elaborate → kernel-check → [--recheck] → lower → region::analyze
      → closure::convert → mono::monomorphize → anf::normalize → LLVM IR → object → clang link
```

- **lower** (`Term → Cir`): erases grade-0 content, turns `Elim → Case` and `Later → Fix`, drops
  the type/cubical layer. Roughly linear in term size.
- **region::analyze**: escape analysis over `Cir::Region` scopes; retags non-escaping allocations
  as arena. Cheap (a single structural pass).
- **closure::convert**: lambda-lifts to top-level functions with env records.
- **mono::monomorphize**: whole-program (intra-term) monomorphization. Can duplicate code, so its
  cost grows with how polymorphic the program is.
- **anf::normalize**: ANF + tail-call→jump + delay-trampoline loop. In this implementation it is the
  **most expensive** pure stage on larger inputs and scales **super-linearly** (see numbers below),
  so it is the first place to look if compile time matters.
- **LLVM + clang**: IR is emitted at `OptimizationLevel::Default` (no custom optimization pass
  pipeline), then handed to `clang` to assemble + link against the C runtime objects.

`--recheck` adds a second, independent verification of every kernel-accepted judgement before emit;
it roughly doubles the "front" type-checking cost but buys the two-checkers-agree soundness story.

### Runtime value representation (spec §7.3)

- **Everything is heap-boxed** via `bl_alloc` — there are no unboxed integers in compiled programs
  yet. A value is a header + fields pointer.
- **`Nat` is unary.** It is a `Succ`/`Zero` cons chain, so the numeral *n* is *n* nested heap cells
  and arithmetic is **O(n) allocations** (`plus a b` allocates ~`a` cells, `mult` ~`a·b`). This is
  great for teaching/proof transparency and terrible for big-number crunching.
- **GC**: a precise **generational copying** collector (`runtime/gc.c`) — a nursery plus a
  semi-space old generation, a write barrier for old→young pointers, and shadow-stack roots. The
  heap is a fixed **64 MiB** (the harness uses smaller heaps to force collections); exhaustion
  aborts.
- **`Later`/`Fix` trampoline**: deep guarded recursion runs in **bounded C stack** via `bl_force`
  (the headline "1,000,000-deep delay without overflow" test), but **each step heap-allocates a
  thunk**, so an *n*-deep force is O(n) allocations.
- **Region arenas** (spec §3.5): allocations inside a `(region r …)` scope that the backend escape
  analysis proves non-escaping are bump-allocated in an arena and reclaimed in **O(1)** at scope
  exit — **bypassing the GC entirely**.
- **wasm runtime** (`runtime/wasm_rt.c`): a freestanding **bump allocator with no GC**, and it omits
  `Later`/effects/regions. It is for small, fragment-compatible programs only.

## 2. Measured numbers

### 2a. Compile pipeline (criterion, `benches/pipeline.rs`)

`main = plus n n` over unary `Nat` literals, timing each stage individually and end-to-end. Per-stage
times (median):

| input `n` | lower | region | closure | mono | anf | **end-to-end** |
|---:|---:|---:|---:|---:|---:|---:|
| 8   | ~9.8 µs | ~3.1 µs | ~5.1 µs | ~16.4 µs | ~18.9 µs | **~56 µs** |
| 32  | ~24.6 µs | ~7.8 µs | ~10.1 µs | ~37.8 µs | ~143 µs | **~227 µs** |
| 128 | ~91 µs | ~28 µs | ~32 µs | ~128 µs | ~1.87 ms | **~2.15 ms** |

Takeaways: the pipeline is fast in absolute terms for normal-sized programs (tens to hundreds of
µs), **ANF dominates and grows super-linearly**, and the front stages (lower/region/closure) stay
roughly linear. If you feed it pathologically large unary literals, ANF is what you feel first.

### 2b. Runtime + memory (criterion, `benches/runtime.rs`, `--features llvm`)

The headline workload is a counted scratch loop that allocates per-iteration garbage either **on the
GC heap** or **in a region arena**, run on a deliberately small 8 MiB heap. Memory counters from the
runtime (`bl_gc_collections()`):

| workload (depth 300, 256 scratch tuples/iter, 8 MiB heap) | GC collections |
|---|---:|
| scratch on the **GC heap** | **2** (forced to collect) |
| identical scratch in a **region arena** | **0** (reclaimed in O(1), never collects) |

This is the proof that **regions bypass the collector** — the same property the
`region_workload_bypasses_gc` acceptance test and the `bench_harness_region_bypasses_gc_and_heap_collects`
sanity test assert. Binary wall-clock for the two variants (these are short programs, so a large
constant is process spawn; the *difference* is the signal):

| depth | GC-heap run | region run |
|---:|---:|---:|
| 200 | ~1.27 ms | ~1.19 ms |
| 800 | ~1.73 ms | ~1.51 ms |

The region variant is consistently faster and the gap widens with allocation pressure, because it
does zero collection work.

### 2c. End-to-end build + run (hyperfine, `bench/run.sh`)

Wall-clock over the buildable examples, measured with hyperfine 1.20 on the reference machine (Apple
Silicon, macOS). "Compile" is the full `blight build` (parse → elaborate → check → lower → LLVM IR →
object → `clang` link); "Run" is the produced native binary. Indicative, not a leaderboard:

| example | output | compile (`blight build`) | run (binary) |
|---|---:|---:|---:|
| `hello_nat.bl` | 7 | ~263 ms | ~1.1 ms |
| `containers.bl` | 2 | ~256 ms | ~0.97 ms |
| `list_sum.bl` | 6 | ~268 ms | ~0.94 ms |
| `fib.bl` | 13 | ~258 ms | ~0.97 ms |
| `minmax.bl` | 7 | ~264 ms | ~0.94 ms |
| `vec_head.bl` | 3 | ~258 ms | ~0.95 ms |
| `either_compute.bl` | 4 | ~257 ms | ~0.95 ms |
| `region_scratch.bl` | 2 | ~257 ms | ~0.95 ms |

Two things stand out. First, **compile time is ~0.26 s and essentially flat** across these examples:
it is dominated by a fixed cost (LLVM module setup + `clang` invocation to link the runtime), not by
the size of these small programs, so they all land within a few percent of each other. Second, **run
time is sub-millisecond and also flat** — for programs this small the binary's wall-clock is almost
entirely process spawn, so the differences are within noise. The runtime *signal* (where the cost
model actually shows up) is the GC-vs-region counter comparison in 2b, not these spawn-dominated
totals.

## 3. Advantages

- **Tiny trusted kernel + independent re-checker.** Soundness rests on two small checkers agreeing
  (`--recheck`), not one large trusted compiler. The whole backend is untrusted: a miscompilation
  can give a wrong answer but can never mint a false `Proof`.
- **Bounded-stack deep recursion.** The `Later`/`Fix` trampoline runs arbitrarily deep guarded
  recursion in constant C stack (the million-deep test), so you don't blow the native stack.
- **O(1) region reclamation.** `(region r …)` scratch is arena-allocated and freed in one pointer
  reset, demonstrably bypassing the GC (table 2b).
- **Precise GC.** Generational copying with precise shadow-stack roots and a write barrier — no
  conservative scanning, no leaked-via-misidentified-pointer during a run.
- **`musttail` tail calls.** General tail calls compile to `tailcc` + `musttail`, so loops are real
  jumps (verified by `tailcc_musttail_on_general_tail`).
- **Fast pipeline for normal programs.** Tens-to-hundreds of µs through the whole pure pipeline for
  realistic inputs.

## 4. Disadvantages / honest caveats

- **Unary `Nat` ⇒ O(n) allocation arithmetic.** There are no unboxed machine integers in compiled
  programs yet; numerals are cons chains. Fine for proofs and small values, unsuitable for heavy
  numeric work.
- **Everything is boxed.** No unboxed scalars or flattened records; every value is a heap object.
- **No LLVM optimization pipeline.** IR is emitted at `OptimizationLevel::Default` with no custom
  pass pipeline, leaning on `clang` for the rest. There is headroom left on the table.
- **Per-step thunk allocation in the trampoline.** Bounded *stack*, but O(n) *heap* for an n-deep
  force.
- **ANF is the pipeline bottleneck** and scales super-linearly on large inputs (table 2a).
- **Fixed 64 MiB heap.** Exhaustion aborts; there is no heap growth policy yet.
- **wasm runtime is minimal.** Bump allocator, no GC, and no `Later`/effects/regions — only small
  fragment-compatible programs target wasm today.

## 5. How to reproduce

Pure-Rust compile-pipeline microbenchmarks (no LLVM needed):

```bash
cargo bench -p blight-codegen --bench pipeline
```

Runtime / memory benchmarks (needs the `llvm` feature, LLVM 18, and `clang`):

```bash
export LLVM_SYS_181_PREFIX="$(brew --prefix llvm@18)"   # macOS/Homebrew
cargo bench -p blight-codegen --features llvm --bench runtime
```

The runtime bench's invariants are guarded by a unit test that runs with the normal test suite:

```bash
cargo test -p blight-codegen --features llvm bench_harness_region
```

End-to-end wall-clock over the buildable examples with [hyperfine](https://github.com/sharkdp/hyperfine)
(optional; install hyperfine first):

```bash
bench/run.sh
```

It builds a release `blight --features llvm` and reports (1) `blight build` compile time and
(2) produced-binary run time per example, as markdown tables.

## 6. See also

- [benchmarks-game.md](benchmarks-game.md) — a "Benchmarks Game"–style writeup: Blight-vs-Blight
  scaling tables (compile pipeline, region-vs-GC, list/tree algorithms, the 1M-deep trampoline) plus
  one loudly-caveated cross-language table against C and Python.
- [roadmap.md](roadmap.md) — what each missing capability (unboxed `Int`/`Float`, I/O, arrays,
  growable heap, FFI, a frame loop) would cost and whether it touches the trusted kernel.
