# Blight benchmarks game

A "Benchmarks Game"–style writeup for Blight — but an *honest* one. Blight is a correctness-first,
proof-carrying language whose trusted kernel ([`crates/blight-kernel`](../crates/blight-kernel))
has **no primitive types**: `Nat` is unary (`Succ`/`Zero`), every value is heap-boxed, and there
are no unboxed machine integers. So a naïve "sum 10⁸ ints in a tight loop vs C" comparison would be
a strawman that says nothing interesting. Instead this doc does two things:

1. **Blight-vs-Blight scaling tables** — input size × strategy (GC vs region, structural depth).
   This is the durable, reproducible signal: how the implementation *scales*, which is what a
   benchmarks game is actually about.
2. **One loudly-caveated cross-language table** — a single structural workload against C and Python,
   stated with the orders-of-magnitude correctness-first trade-off up front, to satisfy the
   benchmarks-game itch without pretending the comparison is apples-to-apples.

> All numbers measured on an **Apple M2 Pro** (macOS, arm64), release builds, LLVM 18, criterion
> medians / hyperfine means. Treat the **shapes** (how a workload scales, whether regions beat the
> GC) as the signal; re-run the harness for absolutes on your machine. Numbers here are from the
> in-tree benches `crates/blight-codegen/benches/{pipeline,runtime}.rs` and `bench/run.sh`.

## Methodology

- **Compile-pipeline benches** (`benches/pipeline.rs`, pure Rust, no LLVM): generate a program of a
  given size, time each pure stage (`lower → region → closure → mono → anf`) and end-to-end. These
  chart how the **compiler** scales with program size.
- **Runtime benches** (`benches/runtime.rs`, `--features llvm`): compile a real `.bl` program all
  the way to a native binary, then time the binary and read the runtime memory counters
  (`bl_gc_collections()`, arena allocs). These chart how the **produced program** scales.
- **Sanity tests**: every invariant-bearing bench has a `#[test]` that runs in the normal suite
  (e.g. `bench_harness_region_bypasses_gc_and_heap_collects`,
  `bench_harness_source_program_builds_and_runs`), so the workloads can't silently rot.
- **Deep-recursion headline** is verified by the standalone runtime test
  `million_deep_via_delay_no_overflow_and_gc_collects_under_pressure` (a real 1,000,000-step
  `bl_force`), discussed in "Deep recursion" below.

Workloads are kept inside Blight's supported fragment, and sizes are bounded by two real ceilings:
the **unary-`Nat`** cost (a literal of size *n* is *n* heap cells and *n*-deep to compile) and the
**process call stack** (non-tail structural recursion descends the spine on the C stack of the
produced binary). Where you see a modest cap, that ceiling — not an arbitrary choice — is why.

## Blight-vs-Blight: compile-pipeline scaling

`main` is built from a unary-`Nat` workload of size `n`; we time the pure pipeline. The headline is
that **ANF normalization dominates and scales super-linearly**, while the front stages stay roughly
linear. (`benches/pipeline.rs`; medians.)

### `plus n n`, per stage

| `n` | lower | region | closure | mono | **anf** | end-to-end |
|---:|---:|---:|---:|---:|---:|---:|
| 8   | 9.6 µs | 3.0 µs | 5.0 µs | 16 µs | **18 µs** | 54 µs |
| 32  | 23 µs | 7.8 µs | 9.8 µs | 36 µs | **139 µs** | 220 µs |
| 128 | 82 µs | 27 µs | 30 µs | 126 µs | **1.79 ms** | 2.06 ms |
| 256 | 163 µs | 53 µs | 56 µs | 242 µs | **7.19 ms** | 7.71 ms |
| 512 | 323 µs | 106 µs | 110 µs | 487 µs | **30.1 ms** | 31.2 ms |

ANF from `n`=256→512 goes 7.19 ms → 30.1 ms: input ×2, time ×4.2 — clearly **super-linear** (the
end-to-end column tracks it because ANF is the bulk). The front stages (`lower`/`region`/`closure`)
roughly double for a doubled input, as expected.

### Structural workloads, end-to-end pipeline

| workload | `n` | end-to-end compile |
|---|---:|---:|
| `list_length` | 8 | 57 µs |
| | 32 | 275 µs |
| | 128 | 2.80 ms |
| | 256 | 10.8 ms |
| | 512 | 41.2 ms |
| `list_reverse` | 8 | 117 µs |
| | 32 | 380 µs |
| | 128 | 3.15 ms |
| | 256 | 11.5 ms |
| `tree_sum` | 8 | 1.11 ms |
| | 32 | 4.61 ms |
| | 96 | 17.9 ms |
| | 192 | 48.4 ms |

`list_length` 256→512 = 10.8 ms → 41.2 ms (×2 input, ×3.8 time): the same super-linear ANF curve.
`tree_sum` carries a larger constant because building the tree literal threads `tree-insert` and the
fold is doubly-recursive.

**Takeaway:** for normal-sized programs the whole pure pipeline is tens-to-hundreds of µs; the first
thing you feel on pathologically large unary literals is ANF. This is the honest cost of unary `Nat`
plus a normalization pass that isn't yet linear.

## Blight-vs-Blight: runtime scaling

Programs compiled to native binaries and timed (`benches/runtime.rs`, `--features llvm`). These run
fully (no laziness) and chart **algorithmic** scaling — the part that *is* legitimately comparable.

### Region arena vs GC heap (the clean cross-strategy story)

An identical counted scratch loop allocates per-iteration garbage either on the GC heap or in a
`(region r …)` arena, on a deliberately small 8 MiB heap. Memory counters:

| depth, 256 scratch tuples/iter, 8 MiB heap | GC collections |
|---|---:|
| scratch on the **GC heap** | **> 0** (forced to collect) |
| identical scratch in a **region arena** | **0** (reclaimed O(1), never collects) |

This is the `region_workload_bypasses_gc` invariant, asserted in-bench before the timings are
trusted. Binary wall-clock for the two strategies as allocation pressure rises (128 scratch
tuples/iter):

| depth | GC-heap run | region run | region speedup |
|---:|---:|---:|---:|
| 200  | 1.06 ms | 0.97 ms | ~1.10× |
| 800  | 1.57 ms | 1.35 ms | ~1.16× |
| 3200 | 3.57 ms | 3.03 ms | ~1.18× |

The region variant is consistently faster and **the gap widens with allocation pressure**, because
it does zero collection work — the headline region property as a measured curve.

### List / tree algorithms

`foldr`-sum over an `n`-element `List Nat`; `length (reverse xs)`; structural `tree-sum` over an
`n`-node `Tree Nat`. Binary wall-clock (run cost):

| workload | `n` | run |
|---|---:|---:|
| `list_sum` (`foldr`) | 100 | 0.83 ms |
| | 300 | 0.85 ms |
| | 800 | 0.91 ms |
| `list_reverse` (TCO reverse + length) | 100 | 0.83 ms |
| | 300 | 0.87 ms |
| | 800 | 0.90 ms |
| `tree_sum` (double recursion) | 50 | 1.01 ms |
| | 100 | 1.54 ms |
| | 200 | 3.71 ms |

The list workloads are dominated by a ~0.8 ms fixed process-spawn cost at these sizes, so they look
nearly flat — the *algorithmic* cost is small relative to spawning a process. `tree_sum` climbs
visibly (50→200: 1.0 → 3.7 ms) because it allocates a tree *and* does doubly-recursive unary `plus`
at every node. Sizes are capped where the produced binary's **non-tail structural recursion**
approaches the process stack limit (a skewed tree near `n`≈300 overflows the 8 MiB C stack) — itself
an honest data point about boxed unary structural recursion.

### Deep recursion via the delay trampoline

The marquee property — **deep guarded recursion in bounded C stack** — is verified directly at the
runtime layer rather than as a compiled-Blight microbench, and for a specific honest reason. The
runtime test
[`million_deep_via_delay_no_overflow_and_gc_collects_under_pressure`](../crates/blight-codegen/src/runtime.rs)
builds a **1,000,000-step** `Later` chain and drives it with `bl_force`: it completes without a
stack overflow, on a 1 MiB heap, while the GC collects under pressure and preserves live roots.

Why not a compiled `.bl` countdown of a million? Because a compiled countdown counts a **unary
`Nat`**, so feeding the trampoline a million-deep chain means first *materializing a million-deep
`Nat` value* — that is the unary-cost story (a million heap cells, a million-deep compile), not the
trampoline's. The runtime test isolates the trampoline using an O(1) integer counter in C, which is
exactly the property we want to measure: **the force loop is O(1) C stack at any depth** (it is
O(n) *heap*, one thunk per step). See [performance.md](performance.md) §1 for the cost model.

## The one cross-language table (read the caveats first)

> **Caveats, stated up front.** (1) Blight has **no machine integers** — this sums unary `Nat`s
> (heap-boxed cons cells), so the per-element constant is enormous compared to a register add. (2)
> The task is tiny on purpose (sum 800 small numbers); at this size *every* contender is dominated
> by **process startup**, which is why Blight and C look close — that similarity is an artifact of
> spawn cost, **not** evidence Blight matches C on arithmetic. (3) Push `n` up and Blight's unary
> cost diverges by orders of magnitude. This table exists to be honest about where Blight stands,
> not to claim a win.

Task: sum `i % 3` for `i` in `0..800`, as a standalone program, timed end-to-end with hyperfine
(`-N`/warmup), reference machine.

| language | program | mean wall-clock | notes |
|---|---|---:|---|
| **C** (`clang -O2`) | `for` loop, `long` accumulator | **~0.84 ms** | register arithmetic; ~all of it is process spawn |
| **Blight** | `foldr plus` over `List Nat` (800 cons cells, unary) | **~0.91 ms** | boxed unary; spawn-dominated *at this size only* |
| **Python 3.11** | `sum(i%3 for i in range(800))` | **~18.5 ms** | interpreter startup dominates |

What this actually shows: for a **small, spawn-dominated** task, Blight's AOT-compiled native binary
is in the **same ballpark as C** and ~20× faster to *start-and-finish* than CPython — because all
three are paying startup, and Blight pays it as a real compiled binary rather than a VM boot. It
does **not** show Blight is as fast as C on arithmetic; increase the input and Blight's unary `Nat`
cost (O(n) allocations) pulls away from C's O(1)-per-add by orders of magnitude. The durable
comparisons are the Blight-vs-Blight scaling tables above.

## Reproduction

Compile-pipeline microbenches (pure Rust, no LLVM):

```bash
cargo bench -p blight-codegen --bench pipeline
```

Runtime / memory benches (needs `llvm`, LLVM 18, `clang`):

```bash
export LLVM_SYS_181_PREFIX="$(brew --prefix llvm@18)"   # macOS/Homebrew
cargo bench -p blight-codegen --features llvm --bench runtime
```

The bench invariants run in the normal test suite:

```bash
cargo test -p blight-codegen --features llvm bench_harness
cargo test -p blight-codegen --features llvm million_deep   # the 1M-deep trampoline headline
```

End-to-end build + run wall-clock over the buildable examples (needs
[hyperfine](https://github.com/sharkdp/hyperfine)):

```bash
bench/run.sh
```

The cross-language row was produced with a one-off C/Python `sum(i%3 for i in 0..800)` timed under
the same hyperfine; reproduce with any equivalent trivial program.

## See also

- [performance.md](performance.md) — cost model, advantages/disadvantages, the per-stage and
  region-vs-GC numbers in narrative form.
- [roadmap.md](roadmap.md) — what unboxed `Int`/`Float`, I/O, arrays, and "can we build games?"
  would cost, and which of them touch the trusted kernel.
