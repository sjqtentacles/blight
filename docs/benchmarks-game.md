# Blight benchmarks game

A "Benchmarks Game"–style writeup for Blight — but an *honest* one. Blight is a correctness-first,
proof-carrying language whose trusted kernel ([`crates/blight-kernel`](../crates/blight-kernel)) is
deliberately minimal: `Nat` is **unary** (`Succ`/`Zero`), and the *only* primitive numeric base type
is the one reviewed `Int` (M10). Compiled values are heap-boxed by default, with M21 tagged-pointer
immediates the exception (machine-word `Nat`/`Int` and nullary constructors ride unboxed in the
pointer). So a naïve "sum 10⁸ unary `Nat`s in a tight loop vs C" comparison would be a strawman that
says nothing interesting. Instead this doc does two things:

1. **Blight-vs-Blight scaling tables** — input size × strategy (GC vs region, structural depth).
   This is the durable, reproducible signal: how the implementation *scales*, which is what a
   benchmarks game is actually about.
2. **One loudly-caveated cross-language table** — structural workloads against C/Rust/OCaml/Haskell/
   Python: the register-bound fib/sum/factorial loops, an alloc-churn `treesum`, a linear-list
   `listfold`, and a compute/recursion `binrec` — stated with the orders-of-magnitude
   correctness-first trade-off up front, to satisfy the benchmarks-game itch without pretending the
   comparison is apples-to-apples.

Both axes — **how fast** and **how memory-efficient** — are reported. Beyond wall-clock, the harness
records a startup-adjusted **RSS delta** (peak RSS minus a per-language near-empty baseline, so the
process/interpreter floor is subtracted out) and, for the Blight rows, a **memory detail** table read
straight from the runtime's `BL_GC_STATS` counters (**bytes allocated**, **GC collections**, **promoted
bytes**). These last three are Blight-specific — no other runtime here exposes a uniform equivalent —
so they live in a Blight-only subsection, not the shared table.

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
**process call stack** (multi-recursive-field *tree* structural recursion still descends on the C
stack of the produced binary — linear folds are lifted to O(1) native stack by P3's elim-loop
transform, see caveat 5). Where you see a modest cap, that ceiling — not an arbitrary choice — is why.

## Blight-vs-Blight: compile-pipeline scaling

`main` is built from a unary-`Nat` workload of size `n`; we time the pure pipeline. The headline is
that **ANF normalization dominates and scales super-linearly**, while the front stages stay roughly
linear. (`benches/pipeline.rs`; medians.)

> **Post-M29 note.** The super-linear ANF curve below was an **O(n²) de Bruijn re-shift**: lowering
> `seq`/`Let`/`Case` eagerly rebuilt whole subtrees to fix indices. M29 replaced that with a
> *deferred* `Shift` applied once at `Var` leaves plus a streamed bind accumulator, making
> normalization linear (the `deep_let_chain_normalizes_linearly` scaling test went from ~48-75× to
> <30× for an 8× deeper input). The tables in this section predate that fix and are kept as the
> historical "this is the bottleneck M29 removed" record — re-run `cargo bench --bench pipeline` for
> current numbers.

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

**Takeaway:** for normal-sized programs the whole pure pipeline is tens-to-hundreds of µs; the rows
above are the **pre-M29** profile where ANF's O(n²) re-shift dominated on large unary literals. M29
made that pass linear (see the post-M29 note above), so on current builds the front stages and ANF
scale together; unary `Nat` literal size remains the real ceiling.

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

### Unary `Nat` vs primitive machine `Int` (the cost of *not* having unboxed integers)

Blight's kernel has no primitive numbers — `Nat` is unary `Succ`/`Zero` — but it *does* ship an
optional primitive `Int` base type (`(int N)` literals + `int+ int- int* int/ int= int<`, reducing
definitionally and lowering to single hardware instructions; see
[std/int.bl](../crates/blight-prelude/std/int.bl) for the named wrappers and the deliberate
"`Int` has no eliminator" TCB note). The same summation workload —
`sum (1..n)`, a fuel-counted loop accumulating `acc + i` — written once over unary `Nat`
([bench/games/sum/sum_nat.bl](../bench/games/sum/sum_nat.bl) shape) and once over `Int`
([bench/games/sum/sum_int.bl](../bench/games/sum/sum_int.bl) shape,
[examples/int_sum.bl](../examples/int_sum.bl) the `foldr` variant) shows the gap directly. Binary
wall-clock (hyperfine `-N`, warmup; reference machine), result is `n(n+1)/2`:

| `n` | result | **`Nat`** run | **`Int`** run |
|---:|---:|---:|---:|
| 100  | 5 050     | ~4.0 ms | ~2.9 ms |
| 400  | 80 200    | ~13.2 ms | ~3.2 ms |
| 1000 | 500 500   | **crashes** (SIGBUS) | ~3.1 ms |
| 2500 | 3 126 250 | **crashes** (SIGBUS) | ~4.1 ms |

Two honest findings. First, **`Int` is flat** (~3 ms, spawn-dominated) as the accumulator grows from
5 050 to 3.1 million: each `+` is one O(1) register add on an unboxed 64-bit value, so the magnitude
of the numbers is free. Second, **unary `Nat` both slows and then hits a hard ceiling**: 100→400 is
already ×3.3 in run time (it must allocate and later walk an 80 200-deep `Succ` chain), and by
`n`=1000 the result is a **500 500-deep `Succ` value** whose construction/printing overflows the
produced binary's C stack (exit 138 / SIGBUS) — the unary representation is not just slower, it
*cannot represent* a moderately large number without a deep heap chain. This is the precise reason
`sum_nat.bl`'s own golden caps at `n`=10 while `sum_int.bl` runs to `n`=1000: the unary tower is for
*proofs and small values*, and `Int` is the escape hatch when you need arithmetic at scale (at the
cost of growing the trusted kernel by a primitive base type — a tracked TCB decision, see
[roadmap.md](roadmap.md)).

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

## Multicore: share-nothing worker-pool scaling (M15-M19)

The most recent runtime work added share-nothing multicore. Each OS-thread worker has its own
thread-local heap/stack, the native worker pool runs independent computations in parallel, and
messages cross worker heaps by structural copy of immutable values. This is the one place Blight's
"everything is immutable" design pays an unambiguous performance dividend: no shared mutable state
means it parallelizes with no locks on the allocation/GC hot path.

Workload: 16 heavy independent tasks (each a real compute + GC-churn loop on its own 256 KiB heap),
run across pools of 1/2/4/8 workers. The reduced result is identical at every pool size (the hard
determinism gate); only the wall-clock changes. Reference 10-core Apple-silicon host, via
`bench/multicore.sh`:

| workers | wall time | speedup vs 1 |
|---|---:|---:|
| 1 | ~91-95 ms | 1.00x |
| 2 | ~42-45 ms | ~2.1x |
| 4 | ~22-24 ms | ~3.7-4.4x |
| 8 | ~15-18 ms | ~5.0-6.4x |

The 1-worker baseline already pays the per-task serialize/deserialize cost, so the speedup measures
parallelism, not setup savings. The whole pool is ThreadSanitizer-clean (`BL_TSAN=1`).

**Serializer throughput** (the cross-heap / cross-machine message primitive): a 2000-node cons-list
serializes to a ~64 KB blob and round-trips (serialize + deserialize + fresh allocation) at roughly
**~280-330 MB/s (~190-220 us/op)** on the same host. This is the rate at which the worker pool and
the `blight-net` distributed transport move data between heaps. The same data-only blobs cross
*machines* too: the M24 distributed-actor addressing layer (`NodeId`/`Router`) routes `std/actor.bl`
`send`/`receive` over per-node TCP transports, proven by a two-separate-OS-process ping/pong over
loopback (`two_process_pingpong_over_loopback_tcp`).

Honest framing: absolute numbers are host- and load-dependent; super-linear rows at 2/4 workers are
cache/GC effects. Messages are **data-only** (closures are rejected), and the `std/actor.bl` actor
surface still runs single-core from `.bl` — the multicore path is the C worker pool. None of it grows
the trusted base.

## The cross-language table (read the caveats first)

> **Caveats, stated up front.** (1) **Two Blight rows per problem.** *Blight-Int* uses the native
> machine `Int` (one tagged word, O(1) arithmetic — M21 unboxing). *Blight-Nat* uses the **inductive**
> `Zero`/`Succ` `Nat`; the **M20** recognizer rewrites the prelude `plus`/`mult` to an O(1)
> machine-word op (`bl_nat_*`) *when every operand is a settled value* (a variable, a literal, a nested
> recognized op). With the recognizer off, the scaled `_nat.bl` programs below **overflow the root
> stack** (the generic O(n) `Succ`-chain eliminator) — so these rows exist *only because M20 fires*.
> (2) **Where M20 does and does not reach.** `fib(30)` carries `(plus a b)` over two `match`-bound
> variables, so every step is recognized and the result is a single `BL_NAT` word — Blight-Nat lands
> right next to C. `sum(1000)` recognizes each `plus`, and the loop carries its running index as its
> own `Nat` accumulator advanced by `(plus idx one)` (var + literal, recognized), so the 1000-deep
> structural recursion over `fuel`/`idx`/`acc` runs at register speed and the result is a single
> `BL_NAT` word — Blight-Nat is now ~1.2 ms / ~2.4 MB, **not** the ~42 ms / ~11 MB of the earlier
> `Succ`-rebuilding shape (a measured correction; `sum_nat.bl` was rewritten to the accumulator form).
> `factorial`'s `mult (Succ k) …` has a **non-canonical** first operand, so `mult` falls back to the
> O(n) chain; unary factorial(20) is 2.4-quintillion-deep and intractable, so Blight-Nat stays at its
> own n=5 golden (`120`) — the documented "where unary genuinely can't go" point. (3) **These tasks are
> tiny on purpose**; at this size *every* native contender is partly **process-startup**-dominated,
> which is why C/Rust/OCaml/Blight-Int cluster within ~2×. The durable signals are the cross-language
> *shape* and the Int-vs-Nat contrast, both of which the harness reproduces. (4) **Memory columns.**
> *Peak RSS* is the OS high-water mark; *RSS delta* subtracts a per-language near-empty baseline
> (`bench/games/_baseline/`) so the process/interpreter floor is removed; the Blight-only memory-detail
> table reads the runtime's `BL_GC_STATS` (`bytes allocated`/`collections`/`promoted bytes`). At the
> register-bound sizes the deltas are dominated by Blight's initial GC nursery (~tens of KiB), and only
> `treesum` moves it meaningfully — `binrec`'s "per-call-closure churn" was the pre-C1 story (see below;
> both fusion and the elim-loop worklist transform have since collapsed it to near-zero allocation too).
> (5) **Why these four shapes.** `treesum` (tree alloc-churn) and `binrec` (compute / native-recursion
> overhead) are only *d*-deep call trees, so they scale freely; `listfold` and the fib/sum loops are
> *linear*-depth recursion. As of
> **P3, the elim-loop transform** ([`crates/blight-codegen/src/elimloop.rs`](../crates/blight-codegen/src/elimloop.rs)) makes structural
> recursion **O(1) native stack** for two shapes. **(3a)** rewrites a *tail-accumulator* catamorphism —
> a function-typed-motive eliminator whose induction hypothesis is used once, in tail position,
> saturated to its accumulators (exactly the `sum`/`fuel`/`idx`/`acc` loop) — into a bounded-stack
> `Tail::Jump` loop (verified at `n = 10^6` by `elim_accumulator_recursion_is_stack_safe`). **(3b)**
> rewrites a *non-tail linear* fold — a single-recursive-field, nullary-base eliminator whose IH is
> consumed by a combiner (`listfold`'s `foldr`, a `Succ (f k)`-style fold) — by a reverse-then-fold
> decomposition ([`crates/blight-codegen/src/elimworklist.rs`](../crates/blight-codegen/src/elimworklist.rs)) into two tail-accumulator
> catamorphisms the (3a) loop then makes bounded-stack (verified at `n = 10^6` by
> `elim_nontail_linear_fold_is_stack_safe`). What remains capped is **multi-recursive-field (tree)**
> recursion (`treesum`, a skewed binary tree): the produced binary still descends the tree on the C
> stack and a skewed tree overflows around ~5·10⁴ frames (the heap-worklist transform that lifts the
> tree case is future work; the trampoline is how you go deep meanwhile), so those sizes are capped
> accordingly. `primes`/Collatz are deliberately absent: they branch on integer divisibility/parity,
> which needs an `Int → Bool` eliminator the kernel intentionally lacks (std/int.bl) — `binrec`
> branches on a structural `Nat` instead. A naïve doubly-recursive **Fibonacci** is also avoided: it
> recurses on two *nested-match-derived* binders (`fib(n-1)+fib(n-2)`), which the current backend
> miscompiles (a tracked tower codegen bug — `treesum`/`binrec` double-recurse on independent /
> single-match binders and are correct); `binrec`'s `t(d-1)+t(d-1)` uses the proven-correct shape.

Problems (each a standalone program, golden-gated for correctness, then timed end-to-end with
`hyperfine --warmup 3`): **fib** = fib(30) = 832040, **sum** = Σ 1..1000 = 500500, **factorial** = 20!
= 2432902008176640000 (Blight-Nat: 5! = 120). Produced by [bench/game.sh](../bench/game.sh) on an
Apple M2 Pro (Darwin arm64), clang/rustc/ocamlopt/ghc/python3 + LLVM 18; numbers copied verbatim from
its output / [bench/game-results.json](../bench/game-results.json) — none invented.

| Problem | Language | Mean run time (ms) | Peak RSS (KiB) | RSS delta (KiB) |
| --- | --- | ---: | ---: | ---: |
| fib | C | 0.637 | 1056 | 0 |
| fib | Rust | 0.819 | 1184 | 16 |
| fib | OCaml | 1.309 | 1984 | 528 |
| fib | Haskell | 16.772 | 10816 | 112 |
| fib | Blight-Int | 0.750 | 2176 | 32 |
| fib | Blight-Nat | 0.811 | 2176 | 32 |
| fib | Python | 21.385 | 11728 | 320 |
| sum | C | 0.645 | 1056 | 0 |
| sum | Rust | 0.941 | 1184 | 16 |
| sum | OCaml | 1.344 | 1792 | 336 |
| sum | Haskell | 16.888 | 10752 | 48 |
| sum | Blight-Int | 1.007 | 2368 | 224 |
| sum | Blight-Nat | 1.204 | 2384 | 240 |
| sum | Python | 20.391 | 11760 | 352 |
| factorial | C | 0.684 | 1056 | 0 |
| factorial | Rust | 1.422 | 1184 | 16 |
| factorial | OCaml | 1.645 | 1920 | 464 |
| factorial | Haskell | 17.086 | 10720 | 16 |
| factorial | Blight-Int | 1.478 | 2176 | 32 |
| factorial | Blight-Nat | 1.622 | 2176 | 32 |
| factorial | Python | 22.967 | 12256 | 848 |

Blight memory detail for these (from `BL_GC_STATS`; all register-bound, so **zero** collections — the
allocator is barely touched):

| Problem | Variant | Bytes allocated | GC collections | Promoted bytes |
| --- | --- | ---: | ---: | ---: |
| fib | Blight-Int | 2 984 | 0 | 0 |
| fib | Blight-Nat | 2 784 | 0 | 0 |
| sum | Blight-Int | 96 112 | 0 | 0 |
| sum | Blight-Nat | 112 144 | 0 | 0 |
| factorial | Blight-Int | 2 032 | 0 | 0 |
| factorial | Blight-Nat | 264 | 0 | 0 |

What this actually shows: **Blight-Int is genuinely in the C/Rust/OCaml cluster** on all three
problems (~0.75–1.5 ms, within ~1.2–2× of C), an order of magnitude faster to start-and-finish than
Haskell/CPython — the M20/M21/M22 sweep put the native-`Int` path at native-compiled-binary speed.
**Blight-Nat** is the interesting one: post-M20 the inductive `Nat` is competitive *exactly when the
recognizer covers the whole computation* — fib(30) lands on par with C (before M20 this n was
intractable in unary), and **sum(1000) is now ~1.2 ms / ~2.4 MB** (the rewritten Nat-accumulator loop;
previously the `Succ`-rebuilding shape paid ~42 ms / ~11 MB), while it still falls off the recognizer
entirely on factorial's `mult (Succ k) …` (left at n=5). The RSS deltas are tiny here (≤ a few hundred
KiB), and the Blight rows allocate only a few KB with **zero collections** — these loops genuinely run
in registers. It does **not** show Blight beats C in general — these are small, partly spawn-dominated
tasks — but it does show the inductive tower is no longer automatically orders of magnitude behind.

### Alloc-churn: `treesum` (where the GC/allocator work shows up)

The fib/sum/factorial loops above run almost entirely in registers on the `Int` path, so they barely
exercise the allocator or collector — the post-M24 sweep's M27 (scalar-replacement-of-aggregates),
M28 (tuned `bl_alloc`/`bl_force` hot path), and the generational GC don't get a workout. The
**`treesum`** problem ([bench/games/treesum/](../bench/games/treesum/)) is the deliberate
counter-workload: build a *full depth-20 binary tree* (allocating ~2^21 `node`s), then fold-sum every
node label. Result is bit-identical (1048575) across C/Rust/OCaml/Haskell/Python and
[treesum_int.bl](../bench/games/treesum/treesum_int.bl). The recursion is only depth-20, so unlike the
linear loops it scales freely (tree recursion descends the spine logarithmically, not linearly).
Reference Apple M2 Pro, `hyperfine --warmup 3` via `bench/game.sh treesum`:

| Problem | Language | Mean run time (ms) | Peak RSS (KiB) | RSS delta (KiB) |
| --- | --- | ---: | ---: | ---: |
| treesum | C | 61.3 | 34496 | 33440 |
| treesum | Rust | 134.4 | 67968 | 66800 |
| treesum | OCaml | 41.1 | 35872 | 34416 |
| treesum | Haskell | 33.5 | 12784 | 2080 |
| treesum | Blight-Int | 76.1 | 2208 | 64 |
| treesum | Python | 300.4 | 77520 | 65376 |

Blight memory detail (`BL_GC_STATS`):

| Problem | Variant | Bytes allocated | GC collections | Promoted bytes |
| --- | --- | ---: | ---: | ---: |
| treesum | Blight-Int | 3 184 | 0 | 0 |

**Update.** The historical reading here (kept in git history for the record) measured Blight-Int at
~276 ms / ~220 MB peak RSS / ~100.7 MB allocated (14 collections, ~48.9 MB promoted) — a genuinely
allocation-bound workload where every `node` was a separate boxed heap object under the semi-space
copying collector. The **P7 deforestation/fusion pass** ([`fusion.rs`](../crates/blight-codegen/src/fusion.rs))
now recognizes `tree-sum (build d)` as exactly its single-consumer build-then-fold shape and fuses the
producer/consumer pair, so the ~2²⁰ intermediate `node`/`leaf` objects are **never materialized at
all**: measured today, `treesum` allocates **3 184 bytes** with **0 collections** and posts the
**smallest peak RSS of any language in this table** (2.2 MB vs C's 34 MB). Wall time (76 ms) is now the
*compute* cost of ~2²¹ native calls with no allocation to amortize it against — a single-digit multiple
off C/OCaml, and it no longer trails Haskell by much either. Run any compiled binary with
**`BL_GC_STATS=1`** to print the counters (incl. `bytes_allocated`) to **stderr** (never stdout, so
goldens are unaffected) — the workload that used to be the memory-churn headline is now the sharpest
demonstration of how far build/consume fusion can go.

### Linear-list alloc: `listfold`

[`listfold`](../bench/games/listfold/) builds the cons-list `[1..N]`, `map`s `(*2)` over it, then
`foldr (+)` it to one `Int` (result `N*(N+1) = 100010000` for `N = 10000`, shared golden) — a *linear*
allocation shape, the spine-shaped counterpart to treesum's tree. There is deliberately no `filter`:
a predicate would need an `Int → Bool` bridge the kernel intentionally lacks (`Int` has no eliminator,
std/int.bl). `range`/`map`/`foldr` are all `deftotal` single-recursive-field, nullary-base structural
folds — exactly the P3 (3b) reverse-then-fold shape (see caveat 5) — so as of P3 they compile to
**O(1) native stack** rather than descending the spine on the C stack. The `N = 10000` here is the
*as-measured* size (and is bounded by the unary-`Nat` fuel's compile cost, not a runtime stack
ceiling); this row measures per-element list-allocation cost, not collection throughput.

| Problem | Language | Mean run time (ms) | Peak RSS (KiB) | RSS delta (KiB) |
| --- | --- | ---: | ---: | ---: |
| listfold | C | 1.10 | 1360 | 304 |
| listfold | Rust | 1.13 | 1376 | 208 |
| listfold | OCaml | 1.78 | 2304 | 848 |
| listfold | Haskell | 16.6 | 10720 | 16 |
| listfold | Blight-Int | 5.62 | 6384 | 4240 |
| listfold | Python | 22.3 | 12400 | 992 |

Blight allocates ~2.08 MB here with **0 collections** (the two 10 000-element lists fit under the
nursery); the RSS delta (~4.2 MB) is the clearest cross-language memory signal at this size.

### Compute / recursion: `binrec`

[`binrec`](../bench/games/binrec/) counts the nodes of a perfect binary tree of height `d` *without
building it*, by naïve binary recursion `t d = 1 + t(d-1) + t(d-1) = 2^(d+1)-1` (result `4194303` for
`d = 21`, shared golden). It is the array-free integer **compute** classic: ~2^22 calls, a pure
call-overhead / arithmetic workload that decisively escapes process-startup time. The recursion is only
`d`-deep (a shallow call tree), and both recursive calls use the *same* single-match binder — the shape
the backend compiles correctly (a naïve Fibonacci, which recurses on two nested-match binders, is
miscompiled today; see caveat 5).

| Problem | Language | Mean run time (ms) | Peak RSS (KiB) | RSS delta (KiB) |
| --- | --- | ---: | ---: | ---: |
| binrec | C | 1.04 | 1056 | 0 |
| binrec | Rust | 1.34 | 1216 | 48 |
| binrec | OCaml | 6.43 | 1888 | 432 |
| binrec | Haskell | 16.9 | 10736 | 32 |
| binrec | Blight-Int | 1.18 | 2176 | 32 |
| binrec | Python | 180.8 | 11936 | 0 |

**Update (Wave 6 / C1).** The historical reading here (kept in git history for the record) was
**~240× off C** (264 ms) with `binrec` allocating **~151 MB**, attributed to "each curried self-call
materializes partial-application closures." C1 set out to fix that with a dedicated known-arity
uncurrying pass — but investigation found the fix already shipped as a side effect of earlier work: the
**P3 elim-loop worklist transform** ([`elimworklist.rs`](../crates/blight-codegen/src/elimworklist.rs))
recognizes `binrec`'s non-tail double-recursion (`t(d-1)+t(d-1)`, an `IntPrim`-combined tree fold) and
rewrites it into a bounded-stack heap-worklist loop with **zero closure allocations at the self-call
site** — confirmed by dumping the compiled ANF (`BL_DUMP_ANF=1`): the recursive step is a bare
`Comp::CallGlobal`/`Tail::Jump` chain, no `MkClosure` in sight. Independently, the **A3 captureless-call
spine fusion** ([`anf.rs`](../crates/blight-codegen/src/anf.rs), gated `BL_NO_SPINEFUSE`) already collapses
*any* captureless self/global call — tail **or non-tail** position, via the `Cir::CallClosure`/`App`
case in `Anfer::atomize` — to a direct `CallGlobal`/`TailCallGlobal`/`Jump`, with no intermediate
`MkClosure`, for exactly the "build a closure just to call it once" shape a naïvely-curried call site
emits. Measured today: `binrec` allocates **2 496 bytes** (0 collections) and runs at **1.18 ms**, i.e.
**~1.1× C**, not 240×. Regression-locking tests for both properties (zero `MkClosure` at the self-call
ANF site, and a companion "a genuinely-capturing closure must not be fused" soundness twin) live in
[`anf.rs`](../crates/blight-codegen/src/anf.rs)'s test module and the `differential_fast_paths_are_bit_identical`
matrix (`BL_NO_SPINEFUSE`) in [`driver.rs`](../crates/blight-codegen/src/driver.rs); see also
[`c1-uncurry-investigation.md`](c1-uncurry-investigation.md) for the residual (genuinely multi-argument,
two-distinct-call-site) shape that is *not* covered by either mechanism, and why it is out of scope here.

**Alloc-churn frontier sweep (A1′/A5/A6).** A post-M30 sweep at this workload's frontier
(`docs/roadmap-post-m6.md` §"Alloc-churn performance frontier", [performance.md](performance.md) §2i):
a whole-program **post-monomorphization** SRA pass (`layout.rs`) deletes the `Proj`/`Case`-of-`Con`
chains that mono+inlining expose (12/17 `Con`s on the new `examples/flat_esc.bl`), and the region
escape analysis joins the B1 bit-identity matrix under `BL_NO_AUTOREGION`. A measured finding at the
time: wrapping `treesum` in `(region r …)` left it **identical** (3 collections, 14.67 MB, ~55.6 ms) —
`build`'s nodes were allocated under a closure binder and the whole tree escaped via the call argument,
so arena-izing it needs *interprocedural* placement, deferred as a use-after-free risk rather than
shipped on hope (a wrong `Arena` tag is a memory-safety bug, not a wrong number). **Update.** The P7
deforestation/fusion pass ([`fusion.rs`](../crates/blight-codegen/src/fusion.rs)) has since gone further
for this exact producer/consumer pair (`tree-sum (build d)`, a single-consumer build-then-fold): it now
folds the *entire* intermediate tree away. Measured today: `treesum` allocates **3 184 bytes** (0
collections, down from ~14.67 MB) and posts the **smallest peak RSS of any language in the table**
(2 208 KiB) — the interprocedural-placement gap above is now moot for this workload because there is no
tree left to place.

**Perf Frontier II (P3–P10).** A second sweep ([performance.md](performance.md) §2j,
`docs/roadmap-post-m6.md` §"Perf Frontier II") ships P3 elim-loop (linear folds → O(1) native stack),
P4 compacting old gen (steady-state footprint ~2×→~1× live), P6 CSE + compile-time normalization, and
P7 deforestation/fusion (`foldr f z (map g xs)` → fused `foldr`, deleting the intermediate list) — all
differentially bit-identical, **zero** kernel/elab lines. It also lands the frontier's edge as
evidence-based no-gos: **P8 auto-parallelism** (the fixed-pool blocking-join deadlocks under recursive
fork-join, and share-nothing copy is O(message) so only fib-shaped work wins) and **P9.1 inlined
bump-alloc** (*measured* no-win: the default LTO build already inlines `bl_alloc`, cutting call sites
49→10 with identical wall time, and the pipeline folds `treesum`'s allocation away entirely). **P10
defunctionalization** ships the mechanism: a closure-bound benchmark `hofold` (a higher-order `iterate`
applying a capturing `(adder k)` closure 10⁶ times, with a hand-defunctionalized `hofold_mono` twin) that
clears the hard gate (real allocation, surviving indirect apply), plus a sound 0-CFA + Stage-A singleton
devirtualization pass ([defunc.rs](../crates/blight-codegen/src/defunc.rs), `CallKnown`/`TailCallKnown`),
proven bit-identical under `BL_NO_DEFUNC`. *Measured win is neutral* (defunc-on 120.4 ms vs off 120.6 ms;
`hofold_mono` 105.9 ms): devirtualization removes the closure-header fnptr load, but the residual gap to the
monomorphic twin is the per-iteration captured-value env-load, which only capture-unboxing closes — logged
as an honest no-go on the wall clock, with the static call edge now in place for that follow-on.

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

The cross-language table above is produced by:

```bash
bench/game.sh                  # fib sum factorial treesum listfold binrec across the languages
bench/game.sh fib              # a single problem
bench/game.sh treesum          # the tree alloc-churn / GC problem
bench/game.sh binrec           # the compute / native-recursion-overhead problem
```

It compiles every available impl (a missing toolchain just shrinks the comparison set), gates each
binary on its golden value, runs `hyperfine --warmup 3`, captures **peak RSS** and a startup-adjusted
**RSS delta** (peak minus a per-language near-empty baseline in `bench/games/_baseline/`), reads each
Blight binary's `BL_GC_STATS` (`bytes_allocated`/`collections`/`promoted_bytes`) for the memory-detail
subsection, prints the markdown tables, and writes `bench/game-results.json` (+ per-problem
`bench/game-<problem>.json`) with all of those fields. Any single binary also reports its own counters:

```bash
BL_GC_STATS=1 ./treesum   # => stderr: BL_GC_STATS collections=0 … bytes_allocated=3184
```

Multicore worker-pool scaling + serializer throughput (needs `clang`):

```bash
bench/multicore.sh            # SPEEDUP table + serializer MB/s
BL_TSAN=1 bench/multicore.sh  # built under ThreadSanitizer
```

## See also

- [performance.md](performance.md) — cost model, advantages/disadvantages, the per-stage and
  region-vs-GC numbers in narrative form.
- [roadmap.md](roadmap.md) — what unboxed `Int`/`Float`, I/O, arrays, and "can we build games?"
  would cost, and which of them touch the trusted kernel.
