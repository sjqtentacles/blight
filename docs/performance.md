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
- **anf::normalize**: ANF + tail-call→jump + delay-trampoline loop. Historically the **most expensive**
  pure stage on large inputs because it re-shifted de Bruijn indices super-linearly; **M29 (§2h) made
  it linear** by deferring the shift and streaming binds, so it no longer dominates. The 2a table rows
  below predate that fix.
- **LLVM + clang**: IR is emitted, optionally run through LLVM's new-pass-manager pipeline
  (`--opt`, see §2d), then handed to `clang` to assemble + link against the C runtime objects.

`--recheck` adds a second, independent verification of every kernel-accepted judgement before emit;
it roughly doubles the "front" type-checking cost but buys the two-checkers-agree soundness story.

### Runtime value representation (spec §7.3)

- **Most values are heap-boxed** via `bl_alloc` — a value is a header + fields pointer. The exception
  is **M21 tagged-pointer immediates**: machine-word `Nat`/`Int` and nullary constructors ride
  *inside* the `BlValue` pointer as low-bit-tagged values (no heap box), and the GC tracer skips them.
  So a recognized `Int`/`Nat` scalar or a nullary `Con` is unboxed; products, closures, and
  `Succ`-chains are still boxed.
- **`Nat` is unary.** It is a `Succ`/`Zero` cons chain, so the numeral *n* is *n* nested heap cells
  and arithmetic is **O(n) allocations** (`plus a b` allocates ~`a` cells, `mult` ~`a·b`). This is
  great for teaching/proof transparency and terrible for big-number crunching.
- **GC**: a precise **generational copying** collector (`runtime/gc.c`) — a nursery plus a
  **single-region mark-compact old generation by default** (C2), a write barrier for old→young
  pointers, and shadow-stack roots. The heap **starts at 64 MiB** (the harness uses smaller heaps to
  force collections) and **grows** on pressure: a major collection doubles the old region until the
  live set plus the request fit (amortized O(1)), so only a true host-OOM aborts. The **mark-compact
  old generation** collapses the old generation to a *single* region (peak ~1× live instead of the
  legacy semi-space's ~2×) and adaptively right-sizes it; `BL_GC_OLDGEN=semispace` reverts to the
  legacy two-space collector. Either way it is observationally invisible (§2h).
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
µs), and the front stages (lower/region/closure) stay roughly linear. **These rows predate M29**,
which removed the O(n²) ANF re-shift (§2h); the super-linear ANF growth they show is exactly the
bottleneck M29 fixed, so re-run `cargo bench --bench pipeline` for post-M29 numbers.

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

### 2d. LLVM optimization pipeline (`--opt`, hyperfine)

`blight build` accepts `--opt <level>` (`0`/`none`, `2`/`default` (the default), `3`/`aggressive`),
running LLVM's new-pass-manager pipeline (`default<O2>` / `default<O3>`) over the emitted IR before
object emission. The pipelines preserve `musttail` markers, so tail-call soundness (spec §7.4) is
unaffected — the `opt_levels_emit_runnable_objects` codegen test pins that every level produces a
runnable object computing the identical result.

Measured on a fold workload (`foldr plus` over a 10 000-element unary-`Nat` list) on the reference
machine (hyperfine 1.20, Apple Silicon, macOS):

| level | compile (`blight build`) | run (binary) |
|---|---:|---:|
| `--opt 0` | ~322 ms | ~2.9 ms |
| `--opt 2` | ~332 ms (+3%) | ~2.9 ms |
| `--opt 3` | ~336 ms (+4%) | ~2.9 ms |

The headline (and deliberately honest) result *for the separate-object build*: **the IR passes cost a
few percent of compile time and buy no measurable runtime improvement on this workload.** That is an
architectural signal, not a bug. Blight's generated `program.o` is a thin layer of `tailcc` thunks;
the runtime cost lives almost entirely in the **separately-compiled C runtime** (GC allocation,
boxing, `bl_force`), which the module-local pass pipeline cannot reach. The fix is cross-object LTO
between the Blight object and the runtime — now implemented and measured in 2f below, which is what
finally lets `--opt 2/3` pay off.

### 2f. Cross-object LTO (M22, zero TCB growth)

By default `blight build` now ships both the Blight program **and** the C runtime as LLVM **bitcode**
and links them with `clang -flto`, so the optimizer runs *across* the former object-file boundary and
inlines the hot runtime helpers (`bl_alloc`, `bl_app`, `bl_force`, `bl_int`/`bl_con`, the `bl_nat_*`
machine-word ops) directly into compiled Blight code. The historical separate-object path is kept
verbatim as a fallback under `BL_NO_LTO` (and is used automatically if a toolchain's `-flto` link
fails), so nothing regresses where LTO is unavailable. This lives entirely in the untrusted driver
(`crates/blight-codegen/src/driver.rs`) plus a bitcode-emission path in `llvm.rs`; the kernel gains
zero lines.

**Inlining actually happens** (the precondition the separate-object build could never meet). In the
LTO binary the runtime symbols become module-local (`nm` reports them as `t`, not external `T`), and
the small constructors are inlined away entirely — e.g. `bl_con` and `bl_nat_add` no longer appear in
the linked binary's symbol table at all, having been folded into their call sites and dead-stripped.

**It pays off, and results stay bit-identical.** On the reference machine (hyperfine 1.20, Apple
Silicon, macOS), an 8 000-element `Int` fold (`foldr int-add`, allocation- and call-heavy), built
`--opt 3` both ways, prints the identical `8000` under LTO and `BL_NO_LTO`:

| build | run (binary) | vs no-LTO |
|---|---:|---:|
| `BL_NO_LTO` (separate objects) | ~3.6 ms | 1.00x |
| LTO (default) | ~3.1 ms | **~1.15x faster** |

The win is the inlined runtime calls (user-CPU drops ~2.4 ms → ~2.1 ms); the remainder is
spawn/heap-init that no optimization can remove. The gain scales with how allocation-heavy the
workload is — a thin `tailcc` program that barely touches the runtime sees little, an allocation- or
arithmetic-bound loop sees the most. Crucially, **LTO only changes speed, never observable behavior**:
the entire `cargo test --workspace --features llvm` suite (including every shipped `examples/*.bl`
end-to-end build/run/recheck) is green through the LTO path by default.

### 2g. Fast `Nat` / `Float` numerics (M20 / M23, zero TCB growth)

The single biggest *algorithmic* win is the fast-`Nat` recognizer (M20). Inductive `Nat` is
`Zero`/`Succ`, so `plus a b` is structurally O(`a`) — it walks an `a`-deep `Succ` chain, allocating a
cell per step. A backend `Cir→Cir` recognizer (`recognize.rs`) fingerprints the *exact* prelude
`plus`/`mult`/`pred`/`sub` eliminator shapes and rewrites them to O(1) machine-word `bl_nat_*` ops
(`numeric.c`), with fully-canonical numerals folded to a single word literal. The kernel still sees
`Zero`/`Succ` (the recognizer is conservative — a user who redefines `plus` falls back to the generic
eliminator), and the rewrite is gated by a fuzzed differential test (`fast_nat_matches_unary_semantics`)
plus an end-to-end one (`nat_arithmetic_is_fast`).

The end-to-end test makes the O(n)→O(1) claim concrete and *measured in a real compiled binary*: it
compiles the same doubling workload (`seed · 2^14`) twice onto a deliberately small heap — once with
the recognizer on, once off — and compares the runtime GC counters:

| build of the same `Nat` workload | result `value` | GC collections |
|---|---:|---:|
| recognizer OFF (pre-M20 `Succ`-chain eliminator) | 16384 | `> 0` (the chain dwarfs the nursery, forcing GC) |
| recognizer ON (M20 machine-word `NatPrim`) | 16384 | **0** (one word add per doubling, zero allocation) |

Same observable `value`, zero allocations on the fast path — the optimization changes only cost, never
the answer (the differential guarantee, here end-to-end).

**Recognizer coverage matrix.** The recognizer is deliberately conservative — it fires only on the
*exact* structural fingerprint of the prelude eliminator (captured from `BL_DUMP_CIR`), so a redefined
op or an effectful operand silently falls back to the generic O(n) lowering (a missed optimization,
never a miscompile). What it currently covers (`recognize.rs`):

| Op | Prelude source | Fast lowering | Arity | Notes / fall-back |
|---|---|---|---|---|
| `plus` | `std/nat.bl` | `bl_nat_add` (`NatPrim::Add`) | binary | operands must be settled pure `Nat` values |
| `mult` | `std/nat.bl` | `bl_nat_mul` (`NatPrim::Mul`) | binary | Succ-arm must embed the recognized `plus` core |
| `sub` | `std/nat.bl` | `bl_nat_sub` (`NatPrim::Sub`) | binary | nested `match b` eliminator fingerprint |
| `pred` | `std/nat.bl` | `bl_nat_pred` (`NatPrim::Pred`) | unary | — |
| `(Succ k)` peel | constructor | `Add(k, 1)` (`NatPrim::Add`) | — | M25b; only when `k` is settled-pure & non-canonical (canonical chains fold to a `NatLit` instead) |
| canonical `Succ`/`Zero` chain | constructor | `NatLit(n)` constant | — | fully-static numerals fold to one machine word |
| `float-add`/`-sub`/`-mul`/`-div`/`-neg` | `std/float.bl` | `bl_float_*` (`FloatPrim`) | binary (neg unary) | fixed-point over `(mkfloat Int)`; leaf `IntPrim` skeleton must match |
| canonical `push`/`empty` string literal (M30) | `std/string.bl` | `StrLit` → `bl_string_from_codepoints` (`BL_STRING`) | — | fully-static literals only; every codepoint a canonical `Nat`, spine ending in `empty`; gated `BL_NO_STRPACK` |
| `min`/`max` (M25b) | runtime helpers | `bl_nat_min`/`bl_nat_max` | binary | helpers + `NatPrimOp`s exist; prelude-fingerprint firing deferred (no bench need, brittle) |
| `eq`/`lt`/`le`/`div`/`mod` | — | — | — | **not covered**: no prelude `Nat` definitions exist to fingerprint (deferred) |

The single hard soundness rule across the whole table: a `NatPrim`/`FloatPrim` lowers to a direct,
*non-OpNode-aware* `bl_*` call, so every operand must be a **settled pure value** (a variable whose
binder is known non-effectful, a literal, or a nested pure prim). The recognizer threads a de Bruijn
"unsafe-binder" environment so a `Var` bound to a bubbling `perform` is never folded (the
`actor_pingpong` 1→5 regression that M26 fixed); function/`Fix`/`Case`/handler-clause binders are
call-by-value settled values and stay fast, preserving every hot-loop win.

`Float` (M23) is the same trick on a different type, and the sharper TCB demonstration. `std/float.bl`
defines `Float` as ordinary inductive `Data` — `(mkfloat (mantissa Int))`, a fixed-point rational
scaled by 10^6 — built entirely from the trusted `Int` base, so there is **no kernel `FloatTy`** and
the independent re-checker *accepts* a `Float` program outright (it is plain `Int`/`Data`). The
recognizer rewrites each `float-*` wrapper to an O(1) `bl_float_*` helper that computes the *same*
fixed-point semantics (so the differential test `float_diff.c` is bit-identical, and `float_arith.bl`
produces the identical scaled mantissa with the recognizer on or off). The headline: floating-point-
*style* arithmetic at machine speed while the checked meaning stays exact `Int` arithmetic, for **zero
trusted lines**.

### 2h. Post-M24 performance sweep (M25-M29, zero TCB growth)

A maximalist correctness-first sweep that widened the fast paths and removed two algorithmic
bottlenecks, every step guarded by the differential/bit-identical harness so no observable behavior
changed. All of it lives in the untrusted backend (`recognize.rs`, `unbox.rs`, `anf.rs`, the C
runtime); the kernel gains zero lines.

- **M25 / M25b — structural Nat-loop recognizer, wider + frame-safe.** The fast-`Nat` recognizer now
  also peels a *non-canonical* `(Succ k)` to an O(1) `Add(k, 1)` (so a loop counter that is `Succ` of
  a runtime value is still fast), and grew runtime `bl_nat_min`/`bl_nat_max` helpers behind new
  `NatPrimOp`s. A latent GC-rooting bug on the recognized loop path (which had silently turned
  `sum_nat` from 500500 into 55 on one HEAD) was fixed by frame-safe rooting and pinned by the
  differential test. The peel stays opt-in and fuzzed.
- **M26 — no per-step heap thunk in the trampoline.** An ANF peephole fuses
  `Let(MkClosure(f, []), TailCall(Var0, arg))` into a direct `Jump`/`TailCallGlobal`, so a guarded
  recursive *step* no longer allocates a throwaway closure thunk. This is the fix for the old "O(n)
  *heap* for an n-deep force" caveat on the common self-tail-recursive shape. The same milestone
  fixed an effect-soundness miscompile: the `Succ`-peel/`NatPrim` rewrite now tracks per-binder
  effectfulness so a variable bound to a `perform` is never folded into a non-effect-aware
  `bl_nat_*` (caught by `actor_pingpong` going 1→5).
- **A3 — captureless-call spine fusion (`anf.rs` + `bl_app_global`).** M26 only removed the *tail*
  `MkClosure(f, []) + TailCall` thunk; the curried calling convention still allocates a throwaway
  captureless closure for **every non-tail partial application** a multi-argument structural/effectful
  loop performs each step — `(loop f …)`, `(h x)`, the `fst`/`snd` projections the lexer/parser
  family run per byte (visible as `MkClosure(rec_N, []) + Call` in `BL_DUMP_ANF`). ANF now folds each
  `CallClosure(MkClosure(f, []), a)` directly to a new `Comp::CallGlobal(f, a)` at construction time
  (no closure allocated, no de Bruijn surgery — the binder is simply never introduced), lowered
  through `bl_app_global`: a captureless function reads no environment, so it is called with a null
  env exactly like `TailCallGlobal`, and an effectful (OpNode) argument falls back to `bl_app` over a
  freshly-built closure so delimited-continuation capture is **bit-identical** to an un-fused call.
  On `paren_depth.bl` this removes 14 of 42 static closure allocations; the per-iteration win is the
  `spine_fusion_reduces_allocations` test (strictly fewer `MkClosure` sites + an end-to-end
  equal-output run). Pure backend representation optimization — the kernel and re-checker never see
  ANF — gated by `BL_NO_SPINEFUSE` and pinned bit-identical over the whole corpus by the differential
  matrix.
- **M27 — scalar replacement of aggregates (`unbox.rs`).** A bottom-up `Cir→Cir` pass folds
  `Proj`-of-`Tuple`/`Con` and `Case`-of-`Con` *in place*, and collapses the build-then-destructure
  idiom (a `let` binding a pure literal product immediately taken apart), so the intermediate product
  never allocates. Gated by `BL_NO_UNBOX`, 11 TDD unit tests, full corpus bit-identical. A more
  aggressive cross-call eliminator-inline extension was prototyped, **caught miscompiling by the
  differential check, and reverted** — the zero-TCB mandate in action.
- **M28 — tuned LTO-inlined allocator/force fast path.** `bl_alloc` is split into a lean inlinable
  nursery bump-and-init fast path plus an out-of-line cold `alloc_slow` (oversized / collect / grow);
  `bl_force`/`bl_gc_poll`/`bl_arena_alloc` are marked hot with branch hints on their rare branches.
  New `BL_HOT`/`BL_COLD`/`BL_LIKELY`/`BL_UNLIKELY`/`BL_ALWAYS_INLINE` macros are no-ops off
  clang/gcc. Byte-for-byte identical output; this is what makes the M22 LTO inlining land on a tighter
  hot path.
- **M29 — ANF normalization made linear.** The previous "ANF scales super-linearly" bottleneck
  (tables 2a) was an **O(n²) re-shift**: `seq`/`Let`/`Case` lowering eagerly rebuilt whole subtrees to
  fix de Bruijn indices. ANF now threads a *deferred* `Shift` (a persistent cons-list of frames with a
  lift-counter, kept sorted by effective cutoff so the common shallow-variable lookup is O(1)) and
  applies it once at `Var` leaves, and streams binds into a shared accumulator instead of copying a
  `Vec` per level. A RED→GREEN scaling test (`deep_let_chain_normalizes_linearly`) pins it: an 8×
  deeper input went from ~48-75× (quadratic) to <30× the time. The shape tests stay green and the
  full corpus is bit-identical.
- **M30 — packed-byte `String` representation (`BL_STRING`, A2).** A `String` is checked as the
  inductive `empty`/`push` cons-list of `Nat` codepoints (`std/string.bl`), so an *n*-character
  literal allocates *n* `push` cells of two pointers each. The recognizer (`recognize.rs`) now folds a
  fully-canonical `push cp0 (push cp1 … empty)` literal to a `Cir::StrLit(Vec<u64>)`, which lowers
  (ANF `Comp::StrLit` → `llvm.rs`) to a single `bl_string_from_codepoints` call building one `BL_STRING`
  object — a *zero-field* heap node (tag 9) whose `header.aux` points at a program-lifetime,
  GC-untraced `BlStrData { cps, off, len }` side buffer of the interned codepoints. This mirrors the
  M20 `BL_NAT` trick exactly (a recognized backend repr of a kernel-inductive type, no kernel/GC
  change: the tracer is `nfields`-driven and a 0-field object is copied by size, `aux` opaque). The
  coherence shim `bl_string_to_con` materializes one `empty`/`push` layer on demand (head `Nat` +
  packed tail), and `llvm.rs::emit_case` chains it after `bl_nat_to_con` so a packed string flowing
  into *any* generic eliminator destructures correctly. Direct runtime spine-walkers
  (`bl_print_string`, the Console `print` decoder `bl_emit_string`, `bl_string_to_cstr`) read a
  `BL_STRING` in O(1)/codepoint **and** tolerate a *mixed* spine — inductive `push` cells terminating
  in a packed tail, the exact shape `string-append`'s `(empty) t` arm splices in. Gated by
  `BL_NO_STRPACK`; the substrate is pinned by `string_diff.c` (packed vs. inductive vs. every
  mixed-spine prefix split, all observations + `to_con`-peel bit-identical) and a GC-survival test,
  and the full corpus — including the stdin-reading effectful programs `greet.bl`/`game/guess.bl` — is
  bit-identical with packing on or off.

**Alloc-churn / GC benchmark (`treesum`).** To *measure* the M27/M28/GC work (the fib/sum loops run in
registers and barely allocate), `bench/games/treesum/` builds a full depth-20 binary `Tree`
(allocating ~2^21 nodes) and folds the node labels — a deliberate allocator + minor-GC stressor.
Result is bit-identical (1048575) across C/Rust/OCaml/Haskell/Python and `treesum_int.bl`. On the
reference machine this is the workload where Blight-Int sits a single-digit multiple off the native
GC'd languages **in time** (~6.7× OCaml, ~4.6× C) while beating CPython, rather than the
orders-of-magnitude gap the unary `Nat` path shows — but it is also where Blight is **most
memory-hungry**: depth-20 peak RSS is ~220 MB (vs C ~34 MB, Haskell ~13 MB), because every node is a
separate boxed object *and* the default semi-space copying collector keeps two halves (the opt-in
**compacting old generation** below halves that to one). Run any compiled program
with `BL_GC_STATS=1` to print a one-line churn report to **stderr** (never stdout, so goldens are
unaffected): `BL_GC_STATS collections=N minor=N major=N grows=N promoted_bytes=N bytes_allocated=N
compacting=0|1 shrinks=N old_capacity=N old_live=N peak_old_reserved=N` —
total collections split into cheap nursery **minor**s vs full **major**s (`grows` counts the majors
that had to enlarge the heap), the bytes promoted nursery→old across all minors, **`bytes_allocated`**
(M-frontier): the cumulative GC-heap bytes the program requested via `bl_alloc` — the startup-independent
"how much did this churn" signal (treesum depth-20 reports ~100.7 MB allocated / 14 collections /
~48.9 MB promoted). It excludes arena allocations and GC copies, so it is exactly the GC-pressure the
program generates; it lives in a thread-local counter reset in `bl_gc_init` and never affects output
(the B1 differential corpus stays bit-identical). The remaining fields belong to the **mark-compact old
generation** (P4): `compacting` is 1 under `BL_GC_OLDGEN=compact`, `shrinks` counts low-occupancy
region shrinks, `old_capacity`/`old_live` are the active region's size and occupancy, and
**`peak_old_reserved`** — the high-water old-generation bytes *reserved* — is the headline footprint
metric: ~**1× live** under compaction (a single region) versus ~**2×** for the legacy semi-space
(from + to). It is a deterministic function of the build, so `bench/check_regress.py` checks it
strictly (any growth beyond a 1% tolerance is a hard regression).

#### Mark-compact old generation (P4.1/P4.2, on by default since C2, untrusted runtime)

The old generation runs as a **single region** reclaimed by a *copying compaction*: a major evacuates
the entire live set (roots + nursery survivors + live old objects, via the same proven forwarding the
semi-space uses — so **zero new use-after-free surface**, gated under AddressSanitizer) into a freshly
right-sized region and frees the source. Steady-state reserved footprint is therefore ~1× the live set
instead of ~2× (`peak_old_reserved` halves; verified 1× vs 2× on treesum). It also **adaptively
shrinks** (P4.2): after a major reveals the live set occupies only a small fraction of a
previously-grown region, the region is right-sized with ~50% growth slack; a hysteresis **band**
(`BL_GC_SHRINK_BAND`, default 2) plus that slack prevent grow/shrink oscillation under a stable or
moderately-varying live set. The mode is **observationally invisible** — the full
example/stdlib/differential corpus is bit-identical under either setting (`gc_diff.c` checksums a
large rooted set built under a small, major-forcing heap and asserts it is bit-identical whether
`BL_GC_OLDGEN` is unset, `semispace`, or `compact`) — and, as of **C2** (Blight Arc II), it is **on by
default**: `BL_GC_OLDGEN=semispace` opts back into the legacy two-space collector (`compact` remains
accepted, now a no-op restating the default). The flip was measured, not assumed: at realistic heap
sizes old-gen majors are rare enough that neither mode is ever exercised (0 collections on the
`binrec`/`treesum`/`listfold` corpus under the default 64 MiB heap), so the common case sees **zero**
throughput change; under a deliberately tiny heap forcing dozens of majors (the worst case for
compaction's extra per-major `malloc`), a repeated `hyperfine` comparison put compaction within noise
of the semi-space (~1.05× either direction across trials) while reserving roughly half the memory —
comfortably inside the "no regression" budget for a 2× footprint win.

**Memory metrics in the cross-language harness.** `bench/game.sh` reports, beyond wall-clock: **peak
RSS**, a startup-adjusted **RSS delta** (peak minus a per-language near-empty baseline in
`bench/games/_baseline/`, so the process/interpreter floor is removed), and — for the Blight rows only
— a memory-detail table fed by `bytes_allocated`/`collections`/`promoted_bytes`. Two newer problems
exercise these: **`listfold`** (a linear cons-list `[1..N]` + `map (*2)` + `foldr (+)`; ~2.08 MB
allocated, 0 collections — a per-element list-allocation cost, deliberately small because linear
self-recursion is not O(1) native stack here, see §4) and **`binrec`** (naïve binary recursion
`t d = 1 + t(d-1) + t(d-1)`, a compute classic). `binrec` used to be the sharpest pointer at a needed
multi-argument / known-callee fast path — it allocated ~151 MB of short-lived partial-application
closures across its ~4.2 M curried self-calls — but Wave 6/C1 found this already fixed by the P3
elim-loop worklist transform plus the A3 captureless-call spine fusion (`anf.rs`, `BL_NO_SPINEFUSE`):
`binrec` now allocates **2 496 bytes** (0 collections) and runs at ~1.18 ms, ~1.1× C (see
`docs/benchmarks-game.md` "Compute / recursion: `binrec`" for the measured before/after and the
regression tests that lock this in). `treesum` similarly dropped from ~100.7 MB/276 ms to 3 184
bytes/76 ms once P7 deforestation/fusion started fusing its single-consumer `tree-sum (build d)` pair
(see `docs/benchmarks-game.md` "Alloc-churn: `treesum`").

#### GC tuning knobs (A4, untrusted runtime only)

The generational split is **env-tunable** at process start; all knobs are read once in `bl_gc_init`
and an unset/invalid value keeps the historical default. Because the collector is precise and its
*semantics* are independent of sizing, tuning these only changes throughput/footprint — **never the
observed result** (verified: `treesum_int.bl` prints `262143` under every setting below, and the B1
differential stays bit-identical). On the treesum stressor (64 MiB default heap), bumping the nursery
collapses 3 minor collections to 1; shrinking it raises them to 6.

| Variable | Default | Effect |
| --- | --- | --- |
| `BL_GC_NURSERY_DIV` | `8` | nursery size = `heap / DIV` |
| `BL_GC_OLD_DIV` | `2` | each old semi-space = `heap / DIV` |
| `BL_GC_NURSERY_BYTES` | — | absolute nursery size (overrides the divisor) |
| `BL_GC_OLD_BYTES` | — | absolute old-semi-space size (overrides the divisor) |
| `BL_GC_MARGIN_NURSERIES` | `2` | promotion headroom, in nurseries, before a minor escalates to a major |
| `BL_GC_OLDGEN` | `compact` | the single-region mark-compact old generation is on by default (peak ~1× live vs ~2×, C2); `semispace` opts back into the legacy two-space collector |
| `BL_GC_SHRINK_BAND` | `2` | compacting-mode anti-oscillation hysteresis: shrink only when capacity exceeds the right-sized target by more than this factor |

### 2i. Alloc-churn frontier (A1′ post-mono SRA, A5 region matrix, A6 go/no-go; zero TCB growth)

Building on §2h, a focused sweep at the allocation/GC frontier (`docs/roadmap-post-m6.md` §"Alloc-churn
performance frontier"). All untrusted-tower, all differentially gated, **zero** `blight-kernel` /
`blight-elab` / `blight-recheck` lines.

- **A1′ post-mono scalar-replacement.** A whole-program post-monomorphization pass
  (`crates/blight-codegen/src/layout.rs`) re-runs the proven `unbox`/`flatten` over every function body
  *after* mono + inlining have folded a producer into its consumer, deleting the `Proj`/`Case`-of-`Con`
  chains the pre-mono passes never saw. Enabled by widening `unbox`'s purity to **pure non-trapping
  arithmetic** (`NatPrim` always; `Int`/`Float` except `Div`). On the new cross-function escaping
  example `examples/flat_esc.bl` this deletes **12 of 17 `Con` allocations** (17→5 in `BL_DUMP_ANF`),
  bit-identical (`(1+2)+3 = 6`, re-checks `Ok`). Gated by `BL_NO_UNBOX`/`BL_NO_FLATTEN` (already in the
  B1 matrix). `BL_LAYOUT_STATS=1` reports per-pass firings.

- **A5 region pass in the bit-identity matrix.** The region escape analysis is now gated by
  `BL_NO_AUTOREGION` and added to `DIFF_FLAGS`, so arena routing is machine-checked bit-identical
  against the always-GC reference across the whole corpus for the first time.

- **`treesum` arena spike (A5/A6 finding).** Wrapping the benchmark in a region —
  `(region r (let t = build d in tree-sum t))` — leaves it **identical to the un-wrapped baseline**, so
  the naive lever does not help and the real fix (interprocedural arena cloning) is a use-after-free
  risk deferred behind a future transient-consumption analysis:

  | treesum (depth 18, 262143) | collections | promoted | wall (hyperfine `-N`) | max RSS |
  | --- | --- | --- | --- | --- |
  | baseline (no region) | 3 minor / 0 major | 14.67 MB | 55.6 ms ± 0.5 | 25.3 MB |
  | `(region r …)` wrapped | 3 minor / 0 major | 14.67 MB | ~55.6 ms | 25.4 MB |

  Root cause (`region.rs`): `build`'s node `Con`s sit under a `Lam`/`Fix` binder (treated as escaping
  closure capture), and the whole tree escapes via the `App`-argument rule — both conservative by
  design, since a wrong `Arena` tag is a UAF, not a wrong number.

- **A6 packed / unboxed-field representation — go/no-go: *no-go for now*.** Two mechanisms could cut
  `treesum`'s churn further, both rejected for this sweep:
  - *Contiguous node arenas* (lay a region's children out in one bump buffer so a tree is cache-dense
    and freed in O(1)) reduce to the same interprocedural-placement problem as A5 plus a layout/aliasing
    contract, with the same use-after-free stakes — so they inherit A5's deferral behind a proven
    transient-consumption analysis.
  - *Inline non-pointer fields + a per-tag pointer bitmap.* The precise GC currently traces **all**
    `nfields` uniformly as pointers (`runtime/blight_rt.h` header `nfields`; `runtime/gc.c` `obj_bytes`
    walks every field). Storing scalar fields inline would need the tracer to consult a per-tag pointer
    bitmap — a real GC-touching change (still tower-only, **zero** kernel TCB). Its payoff here is small
    precisely because M21 already makes `Int`/`Nat`/nullary-`Con` **tagged immediates** the tracer skips
    (`bl_obj_nfields` returns 0; evacuation is identity): `treesum`'s `node` is already a 3-pointer
    object whose `Int 1` rides inside the pointer word, so an inline-scalar layout buys almost nothing
    over the current representation.
  - **Disposition:** no-go. The minimal de-risking step, if revisited, is the A5 transient-consumption
    (linearity) analysis *first* — it unblocks both the plain-arena and contiguous-arena variants with
  no GC change — and only then a bitmap tracer behind a `*_diff.c` differential gate. Net: zero kernel
  growth, no speculative GC surgery. Full reasoning: `docs/roadmap-post-m6.md` §"Alloc-churn
  performance frontier" (A6 row).

### 2j. Perf Frontier II (P3–P10): stack, GC footprint, redundancy, fusion — and where the frontier ends

A second TDD sweep (`docs/roadmap-post-m6.md` §"Perf Frontier II") past the alloc-churn work. Every shipped
item is untrusted-tower, differentially gated, and adds **zero** `blight-kernel`/`blight-elab` lines (all of
P3–P10 lives in `crates/blight-codegen` + `runtime/`). The notable outcome is that the sweep is **as much a
set of evidence-based no-gos as it is wins** — the existing pipeline (M21 immediates, M22 LTO, M27
unbox/SRA, plus the P-series below) already captures most of the reachable gain, and the remaining levers
are either architecturally blocked or unmeasurable on the current corpus.

**Shipped wins.**
- **P3 elim-loop** removes the structural-fold stack ceiling: tail-accumulator catamorphisms become a
  self-`Jump` loop and non-tail *linear* folds become a reverse-then-fold pair, so linear list/`Nat` folds
  run in **O(1) native stack** (only multi-recursive *tree* recursion stays C-stack-bounded, at depth
  `log n`). Gated `BL_NO_ELIMLOOP`, bit-identical.
- **P4 compacting old gen** cuts steady-state old-generation footprint from the semi-space's **~2× live
  to ~1×** (`peak_old_reserved` 32 MiB vs 64 MiB on the treesum heap), adaptively right-sized with a
  hysteresis shrink band, reusing the proven Cheney forwarding (zero new UAF surface). Surfaced via
  `BL_GC_STATS` + `check_regress.py`. **On by default since C2** (Blight Arc II): measured
  throughput-neutral (realistic heaps rarely reach a major at all; a tiny-heap stress comparison put it
  within noise of the semi-space), so the ~2×→~1× footprint win ships unconditionally. `BL_GC_OLDGEN=semispace`
  reverts to the legacy two-space collector.
- **P6 CSE + compile-time normalization** share repeated pure subterms (de Bruijn-aware GVN) and fold
  closed, non-recursive, effect-free subterms via the kernel's own `eval`/`quote` (zero TCB — *reuse*, not
  modify; the `Elim`-exclusion bounds compile time by construction). Both gated + in the differential
  matrix.
- **P7 deforestation/fusion** shortcuts `foldr f z (map g xs)` → `foldr (λx acc. f (g x) acc) z xs`,
  deleting the intermediate list (pure-only + single-consumer guards), gated `BL_NO_FUSION`, bit-identical
  across the corpus incl. `examples/listfold.bl`. This captures at compile time — at far lower risk — the
  very functional-update churn that the P5.1 reference-counting spike declined to chase.

**Go/no-gos (the frontier's edge, full reasoning in the roadmap).**
- **P5.1 RC + reuse — no-go** (moving collector clashes with non-moving reuse; the win is P7's anyway).
  **P5.2 region cloning — deferred** (needs a sound linearity analysis first).
- **P8 auto-parallelism — no-go on the current runtime.** The fixed-size `worker.c` pool with a *blocking*
  `bl_pool_join` deadlocks under recursive fork-join (all `N` workers park in `join` while subtasks queue);
  and share-nothing serialize is O(message), so only a fib-shaped fragment (Int args, big compute) wins
  while `treesum`/sort are copy-dominated and need a shared-heap pivot (a concurrent-safe / no-collect-in-
  region GC — near the trusted boundary). The substrate (M15/M17/M18) stays sound for *independent*
  data-parallel tasks + actors.
- **P9.1 inlined bump-alloc — no-go: already captured by LTO (measured).** The default `-flto -O2` build
  already inlines the `bl_alloc` bump into hot code: `bl _bl_alloc` call sites fall **49 → 10** from the
  `BL_NO_LTO` object build to the LTO build, and the two binaries run in **identical** wall time
  (≈3.66 s vs ≈3.71 s / 50 runs on the treesum tree). Collapsing 49→10 alloc calls changed nothing, so the
  10→0 an `llvm.rs` emitter would add cannot help — and the same pipeline folds `treesum`'s allocation away
  entirely (`collections=0`, `bytes_allocated=3184`). Re-emitting the bump in codegen would only duplicate
  LTO's result and add heap-safety surface (TLS globals, header-layout duplication, the fields-nulling
  invariant). **P9.2 header packing — deferred** (every-field-offset UAF surface for a footprint win the
  corpus does not show binding).
- **P10 defunctionalization — mechanism shipped + proven bit-identical; measured runtime win neutral.**
  Closures *do* survive `mono`+`inline` (mergesort emits 44 `bl_app` sites), the opportunity is real, and the
  rewrite is *value-preserving* (a bug is a wrong value the `BL_NO_DEFUNC` differential catches, not a UAF).
  Built: the closure-bound benchmark `bench/games/hofold/` (a higher-order `iterate` applying a capturing
  `(adder k)` closure 10⁶ times + a hand-defunctionalized `hofold_mono` twin) clears the Phase-1 hard gate
  (`BL_GC_STATS` ≈64 MB / 7 collections — real allocation, not `treesum`-style fold-to-zero — and the apply
  survives `mono`+`inline`); and an ANF→ANF pass ([defunc.rs](../crates/blight-codegen/src/defunc.rs)) with a
  sound 0-CFA + Stage-A singleton devirtualization (`Comp::Call`/`Tail::TailCall` with flow set `{L}` →
  `CallKnown`/`TailCallKnown`, closure object as env, OpNode-operand path unchanged). It devirtualizes 19
  sites in `mergesort` / 2 in `hofold` (confirmed as a direct `tailcc` call in the binary), is **bit-identical
  under `BL_NO_DEFUNC` across the full matrix** (784 s), and adds zero TCB lines. *The win is neutral:*
  defunc-on 120.4 ms vs `BL_NO_DEFUNC` 120.6 ms (`hofold_mono` 105.9 ms). Devirtualization removes the header
  `load_fnptr`, but the residual int↔mono gap (≈15 ns/iter) is the per-iteration **load of the captured `k`
  from the closure env** + the un-inlined call — which only **capture-unboxing/specialization** closes, not
  devirtualization. Shipped as the prerequisite for that follow-on (you cannot specialize a call you cannot
  statically name); the wall-clock win is logged neutral (honest no-go, like P9).

### 2e Multicore / parallelism (share-nothing runtime, M15-M19)

Blight values are immutable, so the runtime parallelizes by **share-nothing**: each OS-thread worker
gets its own thread-local heap/stack (M15), the native worker pool (`worker.c`) runs independent
computations in parallel, and messages cross worker heaps by **structural copy** of immutable values
through the serializer (M18). The two performance claims are measured by C harnesses driven from the
Rust test suite and reproduced by `bench/multicore.sh`.

**Worker-pool scaling** (`worker_pool_scales_with_cores` / `bench/multicore.sh`): a fixed set of 16
heavy, independent tasks (each does a real compute + GC-churn loop on its own heap) run across pools
of 1/2/4/8 workers. The reduced result is identical at every pool size (the hard determinism gate);
the wall-clock drops with worker count. On a 10-core Apple-silicon host:

| Workers | Wall time | Speedup vs 1 |
|---|---|---|
| 1 | ~91-95 ms | 1.00x |
| 2 | ~42-45 ms | ~2.1x |
| 4 | ~22-24 ms | ~3.7-4.4x |
| 8 | ~15-18 ms | ~5.0-6.4x |

The 1-worker baseline already pays the same serialize/deserialize-per-task cost as the parallel runs,
so the speedup isolates parallelism rather than hiding setup overhead. The pool is
ThreadSanitizer-clean (`BL_TSAN=1 bench/multicore.sh`).

**Serializer throughput** (`serializer_throughput_reported`): the data-only (de)serializer is the
boundary primitive both the worker pool and the distributed transport (`blight-net`) ride on. A
2000-node cons-list message serializes to a ~64 KB blob; a full round-trip (serialize +
deserialize + fresh allocation) runs at roughly **~280-330 MB/s (~190-220 us/op)** on the same host.

Honest framing: absolute numbers are host- and load-dependent (core count, cache, scheduler), and
super-linear rows at 2/4 workers reflect cache/GC effects, not magic. Messages are **data-only**
(closures/continuations carry a raw function pointer and are rejected), and the `std/actor.bl` actor
surface still runs under a single-core cooperative scheduler from `.bl` source — the multicore path
is the C worker pool. The same data-only messages also cross *machines*: the M24 distributed
addressing layer (`blight-net` `NodeId`/`Router`) routes the `Actor` `send`/`receive` ops over
per-node TCP transports, proven by a two-separate-OS-process ping/pong over loopback
(`two_process_pingpong_over_loopback_tcp`). None of this grows the trusted base or adds `foreign`
axioms.

## 3. Advantages

- **Tiny trusted kernel + independent re-checker.** Soundness rests on two small checkers agreeing
  (or the second honestly, countably *declining* — never silently disagreeing) via `--recheck`, not
  one large trusted compiler. The whole backend is untrusted: a miscompilation
  can give a wrong answer but can never mint a false `Proof`.
- **Share-nothing multicore.** Immutable values mean the worker pool scales across cores with no
  shared mutable state and no locks on the allocation/GC hot path (§2e), ThreadSanitizer-clean.
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

- **Unary `Nat` ⇒ O(n) allocation arithmetic on the *generic* path.** Numerals are `Succ`/`Zero` cons
  chains, so arithmetic that misses the M20/M25 recognizer (e.g. a user-redefined `plus`) is O(n)
  allocation. The recognized prelude ops (`plus`/`mult`/`pred`/`sub`/`min`/`max`, and the non-canonical
  `Succ`-peel) run as O(1) machine words; outside that fingerprint set it falls back to the chain.
- **Most values are boxed.** M21 unboxes machine-word `Nat`/`Int` and nullary constructors as
  tagged-pointer immediates, but products, closures, `Succ`-chains, and any non-nullary constructor are
  heap objects — there are no flattened records. M27's SRA pass removes *intra-function*
  build-then-destructure products, but a product that escapes a function is still heap-allocated.
- **Per-step thunk allocation in the trampoline (only off the fused path).** M26's ANF peephole fuses
  the common self-tail-recursive `Let(MkClosure(f,[]), TailCall(Var0,arg))` step into a `Jump`, and A3
  folds each *non-tail* captureless partial application (`CallClosure(MkClosure(f,[]), a)`) into a
  `CallGlobal` (`bl_app_global`, no closure alloc) — so the curried multi-argument loop step (the
  `fill-from`/`scan-depth` lexer family, `(loop f …)`) no longer allocates a closure per partial
  application either. What A3 does **not** remove is the loop's own *capturing* partial-application
  closure (`loop f` returns a closure over `f`): currying is single-argument, so a true multi-arg
  *loop back-edge* would need an uncurried calling convention / multi-arg `Jump` (a future codegen
  change), not an ANF fold. A guarded recursion whose step matches neither fused shape still allocates
  a thunk per step (bounded *stack*, O(n) *heap*).
- **ANF was the pipeline bottleneck; now linear.** ANF used to scale super-linearly (the O(n²)
  re-shift behind table 2a's growth); M29 (§2h) made normalization linear via a deferred de Bruijn
  `Shift` and a streamed bind accumulator. The 2a microbench rows predate that fix — re-run
  `cargo bench --bench pipeline` for current numbers.
- **Growable heap, boxing-dominated.** The heap starts at 64 MiB and grows by doubling
  semi-spaces under pressure (`major_collect_grow`), so only a true host-OOM aborts; the standing
  cost is that GC throughput and the still-boxed majority of values (everything past the M21
  immediates) dominate, not exhaustion. The `treesum` row in §2h is where this shows up.
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

Multicore + serializer benchmarks (the share-nothing runtime, §2e — needs `clang`, no LLVM/cargo):

```bash
bench/multicore.sh            # worker-pool SPEEDUP table + serializer MB/s
BL_TSAN=1 bench/multicore.sh  # same, built under ThreadSanitizer (race check)
```

The same two benches also run as guarded unit tests in the normal suite:

```bash
cargo test -p blight-codegen --features llvm worker_pool_scales_with_cores serializer_throughput_reported
```

## 6. See also

- [benchmarks-game.md](benchmarks-game.md) — a "Benchmarks Game"–style writeup: Blight-vs-Blight
  scaling tables (compile pipeline, region-vs-GC, list/tree algorithms, the 1M-deep trampoline) plus
  a measured cross-language table (fib/sum/factorial/treesum across C/Rust/OCaml/Haskell/Blight-Int/
  Blight-Nat/Python, via [bench/game.sh](../bench/game.sh)) where the M20/M21/M22 sweep puts
  Blight-Int in the C/Rust/OCaml cluster on the register-bound loops (~0.9–1.1 ms, within ~1.3–1.9× of
  C), and the alloc-churn `treesum` row (§2h) places it a single-digit multiple off the native GC'd
  languages.
- [roadmap.md](roadmap.md) — what each missing capability (unboxed `Int`/`Float`, I/O, arrays,
  growable heap, FFI, a frame loop) would cost and whether it touches the trusted kernel.
