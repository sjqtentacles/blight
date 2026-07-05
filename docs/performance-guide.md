# Staying fast: the user-facing performance guide

Blight's performance is **deliberately two-speed**, and knowing which speed a line of code runs
at is the single highest-leverage fact in this guide. The measured story lives in
[`performance.md`](performance.md) and [`benchmarks-game.md`](benchmarks-game.md); this page is
the distilled "what do I *do*" version. Numbers below are the in-tree measurements (Apple M2 Pro,
release, LLVM 18) — treat the shapes as durable and re-run the harness for absolutes.

## The two-speed model

| | `Int` (and `Float` on top of it) | unary `Nat` |
|---|---|---|
| representation | 64-bit machine word (tagged immediate) | `Succ`/`Zero` heap cells — a literal of size *n* is *n* cells |
| arithmetic | one hardware instruction | O(n) allocation per operation (unless recognized — below) |
| measured | fib/sum/factorial in the **C/Rust/OCaml cluster** (1.2–2.2× C) | sum caps out around n=10³ (deep `Succ` chains overflow the produced binary's stack) |
| use for | anything arithmetic-heavy, loop counters, keys, sizes | *meaning*: indices you prove things about, structural recursion, specs |

**Rule 1: compute with `Int`, prove with `Nat`.** Decimal literals are `Nat` sugar — `4` is
`(Succ (Succ (Succ (Succ Zero))))`; a machine integer is written `(int 4)`. `std/int.bl` has the
arithmetic (`int-add` … `int-mod`, `int-abs`), `if-zero` is the branch primitive, and
`examples/int_branch.bl` shows the `Bool` bridge.

## The recognizer contract (why some `Nat` code is fast anyway)

The backend recognizes the **prelude's own** `plus`/`mult`/`sub`/`pred` (and `Succ`-peeling) on
machine-word-sized `Nat`s and compiles them to O(1) native ops (M20), with machine-word `Nat`s and
nullary constructors riding unboxed in tagged pointers (M21). The contract:

- **Call the prelude names.** A hand-rolled `my-plus` with the same body falls back to the O(n)
  chain eliminator — the recognizer matches the *known definitions*, not arbitrary code shape.
- Linear folds over lists run in O(1) native stack (the P3 elim-loop transform). **Tree-shaped**
  structural recursion (multiple recursive fields) still descends on the C stack of the produced
  binary — deep trees mean real stack depth.
- Single-consumer build-then-fold pipelines are **fused away at compile time** (P7): the measured
  `treesum` builds a 2²¹-node tree conceptually and allocates ~3 KB actually. Don't contort code
  to avoid intermediate structures the fusion pass already deletes — check first.

## Memory: what allocates, and the two ways out

Values are heap-boxed by default; M21's tagged immediates (machine-word `Nat`/`Int`, nullary
constructors) are the exception. The generational GC (nursery + mark-compact old generation,
~1× live-set peak) is fast; the wins come from not allocating:

- **Region arenas**: `(region r body)` routes the body's non-escaping allocations to an arena
  reclaimed in O(1) at scope exit — zero GC traffic (see `examples/region_scratch.bl`).
- **Mutable runtime storage**: the `Arrays`/`Array`/`Bytes` effects keep bulk data in
  runtime-side storage reached through an `Int` handle — `std/hashmap.bl` is built this way.
- Watch `BL_GC_STATS=1 ./your-binary` — bytes allocated, collections, promoted bytes — before
  optimizing anything.

## Check-time vs run-time

The type-level evaluator is a tree-walking interpreter with native-stack recursion. It is the
wrong place for heavy computation: a ground `main` is *evaluated during checking* by design
(`define-by … compute` proofs likewise). Keep check-time grounds small (the corpus keeps
Ackermann at `A(2,3)`); put the heavy computation in the compiled binary, which gets the
recognizers, unboxing, LTO, and the delay trampoline (`define-rec`'s `later` steps run in bounded
stack).

## Diagnosing a slow program

1. `BL_GC_STATS=1` — is it allocation? (Usually yes.)
2. Grep your hot loop for unary-`Nat` arithmetic or a redefinition shadowing a prelude name.
3. The `BL_NO_*` flags (`BL_NO_NATPRIM`, `BL_NO_NATPEEL`, `BL_NO_UNBOX`, `BL_NO_FLATTEN`, `BL_NO_STRPACK`,
   `BL_NO_ELIMLOOP`, `BL_NO_FUSION`, `BL_NO_CSE`, `BL_NO_CTNORM`, `BL_NO_SPINEFUSE`,
   `BL_NO_INLINE`, `BL_NO_LTO`, `BL_NO_DEFUNC`, `BL_NO_CAPSPEC`, `BL_NO_LINEARITY`,
   `BL_NO_ARITYRAISE`, `BL_NO_AUTOPAR`) each disable one optimization pass.
   They exist as the *differential correctness matrix* (every pass must be bit-identical
   on/off), which makes them perfect for attribution: if `BL_NO_FUSION=1` makes your program
   10× slower, you now know which pass was carrying it. They are diagnostic, not tuning knobs —
   leave them unset in production.
4. The benches: `bench/goldens.sh` (correctness-gated timings) and
   `crates/blight-codegen/benches/{pipeline,runtime}.rs` (criterion, compile- and run-time).

## Honest reference points

From the measured cross-language table (`benchmarks-game.md`): Blight-`Int` register loops sit at
1.2–2.2× C; the fused `treesum` runs 76 ms with a 2.2 MB peak (the smallest footprint of any
language in the table, because the tree never exists); a 10k-element boxed `listfold` is ~5× C —
per-cons boxing is the honest remaining gap on list-shaped code, and closing it further is
tracked research (RC/reuse, escape analysis), not a knob you can turn today.
