# C1 investigation: does Blight still need a dedicated uncurrying pass?

Wave 6/C1 of the Blight Arc II roadmap set out to "add an uncurrying / known-arity call pass on top of
the existing 0-CFA (`cfa.rs`) + `capspec.rs` + `defunc.rs`… when the CFA proves a self-recursive
function's flow-set is a single known function always applied at full arity, rewrite the call to a
direct multi-arg `Tail::Call` with no intermediate `MkClosure`," targeting the `binrec` benchmark's
documented "~151 MB because each curried self-call materializes partial-application closures."

This document records the investigation: what the actual current behavior is (measured, not assumed),
why the specific `binrec` regression no longer needs a new pass, and where a genuine — but narrower and
lower-priority than originally scoped — gap remains.

## 1. The `binrec` claim was stale

`binrec` (`bench/games/binrec/binrec_int.bl`) is **unary**: `Pi ((d Nat)) Int`. Dumping its compiled
ANF (`BL_DUMP_ANF=1 cargo run -p blight-repl --features llvm -- build … `) shows its self-recursive
call compiles to a bare `Comp::CallGlobal`/`Tail::Jump` chain inside a heap-worklist loop — **zero**
`MkClosure` at the call site. Running it with `BL_GC_STATS=1` confirms: **2 496 bytes allocated, 0
collections**, and `hyperfine` puts it at **~1.18 ms, ~1.1× C** (was documented as ~151 MB / 264 ms /
~240× C). Two independent, pre-existing mechanisms already give this result:

1. **P3 elim-loop / elim-worklist** ([`elimloop.rs`](../crates/blight-codegen/src/elimloop.rs),
   [`elimworklist.rs`](../crates/blight-codegen/src/elimworklist.rs)) recognizes `binrec`'s shape — a
   non-tail, two-occurrence, `IntPrim`-combined structural recursion — and rewrites it into a
   bounded-stack heap-worklist loop. The recursive *call* disappears entirely into loop iteration.
2. **A3 captureless-call spine fusion** ([`anf.rs`](../crates/blight-codegen/src/anf.rs), gated
   `BL_NO_SPINEFUSE`) independently ensures that even without (1), a captureless self/global call —
   **tail or non-tail** — never allocates a closure just to invoke it once. The non-tail case is
   handled directly in `Anfer::atomize`'s `Cir::CallClosure`/`App` arm (matching a literal
   `Cir::MkClosure(name, [])` callee), not only in the tail-position `peephole` pass; both were checked
   by dumping ANF for `binrec` and for `tree-sum`/`build` (also unary, also zero-`MkClosure`).

Both are pure, bit-identical, differentially-gated backend transforms with no kernel/elab footprint —
exactly the invariant C1 asked for — they simply already existed before C1 was scoped.

## 2. A synthetic 2-ary curried self-call is *also* cheap — but not for the reason you'd expect

Since `binrec` itself has no currying to speak of (one argument, one call), a fair test of "does
currying still cause closure churn" needs a genuinely multi-argument, non-tail, self-recursive function.
Two synthetic probes (kept out of the shipped example/bench corpus, reproducible from the snippets
below) were built and measured:

```scheme
; curry2.bl — 2-ary, but TAIL-recursive (an accumulator threaded through the second curry level)
(deftotal count2 (Pi ((n Nat)) (Pi ((acc Int)) Int))
  (lam (n) (lam (acc) (match n
    [(Zero) acc]
    [(Succ m) ((count2 m) (int+ acc (int 1)))]))))
```

This compiles to a **single** `AnfFunc` (no separate curry stages survive) because the *whole* 2-level
curried recursion is itself a tail-accumulator shape that P3's elim-loop (3a) recognizes and collapses
to a `Jump` loop, exactly like `sum`. Zero closures, unsurprising given (1) above.

```scheme
; curry3.bl — 2-ary, NON-tail (tree recursion, like binrec, but genuinely curried)
(deftotal binrec2 (Pi ((d Nat)) (Pi ((bias Int)) Int))
  (lam (d) (lam (bias) (match d
    [(Zero) bias]
    [(Succ m) (int+ (int+ ((binrec2 m) bias) ((binrec2 m) bias)) (int 1))]))))
```

This one *does* build real closures: the compiled outer function (`d`-taking) matches on `d` and
returns `MkClosure(lam_2, [<recursive-call-result>])` in the `Succ` arm — a genuine per-call partial
application. But measuring it (`BL_GC_STATS=1`, d ≈ 19–20, ~2²⁰ total leaf evaluations) shows only
**~1 KB allocated**, both with and without `BL_NO_CSE`. The reason: the outer (`d`-taking) function is
only ever called **`d` times** (once per depth level, building a *linear* chain of `d` nested closures,
each one's captured environment pointing at the next-shallower closure); the **exponential** ~2²⁰-call
fan-out happens entirely inside the already-built `bias`-taking closures re-applying an
*already-constructed* captured value twice, which needs no new `MkClosure` per application. Currying
plus tree-shaped self-recursion is not, by itself, exponential closure churn — it degrades gracefully to
*O(depth)* closures as long as both recursive occurrences reference the same sub-call (`m`, here), which
is exactly the shape both `binrec` and `treesum`'s `build`/`tree-sum` use.

## 3. Where a real gap would live — and why it's out of scope here

A genuine *exponential* closure-churn case needs two **syntactically distinct** call sites that can't
share a single built closure — the textbook example is naïve Fibonacci, `fib(n-1) + fib(n-2)`, which
recurses on **two nested-match-derived binders**. This shape is *already* called out in
`docs/benchmarks-game.md` (caveat 5) as one the current backend **miscompiles** — a tracked correctness
bug entirely independent of currying or closure allocation, which is exactly why `binrec` and `treesum`
deliberately use the "same single-match binder, twice" shape instead. Building a new multi-argument
uncurrying pass whose sole live test case is a program shape the backend cannot yet compile *correctly*
would be untestable (no golden to check against) and is not a responsible use of the CFA infrastructure
until that correctness bug is fixed. It remains a candidate for a *future* wave once the nested-match
miscompile is resolved, at which point a real fixture would exist to drive the Red tests C1 specified
(`binrec_recursive_site_has_no_mkclosure`-style structural assertions plus a
`partial_arity_call_is_left_untouched` soundness twin).

## 4. Disposition

C1 is closed as **already satisfied** for its stated target (`binrec`'s closure churn) rather than
requiring new machinery: the Done criterion ("binrec allocation drops from ~151 MB toward the baseline;
matrix bit-identical; no other bench regresses") already holds, verified above. What shipped as part of
C1:

- Corrected, re-measured numbers and mechanism explanation in `docs/benchmarks-game.md` and
  `docs/performance.md` (the previous text was accurate for an earlier point in the codebase's history
  but had gone stale as P3/A3/P7 landed).
- Regression-locking tests in `crates/blight-codegen/src/anf.rs` asserting `binrec`'s compiled
  self-call site has no `MkClosure`, and a soundness twin asserting a genuinely-capturing partial
  application is *not* incorrectly fused — both wired into the crate's existing differential
  (`BL_NO_SPINEFUSE`) bit-identity discipline.
- This document, so a future contributor re-reading the plan doesn't re-implement a pass the codebase
  already subsumes, and knows exactly what the residual (Fibonacci-shaped, correctness-blocked) gap is.
