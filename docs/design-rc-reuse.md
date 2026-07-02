# P6 go-bar: RC + in-place reuse (Perceus-style functional-update reuse)

**Status: SHARPENED NEGATIVE — deferred, with a committed red test.** (roadmap Arc II, Wave 10 / P6).
This is the hardest of the six Wave 10 bets and was pre-declared in the plan as the likeliest to land
this way. It does. This document is the go-bar, the finding (which sharpens and partially *revises*
the earlier `docs/roadmap-post-m6.md` P5.1 investigation), and the committed failing test
(`crates/blight-codegen/runtime/tests/rc_diff.c`) for whoever picks this back up.

## The ask

`linearity.rs` (Wave 6 / C3) is an **analysis-only** substrate today: `is_transiently_consumed`
classifies a `let`-bound heap allocation as `Verdict::Linear` (read exactly once, in a non-retaining
position — a `Proj`, or the scrutinee of a `Case`) / `Shared` / `Dead`, wired into the pipeline as a
pure identity transform (`analyze_gated`, gated `BL_NO_LINEARITY`, deliberately **not** in
`DIFF_FLAGS` since it changes nothing observable). P6 asks: build the *consumer* — an ANF pass that,
at a proven-`Linear` site, reuses the dying cell's memory for a same-shape replacement instead of
calling `bl_alloc` again (the canonical Perceus example: `map (*2)` over a list reuses each `cons`
cell's memory for the transformed cell, instead of building an entirely new spine next to the
about-to-be-garbage old one).

## Go-bar (the falsifiable bar a real implementation must clear)

1. **Zero UAF, proven under AddressSanitizer** — the load-bearing check. Reuse mutates a live cell's
   fields in place; ASan is the only mechanical proof available that no stale or already-relocated
   pointer is written through, and that the reused cell's old field values are never read after they
   would have been (in the non-reuse build) collected.
2. **Bit-identical observable output** whether the pass fires or not (`BL_NO_REUSE`, appended to
   `DIFF_FLAGS` — reuse may change *how* memory is recycled, never *what* the program computes).
3. **"Reuse fires only where C3 proved `Linear`"** — a checkable invariant, not just a claim (a debug
   assertion at the emitted reuse site, or a compiler-side unit test asserting the ANF rewrite never
   fires on a `Shared`/`Dead` classification).
4. **A measured allocation-count or throughput win** on a realistic `map`/`foldr`-shaped workload —
   otherwise this is risk for no reward (see "P7 already captured the headline win" below).

`crates/blight-codegen/runtime/tests/rc_diff.c` pins go-bar items 1 and 2 as a committed, currently
**non-compiling** test (it calls `bl_gc_reused_bytes()`, an accessor that does not exist), and its
header comment documents item 3's shape for a future implementer. It is wired into
`crates/blight-codegen/src/runtime.rs` as `#[ignore]`d test `in_place_reuse_is_observationally_identical`
so `cargo test` stays green while the gap remains loudly discoverable via `cargo test -- --ignored`
(confirmed: it fails with a clear `clang` "undeclared function `bl_gc_reused_bytes`" error, not a
silent skip).

## Finding: this pass's attempt, and where it stopped

The earlier investigation (`docs/roadmap-post-m6.md` P5.1, Grand Arc / Perf Frontier II) found RC +
in-place reuse "no-go for now" on three structural grounds, the first being decisive: *"Perceus reuse
assumes a non-moving heap … Blight's collector moves objects (Cheney/compaction), so 'reuse this slot'
races evacuation and is unsound without a pin/safepoint discipline the runtime does not have."*

This pass re-examined that specific claim, because it conflates two different things Perceus's paper
calls "reuse":

- **General Perceus reuse** (what Koka/Lean implement): a `drop`-to-zero at *any* point produces an
  opaque **reuse token** — a raw address — that can be threaded as an ordinary value through arbitrary
  further control flow (stored in a variable, passed across a call) before a later `alloc` decides
  whether to reuse it. Because the token is an untyped address the GC does not trace, a moving
  collection between the `drop` and the `alloc` invalidates it silently. **This is genuinely
  unsound on Blight's moving collector without a pin/safepoint discipline** — the original finding is
  correct about *this* shape, and it is real Perceus's actual mechanism.
- **A narrower, purely-static "same-arm" reuse** (what `linearity.rs`'s *structural*, whole-function
  local analysis can actually prove, and the only shape this pass considered attempting): the dying
  value is never turned into an opaque address at all. It stays a normal, GC-traced, rooted `BlValue`
  from its last read (the `Case` dispatch on it) through to the point its fields are overwritten with
  the new constructor's values, all within the same eliminator arm. If a GC safepoint falls in that
  window, the collector relocates it exactly as it would any other live value spanning a safepoint
  (the shadow-stack root is updated transparently); the reuse rewrite then simply mutates fields
  through the *current* (possibly-already-relocated) pointer, under the same write-barrier discipline
  every other in-place field mutation in this runtime already uses (boxed arrays, actor state). No
  pin, no opaque address, no new GC mechanism — **this narrower shape does not, by itself, race a
  moving collector.**

So the pure memory-safety argument that shut down the general case does not, on its own, shut down the
narrow one. Having found that, this pass looked at what actually implementing the narrow case would
require, and stopped there — not because it is unsound, but because it is a **large, correctness-
critical new codegen surface** for a win P7 has already mostly captured elsewhere:

- **A new ANF construct and emitter path.** The rewrite needs a new `Comp`/`Tail` shape (e.g.
  `ReuseCon(old_var, tag, field_exprs)`) distinct from `Con`/`Tuple`, plus `llvm.rs` support to lower
  it as a direct field-mutation sequence (GEP + store + `bl_write_barrier` per field, skipping
  `bl_alloc` and the header initialization) — new surface in the one part of the compiler where a bug
  is a memory-safety violation, not a wrong number, and (per `linearity.rs`'s own module doc) "the
  differential harness cannot reliably catch a UAF."
- **A real consumer pass, not a query.** `is_transiently_consumed` answers "is this binding linear in
  its continuation" for one variable at a time; a reuse pass needs to additionally prove the SHAPE
  match (same tag, same field count between the dying value's constructor and the new one being
  built), locate it structurally at the exact right point in the `Tail::Case` arm, and reject anything
  it cannot prove — the current substrate provides the classification query but not this site-finding
  and shape-matching machinery.
- **Correctness under every other backend pass.** The reuse site must survive (or be correctly
  re-derived after) `unbox`/`flatten`/`cse`/`inline`/`mono`/`closure` — several of which restructure
  exactly the `Con`/`Proj`/`Case` shapes a reuse rewrite would need to match against. Getting the
  *interaction* right (not just the standalone transform) is a materially bigger proof obligation than
  the transform itself.
- **The measured win is mostly already banked, at far lower risk.** The textbook motivating case —
  `map`/`foldr` immediately consuming a freshly built structure — is exactly what **P7 deforestation/
  fusion** (`fusion.rs`, shipped, on by default) already removes at compile time for the single-consumer
  `foldr f z (map g xs)` shape: the intermediate list is never built at all, so there is no cons cell
  left to reuse. Reuse would only add value on shapes fusion does not cover (a `map` whose result is
  retained, or a general non-`foldr` consumer) — a narrower and less-measured payoff than the original
  motivating example suggested.

**Disposition: defer.** The moving-collector objection is *not* the wall for the narrow, statically-
proven-linear shape this pass would have to build (a genuine partial revision of the P5.1 finding,
recorded here for whoever revisits this); the wall is that building a sound, checkable, all-passes-
interacting-correctly codegen rewrite for a win P7 has mostly already banked is a large investment for
a shrinking marginal return. If revisited, the prerequisite is *not* a new GC mode (no
`BL_GC_NONMOVING` needed for the narrow shape) but: (a) the new ANF `Reuse` construct + emitter path,
(b) a shape-matching consumer pass built on top of (not instead of) `is_transiently_consumed`, (c)
proof it composes correctly with every pass between `lower` and `llvm`, and (d) `rc_diff.c` actually
compiling and green under ASan with a measured win on a shape P7 does not already fuse away.

## Relationship to the other Wave 4 go-bars

Indexed alongside the other Wave 4 go-bars in
[`docs/design-wave4-gobars.md`](design-wave4-gobars.md) §2, which is updated to point here for the
Arc II Wave 10 / P6 revisit rather than only the original P5.1 investigation.
