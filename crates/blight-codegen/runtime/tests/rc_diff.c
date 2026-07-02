/* rc_diff.c — RED test (committed, NOT YET GREEN) for Wave 10 / P6 (RC + in-place reuse).
 *
 * STATUS: this is the go-bar's committed failing test, not a working feature. It does not compile
 * today: `bl_gc_reused_bytes()` (line ~30 below) is a hoped-for observability accessor for an
 * in-place-reuse pass that does not exist yet (mirroring the `bl_gc_old_shrinks()`/
 * `bl_gc_peak_old_reserved_bytes()` accessor pattern P4.2/P4.3 used for the analogous "prove the
 * mechanism actually fired" gate). See `docs/design-rc-reuse.md` for the full go-bar, the finding
 * that blocked a real attempt this pass, and exactly what a future implementer needs to build before
 * this file can compile, let alone pass. The corresponding Rust harness
 * (`runtime::tests::in_place_reuse_is_observationally_identical`, `crates/blight-codegen/src/runtime.rs`)
 * is `#[ignore]`d with that same pointer, so `cargo test` stays green without silently hiding this gap
 * (it is discoverable via `cargo test -- --ignored`, and fails loudly — a clang compile error, not a
 * silent skip — the moment anyone tries to run it).
 *
 * THE PROPERTY THIS FILE PINS (for whoever implements P6): build a long-lived, alloc-heavy `map`-style
 * workload (transform every cons cell of a long list, once, in a linear/non-retaining way — a real C
 * analogue of `crates/blight-codegen/src/linearity.rs`'s `Verdict::Linear` shape: the OLD cons cell of
 * a `map` step is projected exactly once, immediately re-boxed into a NEW cons cell of the identical
 * `BL_CON`/2-field shape, and never referenced again). The differential gate this test would run
 * (mirroring `gc_diff.c`'s three-way checksum compare) is:
 *
 *   1. `RC_DIFF_CHECKSUM` must be BIT-IDENTICAL whether or not in-place reuse fires (observational
 *      invisibility — reuse may change *how* memory is recycled, never *what* the program computes).
 *   2. Under the (not-yet-real) `BL_NO_REUSE` unset default, `bl_gc_reused_bytes()` must be > 0 for
 *      this workload (the mechanism actually fired — a "the pass ran but did nothing" false green,
 *      exactly what `docs/roadmap-post-m6.md`'s honest-scope invariant forbids); under `BL_NO_REUSE=1`
 *      it must be exactly 0 (the pass is fully disabled, not just quiescent).
 *   3. Built and run under AddressSanitizer (`build_and_run_harness_cfg(..., asan: true, ...)`, the
 *      `gc_test.c` precedent): zero UAF / zero heap-buffer-overflow. This is the load-bearing check —
 *      reuse mutates a cell's fields in place instead of allocating fresh, so ASan is the only
 *      mechanical proof available that no stale/relocated pointer was written through.
 *
 * A real implementation would additionally need to prove "reuse fires ONLY where linearity.rs's
 * `is_transiently_consumed` says `Verdict::Linear`" — a codegen-level assertion (e.g. a debug-build
 * `assert()` in the emitted reuse call site, or a compiler-side unit test on the ANF rewrite) that
 * this pure-C runtime test cannot express on its own; it is listed here for completeness of the
 * go-bar, not as something this file checks.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdint.h>

#define RC_DIFF_N 20000

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  BlValue list = NULL;
  bl_gc_push_root(&list);
  for (int i = RC_DIFF_N - 1; i >= 0; i--) {
    BlValue node = bl_alloc(BL_CON, 2, 0); /* Cons(Int, rest) */
    node->fields[0] = bl_int((int64_t)i);
    node->fields[1] = list;
    bl_write_barrier(node, node->fields[0]);
    bl_write_barrier(node, node->fields[1]);
    list = node;
    bl_gc_poll();
  }

  /* The `map`-shaped reuse candidate: walk `list` once, consuming each cons cell exactly once
   * (a single `->fields[0]`/`->fields[1]` read, never referenced again after this loop iteration —
   * the C analogue of `linearity.rs`'s Linear verdict) and rebuild a transformed list. A real
   * in-place-reuse pass would rewrite this exact shape to mutate each old cell's fields instead of
   * calling `bl_alloc` again; this hand-written C loop always allocates fresh (there is no codegen
   * pass to intercept), which is exactly why `bl_gc_reused_bytes()` — the thing that would prove
   * reuse fired on a *compiled Blight program* doing the same shape — does not exist yet either.
   */
  BlValue mapped = NULL;
  bl_gc_push_root(&mapped);
  BlValue cur = list;
  bl_gc_push_root(&cur);
  while (cur != NULL) {
    int64_t v = bl_int_val(cur->fields[0]);
    BlValue rest = cur->fields[1];
    BlValue node = bl_alloc(BL_CON, 2, 0);
    node->fields[0] = bl_int(v * 2 + 1);
    node->fields[1] = mapped;
    bl_write_barrier(node, node->fields[0]);
    bl_write_barrier(node, node->fields[1]);
    mapped = node;
    cur = rest;
    bl_gc_poll();
  }
  bl_gc_pop_roots(1); /* cur */

  uint64_t checksum = 1469598103934665603ULL; /* FNV-1a offset basis */
  for (BlValue p = mapped; p != NULL; p = p->fields[1]) {
    int64_t v = bl_int_val(p->fields[0]);
    checksum ^= (uint64_t)v;
    checksum *= 1099511628211ULL;
  }
  bl_gc_pop_roots(2); /* mapped, list */

  printf("RC_DIFF_CHECKSUM=%llu\n", (unsigned long long)checksum);
  /* INTENTIONALLY RED: `bl_gc_reused_bytes()` is not declared in `blight_rt.h` and not defined in
   * `gc.c` — there is no in-place-reuse mechanism to observe yet. This call is the go-bar's pinned
   * "prove the mechanism actually fired, not just quiescent" check (item 2 in the header comment);
   * a future implementer makes this file compile by building that accessor for real. */
  printf("RC_DIFF_REUSED_BYTES=%zu\n", bl_gc_reused_bytes());
  printf("RC_DIFF_OK\n");
  return 0;
}
