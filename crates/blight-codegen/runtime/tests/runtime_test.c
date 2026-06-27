/* runtime_test.c — standalone C tests for the Blight runtime (spec §7.3/§7.4, §9 headline).
 *
 * These exercise the runtime in isolation of the compiler, so the deep-recursion and GC-pressure
 * guarantees are verified directly. Built and run by the Rust test harness in `runtime.rs`.
 *
 * Tests:
 *   - million_deep_via_delay_no_overflow: force a 1,000,000-step Delay chain in bounded C stack.
 *   - gc_collects_under_pressure: allocate far more than the heap so the collector must run, and
 *     verify a root survives every collection.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>

/* Local copies of the primitive constructors (normally in prelude_rt.c, which also defines `main`
 * and the program entry; the harness brings its own `main`, so we avoid linking that file). */
BlValue bl_int(int64_t n) { return bl_alloc(BL_INT, 0, (uint64_t)n); }
int64_t bl_int_val(BlValue v) { return (int64_t)v->header.aux; }
BlValue bl_con(uint64_t ctor_index, uint32_t nfields) {
  return bl_alloc(BL_CON, nfields, ctor_index);
}

/* ---- a countdown Delay built from LATER thunks ----
 *
 * A step closure captures the remaining count in field[1] (a BL_INT). Applying it:
 *   count == 0  ->  now(BL_INT 0)        [a BL_NOW holding the final value]
 *   count  > 0  ->  later(next step)     [a BL_LATER holding the next step closure]
 *
 * `bl_force` drives this without growing the C stack, regardless of `count`.
 */
static BlValue countdown_step(BlValue self);

static BlValue make_step(int64_t count) {
  /* closure: header.aux = fn ptr, fields[0] = boxed count */
  BlValue clo = bl_alloc(BL_CLOSURE, 1, (uint64_t)(uintptr_t)countdown_step);
  bl_gc_push_root(&clo);
  clo->fields[0] = bl_int(count);
  bl_gc_pop_roots(1);
  return clo;
}

static BlValue countdown_step(BlValue self) {
  int64_t count = bl_int_val(self->fields[0]);
  if (count <= 0) {
    BlValue now = bl_alloc(BL_NOW, 1, 0);
    now->fields[0] = bl_int(0);
    return now;
  }
  BlValue later = bl_alloc(BL_LATER, 1, 0);
  bl_gc_push_root(&later);
  later->fields[0] = make_step(count - 1);
  bl_gc_pop_roots(1);
  return later;
}

static int test_million_deep(void) {
  BlValue start = bl_alloc(BL_LATER, 1, 0);
  bl_gc_push_root(&start);
  start->fields[0] = make_step(1000000);
  BlValue result = bl_force(start);
  bl_gc_pop_roots(1);
  if (result == NULL || result->header.tag != BL_INT || bl_int_val(result) != 0) {
    fprintf(stderr, "million_deep: wrong result\n");
    return 1;
  }
  return 0;
}

static int test_gc_pressure(void) {
  /* A live root we will verify survives collection. */
  BlValue keep = bl_con(7, 0);
  bl_gc_push_root(&keep);

  /* Allocate a large amount of garbage to force many collections. The heap is small (set by the
   * harness via bl_gc_init); each iteration allocates a 4-field tuple and drops it. */
  for (int i = 0; i < 2000000; i++) {
    BlValue garbage = bl_alloc(BL_TUPLE, 4, 0);
    (void)garbage;
    bl_gc_poll();
  }

  size_t collections = bl_gc_collections();
  if (collections == 0) {
    fprintf(stderr, "gc_pressure: expected at least one collection\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  /* `keep` must have survived (and been forwarded) intact. */
  if (keep == NULL || keep->header.tag != BL_CON || keep->header.aux != 7) {
    fprintf(stderr, "gc_pressure: live root corrupted across %zu collections\n", collections);
    bl_gc_pop_roots(1);
    return 1;
  }
  bl_gc_pop_roots(1);
  return 0;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024); /* small 1 MiB heap to force collections under pressure */
  bl_stack_init();

  int rc = 0;
  rc |= test_million_deep();
  rc |= test_gc_pressure();
  if (rc == 0) printf("RUNTIME_OK\n");
  return rc;
}
