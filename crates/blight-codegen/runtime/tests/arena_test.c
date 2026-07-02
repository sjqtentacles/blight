/* arena_test.c — standalone C tests for the region bump-arena (spec §3.5 / §7.3).
 *
 * Built and run by the Rust harness in `runtime.rs`. Verifies:
 *   - arena_enter_alloc_leave_frees: enter/alloc/leave reclaims all arena bytes (O(1) rewind).
 *   - nested scopes pair like a stack.
 *   - arena_objects_not_evacuated: a GC collection traces through arena objects (so GC-heap objects
 *     reachable only via an arena object survive) but does not move the arena objects themselves,
 *     and arena allocation never triggers a collection.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>

/* `bl_int`/`bl_int_val`/`bl_con` now live in the always-linked numeric.c (M21 unboxing). */

static int test_enter_alloc_leave_frees(void) {
  if (bl_arena_live_bytes() != 0) {
    fprintf(stderr, "arena: expected empty arena at start\n");
    return 1;
  }
  bl_arena_enter();
  for (int i = 0; i < 100000; i++) {
    BlValue o = bl_arena_alloc(BL_TUPLE, 3, 0);
    (void)o;
  }
  if (bl_arena_live_bytes() == 0) {
    fprintf(stderr, "arena: expected live bytes after allocating\n");
    return 1;
  }
  if (bl_arena_alloc_count() < 100000) {
    fprintf(stderr, "arena: alloc count too low\n");
    return 1;
  }
  bl_arena_leave();
  if (bl_arena_live_bytes() != 0) {
    fprintf(stderr, "arena: leave did not reclaim all bytes (%zu remain)\n",
            bl_arena_live_bytes());
    return 1;
  }
  return 0;
}

static int test_nested_scopes(void) {
  bl_arena_enter();
  bl_arena_alloc(BL_TUPLE, 2, 0);
  size_t after_outer = bl_arena_live_bytes();
  bl_arena_enter();
  for (int i = 0; i < 50000; i++) bl_arena_alloc(BL_TUPLE, 4, 0);
  bl_arena_leave();
  if (bl_arena_live_bytes() != after_outer) {
    fprintf(stderr, "arena: inner leave must restore the outer frontier exactly\n");
    return 1;
  }
  bl_arena_leave();
  if (bl_arena_live_bytes() != 0) {
    fprintf(stderr, "arena: outer leave must reclaim everything\n");
    return 1;
  }
  return 0;
}

static int test_objects_not_evacuated(void) {
  size_t collections_before = bl_gc_collections();

  /* Build an arena object that points at a fresh GC-heap object. Root the arena object so the GC
   * sees it; the GC-heap child is reachable ONLY through the arena object. */
  bl_arena_enter();
  BlValue arena_obj = bl_arena_alloc(BL_CON, 1, 42);

  /* Allocating the arena object must not have run the GC. */
  if (bl_gc_collections() != collections_before) {
    fprintf(stderr, "arena: arena_alloc must never trigger a GC\n");
    bl_arena_leave();
    return 1;
  }

  bl_gc_push_root(&arena_obj);
  /* A genuine GC-heap child (boxed, not a tagged immediate) so the collector actually has an object
   * to trace through the arena edge and evacuate. */
  BlValue child = bl_alloc(BL_CON, 0, 7);
  arena_obj->fields[0] = child;

  void *arena_addr_before = (void *)arena_obj;

  /* Force collections by churning GC garbage. */
  for (int i = 0; i < 2000000; i++) {
    BlValue garbage = bl_alloc(BL_TUPLE, 4, 0);
    (void)garbage;
    bl_gc_poll();
  }

  if (bl_gc_collections() == 0) {
    fprintf(stderr, "arena: expected GC to run under pressure\n");
    bl_gc_pop_roots(1);
    bl_arena_leave();
    return 1;
  }
  /* The arena object must NOT have moved (it is not in from-space). */
  if ((void *)arena_obj != arena_addr_before) {
    fprintf(stderr, "arena: arena object was moved by the GC\n");
    bl_gc_pop_roots(1);
    bl_arena_leave();
    return 1;
  }
  if (!BL_IS_ARENA(arena_obj) || BL_TAG(arena_obj) != BL_CON) {
    fprintf(stderr, "arena: arena object header corrupted\n");
    bl_gc_pop_roots(1);
    bl_arena_leave();
    return 1;
  }
  /* Its GC-heap child must have survived (traced through the arena object) and be valid. */
  BlValue traced_child = arena_obj->fields[0];
  if (traced_child == NULL || bl_obj_tag(traced_child) != BL_CON || bl_obj_aux(traced_child) != 7) {
    fprintf(stderr, "arena: GC child reachable only via arena object was lost\n");
    bl_gc_pop_roots(1);
    bl_arena_leave();
    return 1;
  }
  bl_gc_pop_roots(1);
  bl_arena_leave();
  return 0;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  int rc = 0;
  rc |= test_enter_alloc_leave_frees();
  rc |= test_nested_scopes();
  rc |= test_objects_not_evacuated();
  if (rc == 0) printf("ARENA_OK\n");
  return rc;
}
