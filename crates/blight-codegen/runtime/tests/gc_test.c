/* gc_test.c — standalone C tests for the generational copying GC (spec §7.3).
 *
 * Built and run by the Rust harness in `runtime.rs`. Verifies:
 *   - generational_minor_collects_nursery_keeps_old: heavy nursery churn triggers (minor)
 *     collections that reclaim dead young objects while a long-lived rooted object stays valid;
 *   - write_barrier_old_to_young_survives: a young value stored into an already-promoted (old)
 *     object survives a minor GC *only because* the write barrier remembered the old object;
 *   - generational_gc_survives_nursery_churn: a long-lived root is intact after many collections.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>

BlValue bl_int(int64_t n) { return bl_alloc(BL_INT, 0, (uint64_t)n); }
int64_t bl_int_val(BlValue v) { return (int64_t)v->header.aux; }
BlValue bl_con(uint64_t ctor_index, uint32_t nfields) {
  return bl_alloc(BL_CON, nfields, ctor_index);
}

/* A long-lived rooted object survives heavy nursery churn (many minor collections). */
static int test_minor_collects_nursery_keeps_old(void) {
  size_t collections_before = bl_gc_collections();

  /* A distinctive long-lived object, kept live by a root. */
  BlValue keep = bl_con(123, 1);
  keep->header.aux = 123;
  bl_gc_push_root(&keep);

  /* Give it a child too, to check fields survive promotion intact. */
  BlValue child = bl_int(999);
  bl_gc_push_root(&child);
  keep->fields[0] = child;
  /* keep and child are both young here; the edge keep->child is young->young (no barrier needed). */

  /* Churn: allocate a flood of immediately-dead young objects. */
  for (int i = 0; i < 2000000; i++) {
    BlValue garbage = bl_alloc(BL_TUPLE, 4, 0);
    (void)garbage;
    bl_gc_poll();
  }

  if (bl_gc_collections() == collections_before) {
    fprintf(stderr, "gen: expected collections under nursery churn\n");
    bl_gc_pop_roots(2);
    return 1;
  }
  if (keep == NULL || BL_TAG(keep) != BL_CON || keep->header.aux != 123) {
    fprintf(stderr, "gen: long-lived root corrupted after churn\n");
    bl_gc_pop_roots(2);
    return 1;
  }
  if (keep->fields[0] == NULL || BL_TAG(keep->fields[0]) != BL_INT ||
      bl_int_val(keep->fields[0]) != 999) {
    fprintf(stderr, "gen: long-lived root's child lost or corrupted\n");
    bl_gc_pop_roots(2);
    return 1;
  }
  bl_gc_pop_roots(2);
  return 0;
}

/* The write barrier: store a *young* value into an *old* object's field after the object has been
 * promoted, then churn the nursery. Without the barrier the young value would be unreachable from
 * the minor GC's perspective (it scans roots + remembered set only) and be collected. With the
 * barrier the old object is in the remembered set, so the young value survives and is promoted. */
static int test_write_barrier_old_to_young_survives(void) {
  /* Promote `parent` into the old generation by surviving at least one collection. */
  BlValue parent = bl_con(1, 1);
  parent->fields[0] = NULL;
  bl_gc_push_root(&parent);

  /* First churn: forces collection(s); `parent` survives and is promoted to old. */
  for (int i = 0; i < 600000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 2, 0);
    (void)g;
    bl_gc_poll();
  }

  /* Now create a fresh YOUNG value and store it into the (now old) parent's field. This is exactly
   * the old->young edge the write barrier must record. */
  BlValue young = bl_con(55, 0);
  young->header.aux = 55;
  parent->fields[0] = young;
  bl_write_barrier(parent, young);

  /* Churn again to drive minor collections. `young` is reachable ONLY through `parent`'s field, so
   * it survives iff the barrier remembered `parent`. */
  for (int i = 0; i < 600000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 2, 0);
    (void)g;
    bl_gc_poll();
  }

  BlValue survived = parent->fields[0];
  if (survived == NULL || BL_TAG(survived) != BL_CON || survived->header.aux != 55) {
    fprintf(stderr, "gen: write barrier failed — old->young value lost (got %p)\n",
            (void *)survived);
    bl_gc_pop_roots(1);
    return 1;
  }
  bl_gc_pop_roots(1);
  return 0;
}

/* A long-lived root remains intact across many collections (the generational acceptance shape). */
static int test_survives_nursery_churn(void) {
  BlValue root = bl_con(7, 2);
  root->header.aux = 7;
  bl_gc_push_root(&root);
  BlValue a = bl_int(1000);
  BlValue b = bl_int(2000);
  root->fields[0] = a;
  root->fields[1] = b;

  for (int i = 0; i < 3000000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 3, 0);
    (void)g;
    bl_gc_poll();
  }

  if (root == NULL || root->header.aux != 7) {
    fprintf(stderr, "gen: root lost after heavy churn\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  if (bl_int_val(root->fields[0]) != 1000 || bl_int_val(root->fields[1]) != 2000) {
    fprintf(stderr, "gen: root's children corrupted after heavy churn\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  bl_gc_pop_roots(1);
  return 0;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  int rc = 0;
  rc |= test_minor_collects_nursery_keeps_old();
  rc |= test_write_barrier_old_to_young_survives();
  rc |= test_survives_nursery_churn();
  if (rc == 0) printf("GEN_GC_OK\n");
  return rc;
}
