/* gc_diff.c — the differential gate for C2 (old-gen compaction default-on).
 *
 * The autism invariant: the old-generation strategy (the single-region mark-compact collector vs the
 * legacy two-space semi-space) is UNTRUSTED runtime memory tuning — it may change *when* and *how* the
 * old generation is reclaimed, but it must never change what a program computes. This harness runs one
 * deterministic, alloc-heavy workload — many long-lived rooted CON nodes (each carrying a distinctive
 * Int child) interleaved with dead churn, under a small heap that forces repeated major collections —
 * and folds every surviving node's content into a single FNV-1a checksum. That checksum *is* the
 * "observable heap contents" this gate pins: it depends only on values the collector preserved, never
 * on addresses, iteration counts, or any other GC-internal bookkeeping.
 *
 * The Rust harness in runtime.rs runs this SAME binary three times — `BL_GC_OLDGEN` unset (the
 * default), `=semispace`, and `=compact` — and asserts the printed checksum is bit-identical across all
 * three, while `GC_DIFF_COMPACTING` and `GC_DIFF_MAJORS` confirm each leg actually exercised the mode
 * (and stress) it claims to.
 *
 * Prints:
 *   GC_DIFF_CHECKSUM=<u64>
 *   GC_DIFF_MAJORS=<size_t>
 *   GC_DIFF_COMPACTING=<0|1>
 *   GC_DIFF_OK
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdint.h>

#define GC_DIFF_N 20000

static BlValue g_keep[GC_DIFF_N];

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  size_t major_before = bl_gc_major();

  for (int i = 0; i < GC_DIFF_N; i++) {
    BlValue node = bl_con(1, 1);
    node->header.aux = (uint64_t)((uint32_t)i * 2654435761u);
    bl_gc_push_root(&g_keep[i]);
    g_keep[i] = node;
    node->fields[0] = bl_int((int64_t)(i * 3 - 7));
    for (int j = 0; j < 8; j++) {
      BlValue garbage = bl_alloc(BL_TUPLE, 2, 0);
      (void)garbage;
      bl_gc_poll();
    }
  }
  bl_gc_force_collect();
  bl_gc_force_collect();

  uint64_t checksum = 1469598103934665603ULL; /* FNV-1a offset basis */
  for (int i = 0; i < GC_DIFF_N; i++) {
    BlValue node = g_keep[i];
    if (node == NULL || bl_obj_tag(node) != BL_CON) {
      fprintf(stderr, "gc_diff: node %d lost or corrupted\n", i);
      return 1;
    }
    uint64_t aux = bl_obj_aux(node);
    int64_t child = bl_int_val(node->fields[0]);
    checksum ^= aux;
    checksum *= 1099511628211ULL;
    checksum ^= (uint64_t)child;
    checksum *= 1099511628211ULL;
  }
  bl_gc_pop_roots(GC_DIFF_N);

  printf("GC_DIFF_CHECKSUM=%llu\n", (unsigned long long)checksum);
  printf("GC_DIFF_MAJORS=%zu\n", bl_gc_major() - major_before);
  printf("GC_DIFF_COMPACTING=%d\n", bl_gc_oldgen_compacting());
  printf("GC_DIFF_OK\n");
  return 0;
}
