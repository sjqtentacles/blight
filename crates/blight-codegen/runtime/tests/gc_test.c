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
#include <string.h>

/* `bl_int`/`bl_int_val`/`bl_con` now live in the always-linked numeric.c (M21 unboxing). */

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
  if (keep == NULL || bl_obj_tag(keep) != BL_CON || bl_obj_aux(keep) != 123) {
    fprintf(stderr, "gen: long-lived root corrupted after churn\n");
    bl_gc_pop_roots(2);
    return 1;
  }
  if (keep->fields[0] == NULL || bl_obj_tag(keep->fields[0]) != BL_INT ||
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
   * the old->young edge the write barrier must record. A boxed heap object (not a tagged immediate)
   * so it is a real young allocation the barrier must protect. */
  BlValue young = bl_alloc(BL_CON, 0, 55);
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
  if (survived == NULL || bl_obj_tag(survived) != BL_CON || bl_obj_aux(survived) != 55) {
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

  if (root == NULL || bl_obj_aux(root) != 7) {
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

/* A1 (flattened escaping products): a flattened parent is just an ordinary wide all-pointer object
 * with a correctly widened `nfields` — `Pair (Pair a b) c` flattens to one CON with 3 pointer slots.
 * The precise tracer walks `nfields` `BlValue` slots uniformly, so a flattened object must survive a
 * collection with every inlined slot intact and *no tracer change*. This test pins that invariant so
 * a future tracer edit that special-cased layouts could not silently break flattening. */
static int test_flattened_wide_object_survives(void) {
  /* Three distinct boxed children standing in for the flattened slots `a`, `b`, `c`. */
  BlValue flat = bl_alloc(BL_CON, 3, 0);
  flat->header.aux = 77; /* parent constructor index */
  bl_gc_push_root(&flat);

  BlValue a = bl_int(11);
  BlValue b = bl_int(22);
  BlValue c = bl_int(33);
  /* Young->young edges into a young parent: no barrier needed yet. */
  flat->fields[0] = a;
  flat->fields[1] = b;
  flat->fields[2] = c;

  for (int i = 0; i < 2000000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 2, 0);
    (void)g;
    bl_gc_poll();
  }

  if (flat == NULL || bl_obj_tag(flat) != BL_CON || bl_obj_aux(flat) != 77 ||
      flat->header.nfields != 3) {
    fprintf(stderr, "flat: wide parent header corrupted after churn\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  if (flat->fields[0] == NULL || bl_int_val(flat->fields[0]) != 11 ||
      flat->fields[1] == NULL || bl_int_val(flat->fields[1]) != 22 ||
      flat->fields[2] == NULL || bl_int_val(flat->fields[2]) != 33) {
    fprintf(stderr, "flat: a flattened slot was lost or corrupted after churn\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  bl_gc_pop_roots(1);
  return 0;
}

static int test_packed_string_survives_churn(void) {
  /* A2: a packed BL_STRING is a zero-field object whose `aux` is a non-heap (malloc'd, program-
   * lifetime) side buffer. The precise GC must copy it by header size and trace nothing — exactly
   * like BL_NAT — so the object and its readable codepoints survive heavy nursery churn unchanged. */
  static const uint64_t cps[] = {72, 105, 33}; /* "Hi!" */
  BlValue s = bl_string_from_codepoints(cps, 3);
  bl_gc_push_root(&s);

  for (int i = 0; i < 2000000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 2, 0);
    (void)g;
    bl_gc_poll();
  }

  if (s == NULL || bl_obj_tag(s) != BL_STRING || s->header.nfields != 0) {
    fprintf(stderr, "string: packed header corrupted after churn\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  if (bl_string_len_of_value(s) != 3 || bl_string_codepoint_at(s, 0) != 72 ||
      bl_string_codepoint_at(s, 1) != 105 || bl_string_codepoint_at(s, 2) != 33) {
    fprintf(stderr, "string: packed codepoints lost or corrupted after churn\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  bl_gc_pop_roots(1);
  return 0;
}

/* A4 stats accounting: the new BL_GC_STATS counters must stay internally consistent. Every
 * collection is exactly one minor or one major (`collections == minor + major`), every growing major
 * is also counted as a major (`grows <= major`), and heavy nursery churn must drive at least one
 * minor collection that promotes some bytes (a long-lived root is forced into the old generation). */
static int test_stats_counters_consistent(void) {
  size_t minor_before = bl_gc_minor();
  size_t promoted_before = bl_gc_promoted_bytes();
  size_t allocated_before = bl_gc_bytes_allocated();

  /* A long-lived rooted object guarantees something is promoted on the first minor collection. */
  BlValue keep = bl_con(5, 1);
  keep->header.aux = 5;
  bl_gc_push_root(&keep);
  keep->fields[0] = bl_int(4242);

  for (int i = 0; i < 2000000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 2, 0);
    (void)g;
    bl_gc_poll();
  }

  if (bl_gc_collections() != bl_gc_minor() + bl_gc_major()) {
    fprintf(stderr, "stats: collections != minor + major (%zu vs %zu + %zu)\n", bl_gc_collections(),
            bl_gc_minor(), bl_gc_major());
    bl_gc_pop_roots(1);
    return 1;
  }
  if (bl_gc_grows() > bl_gc_major()) {
    fprintf(stderr, "stats: grows > major (%zu > %zu)\n", bl_gc_grows(), bl_gc_major());
    bl_gc_pop_roots(1);
    return 1;
  }
  if (bl_gc_minor() <= minor_before) {
    fprintf(stderr, "stats: expected minor collections under churn\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  if (bl_gc_promoted_bytes() <= promoted_before) {
    fprintf(stderr, "stats: expected promoted bytes for a long-lived root\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  /* bytes_allocated must account for at least the 2,000,000 two-field tuples just churned (each
   * sizeof(BlHeader) + 2 fields), and the cumulative allocated total can never be below what was
   * promoted out of the nursery (everything promoted was allocated first). */
  size_t churn_bytes = (size_t)2000000 * (sizeof(BlHeader) + 2u * sizeof(BlValue));
  if (bl_gc_bytes_allocated() - allocated_before < churn_bytes) {
    fprintf(stderr, "stats: bytes_allocated grew by %zu, expected >= %zu\n",
            bl_gc_bytes_allocated() - allocated_before, churn_bytes);
    bl_gc_pop_roots(1);
    return 1;
  }
  if (bl_gc_bytes_allocated() < bl_gc_promoted_bytes()) {
    fprintf(stderr, "stats: bytes_allocated < promoted_bytes (%zu < %zu)\n",
            bl_gc_bytes_allocated(), bl_gc_promoted_bytes());
    bl_gc_pop_roots(1);
    return 1;
  }
  if (keep == NULL || bl_obj_aux(keep) != 5 || bl_int_val(keep->fields[0]) != 4242) {
    fprintf(stderr, "stats: long-lived root corrupted\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  bl_gc_pop_roots(1);
  return 0;
}

/* P4.1 mark-compact old generation: a heavy, long-lived rooted set must survive repeated *major*
 * collections with every value intact (a use-after-free in the compaction's relocation would corrupt
 * or lose one), AND the old generation's reserved footprint must be ~1x the live set under
 * compaction — a single region — versus the legacy semi-space's ~2x (two regions). We allocate a flat
 * array of long-lived rooted CONs (each carrying a checkable child), interleaving dead churn to force
 * promotions and majors, then assert: (a) at least one major ran; (b) every rooted object and its
 * child is intact (compaction relocated them correctly — the UAF gate, sharpest under ASan); (c) the
 * reserved/region invariant for the active mode. Under `BL_GC_OLDGEN=compact` the harness additionally
 * requires that compaction is actually active (the RED until the single-region collector lands). */
#define BL_OLDGEN_KEEP 20000
static BlValue g_keep[BL_OLDGEN_KEEP];

static int test_oldgen_compaction_peak(void) {
  const char *mode = getenv("BL_GC_OLDGEN");
  int want_compact = mode && strcmp(mode, "compact") == 0;
  size_t major_before = bl_gc_major();

  /* A large, long-lived rooted set: each CON carries an INT child with a distinctive value so a
   * mis-relocation (UAF / lost forwarding) is detectable by content, not just liveness. */
  for (int i = 0; i < BL_OLDGEN_KEEP; i++) {
    BlValue node = bl_con(1, 1);
    node->header.aux = (uint64_t)(0xC0DE0000u + (unsigned)i);
    bl_gc_push_root(&g_keep[i]);
    g_keep[i] = node;
    node->fields[0] = bl_int(1000 + i);
    /* node is young; node->child is a young->young edge (no barrier needed). */

    /* Dead churn between live allocations to force nursery collections and, as the old region fills,
     * major collections / compactions. */
    for (int j = 0; j < 64; j++) {
      BlValue garbage = bl_alloc(BL_TUPLE, 3, 0);
      (void)garbage;
      bl_gc_poll();
    }
  }

  if (bl_gc_major() <= major_before) {
    fprintf(stderr, "compact: expected at least one major collection under the live-set load\n");
    bl_gc_pop_roots(BL_OLDGEN_KEEP);
    return 1;
  }

  /* (b) UAF gate: every long-lived rooted object + its child relocated correctly across the majors. */
  for (int i = 0; i < BL_OLDGEN_KEEP; i++) {
    BlValue node = g_keep[i];
    if (node == NULL || bl_obj_tag(node) != BL_CON ||
        bl_obj_aux(node) != (uint64_t)(0xC0DE0000u + (unsigned)i)) {
      fprintf(stderr, "compact: rooted object %d corrupted/lost after compaction\n", i);
      bl_gc_pop_roots(BL_OLDGEN_KEEP);
      return 1;
    }
    if (node->fields[0] == NULL || bl_obj_tag(node->fields[0]) != BL_INT ||
        bl_int_val(node->fields[0]) != (int64_t)(1000 + i)) {
      fprintf(stderr, "compact: rooted object %d's child corrupted/lost after compaction\n", i);
      bl_gc_pop_roots(BL_OLDGEN_KEEP);
      return 1;
    }
  }

  /* (a)/(c) mode + footprint invariant. */
  int compacting = bl_gc_oldgen_compacting();
  if (want_compact && !compacting) {
    fprintf(stderr, "compact: BL_GC_OLDGEN=compact requested but compaction is not active\n");
    bl_gc_pop_roots(BL_OLDGEN_KEEP);
    return 1;
  }
  size_t cap = bl_gc_old_capacity();
  size_t reserved = bl_gc_old_reserved_bytes();
  if (compacting) {
    /* One region: peak old footprint ~= live (1x), not the semi-space 2x. */
    if (reserved != cap) {
      fprintf(stderr, "compact: expected one old region (reserved %zu == capacity %zu)\n", reserved,
              cap);
      bl_gc_pop_roots(BL_OLDGEN_KEEP);
      return 1;
    }
  } else {
    if (reserved != 2 * cap) {
      fprintf(stderr, "compact: legacy semi-space should reserve two regions (%zu vs 2*%zu)\n",
              reserved, cap);
      bl_gc_pop_roots(BL_OLDGEN_KEEP);
      return 1;
    }
  }

  bl_gc_pop_roots(BL_OLDGEN_KEEP);
  if (compacting) printf("COMPACT_OK\n");
  return 0;
}

/* P4.2 adaptive heap sizing (compacting mode): the old region must SHRINK after the live set collapses
 * to a small fraction of a previously-grown region, and must NOT oscillate (repeatedly grow/shrink)
 * under a subsequently *stable* live set. We grow a large rooted live set (forcing the region to grow),
 * drop almost all of it and force a compaction (which reclaims the garbage, sees low occupancy, and
 * shrinks), then force several more compactions under the now-stable retained set and assert the
 * capacity / grow / shrink counters all stay put — the hysteresis (shrink band + growth slack)
 * guarantees no churn. Shrinking is a compacting-mode feature, so the test is a no-op under the legacy
 * semi-space. */
static int test_oldgen_adaptive_shrink(void) {
  if (!bl_gc_oldgen_compacting()) return 0;

  /* Phase A: a large rooted live set grows the old region well past its initial capacity. */
  for (int i = 0; i < BL_OLDGEN_KEEP; i++) {
    BlValue node = bl_alloc(BL_CON, 4, (uint64_t)i);
    bl_gc_push_root(&g_keep[i]);
    g_keep[i] = node;
    for (int j = 0; j < 16; j++) {
      BlValue garbage = bl_alloc(BL_TUPLE, 2, 0);
      (void)garbage;
      bl_gc_poll();
    }
  }
  bl_gc_force_collect();
  size_t cap_big = bl_gc_old_capacity();

  /* Phase B: drop all but a small retained set; one forced compaction reclaims the garbage, observes
   * low occupancy, and shrinks the region. */
  const int keepW = 1024;
  for (int i = keepW; i < BL_OLDGEN_KEEP; i++) g_keep[i] = NULL;
  size_t shrinks_before = bl_gc_old_shrinks();
  bl_gc_force_collect();
  size_t cap_small = bl_gc_old_capacity();
  if (!(cap_small < cap_big)) {
    fprintf(stderr, "sizing: expected the old region to shrink after low occupancy (%zu !< %zu)\n",
            cap_small, cap_big);
    bl_gc_pop_roots(BL_OLDGEN_KEEP);
    return 1;
  }
  if (bl_gc_old_shrinks() <= shrinks_before) {
    fprintf(stderr, "sizing: expected a shrink event to be recorded\n");
    bl_gc_pop_roots(BL_OLDGEN_KEEP);
    return 1;
  }

  /* Phase C (no oscillation): the retained live set is now stable. Repeated forced compactions must
   * not resize the region — capacity, grows, and shrinks all stay put. */
  size_t cap_c0 = bl_gc_old_capacity();
  size_t grows_c0 = bl_gc_grows();
  size_t shrinks_c0 = bl_gc_old_shrinks();
  for (int k = 0; k < 8; k++) bl_gc_force_collect();
  if (bl_gc_old_capacity() != cap_c0) {
    fprintf(stderr, "sizing: capacity oscillated under a stable live set (%zu -> %zu)\n", cap_c0,
            bl_gc_old_capacity());
    bl_gc_pop_roots(BL_OLDGEN_KEEP);
    return 1;
  }
  if (bl_gc_grows() != grows_c0 || bl_gc_old_shrinks() != shrinks_c0) {
    fprintf(stderr, "sizing: resized repeatedly under a stable live set (grows %zu->%zu shrinks %zu->%zu)\n",
            grows_c0, bl_gc_grows(), shrinks_c0, bl_gc_old_shrinks());
    bl_gc_pop_roots(BL_OLDGEN_KEEP);
    return 1;
  }

  /* Correctness: the retained set survived the shrink relocation intact. */
  for (int i = 0; i < keepW; i++) {
    if (g_keep[i] == NULL || bl_obj_tag(g_keep[i]) != BL_CON ||
        bl_obj_aux(g_keep[i]) != (uint64_t)i) {
      fprintf(stderr, "sizing: retained object %d corrupted after shrink\n", i);
      bl_gc_pop_roots(BL_OLDGEN_KEEP);
      return 1;
    }
  }

  bl_gc_pop_roots(BL_OLDGEN_KEEP);
  return 0;
}

/* C2 (Blight Arc II): old-gen compaction is now ON BY DEFAULT (BL_GC_OLDGEN unset), reversible via
 * `BL_GC_OLDGEN=semispace`. This is the RED-then-GREEN test for the flip itself: with the env var left
 * exactly as the caller set it (which may be unset, "semispace", or "compact" — this harness is run
 * under all three by the Rust suite), a heavier stress than `test_oldgen_compaction_peak` — more
 * rounds, forcing many majors and, when compacting, several grow/shrink cycles — must survive with the
 * live set fully intact, AND the *default* (unset) case must observe `bl_gc_oldgen_compacting() == 1`
 * while an explicit "semispace" must observe `0`. Prints `DEFAULT_COMPACT_ON`/`DEFAULT_COMPACT_OFF`
 * matching the mode actually observed, so the Rust harness can assert the flip landed without having to
 * re-derive the expectation from the env var itself. */
#define BL_DEFAULT_STRESS_KEEP 4096
#define BL_DEFAULT_STRESS_ROUNDS 8
static int test_oldgen_compaction_default_on_survives_stress(void) {
  const char *mode = getenv("BL_GC_OLDGEN");
  int opted_out = mode && strcmp(mode, "semispace") == 0;
  size_t major_before = bl_gc_major();
  static BlValue keep[BL_DEFAULT_STRESS_KEEP];

  for (int round = 0; round < BL_DEFAULT_STRESS_ROUNDS; round++) {
    for (int i = 0; i < BL_DEFAULT_STRESS_KEEP; i++) {
      BlValue node = bl_con(1, 1);
      node->header.aux = (uint64_t)(0xDEFA0000u + (unsigned)(round * BL_DEFAULT_STRESS_KEEP + i));
      bl_gc_push_root(&keep[i]);
      keep[i] = node;
      node->fields[0] = bl_int(round * 100000 + i);
      for (int j = 0; j < 24; j++) {
        BlValue garbage = bl_alloc(BL_TUPLE, 3, 0);
        (void)garbage;
        bl_gc_poll();
      }
    }
    /* Verify this round's live set before dropping it for the next — every round must relocate
     * cleanly, not just the final one (a compaction bug could corrupt an *earlier* generation's
     * survivors while leaving the most recent round, which has had less time to move, intact). */
    for (int i = 0; i < BL_DEFAULT_STRESS_KEEP; i++) {
      BlValue node = keep[i];
      uint64_t want_aux = (uint64_t)(0xDEFA0000u + (unsigned)(round * BL_DEFAULT_STRESS_KEEP + i));
      if (node == NULL || bl_obj_tag(node) != BL_CON || bl_obj_aux(node) != want_aux) {
        fprintf(stderr, "default-stress: round %d object %d corrupted/lost\n", round, i);
        bl_gc_pop_roots(BL_DEFAULT_STRESS_KEEP);
        return 1;
      }
      if (node->fields[0] == NULL || bl_obj_tag(node->fields[0]) != BL_INT ||
          bl_int_val(node->fields[0]) != (int64_t)(round * 100000 + i)) {
        fprintf(stderr, "default-stress: round %d object %d's child corrupted/lost\n", round, i);
        bl_gc_pop_roots(BL_DEFAULT_STRESS_KEEP);
        return 1;
      }
    }
    bl_gc_pop_roots(BL_DEFAULT_STRESS_KEEP);
  }

  if (bl_gc_major() <= major_before) {
    fprintf(stderr, "default-stress: expected many major collections under the stress load\n");
    return 1;
  }

  int compacting = bl_gc_oldgen_compacting();
  if (!opted_out && !compacting) {
    fprintf(stderr, "default-stress: BL_GC_OLDGEN unset (or non-semispace) must default to compaction\n");
    return 1;
  }
  if (opted_out && compacting) {
    fprintf(stderr, "default-stress: BL_GC_OLDGEN=semispace must still opt out of compaction\n");
    return 1;
  }
  printf(compacting ? "DEFAULT_COMPACT_ON\n" : "DEFAULT_COMPACT_OFF\n");
  return 0;
}

/* P1 (roadmap Wave 10, A3b go-bar item 3): a boxed array's backing `BL_TUPLE` object is a normal
 * GC-heap object, but the ONLY reference to it a Blight program ever holds is an opaque `Int`
 * handle indexing `boxed_array.c`'s off-heap `g_boxed[]` table — an edge the precise tracer would
 * never see without `bl_boxed_array_gc_roots`. This test stores freshly-consed heap `BlValue`s (not
 * immediates) into a boxed array, forces both a minor AND a major collection via nursery/old-gen
 * churn, then reads every slot back and asserts it is STRUCTURALLY the same value — not merely "did
 * not crash" (ASan catches a UAF; a silent stale-pointer read that happens not to fault would not
 * fault the sanitizer either, so the check must be by value, per the go-bar). */
static int test_boxed_array_survives_minor_and_major_gc_structurally(void) {
  size_t major_before = bl_gc_major();

  /* Element 0 holds a distinctive Con with a child Int; element 1 holds a plain Int (an immediate
   * or small box, exercising the "never a pointer" path through the same table uniformly). */
  BlValue elem0 = bl_con(42, 1);
  bl_gc_push_root(&elem0);
  elem0->fields[0] = bl_int(4242);
  BlValue elem1 = bl_int(777);

  int64_t h = bl_boxed_array_new(2, elem0);
  if (h < 0) {
    fprintf(stderr, "boxed: allocation failed\n");
    bl_gc_pop_roots(1);
    return 1;
  }
  bl_boxed_array_set(h, 1, elem1);
  bl_gc_pop_roots(1);

  if (bl_boxed_array_length(h) != 2) {
    fprintf(stderr, "boxed: unexpected length %zu\n", bl_boxed_array_length(h));
    return 1;
  }

  /* Churn hard enough to force at least one minor AND one major collection (the go-bar's explicit
   * "across at least one real collection cycle" requirement) while the array handle is the only
   * live reference to its elements. */
  for (int i = 0; i < 3000000; i++) {
    BlValue garbage = bl_alloc(BL_TUPLE, 4, 0);
    (void)garbage;
    bl_gc_poll();
  }
  bl_gc_force_collect(); /* guarantee at least one major, not just minors */

  if (bl_gc_major() <= major_before) {
    fprintf(stderr, "boxed: expected at least one major collection\n");
    return 1;
  }

  BlValue got0 = bl_boxed_array_get(h, 0);
  BlValue got1 = bl_boxed_array_get(h, 1);
  if (got0 == NULL || bl_obj_tag(got0) != BL_CON || bl_obj_aux(got0) != 42 ||
      bl_obj_nfields(got0) != 1 || got0->fields[0] == NULL ||
      bl_obj_tag(got0->fields[0]) != BL_INT || bl_int_val(got0->fields[0]) != 4242) {
    fprintf(stderr, "boxed: element 0 corrupted/lost across GC\n");
    return 1;
  }
  if (got1 == NULL || bl_obj_tag(got1) != BL_INT || bl_int_val(got1) != 777) {
    fprintf(stderr, "boxed: element 1 corrupted/lost across GC\n");
    return 1;
  }
  return 0;
}

/* P1 go-bar item 4: the write-barrier regression test. Promote a boxed array's backing object into
 * the old generation, then — WITHOUT ever re-touching the array handle in the mutator in between —
 * store a fresh (nursery) value into one of its slots via `bl_boxed_array_set` (which must call
 * `bl_write_barrier`) and force a MINOR collection only (not a major, which would trivially survive
 * regardless of the barrier since a major relocates everything). If the barrier were missing, the
 * young value would be unreachable from the minor collector's perspective (roots + remembered set
 * only) and would be silently reclaimed out from under the still-live array slot. */
static int test_boxed_array_write_barrier_old_to_young(void) {
  BlValue init = bl_int(0);
  int64_t h = bl_boxed_array_new(1, init);
  if (h < 0) {
    fprintf(stderr, "boxed-wb: allocation failed\n");
    return 1;
  }

  /* Promote the backing object into the old generation by surviving churn (no live reference to it
   * besides the handle table itself — exactly the scenario bl_boxed_array_gc_roots must handle). */
  for (int i = 0; i < 600000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 2, 0);
    (void)g;
    bl_gc_poll();
  }

  /* A fresh YOUNG heap value (not an immediate) stored into the now-old backing object's slot — the
   * exact old->young edge the write barrier exists to protect. bl_boxed_array_set must barrier it. */
  BlValue young = bl_alloc(BL_CON, 0, 987);
  young->header.aux = 987;
  bl_boxed_array_set(h, 0, young);

  /* Minor-only churn (never bl_gc_force_collect, which would go major and mask a missing barrier). */
  for (int i = 0; i < 600000; i++) {
    BlValue g = bl_alloc(BL_TUPLE, 2, 0);
    (void)g;
    bl_gc_poll();
  }

  BlValue survived = bl_boxed_array_get(h, 0);
  if (survived == NULL || bl_obj_tag(survived) != BL_CON || bl_obj_aux(survived) != 987) {
    fprintf(stderr, "boxed-wb: write barrier failed — old->young value lost (got %p)\n",
            (void *)survived);
    return 1;
  }
  return 0;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  int rc = 0;
  rc |= test_minor_collects_nursery_keeps_old();
  rc |= test_write_barrier_old_to_young_survives();
  rc |= test_survives_nursery_churn();
  rc |= test_flattened_wide_object_survives();
  rc |= test_packed_string_survives_churn();
  rc |= test_stats_counters_consistent();
  rc |= test_oldgen_compaction_peak();
  rc |= test_oldgen_adaptive_shrink();
  rc |= test_oldgen_compaction_default_on_survives_stress();
  rc |= test_boxed_array_survives_minor_and_major_gc_structurally();
  rc |= test_boxed_array_write_barrier_old_to_young();
  if (rc == 0) printf("GEN_GC_OK\nBOXED_ARRAY_OK\n");
  return rc;
}
