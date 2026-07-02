/* serialize_bench.c — structural (de)serializer THROUGHPUT benchmark (M18, perf proof).
 *
 * Built and run by the Rust harness in `runtime.rs`. The serializer is the boundary primitive both
 * the M17 worker pool and the M19 distributed transport ride on: every cross-heap / cross-machine
 * message is one `bl_value_serialize` (flatten to bytes) + one `bl_value_deserialize` (rebuild in the
 * destination heap). This harness quantifies that hot path on a representative message:
 *   - build one deep structure (a long cons-list of small Con/Int nodes, the shape real messages
 *     take — lists, trees, tagged records),
 *   - measure its serialized blob size once,
 *   - loop serialize+deserialize ITERS times under CLOCK_MONOTONIC,
 *   - report blob bytes, ns per round-trip op, and MB/s (bytes moved through serialize, per second).
 *
 * Determinism/correctness is already covered by serialize_test.c; here we additionally assert the
 * round-trip stays structurally equal on the first iteration (cheap sanity) and that throughput is a
 * sane non-zero number, then print the machine-readable summary the Rust driver / docs consume.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

/* `bl_int`/`bl_int_val` now live in the always-linked numeric.c (M21 unboxing). */

/* Length of the representative cons-list message. Each node is a 2-field Con (head Int, tail). */
#define LIST_LEN 2000
/* Round-trip iterations to time (serialize + deserialize each). */
#define ITERS 20000

static int value_eq(BlValue a, BlValue b) {
  if (a == NULL || b == NULL) return a == b;
  if (bl_obj_tag(a) != bl_obj_tag(b) || bl_obj_nfields(a) != bl_obj_nfields(b) || bl_obj_aux(a) != bl_obj_aux(b))
    return 0;
  for (uint32_t i = 0; i < bl_obj_nfields(a); i++)
    if (!value_eq(a->fields[i], b->fields[i])) return 0;
  return 1;
}

int main(void) {
  bl_gc_init(8 * 1024 * 1024);
  bl_stack_init();

  /* Build the representative message: a LIST_LEN cons-list of small nodes, kept rooted. */
  BlValue msg = NULL;
  bl_gc_push_root(&msg);
  for (int i = 0; i < LIST_LEN; i++) {
    BlValue node = bl_alloc(BL_CON, 2, 0);
    node->fields[0] = bl_int((int64_t)i);
    node->fields[1] = msg;
    bl_write_barrier(node, node->fields[0]);
    bl_write_barrier(node, node->fields[1]);
    msg = node;
    bl_gc_poll();
  }

  /* Measure the blob size once and sanity-check a single round-trip. */
  size_t blob_len = 0;
  void *probe = bl_value_serialize(msg, &blob_len);
  if (!probe || blob_len == 0) { fprintf(stderr, "serialize_bench: NULL/empty blob for data value\n"); return 1; }
  BlValue back0 = bl_value_deserialize(probe, blob_len);
  free(probe);
  if (!value_eq(msg, back0)) { fprintf(stderr, "serialize_bench: round-trip not structurally equal\n"); return 1; }

  /* Timed loop: serialize + deserialize ITERS times. */
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  volatile int64_t sink = 0;
  for (int it = 0; it < ITERS; it++) {
    size_t len = 0;
    void *blob = bl_value_serialize(msg, &len);
    if (!blob) { fprintf(stderr, "serialize_bench: NULL blob mid-loop\n"); return 1; }
    BlValue back = bl_value_deserialize(blob, len);
    sink += bl_int_val(back->fields[0]); /* touch the result so nothing is optimized away */
    free(blob);
    bl_gc_poll();
  }
  clock_gettime(CLOCK_MONOTONIC, &t1);
  bl_gc_pop_roots(1);
  (void)sink;

  double secs = (double)(t1.tv_sec - t0.tv_sec) + (double)(t1.tv_nsec - t0.tv_nsec) / 1e9;
  double ns_per_op = (secs * 1e9) / (double)ITERS;
  /* MB/s: total bytes moved THROUGH serialize across all iterations / time. */
  double total_bytes = (double)blob_len * (double)ITERS;
  double mb_per_s = (total_bytes / (1024.0 * 1024.0)) / secs;

  if (!(ns_per_op > 0.0) || !(mb_per_s > 0.0)) {
    fprintf(stderr, "serialize_bench: implausible throughput (ns_per_op=%.3f mb_per_s=%.3f)\n",
            ns_per_op, mb_per_s);
    return 1;
  }

  printf("SERIALIZE_BENCH list_len=%d iters=%d blob_bytes=%zu ns_per_op=%.1f MB_per_s=%.1f\n",
         LIST_LEN, ITERS, blob_len, ns_per_op, mb_per_s);
  printf("SERIALIZE_BENCH_OK blob_bytes=%zu ns_per_op=%.1f MB_per_s=%.1f\n",
         blob_len, ns_per_op, mb_per_s);
  return 0;
}
