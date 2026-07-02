/* worker_test.c — standalone C test for the M17 share-nothing worker pool.
 *
 * Built and run by the Rust harness in `runtime.rs` (with -pthread, optionally ThreadSanitizer).
 * Verifies a parallel map/reduce: submit N independent tasks across a pool of workers, each task
 * computing on its OWN thread-local heap, then join and reduce the results deterministically.
 *
 * The task squares its Int argument after allocating a lot of garbage (to force each worker's own
 * GC to run concurrently with the others — the share-nothing stress). With inputs 0..N-1 the
 * reduced sum of squares is deterministic regardless of scheduling, proving:
 *   - workers run in parallel on isolated heaps (no shared mutable state, tsan-clean);
 *   - arguments/results cross worker boundaries by structural copy (data-only);
 *   - results are correct and order-independent.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>

/* `bl_int`/`bl_int_val` now live in the always-linked numeric.c (M21 unboxing). */

/* Worker task: given Int n, allocate churn garbage (force this worker's GC), build a small live
 * list to exercise tracing, then return Int (n*n). Runs entirely on the worker's thread-local heap. */
static BlValue square_with_churn(BlValue arg) {
  int64_t n = bl_int_val(arg);

  /* Build a short live list and keep it rooted across churn, so the worker's GC must trace real
   * roots while collecting (stresses share-nothing correctness). */
  BlValue list = NULL;
  bl_gc_push_root(&list);
  for (int i = 0; i < 50; i++) {
    BlValue node = bl_alloc(BL_CON, 2, 0);
    node->fields[0] = bl_int((int64_t)i);
    node->fields[1] = list;
    bl_write_barrier(node, node->fields[0]);
    bl_write_barrier(node, node->fields[1]);
    list = node;
    bl_gc_poll();
  }
  for (int i = 0; i < 200000; i++) {
    BlValue garbage = bl_alloc(BL_TUPLE, 3, 0);
    (void)garbage;
    bl_gc_poll();
  }
  /* Sanity: the live list survived this worker's collections. */
  int count = 0;
  for (BlValue p = list; p != NULL; p = p->fields[1]) count++;
  bl_gc_pop_roots(1);
  if (count != 50) { fprintf(stderr, "worker: live list corrupted (len %d)\n", count); abort(); }

  return bl_int(n * n);
}

#define N 64

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  BlPool *pool = bl_pool_create(4, 256 * 1024);

  /* Submit N tasks (square 0..N-1) across the pool. */
  BlTask *tasks[N];
  for (int i = 0; i < N; i++) {
    BlValue arg = bl_int((int64_t)i);
    bl_gc_push_root(&arg);
    tasks[i] = bl_pool_submit(pool, square_with_churn, arg);
    bl_gc_pop_roots(1);
  }

  /* Join and reduce: sum of squares 0..N-1. */
  int64_t total = 0;
  for (int i = 0; i < N; i++) {
    BlValue r = bl_pool_join(pool, tasks[i]);
    total += bl_int_val(r);
  }

  bl_pool_destroy(pool);

  int64_t expected = 0;
  for (int i = 0; i < N; i++) expected += (int64_t)i * (int64_t)i;

  if (total != expected) {
    fprintf(stderr, "worker: parallel sum-of-squares wrong: got %lld want %lld\n",
            (long long)total, (long long)expected);
    return 1;
  }
  printf("WORKER_OK %lld\n", (long long)total);
  return 0;
}
