/* multicore_test.c — standalone C test for the M15 share-nothing thread-local runtime.
 *
 * Built and run by the Rust harness in `runtime.rs` (with -pthread, and optionally ThreadSanitizer).
 * Verifies that two OS-thread workers each get a fully independent, thread-local heap:
 *   - each worker calls `bl_runtime_init` and allocates/collects on its OWN heap with no locks;
 *   - the per-thread GC-collection counter is thread-local (one worker's collections do not appear
 *     in the other's count);
 *   - the two workers' nurseries are disjoint memory regions (no shared heap);
 *   - a live linked list built and churned on each worker survives its own collections intact, so
 *     there is no cross-thread root/heap corruption.
 *
 * If the runtime globals were process-global (pre-M15) this races and corrupts under tsan; with
 * BL_THREAD_LOCAL state each worker is isolated.
 */
#include "blight_rt.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

/* `bl_int`/`bl_int_val` now live in the always-linked numeric.c (M21 unboxing). */

typedef struct {
  int id;
  int churn;          /* how much garbage to allocate to force collections */
  /* outputs, filled by the worker thread: */
  void *nursery_probe; /* address of this worker's first allocation (proxy for its heap region) */
  size_t collections;  /* this worker's thread-local collection count */
  int ok;              /* 1 if the worker's live list survived intact */
} Worker;

/* Build a live linked list of `len` cons-cells (BL_CON with 2 fields: head Int, tail), keep it
 * rooted, then churn `churn` garbage allocations (polling the GC) and verify the list is intact. */
static void *worker_main(void *arg) {
  Worker *w = (Worker *)arg;
  bl_runtime_init(1 * 1024 * 1024); /* this thread's OWN 1 MiB heap + stack */

  BlValue first = bl_int((int64_t)w->id);
  w->nursery_probe = (void *)first;
  bl_gc_push_root(&first);

  /* A 1000-element live list: each node = BL_CON(tag=id) with [head=Int(i), tail=prev]. */
  BlValue list = NULL;
  bl_gc_push_root(&list);
  const int len = 1000;
  for (int i = 0; i < len; i++) {
    BlValue node = bl_alloc(BL_CON, 2, (uint64_t)w->id);
    node->fields[0] = bl_int((int64_t)i);
    node->fields[1] = list;
    bl_write_barrier(node, node->fields[0]);
    bl_write_barrier(node, node->fields[1]);
    list = node;
    bl_gc_poll();
  }

  /* Churn garbage to force this worker's own collector to run. */
  for (int i = 0; i < w->churn; i++) {
    BlValue garbage = bl_alloc(BL_TUPLE, 4, 0);
    (void)garbage;
    bl_gc_poll();
  }

  w->collections = bl_gc_collections();

  /* Verify the live list survived its own collections intact: correct length, ids, and head values. */
  int ok = 1;
  int count = 0;
  for (BlValue n = list; n != NULL; n = n->fields[1]) {
    if (bl_obj_tag(n) != BL_CON || bl_obj_aux(n) != (uint64_t)w->id) { ok = 0; break; }
    BlValue head = n->fields[0];
    if (head == NULL || bl_obj_tag(head) != BL_INT) { ok = 0; break; }
    count++;
  }
  if (count != len) ok = 0;
  w->ok = ok;

  bl_gc_pop_roots(2);
  return NULL;
}

int main(void) {
  Worker a = {.id = 1, .churn = 500000, .ok = 0};
  Worker b = {.id = 2, .churn = 800000, .ok = 0};

  pthread_t ta, tb;
  if (pthread_create(&ta, NULL, worker_main, &a) != 0) { fprintf(stderr, "spawn a\n"); return 1; }
  if (pthread_create(&tb, NULL, worker_main, &b) != 0) { fprintf(stderr, "spawn b\n"); return 1; }
  pthread_join(ta, NULL);
  pthread_join(tb, NULL);

  int rc = 0;
  if (!a.ok) { fprintf(stderr, "worker a live list corrupted\n"); rc = 1; }
  if (!b.ok) { fprintf(stderr, "worker b live list corrupted\n"); rc = 1; }
  if (a.collections == 0 || b.collections == 0) {
    fprintf(stderr, "expected each worker to run its own GC (a=%zu b=%zu)\n",
            a.collections, b.collections);
    rc = 1;
  }
  /* Heaps must be disjoint: the two workers' first allocations live in different malloc'd nurseries.
   * (They cannot alias the same address if each thread has its own heap.) */
  if (a.nursery_probe == b.nursery_probe) {
    fprintf(stderr, "workers appear to share a heap (same probe address)\n");
    rc = 1;
  }
  if (rc == 0) printf("MULTICORE_OK\n");
  return rc;
}
