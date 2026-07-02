/* worker.c — share-nothing multicore worker pool (M17) — UNTRUSTED runtime.
 *
 * A pool of N OS threads, each with its OWN thread-local runtime (M15: heap + segmented stack). The
 * pool runs independent Blight computations in PARALLEL on separate heaps with no shared mutable
 * state and no locks on the allocation/GC hot path — the only synchronization is the task queue.
 *
 * Share-nothing discipline (why this is race-free):
 *   - Each worker calls `bl_runtime_init` on entry, so `bl_alloc`/`bl_gc_*` touch only that thread's
 *     thread-local heap (gc.c/arena.c/stack.c globals are BL_THREAD_LOCAL since M15). Workers never
 *     read or write each other's heaps.
 *   - A task's argument is structurally COPIED into the worker's heap before the task runs, and the
 *     task's result is structurally copied back OUT into the submitter's heap. Blight values are
 *     immutable persistent structures (no cycles, no aliasing, no in-place mutation), so a copy is a
 *     simple recursive structural walk over the 7-tag layout (M18 generalizes this into a
 *     (de)serializer for cross-machine transport). After the copy, the two heaps share nothing.
 *   - Actors are placed at submit (spawn/message) boundaries only; a running task is pinned to its
 *     worker for its whole computation (its handler frames / continuations are thread-local and
 *     non-serializable — see std/actor.bl). No in-flight migration / work stealing of continuations.
 *
 * Task ARGUMENTS/RESULTS carry DATA ONLY: `bl_value_serialize`/`deserialize` (M18) reject
 * BL_CLOSURE/BL_OPNODE (a raw function pointer meaningful only in one address space), so a task's
 * `arg`/`env`/result must be first-order data (the Erlang model). The task's CALLEE, however, can now
 * (P5/P4, roadmap Wave 10) be a lifted Blight function named by its stable `code_id`
 * (`bl_pool_submit_code`) rather than only a hand-written native `BlWorkerFn` — see
 * `docs/design-code-mobility.md` for how `code_id` resolution is made safe (same-binary-only,
 * bounds-checked) and `docs/design-wave10-p4-autopar.md` for what auto-parallelism does (and does
 * not yet) build on top of it.
 */
#include "blight_rt.h"
#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

/* The two-argument calling convention every lifted top-level function shares (env, arg) -> result
 * (mirrors `effects.c`'s identically-named, identically-scoped local typedef). Used by
 * `bl_pool_submit_code` (P4, roadmap Wave 10 / auto-parallelism) to invoke a task resolved by P5
 * `code_id` rather than a native `BlWorkerFn`. */
typedef BlValue (*BlFn2)(BlValue env, BlValue arg);

/* Which calling shape a task uses: a hand-written native C `BlWorkerFn` (the original M17 API,
 * `bl_pool_submit`) or a codegen-resolved lifted Blight function (P4's `bl_pool_submit_code`). */
typedef enum { BL_TASK_NATIVE, BL_TASK_CODE } BlTaskKind;

/* A task: run a function on a worker and copy the result back. Arguments are values owned by the
 * submitter; the worker copies them into its own heap before running. `result` is filled (copied
 * into the submitter's heap) when the task completes. `BlWorkerFn`/`BlTask`/`BlPool` are declared in
 * blight_rt.h; here we define the struct bodies. */
struct BlTask {
  BlTaskKind kind;
  BlWorkerFn fn; /* BL_TASK_NATIVE: fn(arg) */
  void *code_fn; /* BL_TASK_CODE: ((BlFn2)code_fn)(env, arg) — resolved from a P5 code_id at submit */
  /* A serialized snapshot of the captured env (BL_TASK_CODE only; absent for a captureless
   * closure), so the worker can rebuild it in its own heap without touching the submitter's heap. */
  void *env_blob;
  size_t env_blob_len;
  int has_env;
  /* A serialized snapshot of the argument (heap-independent bytes), so the worker can rebuild it in
   * its own heap without touching the submitter's heap. */
  void *arg_blob;
  size_t arg_blob_len;
  /* Filled by the worker: a serialized snapshot of the result. The submitter rebuilds it. */
  void *result_blob;
  size_t result_blob_len;
  struct BlTask *next;
  int done;
};

/* ---- structural (de)serialization is provided by serialize.c (M18) ----
 * The worker pool uses `bl_value_serialize` / `bl_value_deserialize` (declared in blight_rt.h) to
 * copy arguments/results across thread-local heaps: a value is flattened to a heap-independent blob
 * in the submitter's heap, then rebuilt fresh in the worker's heap (and vice-versa for the result),
 * so the two heaps share nothing. Data-only (closures/opnodes are rejected) — see serialize.c. */

/* ---- the pool ---- */

struct BlPool {
  pthread_t *threads;
  int nthreads;
  size_t worker_heap_bytes;
  pthread_mutex_t mtx;
  pthread_cond_t have_work;
  pthread_cond_t task_done;
  BlTask *head, *tail; /* FIFO queue of pending tasks */
  int shutdown;
};

static void enqueue(BlPool *p, BlTask *t) {
  t->next = NULL;
  if (p->tail) p->tail->next = t; else p->head = t;
  p->tail = t;
}

static void *worker_loop(void *arg) {
  BlPool *p = (BlPool *)arg;
  bl_runtime_init(p->worker_heap_bytes); /* this thread's OWN heap + stack (M15) */
  for (;;) {
    pthread_mutex_lock(&p->mtx);
    while (!p->head && !p->shutdown) pthread_cond_wait(&p->have_work, &p->mtx);
    if (!p->head && p->shutdown) { pthread_mutex_unlock(&p->mtx); break; }
    BlTask *t = p->head;
    p->head = t->next;
    if (!p->head) p->tail = NULL;
    pthread_mutex_unlock(&p->mtx);

    /* Rebuild the argument(s) in THIS worker's heap (share-nothing), run, serialize the result out. */
    BlValue arg = t->arg_blob ? bl_value_deserialize(t->arg_blob, t->arg_blob_len) : NULL;
    bl_gc_push_root(&arg);
    BlValue res;
    if (t->kind == BL_TASK_CODE) {
      BlValue env = t->has_env ? bl_value_deserialize(t->env_blob, t->env_blob_len) : NULL;
      bl_gc_push_root(&env);
      res = ((BlFn2)t->code_fn)(env, arg);
      bl_gc_pop_roots(1); /* env */
    } else {
      res = t->fn(arg);
    }
    res = bl_force(res); /* a task may return a Delay; force to a value */
    bl_gc_push_root(&res);
    t->result_blob = bl_value_serialize(res, &t->result_blob_len);
    if (!t->result_blob) {
      fprintf(stderr, "blight: worker task returned a non-data value (data-only v1)\n");
      abort();
    }
    bl_gc_pop_roots(2);

    pthread_mutex_lock(&p->mtx);
    t->done = 1;
    pthread_cond_broadcast(&p->task_done);
    pthread_mutex_unlock(&p->mtx);
  }
  return NULL;
}

/* Create a pool of `nthreads` workers, each with a `worker_heap_bytes` thread-local heap. */
BlPool *bl_pool_create(int nthreads, size_t worker_heap_bytes) {
  BlPool *p = (BlPool *)calloc(1, sizeof(BlPool));
  if (!p) { fprintf(stderr, "blight: pool OOM\n"); abort(); }
  p->nthreads = nthreads;
  p->worker_heap_bytes = worker_heap_bytes;
  pthread_mutex_init(&p->mtx, NULL);
  pthread_cond_init(&p->have_work, NULL);
  pthread_cond_init(&p->task_done, NULL);
  p->threads = (pthread_t *)calloc((size_t)nthreads, sizeof(pthread_t));
  for (int i = 0; i < nthreads; i++) {
    if (pthread_create(&p->threads[i], NULL, worker_loop, p) != 0) {
      fprintf(stderr, "blight: pool thread spawn failed\n");
      abort();
    }
  }
  return p;
}

/* Submit `fn(arg)` to the pool. `arg` (owned by the caller, in the caller's heap) is serialized now
 * so the worker rebuilds it independently. Returns an opaque task handle to join on. */
BlTask *bl_pool_submit(BlPool *p, BlWorkerFn fn, BlValue arg) {
  BlTask *t = (BlTask *)calloc(1, sizeof(BlTask));
  if (!t) { fprintf(stderr, "blight: task OOM\n"); abort(); }
  t->kind = BL_TASK_NATIVE;
  t->fn = fn;
  if (arg != NULL) {
    t->arg_blob = bl_value_serialize(arg, &t->arg_blob_len);
    if (!t->arg_blob) {
      fprintf(stderr, "blight: task argument is a non-data value (data-only v1)\n");
      abort();
    }
  }
  pthread_mutex_lock(&p->mtx);
  enqueue(p, t);
  pthread_cond_signal(&p->have_work);
  pthread_mutex_unlock(&p->mtx);
  return t;
}

/* P4 (roadmap Wave 10 / auto-parallelism): submit a task naming a lifted Blight function by its P5
 * `code_id`. See `blight_rt.h`'s doc comment for the resolve-vs-abort contract (a bad `code_id` here
 * is a codegen bug, not untrusted input, unlike the analogous case in `bl_value_deserialize_mobile`). */
BlTask *bl_pool_submit_code(BlPool *p, uint64_t code_id, BlValue env, BlValue taskarg) {
  void *fn = bl_code_table_resolve(code_id);
  if (!fn) {
    fprintf(stderr, "blight: bl_pool_submit_code: code_id %llu not registered (codegen bug)\n",
            (unsigned long long)code_id);
    abort();
  }
  BlTask *t = (BlTask *)calloc(1, sizeof(BlTask));
  if (!t) { fprintf(stderr, "blight: task OOM\n"); abort(); }
  t->kind = BL_TASK_CODE;
  t->code_fn = fn;
  if (env != NULL) {
    t->env_blob = bl_value_serialize(env, &t->env_blob_len);
    if (!t->env_blob) {
      fprintf(stderr, "blight: task env is a non-data value (data-only v1)\n");
      abort();
    }
    t->has_env = 1;
  }
  if (taskarg != NULL) {
    t->arg_blob = bl_value_serialize(taskarg, &t->arg_blob_len);
    if (!t->arg_blob) {
      fprintf(stderr, "blight: task argument is a non-data value (data-only v1)\n");
      abort();
    }
  }
  pthread_mutex_lock(&p->mtx);
  enqueue(p, t);
  pthread_cond_signal(&p->have_work);
  pthread_mutex_unlock(&p->mtx);
  return t;
}

/* Wait for a submitted task, rebuild its result in the CURRENT (caller's) heap, free the task. */
BlValue bl_pool_join(BlPool *p, BlTask *t) {
  pthread_mutex_lock(&p->mtx);
  while (!t->done) pthread_cond_wait(&p->task_done, &p->mtx);
  pthread_mutex_unlock(&p->mtx);
  BlValue res = bl_value_deserialize(t->result_blob, t->result_blob_len);
  free(t->result_blob);
  free(t->arg_blob);
  free(t->env_blob);
  free(t);
  return res;
}

/* Stop all workers (after all tasks have been joined) and free the pool. */
void bl_pool_destroy(BlPool *p) {
  pthread_mutex_lock(&p->mtx);
  p->shutdown = 1;
  pthread_cond_broadcast(&p->have_work);
  pthread_mutex_unlock(&p->mtx);
  for (int i = 0; i < p->nthreads; i++) pthread_join(p->threads[i], NULL);
  pthread_mutex_destroy(&p->mtx);
  pthread_cond_destroy(&p->have_work);
  pthread_cond_destroy(&p->task_done);
  free(p->threads);
  free(p);
}
