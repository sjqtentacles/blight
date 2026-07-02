/* worker_bench.c — share-nothing worker-pool SCALING benchmark (M17, perf proof).
 *
 * Built and run by the Rust harness in `runtime.rs` (with -pthread, optionally ThreadSanitizer).
 * The correctness of the pool is already covered by worker_test.c; this harness instead PROVES that
 * the pool scales with cores. It runs a fixed set of heavy, independent tasks across pools of
 * 1 / 2 / 4 / 8 workers, times each pool with CLOCK_MONOTONIC, and prints a SPEEDUP table.
 *
 * Why the workload is shaped this way (see the plan's "design constraints" — derived from worker.c):
 *   - The pool's join path is a single mutex + pthread_cond_broadcast on every task completion, so a
 *     "many tiny tasks" workload would measure lock/broadcast contention, not compute. We therefore
 *     use FEW, HEAVY tasks: each task does a large compute+GC-churn loop so the per-task body
 *     dominates the enqueue/serialize/broadcast overhead.
 *   - Arguments/results cross the boundary by serialize+deserialize on EVERY task regardless of
 *     worker count, so the 1-worker run pays the same copy cost: `speedup_vs_1` isolates parallelism
 *     (the fair baseline). The result payload is a single Int, so copy cost is negligible vs compute.
 *   - Every pool size uses the SAME per-worker heap size and the SAME task set, so 1/2/4/8 is
 *     apples-to-apples. Each worker GCs several times (real, not pathological).
 *
 * Worker counts above the host's online core count are skipped (not oversubscribed). The reduced
 * result must be identical across all pool sizes (determinism) — that is the hard correctness gate;
 * the timing is reported for the Rust driver to apply a soft speedup gate (see runtime.rs).
 */
#include "blight_rt.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

/* `bl_int`/`bl_int_val` now live in the always-linked numeric.c (M21 unboxing). */

/* Number of independent tasks in the fixed workload. Few + heavy (see header). */
#define NTASKS 16
/* Per-task compute weight: how much garbage each task churns (forces several GCs on its worker's own
 * heap) while keeping a live list rooted. Heavy enough that compute dominates pool overhead. */
#define CHURN 400000
/* Per-worker thread-local heap (identical across all pool sizes). Small enough to force collections. */
#define WORKER_HEAP (256 * 1024)

/* Heavy task: keep a live list rooted, churn a lot of garbage (each iteration adds to a running
 * sum so the optimizer cannot delete the loop), then return Int(n*n + work-derived-constant). The
 * returned value depends ONLY on n (the work constant is deterministic), so the reduced result is
 * scheduling-independent. */
static BlValue heavy_square(BlValue arg) {
  int64_t n = bl_int_val(arg);

  BlValue list = NULL;
  bl_gc_push_root(&list);
  for (int i = 0; i < 100; i++) {
    BlValue node = bl_alloc(BL_CON, 2, 0);
    node->fields[0] = bl_int((int64_t)i);
    node->fields[1] = list;
    bl_write_barrier(node, node->fields[0]);
    bl_write_barrier(node, node->fields[1]);
    list = node;
    bl_gc_poll();
  }

  volatile int64_t sink = 0;
  for (int i = 0; i < CHURN; i++) {
    BlValue garbage = bl_alloc(BL_TUPLE, 3, 0);
    garbage->fields[0] = NULL;
    sink += (int64_t)(i & 7);
    bl_gc_poll();
  }

  /* Verify the live list survived this worker's collections (share-nothing correctness under load). */
  int count = 0;
  for (BlValue p = list; p != NULL; p = p->fields[1]) count++;
  bl_gc_pop_roots(1);
  if (count != 100) { fprintf(stderr, "worker_bench: live list corrupted (len %d)\n", count); abort(); }

  (void)sink;
  return bl_int(n * n);
}

/* Run the fixed NTASKS workload on a pool of `nworkers`; return the reduced sum of results and write
 * the elapsed wall time (seconds) to *out_secs. */
static int64_t run_pool(int nworkers, double *out_secs) {
  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);

  BlPool *pool = bl_pool_create(nworkers, WORKER_HEAP);
  BlTask *tasks[NTASKS];
  for (int i = 0; i < NTASKS; i++) {
    BlValue arg = bl_int((int64_t)i);
    bl_gc_push_root(&arg);
    tasks[i] = bl_pool_submit(pool, heavy_square, arg);
    bl_gc_pop_roots(1);
  }
  int64_t total = 0;
  for (int i = 0; i < NTASKS; i++) {
    BlValue r = bl_pool_join(pool, tasks[i]);
    total += bl_int_val(r);
  }
  bl_pool_destroy(pool);

  clock_gettime(CLOCK_MONOTONIC, &t1);
  *out_secs = (double)(t1.tv_sec - t0.tv_sec) + (double)(t1.tv_nsec - t0.tv_nsec) / 1e9;
  return total;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  long ncores = sysconf(_SC_NPROCESSORS_ONLN);
  if (ncores < 1) ncores = 1;

  int64_t expected = 0;
  for (int i = 0; i < NTASKS; i++) expected += (int64_t)i * (int64_t)i;

  const int sizes[] = {1, 2, 4, 8};
  double serial_secs = 0.0;
  double best_parallel_secs = 1e18;
  int parallel_rows = 0;

  printf("SPEEDUP workers wall_ms speedup_vs_1\n");
  for (size_t s = 0; s < sizeof(sizes) / sizeof(sizes[0]); s++) {
    int w = sizes[s];
    if (w > ncores) continue; /* don't oversubscribe the host */
    double secs = 0.0;
    int64_t total = run_pool(w, &secs);
    if (total != expected) {
      fprintf(stderr, "worker_bench: nondeterministic/wrong result at %d workers: got %lld want %lld\n",
              w, (long long)total, (long long)expected);
      return 1;
    }
    if (w == 1) serial_secs = secs;
    else { parallel_rows++; if (secs < best_parallel_secs) best_parallel_secs = secs; }
    double speedup = (serial_secs > 0.0) ? serial_secs / secs : 1.0;
    printf("SPEEDUP %d %.3f %.2f\n", w, secs * 1e3, speedup);
  }

  /* Machine-readable summary line for the Rust driver's soft speedup gate. */
  double best_speedup = (serial_secs > 0.0 && parallel_rows > 0 && best_parallel_secs < 1e17)
                            ? serial_secs / best_parallel_secs
                            : 0.0;
  printf("WORKER_BENCH_OK ncores=%ld serial_ms=%.3f best_parallel_ms=%.3f best_speedup=%.2f\n",
         ncores, serial_secs * 1e3,
         (best_parallel_secs < 1e17 ? best_parallel_secs * 1e3 : 0.0), best_speedup);
  return 0;
}
