/* worker_code_test.c — standalone C test for `bl_pool_submit_code` (P4, roadmap Wave 10 /
 * auto-parallelism): submitting a worker-pool task by a P5 `code_id` rather than a native
 * `BlWorkerFn` C pointer — the concrete "hand a lifted Blight function to a worker by id" capability
 * P5's function-index table exists to provide.
 *
 * Hand-registers a two-entry code table (mirroring what a real compiled binary's generated `main.c`
 * does via `bl_code_table_register`) with two `BlFn2`-shaped functions: a captureless `double_fn`
 * (env unused) and a `add_env_fn` that reads its captured `env` (an Int) and adds it to `arg` — so
 * the test exercises both the "no env" and "env crosses the worker boundary by structural copy" paths.
 * Submits N tasks alternating between the two code ids across a small pool, joins them all, and
 * checks the reduced sum against the sequential expectation — the parallel-map-reduce shape
 * `worker_test.c` already proves for the native-`BlWorkerFn` API, now proven for the code-id API too.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>

typedef BlValue (*BlFn2)(BlValue env, BlValue arg);

static BlValue double_fn(BlValue env, BlValue arg) {
  (void)env;
  return bl_int(bl_int_val(arg) * 2);
}

static BlValue add_env_fn(BlValue env, BlValue arg) {
  return bl_int(bl_int_val(env) + bl_int_val(arg));
}

static void *g_table[] = { (void *)double_fn, (void *)add_env_fn };
#define CODE_DOUBLE 0
#define CODE_ADD_ENV 1

#define N 32

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();
  bl_code_table_register(g_table, sizeof(g_table) / sizeof(g_table[0]), 0xC0DE1D5ULL);

  BlPool *pool = bl_pool_create(4, 256 * 1024);

  BlTask *tasks[N];
  for (int i = 0; i < N; i++) {
    BlValue arg = bl_int((int64_t)i);
    bl_gc_push_root(&arg);
    if (i % 2 == 0) {
      tasks[i] = bl_pool_submit_code(pool, CODE_DOUBLE, NULL, arg);
    } else {
      BlValue env = bl_int(1000);
      bl_gc_push_root(&env);
      tasks[i] = bl_pool_submit_code(pool, CODE_ADD_ENV, env, arg);
      bl_gc_pop_roots(1); /* env: already serialized into the task at submit time */
    }
    bl_gc_pop_roots(1); /* arg */
  }

  int64_t total = 0;
  for (int i = 0; i < N; i++) {
    BlValue r = bl_pool_join(pool, tasks[i]);
    total += bl_int_val(r);
  }
  bl_pool_destroy(pool);

  int64_t expected = 0;
  for (int i = 0; i < N; i++) {
    expected += (i % 2 == 0) ? (int64_t)i * 2 : 1000 + (int64_t)i;
  }

  if (total != expected) {
    fprintf(stderr, "worker_code: parallel reduce by code_id wrong: got %lld want %lld\n",
            (long long)total, (long long)expected);
    return 1;
  }
  printf("WORKER_CODE_OK %lld\n", (long long)total);
  return 0;
}
