/* effects_test.c — standalone C tests for the effect trampoline (spec §4.3 deep handlers).
 *
 * Verifies the native handler contract in `effects.c`:
 *   - deep_handler_resumes: a body performs one operation; the handler's op clause resumes the
 *     captured continuation with a value, and the resumed computation runs to completion. The
 *     handler is re-installed across the resume (deep handler), so a *second* operation performed
 *     after resuming is handled by the same handler.
 *   - state_counter_runs_native: a `get`/`put` state handler threads an integer cell through a
 *     body that increments it, returning the final state — the canonical effectful program.
 *
 * Built and run by the Rust harness in `runtime.rs`.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

BlValue bl_int(int64_t n) { return bl_alloc(BL_INT, 0, (uint64_t)n); }
int64_t bl_int_val(BlValue v) { return (int64_t)v->header.aux; }

/* Build a 1-arg closure: header.aux = fn ptr, fields[0..n] = captures. */
static BlValue mkclo(void *fn, BlValue *caps, uint32_t n) {
  BlValue c = bl_alloc(BL_CLOSURE, n, (uint64_t)(uintptr_t)fn);
  for (uint32_t i = 0; i < n; i++) c->fields[i] = caps ? caps[i] : NULL;
  return c;
}

static BlValue apply1(BlValue clo, BlValue arg) {
  typedef BlValue (*Fn1)(BlValue, BlValue);
  Fn1 fn = (Fn1)(void *)(uintptr_t)clo->header.aux;
  return fn(clo, arg);
}

/* Build a bubbling OpNode carrying (arg, continuation-closure). */
static BlValue opnode(const char *effect, const char *op, BlValue arg, BlValue kont) {
  /* bl_perform interns the op and seeds a NULL continuation; we then set the real one. */
  BlValue node = bl_perform(effect, op, arg);
  node->fields[1] = kont;
  return node;
}

/* ===== Test 1: deep_handler_resumes =====
 *
 * Body: perform State.ask (); then in the continuation, perform State.ask () again; sum the two
 * resume values. The handler resumes every `ask` with 21, so the body should total 42, proving the
 * handler is re-installed for the *second* ask (deep handler).
 */

/* continuation after the second ask: k2(v2) = first_v + v2 */
static BlValue k_after_second(BlValue self, BlValue v2) {
  int64_t first_v = bl_int_val(self->fields[0]);
  return bl_int(first_v + bl_int_val(v2));
}

/* continuation after the first ask: k1(v1) = perform ask (), resume into k_after_second(v1, .) */
static BlValue k_after_first(BlValue self, BlValue v1) {
  (void)self;
  BlValue caps[1] = { v1 };
  BlValue k2 = mkclo((void *)k_after_second, caps, 1);
  return opnode("State", "ask", NULL, k2);
}

/* body: perform ask (), resume into k_after_first */
static BlValue ask_body(BlValue env) {
  (void)env;
  BlValue k1 = mkclo((void *)k_after_first, NULL, 0);
  return opnode("State", "ask", NULL, k1);
}

/* return clause: identity */
static BlValue id_ret(BlValue env, BlValue x) { (void)env; return x; }

/* op clause for ask: resume the continuation with 21, and re-handle its result. */
static BlValue ask_clause(BlValue env, BlValue x, BlValue k) {
  (void)env; (void)x;
  /* Resume: apply the continuation closure to the value 21. The handler loop in bl_handle
   * re-folds the returned value/opnode, so the deep handler is re-installed automatically. */
  return apply1(k, bl_int(21));
}

static int test_deep_handler_resumes(void) {
  const char *ops[1] = { "ask" };
  BlOpClause clauses[1] = { ask_clause };
  BlValue result = bl_handle(NULL, ask_body, id_ret, 1, ops, clauses);
  if (result == NULL || result->header.tag != BL_INT || bl_int_val(result) != 42) {
    fprintf(stderr, "deep_handler_resumes: expected 42, got %s\n",
            result ? "wrong" : "null");
    return 1;
  }
  return 0;
}

/* ===== Test 2: state_counter_runs_native =====
 *
 * A State handler threading an integer through `get`/`put`. Body: x = get(); put(x+1); return get().
 * Starting state 0 → final 1. We thread the state via the op clauses' resume value and a captured
 * state cell in the handler env.
 */

/* The handler env holds a mutable state cell as fields[0] (a BL_INT we replace). For simplicity
 * the clauses use a static cell, modelling the threaded state. */
static int64_t g_state;

/* body continuations: get -> put(x+1) -> get -> return */
static BlValue sc_k3(BlValue self, BlValue v) { (void)self; return v; }   /* return final get */
static BlValue sc_k2(BlValue self, BlValue unit) { /* after put: perform get to read final */
  (void)self; (void)unit;
  BlValue k = mkclo((void *)sc_k3, NULL, 0);
  return opnode("State", "get", NULL, k);
}
static BlValue sc_k1(BlValue self, BlValue x) { /* after first get: perform put(x+1) */
  (void)self;
  BlValue k = mkclo((void *)sc_k2, NULL, 0);
  return opnode("State", "put", bl_int(bl_int_val(x) + 1), k);
}
static BlValue sc_body(BlValue env) {
  (void)env;
  BlValue k = mkclo((void *)sc_k1, NULL, 0);
  return opnode("State", "get", NULL, k);
}

static BlValue sc_get_clause(BlValue env, BlValue x, BlValue k) {
  (void)env; (void)x;
  return apply1(k, bl_int(g_state)); /* resume get with current state */
}
static BlValue sc_put_clause(BlValue env, BlValue x, BlValue k) {
  (void)env;
  g_state = bl_int_val(x);            /* update state */
  return apply1(k, bl_int(0));        /* resume put with unit */
}

static int test_state_counter(void) {
  g_state = 0;
  const char *ops[2] = { "get", "put" };
  BlOpClause clauses[2] = { sc_get_clause, sc_put_clause };
  BlValue result = bl_handle(NULL, sc_body, id_ret, 2, ops, clauses);
  if (result == NULL || result->header.tag != BL_INT || bl_int_val(result) != 1) {
    fprintf(stderr, "state_counter: expected 1, got %lld\n",
            result ? (long long)bl_int_val(result) : -999);
    return 1;
  }
  return 0;
}

int main(void) {
  bl_gc_init(8 * 1024 * 1024);
  bl_stack_init();
  int rc = 0;
  rc |= test_deep_handler_resumes();
  rc |= test_state_counter();
  if (rc == 0) printf("EFFECTS_OK\n");
  return rc;
}
