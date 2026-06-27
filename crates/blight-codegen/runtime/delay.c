/* delay.c — the Delay/Later trampoline (Capretta delay monad, spec §4.5).
 *
 * The kernel core has no general fixpoint; unbounded (`define-rec`) recursion is compiled to a
 * `Later`-guarded self-reference of type `Delay A`. A `BL_LATER` object holds a *thunk* (a
 * closure) which, when applied to unit, yields the next `Delay A` step. `bl_force` drives that
 * chain in a **bounded C stack loop**: it never recurses per step, so a million-deep countdown
 * forces in constant stack — this is the M4 "million-deep tail recursion does not overflow"
 * headline (spec §9), realized through the trampoline rather than the C call stack.
 */
#include "blight_rt.h"
#include <stdio.h>

/* A BL_LATER's field[0] is a BL_CLOSURE; its header.aux holds the function pointer and its
 * fields[] hold the captured env. Applying it (passing the closure as the env) steps once. */
typedef BlValue (*BlStep)(BlValue closure);

static BlValue step_thunk(BlValue thunk) {
  /* thunk is a BL_CLOSURE whose header.aux holds the function pointer (as an integer). */
  BlStep fn = (BlStep)(void *)(uintptr_t)thunk->header.aux;
  return fn(thunk);
}

BlValue bl_force(BlValue delay) {
  BlValue cur = delay;
  /* GC root for the in-flight value across collections triggered by stepping. */
  bl_gc_push_root(&cur);
  for (;;) {
    if (cur == NULL) {
      fprintf(stderr, "blight: forced a null delay\n");
      bl_gc_pop_roots(1);
      return NULL;
    }
    switch (cur->header.tag) {
      case BL_NOW:
        bl_gc_pop_roots(1);
        return cur->fields[0];
      case BL_LATER: {
        /* Step once; a safepoint poll at this back-edge keeps the heap bounded. */
        bl_gc_poll();
        cur = step_thunk(cur->fields[0]);
        break;
      }
      default:
        /* A bare value (already-evaluated) is its own result. */
        bl_gc_pop_roots(1);
        return cur;
    }
  }
}
