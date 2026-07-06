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

/* A BL_LATER's field[0] is a BL_CLOSURE thunk (codegen lowers `later a` to `later (λ_. a)`): its
 * header.aux holds the lifted function pointer and its fields[] hold the captured env. Stepping it
 * once means *applying* it through the ordinary closure calling convention — `fn(clo, arg)`, the
 * same two-argument shape `bl_apply1`/`bl_app_global` use to call compiled closures from C. The
 * thunk's parameter is the ignored unit binder of `λ_. a`, so the argument is irrelevant; we pass
 * NULL. (A one-argument call here would mismatch every compiled closure's ABI.) */
typedef BlValue (*BlStep)(BlValue closure, BlValue arg);

static BlValue step_thunk(BlValue thunk) {
  /* Route through bl_call_tailcc: the thunk's code is a lifted (tailcc) function; a direct C-pointer
   * call would use the wrong ABI on x86_64 (tailcc≠ccc) and segfault. See blight_rt.h. */
  return bl_call_tailcc((void *)(uintptr_t)thunk->header.aux, thunk, NULL);
}

BL_HOT BlValue bl_force(BlValue delay) {
  BlValue cur = delay;
  /* GC root for the in-flight value across collections triggered by stepping. */
  bl_gc_push_root(&cur);
  for (;;) {
    if (BL_UNLIKELY(cur == NULL)) {
      fprintf(stderr, "blight: forced a null delay\n");
      bl_gc_pop_roots(1);
      return NULL;
    }
    if (bl_is_imm(cur)) {
      /* A bare immediate value (already-evaluated, e.g. a fast Nat) is its own result. */
      bl_gc_pop_roots(1);
      return cur;
    }
    switch (cur->header.tag) {
      case BL_NOW:
        bl_gc_pop_roots(1);
        return cur->fields[0];
      case BL_LATER: {
        /* Step once; a safepoint poll at this back-edge keeps the heap bounded. This is the hot
         * back-edge of every `Later`-guarded recursion, so it stays in the loop body (no per-step
         * C-stack frame — the headline million-deep bounded-stack property). */
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
