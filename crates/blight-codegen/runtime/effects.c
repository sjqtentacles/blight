/* effects.c — algebraic-effect trampoline with deep handlers (spec §4.3/§4.6).
 *
 * Mirrors the kernel's value-based operational semantics (`do_handle`/`replay`, normalize.rs):
 *   - An effectful computation evaluates to either a *pure value* or a bubbling `BL_OPNODE`
 *     carrying (effect, op, arg, continuation). This is the native analogue of `Value::OpNode`.
 *   - `bl_handle` folds the computation with a handler:
 *       * a pure value runs the `return x. r` clause with x := value;
 *       * a handled op runs `op x k. e` with x := arg and k := a continuation closure that, when
 *         applied to a resume value, replays the captured continuation **and re-installs this same
 *         handler** (deep handlers, spec §4.3);
 *       * an unhandled op bubbles past unchanged.
 *
 * The continuation here is represented as a closure the compiled body provides (CPS-style): the
 * codegen threads the "rest of the computation under the handler" as a one-argument closure. This
 * keeps the model faithful to the kernel without capturing the C stack.
 */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L /* expose getline() on Linux libc */
#endif
#include "blight_rt.h"
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <sys/time.h>

/* Intern table mapping (effect,op) -> index stored in BL_OPNODE.header.aux. Small and append-only;
 * effect/op name sets are tiny per program.
 *
 * M15 (share-nothing multicore): this table is the one piece of effect state that must stay *shared*
 * across worker threads — an OpNode interned on one worker carries an index another worker resolves
 * via `op_name_of` after a message crosses. To make it race-free without a hot-path lock, all ops a
 * program uses are interned **once at single-threaded startup** (codegen/driver calls
 * `bl_effect_intern` for every declared op before any worker spawns), then the table is *frozen*:
 * after `bl_effect_intern_freeze()`, `intern_op` only ever performs read-only lookups, so concurrent
 * `bl_perform`s never mutate it. A miss after freeze is a program/codegen bug, not a runtime event,
 * and aborts rather than racily appending. Single-runtime programs that never freeze keep the old
 * lazy-append behavior, so M0-M14 are unchanged. */
typedef struct { const char *effect; const char *op; } OpKey;
#define BL_MAX_OPS 256
static OpKey g_ops[BL_MAX_OPS];
static size_t g_nops;
static int g_ops_frozen; /* set by bl_effect_intern_freeze(); blocks further appends */

/* Intern (effect,op) returning its stable index. Append-only; safe to call repeatedly. Public so the
 * driver can pre-intern every declared op at single-threaded startup (M15). */
uint64_t bl_effect_intern(const char *effect, const char *op);
/* Freeze the intern table after startup pre-interning: subsequent `intern_op` calls must hit an
 * existing entry (any miss aborts), guaranteeing the shared table is immutable during parallel
 * execution. Idempotent. */
void bl_effect_intern_freeze(void);

static uint64_t intern_op(const char *effect, const char *op) {
  for (size_t i = 0; i < g_nops; i++) {
    if (strcmp(g_ops[i].effect, effect) == 0 && strcmp(g_ops[i].op, op) == 0) return i;
  }
  if (g_ops_frozen) {
    /* The shared table is frozen for parallel execution; a miss means an op was not pre-interned at
     * startup. Appending now would race other workers, so this is a hard error. */
    fprintf(stderr, "blight: effect op (%s.%s) not pre-interned before freeze\n", effect, op);
    abort();
  }
  if (g_nops >= BL_MAX_OPS) { fprintf(stderr, "blight: too many effect ops\n"); abort(); }
  g_ops[g_nops].effect = effect;
  g_ops[g_nops].op = op;
  return g_nops++;
}

uint64_t bl_effect_intern(const char *effect, const char *op) { return intern_op(effect, op); }

void bl_effect_intern_freeze(void) { g_ops_frozen = 1; }

static const char *op_name_of(uint64_t idx) {
  return idx < g_nops ? g_ops[idx].op : "?";
}

/* Public wrapper (P2, roadmap Wave 10 / graphics FFI): `graphics.c` is a separate translation unit
 * and needs the exact same op-name lookup `bl_run_console`'s dispatch loop uses — the intern table
 * itself must stay file-private (it is effects.c's own append/freeze-guarded state), so this is a
 * thin read-only accessor rather than exposing `g_ops` directly. */
const char *bl_op_name_of(uint64_t idx) { return op_name_of(idx); }

/* Public wrapper (P5, roadmap Wave 10 / code mobility): `serialize.c`'s mobile serializer needs the
 * EFFECT half of a `BL_OPNODE`'s (effect, op) pair too — an OpNode's `header.aux` is meaningful only
 * as a LOCAL, first-use-order index into this process's own `g_ops` (unlike P5's codegen-emitted,
 * compile-time-fixed function-index table), so the wire format ships the two NAME strings instead of
 * the index, and the receiving process re-derives its own local index via `bl_effect_intern`. */
static const char *effect_name_of(uint64_t idx) {
  return idx < g_nops ? g_ops[idx].effect : "?";
}
const char *bl_effect_name_of(uint64_t idx) { return effect_name_of(idx); }

static int is_opnode(BlValue v);
static BlValue bl_perform_idx(uint64_t opidx, BlValue arg);
static BlValue bl_apply1(BlValue clo, BlValue arg); /* fwd */

/* A "perform on resume" closure: fields [0]=old continuation (or NULL), [1]=BL_INT op-index. When
 * resumed with a value, replay the captured continuation then perform the recorded op on the result.
 * This is how a `perform` whose *argument* is itself effectful bubbles outward (delimited capture). */
static BlValue bl_perform_apply(BlValue clo, BlValue v) {
  bl_gc_push_root(&clo);
  bl_gc_push_root(&v);
  BlValue old_cont = clo->fields[0];
  uint64_t opidx = clo->fields[1]->header.aux;
  BlValue resumed = (old_cont == NULL) ? v : bl_apply1(old_cont, v);
  bl_gc_push_root(&resumed);
  BlValue out = bl_perform_idx(opidx, resumed);
  bl_gc_pop_roots(3);
  return out;
}

static BlValue make_perform_cont(BlValue old_cont, uint64_t opidx) {
  BlValue clo = bl_alloc(BL_CLOSURE, 2, (uint64_t)(uintptr_t)(void *)bl_perform_apply);
  clo->fields[0] = old_cont;
  bl_gc_push_root(&clo);
  BlValue idxbox = bl_alloc(BL_INT, 0, opidx);
  clo->fields[1] = idxbox;
  bl_gc_pop_roots(1);
  return clo;
}

/* Perform op `opidx` on `arg`. If `arg` is itself a bubbling effect, the perform is *stuck* on it:
 * bubble that effect, composing "perform opidx on the resume value" onto its continuation. */
static BlValue bl_perform_idx(uint64_t opidx, BlValue arg) {
  if (is_opnode(arg)) {
    bl_gc_push_root(&arg);
    BlValue node = bl_alloc(BL_OPNODE, 2, arg->header.aux);
    node->fields[0] = arg->fields[0];
    bl_gc_push_root(&node);
    node->fields[1] = make_perform_cont(arg->fields[1], opidx);
    bl_gc_pop_roots(2);
    return node;
  }
  BlValue node = bl_alloc(BL_OPNODE, 2, opidx);
  node->fields[0] = arg;
  node->fields[1] = NULL; /* continuation; composed by bl_app as the node bubbles outward */
  return node;
}

BlValue bl_perform(const char *effect, const char *op, BlValue arg) {
  /* Build an OpNode with a NULL continuation (the "identity" continuation). As the OpNode bubbles
   * out through enclosing eliminations, `bl_app` composes the pending work onto field[1] so that a
   * handler resuming `k v` replays the captured rest of the computation (delimited continuation).
   * If `arg` itself bubbled (a `perform` whose argument performs), we bubble that first. */
  return bl_perform_idx(intern_op(effect, op), arg);
}

/* ---- OpNode-aware application: native delimited-continuation capture (spec §4.3). ----
 *
 * Compiled call sites route through `bl_app(f, a)`. If neither operand is a bubbling effect, this is
 * an ordinary closure call. If an operand IS an OpNode, the application is *stuck* on that effect:
 * we return a new OpNode that carries the same (effect, op, arg) but whose continuation has the
 * pending application composed onto it, exactly mirroring the kernel's `apply` (normalize.rs):
 *   - effectful argument `a`: bubble, recording "apply the fixed function `f` to my resume value";
 *   - effectful function `f`: bubble, recording "apply my resume value to the fixed argument `a`".
 * When a handler later resumes the continuation with a value `v`, the composed closure replays the
 * old continuation then performs the recorded application — excavating the captured computation. */
static BlValue bl_apply1(BlValue clo, BlValue arg); /* fwd */

/* A composed-continuation closure. fields: [0]=old continuation (or NULL), [1]=mode tag boxed as
 * BL_INT (0 = apply f to resume; 1 = apply resume to a), [2]=the fixed operand (f or a). */
BlValue bl_app(BlValue f, BlValue a); /* fwd; public (declared in blight_rt.h) */

static BlValue bl_compose_apply(BlValue clo, BlValue v) {
  bl_gc_push_root(&clo);
  bl_gc_push_root(&v);
  BlValue old_cont = clo->fields[0];
  uint64_t mode = clo->fields[1]->header.aux;
  /* First replay the captured continuation (the rest of the computation that produced this operand),
   * then perform the recorded application. Re-read `fixed` from the rooted closure after the
   * (possibly collecting) replay. */
  BlValue resumed = (old_cont == NULL) ? v : bl_apply1(old_cont, v);
  bl_gc_push_root(&resumed);
  BlValue fixed = clo->fields[2];
  BlValue out;
  if (mode == 0) {
    /* argument was effectful: apply the fixed function to the resumed argument value */
    out = bl_app(fixed, resumed);
  } else {
    /* function was effectful: apply the resumed function value to the fixed argument */
    out = bl_app(resumed, fixed);
  }
  bl_gc_pop_roots(3);
  return out;
}

static BlValue make_compose(BlValue old_cont, uint64_t mode, BlValue fixed) {
  /* GC-safe: allocate the closure first (its NULL fields are traced harmlessly) and root it before
   * any further allocation that could move/collect `old_cont`/`fixed`. */
  BlValue clo = bl_alloc(BL_CLOSURE, 3, (uint64_t)(uintptr_t)(void *)bl_compose_apply);
  clo->fields[0] = old_cont;
  clo->fields[2] = fixed;
  bl_gc_push_root(&clo);
  BlValue modebox = bl_alloc(BL_INT, 0, mode);
  clo->fields[1] = modebox;
  bl_gc_pop_roots(1);
  return clo;
}

static int is_opnode(BlValue v) { return v != NULL && !bl_is_imm(v) && BL_TAG(v) == BL_OPNODE; }

BlValue bl_app(BlValue f, BlValue a) {
  if (is_opnode(f)) {
    /* function position is stuck: bubble, recording "apply resume value to `a`" (mode 1). */
    bl_gc_push_root(&f);
    bl_gc_push_root(&a);
    BlValue node = bl_alloc(BL_OPNODE, 2, f->header.aux);
    node->fields[0] = f->fields[0];
    bl_gc_push_root(&node);
    node->fields[1] = make_compose(f->fields[1], 1, a);
    bl_gc_pop_roots(3);
    return node;
  }
  if (is_opnode(a)) {
    /* argument position is stuck: bubble, recording "apply `f` to resume value" (mode 0). */
    bl_gc_push_root(&f);
    bl_gc_push_root(&a);
    BlValue node = bl_alloc(BL_OPNODE, 2, a->header.aux);
    node->fields[0] = a->fields[0];
    bl_gc_push_root(&node);
    node->fields[1] = make_compose(a->fields[1], 0, f);
    bl_gc_pop_roots(3);
    return node;
  }
  return bl_apply1(f, a);
}

/* Direct application of a *captureless* top-level function (A3 spine fusion). The compiler proved
 * the callee captures nothing (it was a `MkClosure(f, [])`), so its lifted code reads no
 * environment: we invoke it with a NULL env, skipping the per-call closure allocation the un-fused
 * `MkClosure(f, []) + bl_app` would do. Effect semantics are preserved *exactly*: if the argument is
 * a suspended effect (an OpNode), we fall back to `bl_app` over a freshly-built closure so the
 * pending application composes onto the continuation identically to a normal `Call` (mode-0 bubble).
 * The common pure-argument path is a single indirect call with zero allocation. `fnptr` is the
 * lifted function pointer (passed as an opaque `ptr` from codegen), not a `BlValue`. */
typedef BlValue (*BlFn2)(BlValue env, BlValue arg);
BlValue bl_app_global(void *fnptr, BlValue a) {
  if (is_opnode(a)) {
    /* rare: the argument bubbled — rebuild a real captureless closure and defer to the OpNode-aware
     * path, so composition matches the un-fused call bit-for-bit (only the effectful-arg path pays
     * the allocation, exactly as the baseline always did). */
    bl_gc_push_root(&a);
    BlValue clo = bl_alloc(BL_CLOSURE, 0, (uint64_t)(uintptr_t)fnptr);
    bl_gc_pop_roots(1);
    return bl_app(clo, a);
  }
  return bl_call_tailcc(fnptr, NULL, a);
}

/* ---- OpNode-aware data construction (spec §4.3). ----
 *
 * A constructor or tuple is *not* an elimination, but under call-by-value an effectful field still
 * forces the surrounding construction to be suspended: `Succ (perform get tt)` must bubble the `get`
 * with the continuation `λn. Succ n`. After the codegen builds a Con/Tuple object eagerly, it calls
 * `bl_con_bubble(obj)`: if some field is an OpNode, we bubble it, recording "rebuild this object with
 * that field replaced by the resume value" onto the continuation. Re-entry handles the (rare) case of
 * several effectful fields, peeling them left to right. */
static BlValue bl_rebuild_field_apply(BlValue clo, BlValue v);

/* Rebuild closure. fields: [0]=old continuation (or NULL), [1]=the partially-built object,
 * [2]=BL_INT boxing the field index to fill on resume. */
static BlValue make_rebuild(BlValue old_cont, BlValue obj, uint64_t field_idx) {
  BlValue clo = bl_alloc(BL_CLOSURE, 3, (uint64_t)(uintptr_t)(void *)bl_rebuild_field_apply);
  clo->fields[0] = old_cont;
  clo->fields[1] = obj;
  bl_gc_push_root(&clo);
  BlValue idxbox = bl_alloc(BL_INT, 0, field_idx);
  clo->fields[2] = idxbox;
  bl_gc_pop_roots(1);
  return clo;
}

BlValue bl_con_bubble(BlValue obj) {
  if (obj == NULL) return obj;
  if (bl_is_imm(obj)) return obj; /* an immediate has no fields: nothing to bubble */
  uint32_t tag = BL_TAG(obj);
  /* Con/Tuple fields can hold a stuck OpNode: a `let x = perform op … in (C … x …)` builds the
   * constructor with `x` (the OpNode) as a field. Freezing that OpNode into the value would silently
   * never resume the effect; bubbling it composes "rebuild this Con with the resumed field" onto the
   * continuation. (Closures are *not* bubbled here: a closure capture may legitimately be a suspended
   * effectful computation — e.g. a structural eliminator's induction hypothesis `self k : ! E A` —
   * and eagerly bubbling it would run the recursion's per-step effects out of order. Construction of
   * closures is therefore identity; their captures resume when the closure is *applied*.) */
  if (tag != BL_CON && tag != BL_TUPLE) return obj;
  uint32_t n = obj->header.nfields;
  for (uint32_t i = 0; i < n; i++) {
    BlValue fld = obj->fields[i];
    if (is_opnode(fld)) {
      /* Field i is stuck: bubble, recording "fill field i with the resume value, then re-bubble". */
      bl_gc_push_root(&obj);
      BlValue node = bl_alloc(BL_OPNODE, 2, fld->header.aux);
      node->fields[0] = obj->fields[i]->fields[0];
      bl_gc_push_root(&node);
      node->fields[1] = make_rebuild(obj->fields[i]->fields[1], obj, i);
      bl_gc_pop_roots(2);
      return node;
    }
  }
  return obj;
}

static BlValue bl_rebuild_field_apply(BlValue clo, BlValue v) {
  bl_gc_push_root(&clo);
  bl_gc_push_root(&v);
  BlValue old_cont = clo->fields[0];
  uint64_t idx = clo->fields[2]->header.aux;
  BlValue resumed = (old_cont == NULL) ? v : bl_apply1(old_cont, v);
  bl_gc_push_root(&resumed);
  /* Shallow-copy the object with field idx filled by the resumed value (keep the partial build
   * immutable across multiple resumes of a multi-shot continuation). `obj` is re-read from the rooted
   * closure after the (possibly collecting) resume above. */
  BlValue obj = clo->fields[1];
  bl_gc_push_root(&obj);
  BlValue rebuilt = bl_alloc(obj->header.tag, obj->header.nfields, obj->header.aux);
  for (uint32_t j = 0; j < obj->header.nfields; j++) rebuilt->fields[j] = obj->fields[j];
  rebuilt->fields[idx] = resumed;
  bl_gc_pop_roots(4);
  /* Another field might still be effectful: peel the next one. */
  return bl_con_bubble(rebuilt);
}

BlValue bl_handle(BlValue env, BlThunk body, BlReturnClause ret,
                  size_t n_ops, const char **op_names, BlOpClause *op_clauses) {
  /* Run the body to a value or an OpNode. */
  BlValue comp = body(env);
  bl_gc_push_root(&comp);

  for (;;) {
    if (!is_opnode(comp)) {
      /* Pure value: run the return clause. */
      BlValue r = ret(env, comp);
      bl_gc_pop_roots(1);
      return r;
    }
    /* An operation bubbled. Is it handled here? */
    const char *opn = op_name_of(comp->header.aux);
    size_t which = (size_t)-1;
    for (size_t i = 0; i < n_ops; i++) {
      if (strcmp(op_names[i], opn) == 0) { which = i; break; }
    }
    if (which == (size_t)-1) {
      /* Unhandled: bubble past unchanged. */
      bl_gc_pop_roots(1);
      return comp;
    }
    BlValue arg = comp->fields[0];
    BlValue kont = comp->fields[1]; /* continuation closure (resume value -> Delay/computation) */

    /* The op clause receives x := arg and k := a continuation that, applied to a resume value,
     * replays `kont` and re-installs this handler (deep handler). We model k as `kont` directly:
     * applying it resumes the captured computation; the handler loop below re-folds the result, so
     * the handler is effectively re-installed. */
    BlValue result = op_clauses[which](env, arg, kont);

    /* `result` may itself be a value or another OpNode (the clause re-performed). If the clause
     * resumed via k, `result` is the resumed computation's value/opnode: loop to re-handle. */
    comp = result;
  }
}

/* Closure-based deep handler used by the compiler backend.
 *
 * The codegen lifts each handler clause to an ordinary Blight closure (a BL_CLOSURE whose
 * header.aux is the lifted function pointer and whose fields[] are its captured free variables),
 * exactly like any other lambda. This variant therefore takes *closure values* rather than raw C
 * function pointers, and applies them through the closure calling convention (the same `fn(clo,
 * arg)` shape `delay.c` uses to step `Later` thunks):
 *   - `body_clo`  is a thunk `λ_. body` — applied to unit to run the body once;
 *   - `ret_clo`   is `λx. r`           — applied to the pure result;
 *   - `op_clos[i]` is curried `λx. λk. e` — applied to the op argument, then to the continuation.
 *
 * Semantics are identical to `bl_handle` (deep handler, re-installed on resume, spec §4.3); only
 * the clause representation differs. */
typedef BlValue (*BlClo1)(BlValue clo, BlValue arg);

/* Weak ccc fallback for `bl_call_tailcc` (declared in blight_rt.h). Codegen emits a STRONG `tailcc`
 * definition that overrides this in every real `blight build` binary; this fallback exists only so
 * C-only runtime test harnesses (which link the runtime but emit no Blight program, hence no strong
 * definition) still link. In those harnesses every linked function is ccc, so a plain call is correct. */
__attribute__((weak)) BlValue bl_call_tailcc(void *fn, BlValue clo, BlValue arg) {
  return ((BlClo1)fn)(clo, arg);
}

/* `bl_cont_apply` (the delimited continuation's code) is EXTERNAL: the codegen emits a strong tailcc
 * `bl_cont_apply_tc` wrapping it (see llvm.rs), and `make_cont` stores that wrapper as the continuation
 * closure's code pointer so it is tailcc-callable on the pure IR application path too. This weak ccc
 * `bl_cont_apply_tc` only keeps C-only runtime harnesses (no codegen; everything ccc) linking. */
BlValue bl_cont_apply(BlValue clo, BlValue arg);
__attribute__((weak)) BlValue bl_cont_apply_tc(BlValue clo, BlValue arg) {
  return bl_cont_apply(clo, arg);
}

static BlValue bl_apply1(BlValue clo, BlValue arg) {
  void *fn = (void *)(uintptr_t)clo->header.aux;
  /* Two kinds of closure share this apply path with DIFFERENT native calling conventions. A lifted
   * Blight closure's code is `tailcc` and goes through the adapter (calling it as ccc corrupts the
   * x86_64 stack — the original Linux segfault). The runtime also synthesizes closures whose code is
   * an ordinary C (`ccc`) function applied ONLY from here — the `perform`/compose thunks and the
   * con-bubble field rebuilder — which must be called ccc (calling ccc as tailcc corrupts the stack
   * just the same). Dispatch by code pointer. (The delimited continuation is the one runtime closure
   * user code can also apply via the pure IR path, so it instead carries the tailcc `bl_cont_apply_tc`
   * wrapper and needs no special case here — it falls through to the adapter like any lifted closure.) */
  if (fn == (void *)bl_perform_apply || fn == (void *)bl_compose_apply ||
      fn == (void *)bl_rebuild_field_apply) {
    return ((BlClo1)fn)(clo, arg);
  }
  return bl_call_tailcc(fn, clo, arg);
}

/* A heap "handler record" capturing everything needed to re-fold a resumed computation under the
 * same deep handler. The BlValue members (`ret_clo`, `op_clos[]`) are registered as persistent GC
 * roots for the handler's lifetime so the collector keeps them alive even though they are reached
 * through this malloc'd (non-GC) struct rather than a traced object. Effect handlers are
 * lexically scoped and short-lived here, so a handful of pinned roots is acceptable. */
typedef struct BlHandler {
  BlValue ret_clo;
  size_t n_ops;
  const char **op_names; /* points at the program's interned string literals (stable) */
  BlValue *op_clos;      /* heap-owned copy so it outlives the codegen's stack array */
} BlHandler;

/* Continuation closures are tagged BL_CLOSURE objects with exactly one traced field (`kont`); the
 * owning handler record is recovered from the closure's `aux` is the C function pointer, so we keep
 * the `BlHandler*` in a parallel registry indexed by a small integer stored in field[1]'s aux. To
 * avoid that bookkeeping we instead allocate the closure with two fields where field[0] is `kont`
 * (traced) and field[1] is a BL_INT boxing the `BlHandler*` (not a heap pointer, so safe to trace as
 * an opaque integer-tagged object). */
static BlValue bl_handle_fold(BlHandler *h, BlValue comp);

/* EXTERNAL (not static): the codegen's strong tailcc `bl_cont_apply_tc` wrapper ccc-calls this. */
BlValue bl_cont_apply(BlValue clo, BlValue v) {
  BlValue kont = clo->fields[0];
  BlHandler *h = (BlHandler *)(uintptr_t)clo->fields[1]->header.aux;
  BlValue resumed = (kont == NULL) ? v : bl_apply1(kont, v);
  return bl_handle_fold(h, resumed);
}

static BlValue make_cont(BlHandler *h, BlValue kont) {
  /* field[1] boxes the handler pointer as a BL_INT (an opaque, fieldless object the GC won't chase
   * into the malloc'd record). field[0] is the real captured continuation (traced). GC-safe: alloc
   * the closure first and root it before allocating the box. */
  /* Store the codegen's tailcc `bl_cont_apply_tc` wrapper (weak ccc fallback in C-only harnesses), not
   * the raw ccc `bl_cont_apply`, so user code applying this continuation on the pure IR path (a tailcc
   * indirect call) hits the right ABI. See blight_rt.h / llvm.rs. */
  BlValue clo = bl_alloc(BL_CLOSURE, 2, (uint64_t)(uintptr_t)(void *)bl_cont_apply_tc);
  clo->fields[0] = kont;
  bl_gc_push_root(&clo);
  BlValue hbox = bl_alloc(BL_INT, 0, (uint64_t)(uintptr_t)h);
  clo->fields[1] = hbox;
  bl_gc_pop_roots(1);
  return clo;
}

static BlValue bl_handle_fold(BlHandler *h, BlValue comp) {
  for (;;) {
    if (!is_opnode(comp)) {
      return bl_apply1(h->ret_clo, comp);
    }
    const char *opn = op_name_of(comp->header.aux);
    size_t which = (size_t)-1;
    for (size_t i = 0; i < h->n_ops; i++) {
      if (strcmp(h->op_names[i], opn) == 0) { which = i; break; }
    }
    if (which == (size_t)-1) {
      return comp; /* unhandled: bubble past unchanged */
    }
    BlValue arg = comp->fields[0];
    BlValue kont = comp->fields[1];
    BlValue k = make_cont(h, kont);
    BlValue partial = bl_apply1(h->op_clos[which], arg);
    comp = bl_apply1(partial, k);
#ifdef BL_EFFECTS_DEBUG
    fprintf(stderr, "[handle] op which=%zu arg_tag=%u partial_tag=%u result_tag=%u\n",
            which, arg ? bl_obj_tag(arg) : 999, partial ? bl_obj_tag(partial) : 999,
            comp ? bl_obj_tag(comp) : 999);
#endif
  }
}

BlValue bl_handle_clo(BlValue body_clo, BlValue ret_clo,
                      size_t n_ops, const char **op_names, BlValue *op_clos) {
  BlHandler *h = (BlHandler *)malloc(sizeof(BlHandler));
  h->ret_clo = ret_clo;
  h->n_ops = n_ops;
  h->op_names = op_names; /* string literals: already program-lifetime stable */
  h->op_clos = (BlValue *)malloc(n_ops ? n_ops * sizeof(BlValue) : 1);
  for (size_t i = 0; i < n_ops; i++) h->op_clos[i] = op_clos[i];
  /* Pin the handler's heap values so a GC during the fold keeps them alive. */
  bl_gc_push_root(&h->ret_clo);
  for (size_t i = 0; i < n_ops; i++) bl_gc_push_root(&h->op_clos[i]);

  BlValue comp = bl_apply1(body_clo, NULL);
#ifdef BL_EFFECTS_DEBUG
  fprintf(stderr, "[handle] body -> tag=%u n_ops=%zu\n", comp ? bl_obj_tag(comp) : 999, n_ops);
#endif
  BlValue r = bl_handle_fold(h, comp);
  bl_gc_pop_roots(1 + n_ops);
  return r;
}

/* ---- native top-level Console handler (spec §4, std/io.bl). ----
 *
 * A program `main : (! Console A)` evaluates (via `bl_program_entry`) to a bubbling OpNode tree of
 * `Console` operations. `bl_run_console` is the *native* deep handler the build driver installs as
 * the top-level interpreter: it folds that tree against real stdio, resuming each operation's
 * continuation with the I/O result, until a pure value remains.
 *
 *   * `print s`  — decode the `String` argument and write its bytes to stdout (no implicit newline),
 *                  then resume with `tt` (Unit, constructor index 0);
 *   * `read tt`  — read one line from stdin (newline stripped, EOF -> empty), build a `String`, and
 *                  resume with it.
 *
 * `String` is std/string.bl's cons-list: `empty` = ctor 0 (0 fields), `push` = ctor 1 (codepoint
 * `Nat` in field[0], rest in field[1]). A codepoint `Nat` is the unary `Succ^n Zero` (Zero = ctor 0,
 * Succ = ctor 1). All construction is GC-rooted: each step may allocate and trigger a collection. */

/* Unit `tt` (Unit's sole constructor, index 0, no fields). */
static BlValue bl_unit(void) { return bl_alloc(BL_CON, 0, 0); }

/* Build the unary `Nat` for codepoint `n` (`Succ^n Zero`), rooting the accumulator across allocs. */
static BlValue bl_nat_of(uint64_t n) {
  BlValue acc = bl_alloc(BL_CON, 0, 0); /* Zero */
  bl_gc_push_root(&acc);
  for (uint64_t i = 0; i < n; i++) {
    BlValue s = bl_alloc(BL_CON, 1, 1); /* Succ _ */
    s->fields[0] = acc;
    acc = s;
  }
  bl_gc_pop_roots(1);
  return acc;
}

/* Build a `String` from `len` bytes of `buf` (a cons-list, head = first byte). Built back-to-front so
 * each `push` is allocated after its `rest`, keeping a single rooted accumulator. */
static BlValue bl_string_of(const unsigned char *buf, size_t len) {
  BlValue acc = bl_alloc(BL_CON, 0, 0); /* empty */
  bl_gc_push_root(&acc);
  for (size_t i = len; i > 0; i--) {
    BlValue cp = bl_nat_of(buf[i - 1]); /* may GC; acc is rooted */
    bl_gc_push_root(&cp);
    BlValue node = bl_alloc(BL_CON, 2, 1); /* push cp rest */
    node->fields[0] = cp;
    node->fields[1] = acc;
    bl_gc_pop_roots(1); /* cp */
    acc = node;
  }
  bl_gc_pop_roots(1); /* acc */
  return acc;
}

/* Decode a `String` to stdout bytes (no trailing newline). Mirrors prelude_rt.c's `bl_print_string`
 * but without the implicit newline, so `print` is faithful line-by-line output. Reads a packed
 * BL_STRING (A2) directly in O(1)/codepoint, or walks an `empty`/`push` cons-list otherwise —
 * observationally identical (a packed literal is the same byte sequence as its inductive spine). */
static void bl_emit_string(BlValue s) {
  BlValue cur = s;
  for (;;) {
    if (cur && !bl_is_imm(cur) && bl_obj_tag(cur) == BL_STRING) {
      /* A packed BL_STRING (A2) — possibly the whole value or a packed *tail* spliced in by
       * `string-append` (whose `(empty) t` arm returns the second operand verbatim). Emit it in
       * O(1)/codepoint, then we are done (a packed string has no further cons tail). */
      uint64_t n = bl_string_len_of_value(cur);
      for (uint64_t i = 0; i < n; i++) {
        putchar((int)(unsigned char)bl_string_codepoint_at(cur, i));
      }
      return;
    }
    if (!(cur && bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == 1 && bl_obj_nfields(cur) == 2)) {
      return;
    }
    /* field[0] is a Nat codepoint (a fast immediate Nat, a boxed BL_NAT, or a `Succ` chain). */
    putchar((int)(unsigned char)bl_nat_of_value(bl_obj_field(cur, 0)));
    cur = bl_obj_field(cur, 1);
  }
}

/* ---- FileIO native handler helpers (C1, std/io.bl). ----
 *
 * Decode a `String` cons-list to a freshly malloc'd, NUL-terminated byte buffer; `*out_len` gets the
 * byte length (excluding the NUL). The caller frees. Used to turn a `String` path/contents into the
 * C string `fopen`/`fwrite` need. Returns NULL only on allocation failure. */
static char *bl_string_to_cstr(BlValue s, size_t *out_len) {
  size_t cap = 64, len = 0;
  char *buf = (char *)malloc(cap);
  if (!buf) { if (out_len) *out_len = 0; return NULL; }
  BlValue cur = s;
  for (;;) {
    if (cur && !bl_is_imm(cur) && bl_obj_tag(cur) == BL_STRING) {
      /* A packed BL_STRING (A2), possibly a packed tail spliced in by `string-append`. */
      uint64_t n = bl_string_len_of_value(cur);
      for (uint64_t i = 0; i < n; i++) {
        if (len + 1 >= cap) {
          cap *= 2;
          char *grown = (char *)realloc(buf, cap);
          if (!grown) { free(buf); if (out_len) *out_len = 0; return NULL; }
          buf = grown;
        }
        buf[len++] = (char)(unsigned char)bl_string_codepoint_at(cur, i);
      }
      break;
    }
    if (!(cur && bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == 1 && bl_obj_nfields(cur) == 2)) {
      break;
    }
    if (len + 1 >= cap) {
      cap *= 2;
      char *grown = (char *)realloc(buf, cap);
      if (!grown) { free(buf); if (out_len) *out_len = 0; return NULL; }
      buf = grown;
    }
    buf[len++] = (char)(unsigned char)bl_nat_of_value(bl_obj_field(cur, 0));
    cur = bl_obj_field(cur, 1);
  }
  buf[len] = '\0';
  if (out_len) *out_len = len;
  return buf;
}

/* Read an entire file by `path` (a `String`) into a fresh `String`. A missing/unreadable file or any
 * read error yields the empty `String` (never a crash) — the handler's job is to fold I/O, not to
 * surface error codes into pure code (a future `Either`-typed variant could). */
static BlValue bl_read_whole_file(BlValue path) {
  size_t plen = 0;
  char *cpath = bl_string_to_cstr(path, &plen);
  if (!cpath) return bl_alloc(BL_CON, 0, 0); /* empty */
  FILE *f = fopen(cpath, "rb");
  free(cpath);
  if (!f) return bl_alloc(BL_CON, 0, 0); /* empty on open failure */
  size_t cap = 4096, len = 0;
  unsigned char *data = (unsigned char *)malloc(cap);
  if (!data) { fclose(f); return bl_alloc(BL_CON, 0, 0); }
  for (;;) {
    if (len == cap) {
      cap *= 2;
      unsigned char *grown = (unsigned char *)realloc(data, cap);
      if (!grown) { free(data); fclose(f); return bl_alloc(BL_CON, 0, 0); }
      data = grown;
    }
    size_t got = fread(data + len, 1, cap - len, f);
    len += got;
    if (got == 0) break;
  }
  fclose(f);
  BlValue s = bl_string_of(data, len);
  free(data);
  return s;
}

/* Write `contents` (a `String`) to the file named by `path` (a `String`), truncating. A `mk-pair`
 * envelope carries both: field[0] = path, field[1] = contents. Errors print a warning to stderr and
 * are otherwise a no-op (the op still resumes with `tt`). */
static void bl_write_whole_file(BlValue pair) {
  if (!pair || bl_obj_tag(pair) != BL_CON || bl_obj_nfields(pair) != 2) return;
  BlValue path = bl_obj_field(pair, 0);
  BlValue contents = bl_obj_field(pair, 1);
  size_t plen = 0, clen = 0;
  char *cpath = bl_string_to_cstr(path, &plen);
  char *cdata = bl_string_to_cstr(contents, &clen);
  if (cpath && cdata) {
    FILE *f = fopen(cpath, "wb");
    if (f) {
      fwrite(cdata, 1, clen, f);
      fclose(f);
    } else {
      fprintf(stderr, "blight: write-file could not open '%s'\n", cpath);
    }
  }
  free(cpath);
  free(cdata);
}

/* ---- Bytes native handler helpers (C2, std/bytes.bl). ----
 *
 * A `Bytes` effect gives untrusted `.bl` code a mutable, runtime-backed byte buffer — the substrate a
 * self-hosted lexer/parser (C3) needs to walk a file's bytes without rebuilding a cons-list on every
 * step. The *pure* Blight value is just a plain `Int` HANDLE (a trusted, re-checkable kernel type)
 * indexing this C-side table; the actual mutable storage lives entirely outside the GC graph (like a
 * file lives in the OS for `FileIO`), so the byte arrays add ZERO new traced object kinds and ZERO
 * TCB — a program only ever passes an `Int` around. Handles are never recycled (monotonic), so a
 * stale handle is always detectably out of range rather than aliasing a new buffer.
 *
 * The table is thread-local: each native worker (M15 pool) gets its own buffers, matching the
 * thread-local GC nursery and `g_collections`. Buffers are freed at process exit by the OS; a
 * long-running embedding could add an explicit free op later (not needed for the batch compiler). */
typedef struct {
  unsigned char *data;
  size_t len;
} BlByteBuf;

static BL_THREAD_LOCAL BlByteBuf *g_bytes = NULL;
static BL_THREAD_LOCAL size_t g_bytes_len = 0; /* number of live handles */
static BL_THREAD_LOCAL size_t g_bytes_cap = 0; /* table capacity */

/* Allocate a zero-filled buffer of `len` bytes, returning its handle (a non-negative table index).
 * Returns -1 on allocation failure (the op then resumes with `Int -1`, an out-of-range handle every
 * subsequent get/set rejects, so a failed allocation degrades to no-ops rather than a crash). */
static int64_t bl_bytes_new(size_t len) {
  if (g_bytes_len == g_bytes_cap) {
    size_t ncap = g_bytes_cap == 0 ? 8 : g_bytes_cap * 2;
    BlByteBuf *grown = (BlByteBuf *)realloc(g_bytes, ncap * sizeof(BlByteBuf));
    if (!grown) return -1;
    g_bytes = grown;
    g_bytes_cap = ncap;
  }
  unsigned char *data = (unsigned char *)calloc(len ? len : 1, 1);
  if (!data) return -1;
  int64_t h = (int64_t)g_bytes_len;
  g_bytes[g_bytes_len].data = data;
  g_bytes[g_bytes_len].len = len;
  g_bytes_len++;
  return h;
}

/* True iff `h` names a live buffer. */
static int bl_bytes_valid(int64_t h) {
  return h >= 0 && (size_t)h < g_bytes_len && g_bytes[h].data != NULL;
}

/* Read byte `i` of buffer `h`; out-of-range handle/index reads as 0 (total, never traps). */
static uint64_t bl_bytes_get(int64_t h, uint64_t i) {
  if (!bl_bytes_valid(h) || i >= g_bytes[h].len) return 0;
  return g_bytes[h].data[i];
}

/* Write the low 8 bits of `v` to byte `i` of buffer `h`; out-of-range handle/index is a no-op. */
static void bl_bytes_set(int64_t h, uint64_t i, uint64_t v) {
  if (!bl_bytes_valid(h) || i >= g_bytes[h].len) return;
  g_bytes[h].data[i] = (unsigned char)(v & 0xFFu);
}

/* Length of buffer `h` (0 for an invalid handle). */
static size_t bl_bytes_length(int64_t h) {
  return bl_bytes_valid(h) ? g_bytes[h].len : 0;
}

/* ---- Arrays native handler helpers (A3a, std/array.bl). ----
 *
 * A scalar `Int`-valued mutable array: the exact `Bytes` pattern above, except each element is a raw
 * `int64_t` rather than a byte. Because elements are machine integers (never GC pointers), a
 * `malloc`'d table of them can never hold a stale/moved pointer, so this is GC-safe with zero tracer
 * changes — unlike a hypothetical array of boxed `BlValue`s (see A3b, gated). Handles are monotonic
 * and thread-local, mirroring `g_bytes`. */
typedef struct {
  int64_t *data;
  size_t len;
} BlIntArray;

static BL_THREAD_LOCAL BlIntArray *g_arrays = NULL;
static BL_THREAD_LOCAL size_t g_arrays_len = 0; /* number of live handles */
static BL_THREAD_LOCAL size_t g_arrays_cap = 0; /* table capacity */

/* Allocate a zero-filled array of `len` `Int` elements, returning its handle (a non-negative table
 * index). Returns -1 on allocation failure (an always-invalid handle, so subsequent ops degrade to
 * no-ops rather than a crash). */
static int64_t bl_array_new(size_t len) {
  if (g_arrays_len == g_arrays_cap) {
    size_t ncap = g_arrays_cap == 0 ? 8 : g_arrays_cap * 2;
    BlIntArray *grown = (BlIntArray *)realloc(g_arrays, ncap * sizeof(BlIntArray));
    if (!grown) return -1;
    g_arrays = grown;
    g_arrays_cap = ncap;
  }
  int64_t *data = (int64_t *)calloc(len ? len : 1, sizeof(int64_t));
  if (!data) return -1;
  int64_t h = (int64_t)g_arrays_len;
  g_arrays[g_arrays_len].data = data;
  g_arrays[g_arrays_len].len = len;
  g_arrays_len++;
  return h;
}

/* True iff `h` names a live array. */
static int bl_array_valid(int64_t h) {
  return h >= 0 && (size_t)h < g_arrays_len && g_arrays[h].data != NULL;
}

/* Read element `i` of array `h`; out-of-range handle/index reads as 0 (total, never traps). */
static int64_t bl_array_get(int64_t h, uint64_t i) {
  if (!bl_array_valid(h) || i >= g_arrays[h].len) return 0;
  return g_arrays[h].data[i];
}

/* Write `v` to element `i` of array `h`; out-of-range handle/index is a no-op. */
static void bl_array_set(int64_t h, uint64_t i, int64_t v) {
  if (!bl_array_valid(h) || i >= g_arrays[h].len) return;
  g_arrays[h].data[i] = v;
}

/* Length of array `h` (0 for an invalid handle). */
static size_t bl_array_length(int64_t h) {
  return bl_array_valid(h) ? g_arrays[h].len : 0;
}

/* ---- `Clock` effect (Wave 2 / L1, std/time.bl): wall-clock time as a machine `Int` ----------------
 *
 * `Clock` is another ordinary user effect folded by the same top-level handler, exactly like
 * `Bytes`/`Arrays`: a single total op `now : Unit -> Int` with zero mutable state of its own (unlike
 * `Bytes`/`Arrays` it needs no side table at all — it just reads the OS clock). Milliseconds since the
 * Unix epoch is used (rather than seconds) so that two `now` calls close together in a test are very
 * likely to differ, without needing sub-millisecond precision no test here depends on. */
static int64_t bl_clock_now_ms(void) {
  struct timeval tv;
  if (gettimeofday(&tv, NULL) != 0) return 0; /* total: a clock failure reads as epoch 0, never traps */
  return (int64_t)tv.tv_sec * 1000 + (int64_t)(tv.tv_usec / 1000);
}

BlValue bl_run_console(BlValue comp) {
  bl_gc_push_root(&comp);
  for (;;) {
    if (!is_opnode(comp)) {
      bl_gc_pop_roots(1);
      return comp; /* pure result */
    }
    const char *opn = op_name_of(comp->header.aux);
    BlValue arg = comp->fields[0];
    BlValue kont = comp->fields[1];
    if (strcmp(opn, "print") == 0) {
      bl_emit_string(arg);
      fflush(stdout);
      BlValue u = bl_unit();
      comp = (kont == NULL) ? u : bl_apply1(kont, u);
    } else if (strcmp(opn, "read") == 0) {
      char *line = NULL;
      size_t cap = 0;
      ssize_t got = getline(&line, &cap, stdin);
      size_t len = 0;
      if (got > 0) {
        len = (size_t)got;
        if (line[len - 1] == '\n') len--; /* strip the trailing newline */
      }
      BlValue s = bl_string_of((const unsigned char *)line, len);
      free(line);
      bl_gc_push_root(&s);
      comp = (kont == NULL) ? s : bl_apply1(kont, s);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "read-file") == 0) {
      BlValue s = bl_read_whole_file(arg);
      bl_gc_push_root(&s);
      comp = (kont == NULL) ? s : bl_apply1(kont, s);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "write-file") == 0) {
      bl_write_whole_file(arg);
      BlValue u = bl_unit();
      comp = (kont == NULL) ? u : bl_apply1(kont, u);
    } else if (strcmp(opn, "new-bytes") == 0) {
      /* arg : Nat (length). Resume with the Int handle (-1 on allocation failure). */
      int64_t h = bl_bytes_new((size_t)bl_nat_of_value(arg));
      BlValue r = bl_int(h);
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "bytes-len") == 0) {
      /* arg : Int (handle). Resume with the Nat length. */
      BlValue r = bl_nat_from_u64((uint64_t)bl_bytes_length(bl_int_val(arg)));
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "get-byte") == 0) {
      /* arg : (Pair Int Nat) = (handle, index). Resume with the Nat byte (0 if out of range). */
      int64_t h = bl_int_val(bl_obj_field(arg, 0));
      uint64_t i = bl_nat_of_value(bl_obj_field(arg, 1));
      BlValue r = bl_nat_from_u64(bl_bytes_get(h, i));
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "set-byte") == 0) {
      /* arg : (Pair Int (Pair Nat Nat)) = (handle, (index, value)). Resume with Unit. */
      int64_t h = bl_int_val(bl_obj_field(arg, 0));
      BlValue rest = bl_obj_field(arg, 1);
      uint64_t i = bl_nat_of_value(bl_obj_field(rest, 0));
      uint64_t v = bl_nat_of_value(bl_obj_field(rest, 1));
      bl_bytes_set(h, i, v);
      BlValue u = bl_unit();
      comp = (kont == NULL) ? u : bl_apply1(kont, u);
    } else if (strcmp(opn, "new-array") == 0) {
      /* arg : Nat (length). Resume with the Int handle (-1 on allocation failure). */
      int64_t h = bl_array_new((size_t)bl_nat_of_value(arg));
      BlValue r = bl_int(h);
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "array-len") == 0) {
      /* arg : Int (handle). Resume with the Nat length. */
      BlValue r = bl_nat_from_u64((uint64_t)bl_array_length(bl_int_val(arg)));
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "get-elem") == 0) {
      /* arg : (Pair Int Nat) = (handle, index). Resume with the Int element (0 if out of range). */
      int64_t h = bl_int_val(bl_obj_field(arg, 0));
      uint64_t i = bl_nat_of_value(bl_obj_field(arg, 1));
      BlValue r = bl_int(bl_array_get(h, i));
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "set-elem") == 0) {
      /* arg : (Pair Int (Pair Nat Int)) = (handle, (index, value)). Resume with Unit. */
      int64_t h = bl_int_val(bl_obj_field(arg, 0));
      BlValue rest = bl_obj_field(arg, 1);
      uint64_t i = bl_nat_of_value(bl_obj_field(rest, 0));
      int64_t v = bl_int_val(bl_obj_field(rest, 1));
      bl_array_set(h, i, v);
      BlValue u = bl_unit();
      comp = (kont == NULL) ? u : bl_apply1(kont, u);
    } else if (strcmp(opn, "new-boxed-array") == 0) {
      /* arg : (Pair Nat A) = (length, initial value). Resume with the Int handle (-1 on failure). */
      uint64_t len = bl_nat_of_value(bl_obj_field(arg, 0));
      BlValue init = bl_obj_field(arg, 1);
      int64_t h = bl_boxed_array_new((size_t)len, init);
      BlValue r = bl_int(h);
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "boxed-len") == 0) {
      /* arg : Int (handle). Resume with the Nat length. */
      BlValue r = bl_nat_from_u64((uint64_t)bl_boxed_array_length(bl_int_val(arg)));
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "get-boxed") == 0) {
      /* arg : (Pair Int Nat) = (handle, index). Resume with the element (a fresh nullary Con if the
       * handle/index is invalid — see bl_boxed_array_get's header comment for why). */
      int64_t h = bl_int_val(bl_obj_field(arg, 0));
      uint64_t i = bl_nat_of_value(bl_obj_field(arg, 1));
      BlValue r = bl_boxed_array_get(h, i);
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "set-boxed") == 0) {
      /* arg : (Pair Int (Pair Nat A)) = (handle, (index, value)). Resume with Unit. */
      int64_t h = bl_int_val(bl_obj_field(arg, 0));
      BlValue rest = bl_obj_field(arg, 1);
      uint64_t i = bl_nat_of_value(bl_obj_field(rest, 0));
      BlValue v = bl_obj_field(rest, 1);
      bl_boxed_array_set(h, i, v);
      BlValue u = bl_unit();
      comp = (kont == NULL) ? u : bl_apply1(kont, u);
    } else if (strcmp(opn, "now") == 0) {
      /* arg : Unit (ignored). Resume with the Int wall-clock time (milliseconds since the epoch). */
      BlValue r = bl_int(bl_clock_now_ms());
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else {
      /* An operation we do not interpret bubbled to the top: report and stop. */
      fprintf(stderr, "blight: unhandled Console operation %s\n", opn);
      bl_gc_pop_roots(1);
      return comp;
    }
  }
}
