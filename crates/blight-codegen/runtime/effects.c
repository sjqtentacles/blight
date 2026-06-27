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

/* Intern table mapping (effect,op) -> index stored in BL_OPNODE.header.aux. Small and append-only;
 * effect/op name sets are tiny per program. */
typedef struct { const char *effect; const char *op; } OpKey;
#define BL_MAX_OPS 256
static OpKey g_ops[BL_MAX_OPS];
static size_t g_nops;

static uint64_t intern_op(const char *effect, const char *op) {
  for (size_t i = 0; i < g_nops; i++) {
    if (strcmp(g_ops[i].effect, effect) == 0 && strcmp(g_ops[i].op, op) == 0) return i;
  }
  if (g_nops >= BL_MAX_OPS) { fprintf(stderr, "blight: too many effect ops\n"); abort(); }
  g_ops[g_nops].effect = effect;
  g_ops[g_nops].op = op;
  return g_nops++;
}

static const char *op_name_of(uint64_t idx) {
  return idx < g_nops ? g_ops[idx].op : "?";
}

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

static int is_opnode(BlValue v) { return v != NULL && v->header.tag == BL_OPNODE; }

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
  uint32_t tag = obj->header.tag;
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
    if (comp == NULL || comp->header.tag != BL_OPNODE) {
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

static BlValue bl_apply1(BlValue clo, BlValue arg) {
  BlClo1 fn = (BlClo1)(void *)(uintptr_t)clo->header.aux;
  return fn(clo, arg);
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

static BlValue bl_cont_apply(BlValue clo, BlValue v) {
  BlValue kont = clo->fields[0];
  BlHandler *h = (BlHandler *)(uintptr_t)clo->fields[1]->header.aux;
  BlValue resumed = (kont == NULL) ? v : bl_apply1(kont, v);
  return bl_handle_fold(h, resumed);
}

static BlValue make_cont(BlHandler *h, BlValue kont) {
  /* field[1] boxes the handler pointer as a BL_INT (an opaque, fieldless object the GC won't chase
   * into the malloc'd record). field[0] is the real captured continuation (traced). GC-safe: alloc
   * the closure first and root it before allocating the box. */
  BlValue clo = bl_alloc(BL_CLOSURE, 2, (uint64_t)(uintptr_t)(void *)bl_cont_apply);
  clo->fields[0] = kont;
  bl_gc_push_root(&clo);
  BlValue hbox = bl_alloc(BL_INT, 0, (uint64_t)(uintptr_t)h);
  clo->fields[1] = hbox;
  bl_gc_pop_roots(1);
  return clo;
}

static BlValue bl_handle_fold(BlHandler *h, BlValue comp) {
  for (;;) {
    if (comp == NULL || comp->header.tag != BL_OPNODE) {
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
            which, arg ? arg->header.tag : 999, partial ? partial->header.tag : 999,
            comp ? comp->header.tag : 999);
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
  fprintf(stderr, "[handle] body -> tag=%u n_ops=%zu\n", comp ? comp->header.tag : 999, n_ops);
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
 * but without the implicit newline, so `print` is faithful line-by-line output. */
static void bl_emit_string(BlValue s) {
  BlValue cur = s;
  while (cur && cur->header.tag == BL_CON && cur->header.aux == 1 && cur->header.nfields == 2) {
    /* field[0] is a unary Nat codepoint: count Succ depth. */
    uint64_t cp = 0;
    BlValue n = cur->fields[0];
    while (n && n->header.tag == BL_CON && n->header.aux == 1 && n->header.nfields == 1) {
      cp++;
      n = n->fields[0];
    }
    putchar((int)(unsigned char)cp);
    cur = cur->fields[1];
  }
}

BlValue bl_run_console(BlValue comp) {
  bl_gc_push_root(&comp);
  for (;;) {
    if (comp == NULL || comp->header.tag != BL_OPNODE) {
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
    } else {
      /* An operation we do not interpret bubbled to the top: report and stop. */
      fprintf(stderr, "blight: unhandled Console operation %s\n", opn);
      bl_gc_pop_roots(1);
      return comp;
    }
  }
}
