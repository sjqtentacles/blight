/* wasm_rt.c — a *freestanding* WebAssembly runtime ABI for Blight (Wave 10 / P3).
 *
 * The native runtime (gc.c / arena.c / stack.c / effects.c / prelude_rt.c) leans on libc (mmap,
 * stdio) and a precise copying GC, none of which exist in a bare `wasm32-unknown-unknown` module.
 * This shim provides the ABI a compiled Blight `program.o` links against so a `wasm-ld` step
 * produces a runnable `.wasm` module:
 *
 *   - `bl_alloc` / `bl_con` / `bl_int` / `bl_int_val` — a bump allocator over wasm linear memory,
 *     growing it with `memory.grow` on demand rather than silently overrunning the module's
 *     initial page count.
 *   - `bl_gc_init` / `bl_stack_init` / `bl_gc_poll` / root push+pop / `bl_write_barrier` — no-ops
 *     (a wasm module is short-lived and the bump heap is never collected here).
 *   - `bl_force` (the `Delay`/`Later` trampoline), `bl_perform` / `bl_app` / `bl_app_global` /
 *     `bl_con_bubble` / `bl_handle_clo` (the algebraic-effect machinery), and `bl_arena_enter` /
 *     `bl_arena_alloc` / `bl_arena_leave` (region arenas) — a REAL, if simplified, port: these are
 *     all *pure compute* over the object model (no stdio, no threads, no moving GC to race), so
 *     they port with no semantic loss once every `bl_gc_push_root`/`bl_write_barrier` call they
 *     make becomes the no-op it already is on this target. See "Honest scope" below for the one
 *     deliberate simplification (region reclaim).
 *
 * ── Honest scope: what is genuinely unsupported here (WASI/GC/threads) ─────────────────────────
 * `Console`/`FileIO`/`Clock` are NOT provided: they need `stdio`/`getline`/`sys/time.h`, none of
 * which exist in this `-nostdlib` freestanding build. A program whose `main` performs any of these
 * (rather than just `Delay`/generic algebraic effects/regions) will link (thanks to `wasm-ld
 * --allow-undefined`) but TRAP when `bl_main` actually calls the missing import — an honest runtime
 * failure, not silent wrong output. Supporting them for real is a WASI target (`wasm32-wasip1`),
 * not this freestanding one, and is out of scope. Likewise there is no moving/generational GC here
 * (the bump heap never reclaims — see below) and no `worker.c` (no pthreads on
 * `wasm32-unknown-unknown`): multicore/auto-parallelism (P4) has no wasm story.
 *
 * Region reclaim (`bl_arena_leave`) is a documented no-op simplification: `bl_arena_alloc` routes
 * to the exact same growing bump heap as `bl_alloc` (rather than a second chunk-stack the way
 * native `arena.c` does), because that heap is *already* never reclaimed on this target — regions
 * exist natively purely to make reclaim O(1) instead of waiting for a GC that doesn't happen; since
 * nothing on this target ever reclaims at all, collapsing "arena" and "heap" allocation loses no
 * *correctness* (a region's values are used only within their lexical scope by construction — the
 * Rust-side escape analysis that decides what goes through `bl_arena_alloc` doesn't change per
 * target), only the memory-reuse optimization region.c exists to provide natively.
 *
 * The module exports `bl_main`, which runs the compiled entry and returns the result as an i32
 * (a Nat's Succ-depth, or a boxed integer's payload), so a host (e.g. `wasmtime`) can call it and
 * read a value back.
 */

#include <stddef.h>
#include <stdint.h>

/* Mirror of the native object layout (blight_rt.h) — kept in sync by hand; this file is only
 * compiled for the wasm target. */
typedef enum {
  BL_CON = 0,
  BL_TUPLE = 1,
  BL_CLOSURE = 2,
  BL_NOW = 3,
  BL_LATER = 4,
  BL_INT = 5,
  BL_OPNODE = 6,
  BL_FWD = 7
} BlTag;

typedef struct BlHeader {
  uint32_t tag;
  uint32_t nfields;
  uint64_t aux;
} BlHeader;

typedef struct BlObj {
  BlHeader header;
  struct BlObj *fields[];
} BlObj;

typedef BlObj *BlValue;

/* ---- tagged-immediate unboxing (M21) — kept in sync with blight_rt.h ----
 * The native runtime carries small Nat/Int and nullary constructors inline in the pointer's low
 * bits (no heap box). The codegen emits the same immediates for every target, so this freestanding
 * wasm shim mirrors the decode so a `case`/`bl_to_i32` over an immediate behaves identically. */
#define BL_IMM_FLAG 0x1u
#define BL_IMM_KIND_SHIFT 1u
#define BL_IMM_KIND_MASK 0x7u
#define BL_IMM_PAYLOAD_SHIFT 4u
typedef enum { BL_IMM_NAT = 0u, BL_IMM_INT = 1u, BL_IMM_CON = 2u } BlImmKind;
#define BL_NAT 8 /* observational tag of an immediate/boxed fast Nat (native blight_rt.h) */

static inline int bl_is_imm(BlValue v) { return ((uintptr_t)v & BL_IMM_FLAG) != 0u; }
static inline BlImmKind bl_imm_kind(BlValue v) {
  return (BlImmKind)(((uintptr_t)v >> BL_IMM_KIND_SHIFT) & BL_IMM_KIND_MASK);
}
static inline uint64_t bl_imm_payload(BlValue v) {
  return (uint64_t)((uintptr_t)v >> BL_IMM_PAYLOAD_SHIFT);
}
static inline BlValue bl_make_imm(BlImmKind kind, uint64_t payload) {
  return (BlValue)(uintptr_t)(((uintptr_t)payload << BL_IMM_PAYLOAD_SHIFT) |
                              ((uintptr_t)kind << BL_IMM_KIND_SHIFT) | BL_IMM_FLAG);
}
static inline int bl_imm_fits(uint64_t payload) {
  return (payload >> (64u - BL_IMM_PAYLOAD_SHIFT)) == 0u;
}
/* Only BL_ARENA_BIT is ever meaningful on this target (no remembered-set/gray-worklist bits — there
 * is no generational GC to need them); masking it out mirrors native's `BL_TAG(o)` macro so a raw
 * `header.tag` compare (`== BL_OPNODE`, `== BL_NOW`, …) still works even though `bl_arena_alloc`
 * (below) never actually sets the bit today. */
#define BL_ARENA_BIT 0x80000000u

static inline uint32_t bl_obj_tag_w(BlValue v) {
  if (bl_is_imm(v)) {
    switch (bl_imm_kind(v)) {
      case BL_IMM_NAT: return BL_NAT;
      case BL_IMM_INT: return BL_INT;
      case BL_IMM_CON: return BL_CON;
    }
  }
  return v->header.tag & ~BL_ARENA_BIT;
}
static inline uint64_t bl_obj_aux_w(BlValue v) {
  return bl_is_imm(v) ? bl_imm_payload(v) : v->header.aux;
}
static inline uint32_t bl_obj_nfields_w(BlValue v) {
  return bl_is_imm(v) ? 0u : v->header.nfields;
}

/* ---- bump allocator over wasm linear memory ----
 * `__heap_base` is provided by wasm-ld: the first byte past static data. We bump from there; the
 * module never frees (a short-lived computation), so no GC is needed for this minimal ABI.
 *
 * Growth: the previous version of this shim never grew linear memory at all, so any program
 * allocating past the module's initial page count (the default `wasm-ld` gives a handful of pages
 * — a few hundred KB) would silently write out of bounds. `bl_bump_ensure` grows memory with the
 * `memory.grow` instruction (via clang's `__builtin_wasm_memory_*` builtins — freestanding-safe, no
 * libc) whenever the bump frontier would cross the currently-available memory, so `perform`/
 * `handle`/`force`-using programs get a real (if still bounded by wasm's own max-memory limit)
 * heap rather than corrupting memory the first time they allocate more than a few KB. */
extern unsigned char __heap_base;
static uintptr_t bl_bump = 0;

static void bl_bump_init(void) {
  if (bl_bump == 0) {
    bl_bump = (uintptr_t)&__heap_base;
    /* 8-byte align the frontier. */
    bl_bump = (bl_bump + 7u) & ~(uintptr_t)7u;
  }
}

#define BL_WASM_PAGE_BYTES 65536u

static void bl_bump_ensure(size_t extra) {
  uintptr_t need = bl_bump + (uintptr_t)extra;
  uintptr_t have = (uintptr_t)__builtin_wasm_memory_size(0) * BL_WASM_PAGE_BYTES;
  if (need <= have) return;
  uintptr_t deficit = need - have;
  uint32_t pages = (uint32_t)((deficit + (BL_WASM_PAGE_BYTES - 1u)) / BL_WASM_PAGE_BYTES);
  if (__builtin_wasm_memory_grow(0, pages) == -1) {
    /* Out of memory (hit wasm's own max-memory limit): nothing sensible to return: trap rather
     * than silently corrupt memory by bumping past what's actually mapped. */
    __builtin_trap();
  }
}

/* A minimal bump "allocator" for raw (non-`BlObj`) bytes, used by the effect-handler machinery
 * below in place of `malloc` (unavailable in this freestanding build). Like `bl_alloc`, this never
 * frees — the same short-lived-module model the whole file already uses; `wasm_free` exists only so
 * call sites read symmetrically with the native `malloc`/`free` code they mirror. */
static void *wasm_malloc(size_t n) {
  bl_bump_init();
  n = (n + 7u) & ~(size_t)7u;
  bl_bump_ensure(n);
  void *p = (void *)bl_bump;
  bl_bump += n;
  return p;
}
static void wasm_free(void *p) { (void)p; }

BlValue bl_alloc(BlTag tag, uint32_t nfields, uint64_t aux) {
  bl_bump_init();
  size_t bytes = sizeof(BlHeader) + (size_t)nfields * sizeof(BlValue);
  bytes = (bytes + 7u) & ~(size_t)7u;
  bl_bump_ensure(bytes);
  BlValue o = (BlValue)bl_bump;
  bl_bump += bytes;
  o->header.tag = (uint32_t)tag;
  o->header.nfields = nfields;
  o->header.aux = aux;
  return o;
}

BlValue bl_int(int64_t n) {
  uint64_t bits = (uint64_t)n;
  if (bl_imm_fits(bits)) return bl_make_imm(BL_IMM_INT, bits);
  return bl_alloc(BL_INT, 0, bits);
}
int64_t bl_int_val(BlValue v) { return (int64_t)bl_obj_aux_w(v); }
BlValue bl_con(uint64_t ctor_index, uint32_t nfields) {
  if (nfields == 0 && bl_imm_fits(ctor_index)) return bl_make_imm(BL_IMM_CON, ctor_index);
  return bl_alloc(BL_CON, nfields, ctor_index);
}

/* ---- machine-word Nat helpers (mirror numeric.c) so a `case`/recognized Nat links on wasm ---- */
static uint64_t bl_nat_of_value_w(BlValue v) {
  if (v == NULL) return 0;
  if (bl_obj_tag_w(v) == BL_NAT) return bl_obj_aux_w(v);
  uint64_t n = 0;
  BlValue cur = v;
  while (cur && bl_obj_tag_w(cur) == BL_CON && bl_obj_aux_w(cur) == 1 && bl_obj_nfields_w(cur) == 1) {
    n++;
    cur = cur->fields[0];
  }
  return n;
}
BlValue bl_nat_from_u64(uint64_t n) {
  if (bl_imm_fits(n)) return bl_make_imm(BL_IMM_NAT, n);
  return bl_alloc((BlTag)BL_NAT, 0, n);
}
uint64_t bl_nat_of_value(BlValue v) { return bl_nat_of_value_w(v); }
BlValue bl_nat_add(BlValue a, BlValue b) { return bl_nat_from_u64(bl_nat_of_value_w(a) + bl_nat_of_value_w(b)); }
BlValue bl_nat_mul(BlValue a, BlValue b) { return bl_nat_from_u64(bl_nat_of_value_w(a) * bl_nat_of_value_w(b)); }
BlValue bl_nat_sub(BlValue a, BlValue b) {
  uint64_t x = bl_nat_of_value_w(a), y = bl_nat_of_value_w(b);
  return bl_nat_from_u64(x > y ? x - y : 0);
}
BlValue bl_nat_pred(BlValue a) {
  uint64_t x = bl_nat_of_value_w(a);
  return bl_nat_from_u64(x == 0 ? 0 : x - 1);
}
/* Materialize one inductive layer for a generic destructuring reader (codegen `emit_case`), boxing
 * the result so the reader can read a real header. Identity on a non-Nat boxed value. */
BlValue bl_nat_to_con(BlValue v) {
  if (v == NULL) return v;
  if (bl_is_imm(v)) {
    switch (bl_imm_kind(v)) {
      case BL_IMM_CON: return bl_alloc(BL_CON, 0, bl_imm_payload(v));
      case BL_IMM_INT: return bl_alloc(BL_INT, 0, bl_imm_payload(v));
      case BL_IMM_NAT: break;
    }
  } else if (v->header.tag != BL_NAT) {
    return v;
  }
  uint64_t n = bl_obj_aux_w(v);
  if (n == 0) return bl_alloc(BL_CON, 0, 0);
  BlValue pred = bl_nat_from_u64(n - 1);
  BlValue succ = bl_alloc(BL_CON, 1, 1);
  succ->fields[0] = pred;
  return succ;
}

/* ---- GC / stack / safepoint: no-ops on this freestanding target ---- */
/* `bl_gc_pop_roots`'s count parameter is `uint64_t`, not `size_t`, even though this file otherwise
 * uses `size_t` freely: the LLVM emitter (`llvm.rs::declare_runtime`) hardcodes every ABI-visible
 * count/aux parameter as `i64` regardless of target (it mirrors the *native* `size_t`, which is
 * 64-bit on every native target Blight ships for), but C's `size_t` on `wasm32-unknown-unknown` is
 * 32-bit — so declaring this `size_t` here would silently mismatch the caller's `i64` argument (an
 * ABI bug `wasm-ld` reports as a "function signature mismatch" warning and `wasmtime` then traps
 * on, since a 32-bit callee reading a 64-bit push cannot possibly see the right value). Every
 * *other* function below either only takes pointer/`uint32_t`/`uint64_t` params already (`bl_alloc`,
 * `bl_handle_clo`'s `n_ops`, …) or is never called from LLVM-generated code (`bl_gc_init`,
 * `bl_arena_live_bytes`, …), so this is the one place the mismatch actually bites. */
void bl_gc_init(size_t heap_bytes) { (void)heap_bytes; bl_bump_init(); }
void bl_gc_poll(void) {}
void bl_gc_push_root(BlValue *slot) { (void)slot; }
void bl_gc_pop_roots(uint64_t n) { (void)n; }
void bl_write_barrier(BlValue obj, BlValue val) { (void)obj; (void)val; }
void bl_stack_init(void) {}

/* ---- region arenas (spec §3.5) — see the file header's "Honest scope" note on why this collapses
 * to the general heap on this target rather than a second chunk-stack: nothing here ever reclaims
 * anyway, so there is no O(1)-reclaim property to actually provide. */
void bl_arena_enter(void) {}
BlValue bl_arena_alloc(BlTag tag, uint32_t nfields, uint64_t aux) { return bl_alloc(tag, nfields, aux); }
void bl_arena_leave(void) {}
size_t bl_arena_live_bytes(void) { return 0; }
size_t bl_arena_alloc_count(void) { return 0; }

/* ---- Delay/Later trampoline (mirror delay.c) ----
 * Ported directly rather than compiling delay.c itself: delay.c includes the native `blight_rt.h`
 * (pulls in libc declarations this freestanding build doesn't have) and prints a diagnostic via
 * `stderr` on a null delay, which isn't available here either. The trampoline logic itself needs
 * only `bl_gc_push_root`/`bl_gc_pop_roots` (already no-ops above) and the BL_NOW/BL_LATER tags, so
 * it is otherwise bit-for-bit the same loop. */
typedef BlValue (*BlStep)(BlValue closure, BlValue arg);

static BlValue wasm_step_thunk(BlValue thunk) {
  BlStep fn = (BlStep)(void *)(uintptr_t)thunk->header.aux;
  return fn(thunk, NULL);
}

BlValue bl_force(BlValue delay) {
  BlValue cur = delay;
  for (;;) {
    if (cur == NULL) return NULL;
    if (bl_is_imm(cur)) return cur; /* an immediate is already a value */
    switch (bl_obj_tag_w(cur)) {
      case BL_NOW: return cur->fields[0];
      case BL_LATER: cur = wasm_step_thunk(cur->fields[0]); break;
      default: return cur; /* a bare (already-evaluated) value */
    }
  }
}

/* ---- algebraic-effect machinery (mirror effects.c) ----
 * Direct port of the OpNode-aware application / construction / deep-handler trampoline: every
 * `bl_gc_push_root`/`bl_gc_pop_roots` call in the native version is a no-op here (no moving GC to
 * root against), so the logic carries over with no semantic change — only `malloc` (handler
 * records) becomes `wasm_malloc` and the op-name intern table drops its multicore freeze/thread-
 * local bookkeeping (this target never spawns a second thread). */

typedef struct { const char *effect; const char *op; } BlOpKey;
#define BL_MAX_OPS 256
static BlOpKey g_ops[BL_MAX_OPS];
static size_t g_nops;

static int bl_streq(const char *a, const char *b) {
  while (*a && *a == *b) { a++; b++; }
  return *a == *b;
}

static uint64_t wasm_intern_op(const char *effect, const char *op) {
  for (size_t i = 0; i < g_nops; i++) {
    if (bl_streq(g_ops[i].effect, effect) && bl_streq(g_ops[i].op, op)) return i;
  }
  if (g_nops >= BL_MAX_OPS) __builtin_trap();
  g_ops[g_nops].effect = effect;
  g_ops[g_nops].op = op;
  return g_nops++;
}

uint64_t bl_effect_intern(const char *effect, const char *op) { return wasm_intern_op(effect, op); }
void bl_effect_intern_freeze(void) { /* no-op: single-threaded target, nothing to race */ }

static const char *wasm_op_name_of(uint64_t idx) { return idx < g_nops ? g_ops[idx].op : "?"; }

static int is_opnode(BlValue v) { return v != NULL && !bl_is_imm(v) && bl_obj_tag_w(v) == BL_OPNODE; }

static BlValue wasm_apply1(BlValue clo, BlValue arg) {
  BlStep fn = (BlStep)(void *)(uintptr_t)clo->header.aux;
  return fn(clo, arg);
}

static BlValue wasm_perform_idx(uint64_t opidx, BlValue arg);

static BlValue wasm_perform_apply(BlValue clo, BlValue v) {
  BlValue old_cont = clo->fields[0];
  uint64_t opidx = clo->fields[1]->header.aux;
  BlValue resumed = (old_cont == NULL) ? v : wasm_apply1(old_cont, v);
  return wasm_perform_idx(opidx, resumed);
}

static BlValue make_perform_cont(BlValue old_cont, uint64_t opidx) {
  BlValue clo = bl_alloc(BL_CLOSURE, 2, (uint64_t)(uintptr_t)(void *)wasm_perform_apply);
  clo->fields[0] = old_cont;
  BlValue idxbox = bl_alloc(BL_INT, 0, opidx);
  clo->fields[1] = idxbox;
  return clo;
}

static BlValue wasm_perform_idx(uint64_t opidx, BlValue arg) {
  if (is_opnode(arg)) {
    BlValue node = bl_alloc(BL_OPNODE, 2, arg->header.aux);
    node->fields[0] = arg->fields[0];
    node->fields[1] = make_perform_cont(arg->fields[1], opidx);
    return node;
  }
  BlValue node = bl_alloc(BL_OPNODE, 2, opidx);
  node->fields[0] = arg;
  node->fields[1] = NULL;
  return node;
}

BlValue bl_perform(const char *effect, const char *op, BlValue arg) {
  return wasm_perform_idx(wasm_intern_op(effect, op), arg);
}

static BlValue make_compose(BlValue old_cont, uint64_t mode, BlValue fixed);
BlValue bl_app(BlValue f, BlValue a);

static BlValue wasm_compose_apply(BlValue clo, BlValue v) {
  BlValue old_cont = clo->fields[0];
  uint64_t mode = clo->fields[1]->header.aux;
  BlValue resumed = (old_cont == NULL) ? v : wasm_apply1(old_cont, v);
  BlValue fixed = clo->fields[2];
  return (mode == 0) ? bl_app(fixed, resumed) : bl_app(resumed, fixed);
}

static BlValue make_compose(BlValue old_cont, uint64_t mode, BlValue fixed) {
  BlValue clo = bl_alloc(BL_CLOSURE, 3, (uint64_t)(uintptr_t)(void *)wasm_compose_apply);
  clo->fields[0] = old_cont;
  clo->fields[2] = fixed;
  BlValue modebox = bl_alloc(BL_INT, 0, mode);
  clo->fields[1] = modebox;
  return clo;
}

BlValue bl_app(BlValue f, BlValue a) {
  if (is_opnode(f)) {
    BlValue node = bl_alloc(BL_OPNODE, 2, f->header.aux);
    node->fields[0] = f->fields[0];
    node->fields[1] = make_compose(f->fields[1], 1, a);
    return node;
  }
  if (is_opnode(a)) {
    BlValue node = bl_alloc(BL_OPNODE, 2, a->header.aux);
    node->fields[0] = a->fields[0];
    node->fields[1] = make_compose(a->fields[1], 0, f);
    return node;
  }
  return wasm_apply1(f, a);
}

typedef BlValue (*BlFn2)(BlValue env, BlValue arg);
BlValue bl_app_global(void *fnptr, BlValue a) {
  if (is_opnode(a)) {
    BlValue clo = bl_alloc(BL_CLOSURE, 0, (uint64_t)(uintptr_t)fnptr);
    return bl_app(clo, a);
  }
  return ((BlFn2)fnptr)(NULL, a);
}

static BlValue wasm_rebuild_field_apply(BlValue clo, BlValue v);

static BlValue make_rebuild(BlValue old_cont, BlValue obj, uint64_t field_idx) {
  BlValue clo = bl_alloc(BL_CLOSURE, 3, (uint64_t)(uintptr_t)(void *)wasm_rebuild_field_apply);
  clo->fields[0] = old_cont;
  clo->fields[1] = obj;
  BlValue idxbox = bl_alloc(BL_INT, 0, field_idx);
  clo->fields[2] = idxbox;
  return clo;
}

BlValue bl_con_bubble(BlValue obj) {
  if (obj == NULL || bl_is_imm(obj)) return obj;
  uint32_t tag = bl_obj_tag_w(obj);
  if (tag != BL_CON && tag != BL_TUPLE) return obj;
  uint32_t n = obj->header.nfields;
  for (uint32_t i = 0; i < n; i++) {
    BlValue fld = obj->fields[i];
    if (is_opnode(fld)) {
      BlValue node = bl_alloc(BL_OPNODE, 2, fld->header.aux);
      node->fields[0] = fld->fields[0];
      node->fields[1] = make_rebuild(fld->fields[1], obj, i);
      return node;
    }
  }
  return obj;
}

static BlValue wasm_rebuild_field_apply(BlValue clo, BlValue v) {
  BlValue old_cont = clo->fields[0];
  uint64_t idx = clo->fields[2]->header.aux;
  BlValue resumed = (old_cont == NULL) ? v : wasm_apply1(old_cont, v);
  BlValue obj = clo->fields[1];
  BlValue rebuilt = bl_alloc((BlTag)bl_obj_tag_w(obj), obj->header.nfields, obj->header.aux);
  for (uint32_t j = 0; j < obj->header.nfields; j++) rebuilt->fields[j] = obj->fields[j];
  rebuilt->fields[idx] = resumed;
  return bl_con_bubble(rebuilt);
}

/* Closure-based deep handler (mirror `bl_handle_clo`/`bl_handle_fold` in effects.c). The handler
 * record is `wasm_malloc`'d rather than `malloc`'d; there is no GC-root pinning to do since roots
 * are no-ops on this target. */
typedef struct BlHandler {
  BlValue ret_clo;
  uint64_t n_ops; /* uint64_t, not size_t: see `bl_gc_pop_roots`'s doc comment above for why */
  const char **op_names;
  BlValue *op_clos;
} BlHandler;

static BlValue wasm_handle_fold(BlHandler *h, BlValue comp);

static BlValue wasm_cont_apply(BlValue clo, BlValue v) {
  BlValue kont = clo->fields[0];
  BlHandler *h = (BlHandler *)(uintptr_t)clo->fields[1]->header.aux;
  BlValue resumed = (kont == NULL) ? v : wasm_apply1(kont, v);
  return wasm_handle_fold(h, resumed);
}

static BlValue make_cont(BlHandler *h, BlValue kont) {
  BlValue clo = bl_alloc(BL_CLOSURE, 2, (uint64_t)(uintptr_t)(void *)wasm_cont_apply);
  clo->fields[0] = kont;
  BlValue hbox = bl_alloc(BL_INT, 0, (uint64_t)(uintptr_t)h);
  clo->fields[1] = hbox;
  return clo;
}

static BlValue wasm_handle_fold(BlHandler *h, BlValue comp) {
  for (;;) {
    if (!is_opnode(comp)) return wasm_apply1(h->ret_clo, comp);
    const char *opn = wasm_op_name_of(comp->header.aux);
    uint64_t which = (uint64_t)-1;
    for (uint64_t i = 0; i < h->n_ops; i++) {
      if (bl_streq(h->op_names[i], opn)) { which = i; break; }
    }
    if (which == (uint64_t)-1) return comp; /* unhandled: bubble past unchanged */
    BlValue arg = comp->fields[0];
    BlValue kont = comp->fields[1];
    BlValue k = make_cont(h, kont);
    BlValue partial = wasm_apply1(h->op_clos[which], arg);
    comp = wasm_apply1(partial, k);
  }
}

/* ---- packed `String` coherence shim (mirror numeric.c's `bl_string_to_con`) ----
 * `emit_case` (llvm.rs) calls `bl_string_to_con` unconditionally on *every* generic `match`
 * scrutinee (Nat included, not just String matches) as a coherence shim materializing one packed-
 * String `empty`/`push` layer — see that call site's comment for why it is always safe to call.
 * This target never constructs a packed `BL_STRING` in the first place: `bl_string_from_codepoints`
 * (needed for an actual string *literal*) is deliberately NOT provided here, joining
 * `Console`/`FileIO`/`Clock` in the file header's "Honest scope" list — a program with a string
 * literal will link (thanks to `wasm-ld --allow-undefined`) but trap the moment it is built, not
 * silently miscompile. Given that, `bl_string_to_con` is unconditionally the identity: every value
 * this shim will ever actually see is already a real Con (or Nat/Int/etc.), never a BL_STRING. */
BlValue bl_string_to_con(BlValue v) { return v; }

BlValue bl_handle_clo(BlValue body_clo, BlValue ret_clo,
                      uint64_t n_ops, const char **op_names, BlValue *op_clos) {
  BlHandler *h = (BlHandler *)wasm_malloc(sizeof(BlHandler));
  h->ret_clo = ret_clo;
  h->n_ops = n_ops;
  h->op_names = op_names;
  h->op_clos = (BlValue *)wasm_malloc(n_ops ? (size_t)n_ops * sizeof(BlValue) : 1);
  for (uint64_t i = 0; i < n_ops; i++) h->op_clos[i] = op_clos[i];

  BlValue comp = wasm_apply1(body_clo, NULL);
  BlValue r = wasm_handle_fold(h, comp);
  wasm_free(h->op_clos);
  wasm_free(h);
  return r;
}

/* The compiled program's entry point, emitted by codegen. */
extern BlValue bl_program_entry(void);

/* Reduce a result value to an i32 the host can read: a Nat (Zero/Succ chain) becomes its numeral,
 * a boxed INT its (truncated) payload, otherwise the constructor index. Mirrors prelude_rt's
 * `bl_print` minus the stdio. */
static int32_t bl_to_i32(BlValue v) {
  if (v == NULL) return -1;
  uint32_t tag = bl_obj_tag_w(v);
  if (tag == BL_INT) return (int32_t)(int64_t)bl_obj_aux_w(v);
  if (tag == BL_NAT) return (int32_t)bl_obj_aux_w(v);
  if (tag == BL_CON) {
    int32_t n = 0;
    BlValue cur = v;
    while (cur && bl_obj_tag_w(cur) == BL_CON && bl_obj_aux_w(cur) == 1 && bl_obj_nfields_w(cur) == 1) {
      n++;
      cur = cur->fields[0];
    }
    if (cur && bl_obj_tag_w(cur) == BL_CON && bl_obj_aux_w(cur) == 0) return n;
    if (cur && bl_obj_tag_w(cur) == BL_NAT) return n + (int32_t)bl_obj_aux_w(cur);
    return (int32_t)(int64_t)bl_obj_aux_w(v);
  }
  return -2;
}

/* The exported entry: run the program and return its value as an i32. */
__attribute__((export_name("bl_main")))
int32_t bl_main(void) {
  bl_gc_init(0);
  bl_stack_init();
  return bl_to_i32(bl_program_entry());
}
