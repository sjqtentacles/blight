/* wasm_rt.c — a minimal *freestanding* WebAssembly runtime ABI for Blight (stretch, spec §7).
 *
 * The native runtime (gc.c / arena.c / stack.c / effects.c / prelude_rt.c) leans on libc (mmap,
 * stdio) and a precise copying GC, none of which exist in a bare `wasm32-unknown-unknown` module.
 * This shim provides the *smallest* ABI a compiled Blight `program.o` actually links against so a
 * `wasm-ld` step can produce a runnable `.wasm` module rather than a bare object:
 *
 *   - `bl_alloc` / `bl_con` / `bl_int` / `bl_int_val` — a bump allocator over wasm linear memory.
 *   - `bl_gc_init` / `bl_stack_init` / `bl_gc_poll` / root push+pop / `bl_write_barrier` — no-ops
 *     (a wasm module is short-lived and the bump heap is never collected here).
 *
 * It deliberately does NOT provide the delay/effect trampolines or region arenas: programs that use
 * them are out of scope for this minimal target and will fail to link (an honest, explicit error),
 * exactly like the kernel's re-checker honestly declines an out-of-fragment construct.
 *
 * The module exports `bl_main`, which runs the compiled entry and returns the result as an i32
 * (a Nat's Succ-depth, or a boxed integer's payload), so a host can call it and read a value back.
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

/* ---- bump allocator over wasm linear memory ----
 * `__heap_base` is provided by wasm-ld: the first byte past static data. We bump from there; the
 * module never frees (a short-lived computation), so no GC is needed for this minimal ABI. */
extern unsigned char __heap_base;
static uintptr_t bl_bump = 0;

static void bl_bump_init(void) {
  if (bl_bump == 0) {
    bl_bump = (uintptr_t)&__heap_base;
    /* 8-byte align the frontier. */
    bl_bump = (bl_bump + 7u) & ~(uintptr_t)7u;
  }
}

BlValue bl_alloc(BlTag tag, uint32_t nfields, uint64_t aux) {
  bl_bump_init();
  size_t bytes = sizeof(BlHeader) + (size_t)nfields * sizeof(BlValue);
  bytes = (bytes + 7u) & ~(size_t)7u;
  BlValue o = (BlValue)bl_bump;
  bl_bump += bytes;
  o->header.tag = (uint32_t)tag;
  o->header.nfields = nfields;
  o->header.aux = aux;
  return o;
}

BlValue bl_int(int64_t n) { return bl_alloc(BL_INT, 0, (uint64_t)n); }
int64_t bl_int_val(BlValue v) { return (int64_t)v->header.aux; }
BlValue bl_con(uint64_t ctor_index, uint32_t nfields) {
  return bl_alloc(BL_CON, nfields, ctor_index);
}

/* ---- GC / stack / safepoint: no-ops on this freestanding target ---- */
void bl_gc_init(size_t heap_bytes) { (void)heap_bytes; bl_bump_init(); }
void bl_gc_poll(void) {}
void bl_gc_push_root(BlValue *slot) { (void)slot; }
void bl_gc_pop_roots(size_t n) { (void)n; }
void bl_write_barrier(BlValue obj, BlValue val) { (void)obj; (void)val; }
void bl_stack_init(void) {}

/* The compiled program's entry point, emitted by codegen. */
extern BlValue bl_program_entry(void);

/* Reduce a result value to an i32 the host can read: a Nat (Zero/Succ chain) becomes its numeral,
 * a boxed INT its (truncated) payload, otherwise the constructor index. Mirrors prelude_rt's
 * `bl_print` minus the stdio. */
static int32_t bl_to_i32(BlValue v) {
  if (v == NULL) return -1;
  if (v->header.tag == BL_INT) return (int32_t)(int64_t)v->header.aux;
  if (v->header.tag == BL_CON) {
    int32_t n = 0;
    BlValue cur = v;
    while (cur && cur->header.tag == BL_CON && cur->header.aux == 1 && cur->header.nfields == 1) {
      n++;
      cur = cur->fields[0];
    }
    if (cur && cur->header.tag == BL_CON && cur->header.aux == 0) return n;
    return (int32_t)(int64_t)v->header.aux;
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
