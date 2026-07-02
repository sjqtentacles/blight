/* boxed_array.c — the `Array A` effect's native handle table (roadmap Wave 10 / P1, A3b).
 *
 * `effects.c`'s `Arrays` (A3a) is `Int`-only: a `malloc`'d table of raw `int64_t`s can never hold a
 * stale/moved GC pointer because it never holds a pointer at all. A generic array of arbitrary
 * *boxed* `BlValue` elements loses that property, so it needs a genuinely GC-aware design — this
 * file, plus one new root-scanning hook in `gc.c` (`bl_boxed_array_gc_roots`, called from both
 * `minor_collect` and `major_collect_into`) and one call to the existing `bl_write_barrier` on
 * writes. See `docs/design-a3b-boxed-arrays.md` (Design 1, the recommendation this implements) for
 * the full rationale and the two blockers it closes.
 *
 * Representation: each array's backing storage is an ordinary GC-heap `BL_TUPLE` (allocated via the
 * normal `bl_alloc`), so the precise tracer already walks and relocates every element slot with ZERO
 * changes to the tracer itself — `header.nfields` is the array length, `fields[i]` is element `i`.
 * The only genuinely new piece is that a Blight program never holds that `BL_TUPLE` pointer directly
 * (a GC copy would invalidate it under the mutator's feet the instant a collection moved it) —
 * instead it holds an opaque `Int` HANDLE (exactly the `g_arrays`/`g_bytes` convention) indexing into
 * `g_boxed[]` below, a growable side table whose *entries* point at the backing objects. Because
 * `g_boxed[]` itself lives outside the GC heap (plain `malloc`), its entries are edges the tracer
 * would never otherwise see, so `bl_boxed_array_gc_roots` treats every live entry as an extra root —
 * scanned every collection, exactly like a shadow-stack slot (`gc.c`'s `g_roots`) — updating it in
 * place if the backing object moves. `bl_boxed_array_set` calls `bl_write_barrier` on every write so
 * a young value stored into an already-promoted (old-generation) backing object is remembered for
 * the next minor collection, exactly as codegen-emitted field stores do.
 *
 * The element type `A` is erased at runtime (Wave 7/E2 parameterized effects: `lower.rs` drops
 * `type_args`, like a `Data`'s params), so this table is untyped `BlValue` storage — the surface
 * `std/array.bl` `Array A` effect is what gives it a type at the tower level; here it is simply "an
 * array of whatever pointers the caller stored". */
#include "blight_rt.h"
#include <stdlib.h>

typedef struct {
  BlValue obj; /* the backing BL_TUPLE, or NULL for a freed/invalid handle */
} BlBoxedArray;

static BL_THREAD_LOCAL BlBoxedArray *g_boxed = NULL;
static BL_THREAD_LOCAL size_t g_boxed_len = 0; /* number of live handles */
static BL_THREAD_LOCAL size_t g_boxed_cap = 0; /* table capacity */

/* Allocate a boxed array of `len` elements, each initialized to `init` (there is no runtime notion
 * of "the zero value of A" once the element type is erased, so unlike the Int-only `Arrays` effect's
 * zero-fill, the caller supplies an explicit initial value — `std/array.bl`'s `array-new` takes one).
 * Returns the new handle, or -1 on allocation failure (an always-invalid handle, so subsequent ops
 * degrade to no-ops rather than a crash, matching every other native-effect table in this runtime).
 * `init` may be an arbitrary (possibly young, possibly heap-boxed) `BlValue`, so it is rooted across
 * the `bl_alloc` call below, which can itself trigger a collection. */
int64_t bl_boxed_array_new(size_t len, BlValue init) {
  if (g_boxed_len == g_boxed_cap) {
    size_t ncap = g_boxed_cap == 0 ? 8 : g_boxed_cap * 2;
    BlBoxedArray *grown = (BlBoxedArray *)realloc(g_boxed, ncap * sizeof(BlBoxedArray));
    if (!grown) return -1;
    g_boxed = grown;
    g_boxed_cap = ncap;
  }
  bl_gc_push_root(&init);
  BlValue obj = bl_alloc(BL_TUPLE, (uint32_t)len, 0);
  bl_gc_pop_roots(1);
  /* `obj` is a freshly-allocated nursery object: these are initializing stores (no write barrier
   * needed, exactly like codegen-emitted constructor field stores), and no allocation happens in
   * this loop, so `obj`/`init` cannot be invalidated mid-loop by a collection. */
  for (size_t i = 0; i < len; i++) obj->fields[i] = init;
  int64_t h = (int64_t)g_boxed_len;
  g_boxed[g_boxed_len].obj = obj;
  g_boxed_len++;
  return h;
}

/* True iff `h` names a live boxed array. */
static int bl_boxed_array_valid(int64_t h) {
  return h >= 0 && (size_t)h < g_boxed_len && g_boxed[h].obj != NULL;
}

/* Length of boxed array `h` (0 for an invalid handle). */
size_t bl_boxed_array_length(int64_t h) {
  return bl_boxed_array_valid(h) ? (size_t)g_boxed[h].obj->header.nfields : 0;
}

/* Read element `i` of boxed array `h`. Every in-bounds slot was written by `bl_boxed_array_new`'s
 * fill loop or a later `bl_boxed_array_set`, so it is always a genuine element value, never NULL; an
 * out-of-range handle/index has no element of type `A` to fabricate, so it degrades to a fresh
 * nullary `BL_CON` (the same total-but-inert value `bl_unit()` in effects.c builds) rather than
 * returning NULL, which would crash the first generic reader (`case`/`bl_obj_tag`) it reached. */
BlValue bl_boxed_array_get(int64_t h, uint64_t i) {
  if (bl_boxed_array_valid(h) && i < (uint64_t)g_boxed[h].obj->header.nfields) {
    return g_boxed[h].obj->fields[i];
  }
  return bl_alloc(BL_CON, 0, 0);
}

/* Write `v` to element `i` of boxed array `h`; out-of-range handle/index is a no-op. `v` may be a
 * young value stored into an old-generation backing object, so the write barrier is unconditional
 * (cheap and idempotent — see `bl_write_barrier`'s own fast-reject checks). */
void bl_boxed_array_set(int64_t h, uint64_t i, BlValue v) {
  if (!bl_boxed_array_valid(h) || i >= (uint64_t)g_boxed[h].obj->header.nfields) return;
  BlValue arr = g_boxed[h].obj;
  arr->fields[i] = v;
  bl_write_barrier(arr, v);
}

/* GC-internal root hook (gc.c only): every live handle's backing-object pointer is an extra root,
 * exactly like a shadow-stack slot in `g_roots`. Called once per collection from both
 * `minor_collect` and `major_collect_into`, passing that collection's own `evac_minor`/`evac_major`
 * (same `BlValue (*)(BlValue, char **)` signature) so a moved backing object's table entry is
 * rewritten in place — never dangling, whether or not the mutator happens to hold its own root to the
 * same object right now. There is no minor/major race to guard against: this runtime is single-
 * mutator per (thread-local) heap, so at most one collection is ever in flight scanning this table. */
void bl_boxed_array_gc_roots(BlValue (*evac)(BlValue, char **), char **alloc) {
  for (size_t i = 0; i < g_boxed_len; i++) {
    if (g_boxed[i].obj) g_boxed[i].obj = evac(g_boxed[i].obj, alloc);
  }
}
