/* blight_rt.h — shared runtime value representation and entry points (spec §7.3/§7.4).
 *
 * The Blight native runtime is a small C library linked into every compiled binary. It provides:
 *   - a uniform boxed value representation with a tag+size object header (gc.c),
 *   - a precise copying / semi-space garbage collector (gc.c),
 *   - a segmented / growable stack so deep non-tail recursion never hits a fixed limit (stack.c),
 *   - the Delay/Later trampoline that drives the Capretta delay monad in bounded stack (delay.c),
 *   - the algebraic-effect trampoline with delimited-continuation capture/resume (effects.c).
 *
 * All multi-word objects are heap-allocated through `bl_alloc` and carry a `BlHeader`. Small
 * scalars (Nat as a machine integer in this M4 subset) are still boxed for uniformity so the GC
 * can trace every field; a later milestone can unbox.
 */
#ifndef BLIGHT_RT_H
#define BLIGHT_RT_H

#include <stddef.h>
#include <stdint.h>

/* Object tags. The codegen emits constructor values as BL_CON with a constructor index. */
typedef enum {
  BL_CON = 0,      /* a data constructor: header.aux = constructor index, fields follow */
  BL_TUPLE = 1,    /* an anonymous product */
  BL_CLOSURE = 2,  /* a closure: header.aux = function pointer; fields[] = captured env (traced) */
  BL_NOW = 3,      /* delay monad: an immediately-available value in field[0] */
  BL_LATER = 4,    /* delay monad: a thunk (closure) in field[0] producing the next Delay */
  BL_INT = 5,      /* a machine integer payload (in `aux`), no fields */
  BL_OPNODE = 6,   /* a bubbling effect operation: field[0]=arg, field[1]=continuation closure;
                      header.aux indexes into a runtime intern table of (effect,op) name pairs */
  BL_FWD = 7,      /* GC forwarding pointer (used only during collection) */
  BL_NAT = 8,      /* a machine-word natural number (count in `aux`, no fields), OBSERVATIONALLY
                      identical to the inductive `Zero`/`Succ` chain (numeric.c, M20). It is a
                      zero-field object, so the precise GC traces it exactly like BL_INT (nothing
                      to trace) and copies it by size — no collector change is needed. The two
                      generic readers that destructure data (codegen `emit_case` and `load_field`)
                      materialize a real `Zero`/`Succ` node on demand via `bl_nat_to_con`, so any
                      code that pattern-matches a fast-Nat sees the inductive value it expects. The
                      recognizer (recognize.rs) keeps hot arithmetic in raw words and only pays this
                      materialization cost at a genuine destructuring boundary. */
  BL_STRING = 9    /* a packed `String` (std/string.bl), A2: the codepoint sequence stored
                      contiguously in a program-lifetime side buffer pointed to by `header.aux`
                      (a `BlStrData *`), with ZERO traced fields. OBSERVATIONALLY identical to the
                      inductive `empty`/`push` cons-list: like BL_NAT it is a zero-field object the
                      precise GC copies by size with nothing to trace (the side buffer is not in the
                      GC graph — it is interned for the program's lifetime, exactly like the effect
                      op-name table), and the generic destructuring readers materialize one
                      `empty`/`push` layer on demand via `bl_string_to_con`. So packing a `String`
                      literal into one BL_STRING needs NO collector change and composes with any
                      generic `case`/projection that walks the spine. (numeric.c) */
} BlTag;

/* A header flag bit OR'd into `tag` marking an object that lives in a region arena (arena.c), not
 * the GC heap. The GC must NOT copy such objects (they are not in from-space and are reclaimed in
 * O(1) at arena-leave), but it MUST still trace their fields so any GC-heap object reachable only
 * through an arena object survives a collection (spec §3.5 / §7.3). The real tag is recovered with
 * `BL_TAG(o)` and the bit tested with `BL_IS_ARENA(o)`. */
#define BL_ARENA_BIT 0x80000000u
/* Two further header bits used transiently by the generational GC (gc.c), kept in the high `tag`
 * space so they never collide with the `aux` payload (constructor index / machine integer):
 *   - BL_REMEMBERED_BIT marks an old-generation object already in the remembered set (dedup).
 *   - BL_GC_SEEN_BIT marks an arena object already enqueued on the gray worklist during a collection.
 * Both are cleared by the collector before it returns, so the steady-state tag is just BlTag (+arena
 * bit). The real tag is recovered with BL_TAG(o). */
#define BL_REMEMBERED_BIT 0x40000000u
#define BL_GC_SEEN_BIT 0x20000000u
#define BL_TAG(o) ((BlTag)((o)->header.tag & ~(BL_ARENA_BIT | BL_REMEMBERED_BIT | BL_GC_SEEN_BIT)))
#define BL_IS_ARENA(o) (((o)->header.tag & BL_ARENA_BIT) != 0u)

/* Every heap object starts with this header. */
typedef struct BlHeader {
  uint32_t tag;     /* a BlTag */
  uint32_t nfields; /* number of trailing BlValue fields traced by the GC */
  uint64_t aux;     /* tag-specific: constructor index (BL_CON) or integer payload (BL_INT) */
} BlHeader;

/* A Blight value is a pointer to a heap object, OR a *tagged immediate* (M21 unboxing). */
typedef struct BlObj {
  BlHeader header;
  struct BlObj *fields[];
} BlObj;

typedef BlObj *BlValue;

/* ---- tagged-immediate unboxing (numeric.c/gc.c, M21, zero TCB) ----
 *
 * Heap objects are allocated by `malloc`/bump pointers that are at least 8-byte aligned, so the low
 * 3 bits of a genuine `BlValue` pointer are always 0 and NULL is all-zero. We steal the low bit as
 * an *immediate flag*: a value with bit0 set is NOT a pointer but a small scalar carried inline in
 * the word itself — no heap box, so no allocation, no GC tracing, no copy. Bits [3:1] select the
 * immediate KIND; the remaining high 60 bits carry the payload.
 *
 *   bit0 == 0 : a boxed heap pointer (or NULL) — the historical representation, unchanged.
 *   bit0 == 1 : an immediate; bits[3:1] = kind, bits[63:4] = payload.
 *
 * Kinds mirror the boxed tags they replace, so every generic observer can recover the *same*
 * tag/aux/nfields it would have read from a heap object (the genericity firewall: an immediate is
 * observationally identical to the box it elides):
 *   - BL_IMM_NAT : a machine-word `Nat`  (payload = the count; observationally tag BL_NAT, 0 fields)
 *   - BL_IMM_INT : a machine integer      (payload = the value; observationally tag BL_INT, 0 fields)
 *   - BL_IMM_CON : a nullary constructor  (payload = the ctor index; tag BL_CON, 0 fields)
 *
 * The GC treats any immediate as a non-pointer leaf (evacuate = identity, never deref, never trace).
 * The two codegen destructuring readers (`emit_case`/`load_field`) and the C generic readers route
 * through `bl_obj_tag`/`bl_obj_aux`/`bl_obj_nfields`/`bl_obj_field`, which decode an immediate to its
 * synthesized header, so a fast immediate flowing into generic code behaves exactly like the box. */
#define BL_IMM_FLAG 0x1u
#define BL_IMM_KIND_SHIFT 1u
#define BL_IMM_KIND_MASK 0x7u /* bits [3:1] */
#define BL_IMM_PAYLOAD_SHIFT 4u
typedef enum {
  BL_IMM_NAT = 0u, /* observationally BL_NAT */
  BL_IMM_INT = 1u, /* observationally BL_INT */
  BL_IMM_CON = 2u  /* observationally BL_CON, nullary */
} BlImmKind;

/* True if `v` is a tagged immediate (low bit set) rather than a heap pointer. NULL is a (boxed)
 * pointer, not an immediate. */
static inline int bl_is_imm(BlValue v) { return ((uintptr_t)v & BL_IMM_FLAG) != 0u; }
static inline BlImmKind bl_imm_kind(BlValue v) {
  return (BlImmKind)(((uintptr_t)v >> BL_IMM_KIND_SHIFT) & BL_IMM_KIND_MASK);
}
static inline uint64_t bl_imm_payload(BlValue v) {
  return (uint64_t)((uintptr_t)v >> BL_IMM_PAYLOAD_SHIFT);
}
/* Build an immediate of `kind` carrying `payload`. The payload must fit in 60 bits (the runtime
 * checks this at the allocation boundary and falls back to a heap box if it does not). */
static inline BlValue bl_make_imm(BlImmKind kind, uint64_t payload) {
  return (BlValue)(uintptr_t)(((uintptr_t)payload << BL_IMM_PAYLOAD_SHIFT) |
                              ((uintptr_t)kind << BL_IMM_KIND_SHIFT) | BL_IMM_FLAG);
}
/* A payload fits inline iff it survives the 4-bit left shift without losing high bits. */
static inline int bl_imm_fits(uint64_t payload) {
  return (payload >> (64u - BL_IMM_PAYLOAD_SHIFT)) == 0u;
}

/* Generic header readers that transparently decode an immediate to the (tag,aux,nfields) it stands
 * for. Every observer that inspects an *arbitrary* (possibly-immediate) value uses these instead of
 * `v->header.*` so immediates and boxes are indistinguishable. (Code that built a value itself and
 * knows it is boxed — e.g. a freshly `bl_alloc`'d closure — may still touch `->fields` directly.) */
static inline BlTag bl_obj_tag(BlValue v) {
  if (bl_is_imm(v)) {
    switch (bl_imm_kind(v)) {
      case BL_IMM_NAT: return BL_NAT;
      case BL_IMM_INT: return BL_INT;
      case BL_IMM_CON: return BL_CON;
    }
  }
  return BL_TAG(v);
}
static inline uint64_t bl_obj_aux(BlValue v) {
  if (bl_is_imm(v)) return bl_imm_payload(v);
  return v->header.aux;
}
static inline uint32_t bl_obj_nfields(BlValue v) {
  if (bl_is_imm(v)) return 0u; /* every immediate kind is a zero-field object */
  return v->header.nfields;
}
static inline BlValue bl_obj_field(BlValue v, uint32_t i) {
  /* Immediates have no fields; this is only ever called after checking nfields > 0. */
  return v->fields[i];
}

/* Thread-local storage class for the runtime's per-worker mutable state (gc.c/arena.c/stack.c, and
 * the effect-op intern table). Share-nothing multicore (M15+) gives each OS-thread worker its own
 * heap, roots, arenas, and segmented stack by making those globals `_Thread_local`; the public API
 * (`bl_alloc`, `bl_gc_*`, `bl_arena_*`, `bl_stack_*`) is byte-for-byte unchanged, so codegen and the
 * single-runtime M0-M14 behavior are untouched (a program that never spawns a second runtime sees
 * exactly one thread-local instance, identical to the old globals). C11 `_Thread_local` when
 * available, else the GNU `__thread` extension (clang/gcc default `gnu*` std provides it). */
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
#define BL_THREAD_LOCAL _Thread_local
#elif defined(__GNUC__) || defined(__clang__)
#define BL_THREAD_LOCAL __thread
#else
#define BL_THREAD_LOCAL
#endif

/* Branch- and inline-shaping hints (M28). The hot allocator/forcer fast paths are tiny and run on
 * essentially every allocation/step; the slow paths (collect, grow, oversized) run rarely. Marking
 * the rare paths `BL_COLD`/`BL_NOINLINE` and the common branches `BL_LIKELY` tells the LTO inliner to
 * inline only the bump-and-init fast path into compiled Blight code and keep the cold machinery out
 * of line — small, branch-predicted call sites with good I-cache behavior. No-ops on toolchains that
 * lack the attributes/builtins (the semantics are identical; only code layout changes). */
#if defined(__GNUC__) || defined(__clang__)
#define BL_LIKELY(x) __builtin_expect(!!(x), 1)
#define BL_UNLIKELY(x) __builtin_expect(!!(x), 0)
#define BL_HOT __attribute__((hot))
#define BL_COLD __attribute__((cold, noinline))
#define BL_ALWAYS_INLINE __attribute__((always_inline))
#else
#define BL_LIKELY(x) (x)
#define BL_UNLIKELY(x) (x)
#define BL_HOT
#define BL_COLD
#define BL_ALWAYS_INLINE
#endif

/* Mark an allocation as intentionally immortal so LeakSanitizer does not report it. A few runtime
 * buffers — notably the program-lifetime codepoint intern pool behind BL_STRING (numeric.c), which
 * is deliberately never freed and shared by every tail view for the whole run — are immortal by
 * design; LSan cannot know that and flags them as leaks. `__lsan_ignore_object` is the sanitizer's
 * own API for exactly this case, so genuine leaks are still caught. Compiles to nothing unless the
 * translation unit is built under AddressSanitizer (whose LSan component ships the interface header);
 * an ordinary build takes no dependency on any sanitizer runtime. */
#if defined(__SANITIZE_ADDRESS__)
#define BL_ASAN 1
#elif defined(__has_feature)
#if __has_feature(address_sanitizer)
#define BL_ASAN 1
#endif
#endif
#ifdef BL_ASAN
#include <sanitizer/lsan_interface.h>
#define BL_LSAN_IGNORE(p) __lsan_ignore_object(p)
#else
#define BL_LSAN_IGNORE(p) ((void)(p))
#endif

/* ---- allocation + GC (gc.c) ---- */
void bl_gc_init(size_t heap_bytes);
BlValue bl_alloc(BlTag tag, uint32_t nfields, uint64_t aux);
/* A GC safepoint poll, emitted by codegen at loop back-edges and function entry (never right
 * before a tail call). Runs a collection if the heap is under pressure. */
void bl_gc_poll(void);
/* Push/pop a stack of GC roots (the codegen-emitted shadow stack of live pointers). */
void bl_gc_push_root(BlValue *slot);
void bl_gc_pop_roots(size_t n);
/* Statistics for tests and `BL_GC_STATS`. */
size_t bl_gc_collections(void);
size_t bl_gc_minor(void);          /* minor (nursery) collections */
size_t bl_gc_major(void);          /* major (full) collections, including growing ones */
size_t bl_gc_grows(void);          /* heap-growing major collections */
size_t bl_gc_promoted_bytes(void); /* total bytes promoted nursery->old over all minors */
size_t bl_gc_bytes_allocated(void); /* total GC-heap bytes requested via bl_alloc (excludes arena) */
/* Old-generation sizing observability (P4.1 mark-compact). `bl_gc_oldgen_compacting()` is 1 when the
 * old generation runs in single-region compacting mode (`BL_GC_OLDGEN=compact`), 0 for the legacy
 * two-space semi-space. `bl_gc_old_capacity()` is the active region's byte capacity; in the legacy
 * mode the heap also reserves a second region of equal size, so `bl_gc_old_reserved_bytes()` is twice
 * the capacity there and exactly the capacity (one region) under compaction — i.e. compaction's peak
 * old-generation footprint is ~1x the live set where semi-space is ~2x. */
int bl_gc_oldgen_compacting(void);
size_t bl_gc_old_capacity(void);       /* bytes of the active old region (one semi-space) */
size_t bl_gc_old_reserved_bytes(void); /* total bytes reserved for the old generation (incl. to-space) */
size_t bl_gc_old_live_bytes(void);     /* bytes currently occupied in the active old region */
/* P4.2 adaptive heap sizing. `bl_gc_old_shrinks()` counts collections that shrank the old region after
 * sustained low occupancy (compacting mode only; the legacy semi-space only ever grows). */
size_t bl_gc_old_shrinks(void);
size_t bl_gc_peak_old_reserved_bytes(void); /* high-water mark of old-generation bytes reserved */
/* Test/diagnostic hook: run a full (major / compacting) collection now, at a safepoint where the
 * caller's roots are accurate. UNTRUSTED — running the collector is observationally invisible; this
 * only lets tests and stats drive collection deterministically. */
void bl_gc_force_collect(void);
/* The generational write barrier (spec §7.3): record a post-initialization store of `val` into a
 * field of `obj` so the next minor collection treats `obj` as a root if it now points into the
 * nursery (an old→young edge). Idempotent; cheap; a no-op for young or arena `obj`. Codegen emits
 * this on field stores into already-allocated objects (never on a fresh object's initializing
 * stores). */
void bl_write_barrier(BlValue obj, BlValue val);

/* ---- region arenas (arena.c, spec §3.5) ---- */
/* A region arena is a stack of bump-pointer buffers. The compiled code brackets a `(region r …)`
 * scope with enter/leave; allocations the escape analysis proved non-escaping are bump-allocated in
 * the top arena and reclaimed in O(1) at leave — bypassing the GC entirely. Marks are kept on an
 * internal stack so codegen needs no mark value: region scopes are lexically nested, so enter/leave
 * pair up like a stack (mirrors the §7.4 safepoint discipline — leave at the lexical boundary). */
/* Open a region scope: push a fresh mark naming the current arena frontier. */
void bl_arena_enter(void);
/* Bump-allocate an object in the current (top) arena. Sets BL_ARENA_BIT so the GC won't move it.
 * Never triggers a collection, so it is always safe in tail position (spec §7.4). */
BlValue bl_arena_alloc(BlTag tag, uint32_t nfields, uint64_t aux);
/* Close the most-recently-entered region scope: reclaim its objects in O(1). */
void bl_arena_leave(void);
/* Stats for tests: total bytes currently reserved across live arenas, and arena alloc count. */
size_t bl_arena_live_bytes(void);
size_t bl_arena_alloc_count(void);


/* ---- boxed (generic) arrays (boxed_array.c, roadmap Wave 10 / P1, A3b) ---- */
/* A mutable array of arbitrary boxed `BlValue` elements, backing `std/array.bl`'s parameterized
 * `Array A` effect. See boxed_array.c's header comment for the full design (a GC-heap `BL_TUPLE`
 * backing object per array, referenced by an off-heap handle table whose entries are themselves
 * scanned as GC roots every collection). Handles are plain non-negative `Int`s (-1 = invalid),
 * exactly like the Int-only `Arrays` effect's (A3a) handles. */
int64_t bl_boxed_array_new(size_t len, BlValue init);
size_t bl_boxed_array_length(int64_t h);
BlValue bl_boxed_array_get(int64_t h, uint64_t i);
void bl_boxed_array_set(int64_t h, uint64_t i, BlValue v);
/* GC-internal hook, called only from gc.c's minor/major root-scanning loops: evacuate every live
 * handle's backing-object pointer via `evac` (that collection's own `evac_minor`/`evac_major`),
 * rewriting the table entry in place exactly like a shadow-stack root slot. */
void bl_boxed_array_gc_roots(BlValue (*evac)(BlValue, char **), char **alloc);

/* ---- segmented stack (stack.c) ---- */
void bl_stack_init(void);
/* Ensure at least `bytes` of contiguous stack headroom, growing (segmenting) if needed. */
void *bl_stack_grow(size_t bytes);

/* ---- delay trampoline (delay.c) ---- */
/* Force a Delay value: repeatedly step BL_LATER thunks until a BL_NOW, returning its payload.
 * Runs in bounded C stack regardless of recursion depth (the headline million-deep path). */
BlValue bl_force(BlValue delay);

/* ---- effect trampoline (effects.c) ---- */
/* Intern an (effect,op) name pair to its stable runtime index. Append-only. The build driver calls
 * this for every declared op at single-threaded startup (M15) so the shared intern table can be
 * frozen before any worker thread spawns. */
uint64_t bl_effect_intern(const char *effect, const char *op);
/* Freeze the intern table: after this, interning a not-yet-seen op aborts (it would race other
 * workers). Call once after startup pre-interning, before spawning workers. Idempotent. */
void bl_effect_intern_freeze(void);
/* Initialize the calling thread's thread-local runtime (heap + segmented stack). Each share-nothing
 * worker (M15+) calls this once on entry; the process main thread keeps using the explicit
 * `bl_gc_init`/`bl_stack_init` it already does. `heap_bytes` is the worker's initial heap (it still
 * grows on demand per gc.c). Safe to call from any OS thread; touches only thread-local state. */
void bl_runtime_init(size_t heap_bytes);
/* Perform an operation: bubble an OpNode to the nearest handler installed by bl_handle. */
BlValue bl_perform(const char *effect, const char *op, BlValue arg);
/* Install a deep handler around a thunk; re-installs itself on resume (spec §4.3). */
typedef BlValue (*BlThunk)(BlValue env);
typedef BlValue (*BlReturnClause)(BlValue env, BlValue x);
typedef BlValue (*BlOpClause)(BlValue env, BlValue x, BlValue k);
BlValue bl_handle(BlValue env, BlThunk body, BlReturnClause ret,
                  size_t n_ops, const char **op_names, BlOpClause *op_clauses);
/* Closure-based deep handler used by the compiler backend: each clause is a Blight closure value
 * (body = thunk `λ_.body`, ret = `λx.r`, op = curried `λx.λk.e`), applied via the closure calling
 * convention. Same deep-handler semantics as `bl_handle`. */
BlValue bl_handle_clo(BlValue body_clo, BlValue ret_clo,
                      size_t n_ops, const char **op_names, BlValue *op_clos);
/* OpNode-aware application (spec §4.3): the native delimited-continuation capture. Compiled call
 * sites route through this so that effects performed inside an argument/function bubble out with
 * the pending application composed onto their continuation. A pure call is just a closure apply. */
BlValue bl_app(BlValue f, BlValue a);

/* Direct application of a captureless top-level function (A3 spine fusion): call `fnptr` (a lifted
 * function pointer) with a NULL env and argument `a`, skipping the per-call closure allocation. An
 * effectful (OpNode) argument falls back to `bl_app` so effects bubble identically to a normal call. */
BlValue bl_app_global(void *fnptr, BlValue a);

/* Call a *lifted* function pointer (`fn`, an opaque code pointer stored in a closure's header.aux)
 * with the object's calling convention. Every C-runtime site that applies compiled closure code —
 * `bl_apply1`, `bl_app_global`, the delay stepper, graphics dispatch — MUST go through this rather
 * than casting `fn` to a plain C function pointer and calling it directly: on native the lifted
 * functions use `tailcc`, whose x86_64 register/stack ABI differs from the C convention, so a direct
 * C call corrupts the stack and segfaults (it happens to coincide on arm64). Codegen emits a strong
 * definition that performs the call under `tailcc`; a weak C fallback (ccc) below keeps C-only test
 * harnesses — which link the runtime but never emit a Blight program — linkable. */
BlValue bl_call_tailcc(void *fn, BlValue clo, BlValue arg);

/* OpNode-aware data construction (spec §4.3): after a Con/Tuple is built eagerly, this bubbles any
 * effectful field so `Succ (perform op a)` suspends with continuation `λn. Succ n`. Pure objects are
 * returned unchanged. */
BlValue bl_con_bubble(BlValue obj);

/* Native top-level `Console` handler (std/io.bl): drive a bubbling `Console` OpNode tree against
 * real stdio (`print` -> stdout, `read` -> stdin line), returning the pure result. The build driver
 * installs this as `main`'s interpreter when `main : (! Console A)`. */
BlValue bl_run_console(BlValue comp);
/* Read-only accessor into the (effect,op) intern table for a translation unit other than effects.c
 * itself (currently only `graphics.c`, roadmap Wave 10 / P2): the same lookup `bl_run_console`'s
 * dispatch loop uses internally, without exposing the table's private append/freeze state. */
const char *bl_op_name_of(uint64_t idx);
/* Like `bl_op_name_of` but the EFFECT half of the pair (P5, roadmap Wave 10 / code mobility;
 * `serialize.c`'s mobile serializer). */
const char *bl_effect_name_of(uint64_t idx);
/* Intern `(effect, op)`, returning its LOCAL index in this process's table (appending if new; see
 * effects.c's header comment for the append/freeze discipline this already supports for M15
 * multicore). P5's mobile deserializer calls this to turn a wire-format (effect,op) NAME pair back
 * into a valid local `BL_OPNODE.header.aux` index — the index itself is never shipped over the wire,
 * only re-derived, since it is assigned by this process's own first-use order. */
uint64_t bl_effect_intern(const char *effect, const char *op);

/* ---- `Graphics` native effect handler (graphics.c, roadmap Wave 10 / P2, cargo feature
 * `graphics`) ---- */
/* Drive a bubbling `Graphics` OpNode tree (std/graphics.bl) against a real SDL2 window/renderer,
 * returning the pure result. Mirrors `bl_run_console`'s loop/dispatch shape exactly (Design B,
 * `docs/design-wave4-gobars.md` §5): every SDL call is hidden inside this file's op-name branches, so
 * no raw pointer or SDL type ever crosses into Blight-visible code. The build driver installs this as
 * `main`'s interpreter when `main : (! Graphics A)` AND the `graphics` cargo feature is enabled (the
 * symbol only exists in that build configuration — this declaration is unconditional so callers do
 * not need their own `#ifdef`, but linking a `Graphics` program without the feature fails at link
 * time with a clear undefined-symbol error, not silently). */
BlValue bl_run_graphics(BlValue comp);

/* ---- structural (de)serialization (serialize.c, M18) ---- */
/* Flatten an immutable value to a self-contained byte blob and rebuild it in the CURRENT thread's
 * heap. The boundary primitive for share-nothing messaging (M17 worker pool, M19 distributed
 * transport). DATA-ONLY: only BL_CON/BL_TUPLE/BL_INT are serializable; closures/opnodes/delays carry
 * a raw function pointer meaningful in one address space only, so serialize returns NULL for them
 * (the transport must reject such a message). See serialize.c for the wire format. */
int bl_value_is_serializable_tag(BlTag t);
/* Serialize `v` to a freshly malloc'd blob (caller frees). `*out_len` gets the byte length. Returns
 * NULL (and sets `*out_len`=0) if `v` contains a non-data tag. */
void *bl_value_serialize(BlValue v, size_t *out_len);
/* Rebuild a value from a blob into the current thread's heap. */
BlValue bl_value_deserialize(const void *buf, size_t len);

/* ---- P5 code mobility (roadmap Wave 10): codegen-emitted stable function-index table ---- */
/* A real `blight build` binary's generated `main.c` calls this once at startup (right after
 * `bl_gc_init`/`bl_stack_init`, before running the program) with THREE globals `driver.rs`'s
 * `code_table_source_for` authors as a small separate C translation unit: `table[i]` is the address
 * of the `i`-th lifted top-level function in the SAME order the compiler assigned (`AnfProgram.funcs`
 * order — a property of the compiled program, fixed at codegen time, unlike `effects.c`'s `g_ops`,
 * whose indices are assigned by runtime first-USE order), `len` is its length, and `binary_id` is a
 * compile-time content hash (FNV-1a over the ordered function-name list) — identical for two
 * processes running the SAME compiled binary (unlike raw addresses, which ASLR randomizes
 * per-process), used to reject a mismatched-binary blob BEFORE any `code_id` is ever resolved to a
 * pointer (`docs/design-code-mobility.md`'s security model).
 *
 * This is a runtime REGISTRATION call, not a direct `extern` reference from `serialize.c` to
 * codegen-emitted globals, deliberately: `serialize.c` is unconditionally linked into every C-only
 * runtime test harness (`runtime.rs`'s `build_and_run_harness*`), which hand-build `BlValue`s and
 * never link an actual `program.o` — an `extern` symbol serialize.c itself referenced would leave
 * every one of those harnesses with an unresolved external at link time. Registration means
 * serialize.c needs no symbol from anywhere else to exist: an unregistered process (every existing
 * test, and any program that performs no code mobility) simply leaves the table empty (`bl_code_id_of`
 * reports "not found" for everything), and a dedicated test harness can call this directly with its
 * own hand-built table instead of the codegen-emitted one (see `runtime/tests/serialize_test.c`). */
void bl_code_table_register(void *const *table, uint64_t len, uint64_t binary_id);
/* Bounds-checked `code_id -> function pointer` lookup against the table `bl_code_table_register`
 * installed (NULL if `code_id` is out of range, e.g. the table was never registered). Public so
 * `worker.c`'s `bl_pool_submit_code` (P4) can resolve a task's callee without `serialize.c` exposing
 * its table storage directly. */
void *bl_code_table_resolve(uint64_t code_id);

/* ---- P5 code mobility: mobile (de)serialization of BL_CLOSURE / BL_OPNODE ---- */
/* Like `bl_value_serialize`/`bl_value_deserialize` above, but additionally accepts `BL_CLOSURE`
 * (resolved to/from a portable `code_id` via `bl_code_table`) and `BL_OPNODE` (resolved to/from its
 * (effect, op) NAME pair via `bl_effect_intern`/`bl_op_name_of`/`bl_effect_name_of` — NOT its raw
 * `header.aux` index, which (unlike `bl_code_table`'s compile-time-fixed order) is assigned by
 * runtime first-use order and is therefore only meaningful re-derived by name on the receiving side).
 * The wire format is prefixed with `bl_binary_id`, checked by the deserializer BEFORE any `code_id`
 * is ever resolved to a pointer: a mismatched id is a hard reject (`bl_value_deserialize_mobile`
 * returns NULL), never a dereference of a foreign process's function-pointer space. Scope: SAME-BINARY
 * mobility only (`docs/design-code-mobility.md`); shipping a closure to a *different* build is a
 * documented, deliberate non-goal, not a silent unsoundness. `BL_NOW`/`BL_LATER` (delay thunks, which
 * wrap a closure) remain out of scope, same as the base `bl_value_serialize`. */
int bl_value_is_mobile_tag(BlTag t);
/* Serialize `v` (which may contain `BL_CLOSURE`/`BL_OPNODE` nodes) to a freshly malloc'd blob
 * (caller frees). `*out_len` gets the byte length. Returns NULL (and sets `*out_len`=0) if `v`
 * contains a tag neither the base data set nor `BL_CLOSURE`/`BL_OPNODE` cover. */
void *bl_value_serialize_mobile(BlValue v, size_t *out_len);
/* Rebuild a value from a mobile blob into the CURRENT thread's heap. Returns NULL — WITHOUT resolving
 * or dereferencing any `code_id` — if the blob's embedded `bl_binary_id` does not match this
 * process's own, or if a `code_id`/op index is malformed. */
BlValue bl_value_deserialize_mobile(const void *buf, size_t len);

/* ---- share-nothing worker pool (worker.c, M17) ---- */
/* A pool of N OS-thread workers, each with its own thread-local runtime (heap+stack). Independent
 * Blight computations run in parallel on separate heaps; arguments/results cross worker boundaries
 * by structural copy of immutable values (data-only v1). Opaque handles. */
typedef struct BlPool BlPool;
typedef struct BlTask BlTask;
typedef BlValue (*BlWorkerFn)(BlValue arg);
/* Create a pool of `nthreads` workers; each worker's thread-local heap starts at `worker_heap_bytes`
 * (it still grows on demand). */
BlPool *bl_pool_create(int nthreads, size_t worker_heap_bytes);
/* Submit `fn(arg)` to the pool. `arg` is structurally copied out of the caller's heap now. Returns a
 * task handle to join. `fn` must return first-order data (data-only v1). */
BlTask *bl_pool_submit(BlPool *p, BlWorkerFn fn, BlValue arg);
/* P4 (roadmap Wave 10 / auto-parallelism): submit a task naming a **lifted Blight function** by its
 * P5 `code_id` instead of a native `BlWorkerFn` C pointer — this is what a codegen-emitted
 * `bl_pool_submit_code` call site (an auto-parallelized divide-and-conquer recursive call) uses,
 * since the callee is a compiled Blight closure's underlying function, not hand-written C. Resolves
 * `code_id` through the SAME registered table `bl_value_*_mobile` uses (`bl_code_table_register`);
 * an unresolvable `code_id` (table not registered, or the id is out of range) aborts rather than
 * dereferencing garbage — this is only ever reached from codegen-emitted call sites, so a bad id
 * here is a codegen bug, not an untrusted-input event (contrast `bl_value_deserialize_mobile`, which
 * treats the analogous case as an ordinary, non-fatal wire-format rejection because ITS input can be
 * adversarial). `arg` is the pre-copied `env` value for a captured closure (or `NULL` for a
 * captureless one); the task calls the resolved function with that `env` and `taskarg`. */
BlTask *bl_pool_submit_code(BlPool *p, uint64_t code_id, BlValue env, BlValue taskarg);
/* Wait for a task and return its result, structurally copied into the CURRENT (caller's) heap. */
BlValue bl_pool_join(BlPool *p, BlTask *t);
/* Stop all workers (after joining all tasks) and free the pool. */
void bl_pool_destroy(BlPool *p);

/* ---- machine-word natural numbers (numeric.c, M20) ---- */
/* A fast `Nat` representation: a BL_NAT object stores its value directly in `header.aux` (no Succ
 * chain), so arithmetic is O(1) register work instead of O(n) allocation. It is OBSERVATIONALLY
 * identical to the inductive `Zero`/`Succ` encoding: `bl_nat_to_con` materializes the corresponding
 * `Zero`/`Succ` node (using the prelude's declaration-order tags Zero=0, Succ=1) on demand, and
 * `bl_nat_of_value` reads a value back to a u64 whether it is already a BL_NAT or a `Zero`/`Succ`
 * chain. This keeps the fast path coherent with every generic consumer (pattern match, GC) without
 * growing the trusted kernel — the kernel still only ever sees the inductive definition; this is a
 * pure backend representation choice, gated by a differential test against the unary semantics. */
/* The prelude `Nat` constructor tags (std/nat.bl declaration order). */
#define BL_NAT_ZERO_TAG 0u
#define BL_NAT_SUCC_TAG 1u
/* Allocate a fast Nat holding `n`. */
BlValue bl_nat_from_u64(uint64_t n);
/* Read any Nat-shaped value to a u64: a BL_NAT in O(1), or a `Zero`/`Succ` chain by counting. */
uint64_t bl_nat_of_value(BlValue v);
/* O(1) arithmetic on fast Nats (operands may be BL_NAT or chains; result is a fresh BL_NAT). */
BlValue bl_nat_add(BlValue a, BlValue b);
BlValue bl_nat_mul(BlValue a, BlValue b);
BlValue bl_nat_sub(BlValue a, BlValue b);  /* truncated: max(0, a-b) */
BlValue bl_nat_pred(BlValue a);            /* truncated: pred 0 = 0 */
BlValue bl_nat_min(BlValue a, BlValue b);  /* min(a, b) */
BlValue bl_nat_max(BlValue a, BlValue b);  /* max(a, b) */
/* Materialize one inductive layer of a BL_NAT for a generic destructuring reader: for n=0 this is a
 * `Zero` Con (tag 0, 0 fields); for n>0 a `Succ` Con (tag 1, 1 field) whose field is the fast Nat
 * `n-1`. A value that is already a `Zero`/`Succ` Con is returned unchanged. This is what `emit_case`
 * and `load_field` call so a fast Nat flowing into generic code behaves exactly like the chain. */
BlValue bl_nat_to_con(BlValue v);
/* Peel one inductive layer of a Nat-shaped value WITHOUT materializing a `Succ` box (M25): the
 * codegen uses these to destructure a fast-`Nat` loop driver (`match fuel [Zero][Succ f]`) with zero
 * allocation per step. `bl_nat_is_succ` is the tag (1 = Succ, 0 = Zero); `bl_nat_pred_value` is the
 * `Succ` arm's predecessor field (a fast Nat for a BL_NAT input — no heap). Observationally identical
 * to `bl_nat_to_con` + tag-read + field-load; gated by numeric_diff.c. */
uint64_t bl_nat_is_succ(BlValue v);
BlValue bl_nat_pred_value(BlValue v);

/* ---- packed `String` (numeric.c, A2) ---- */
/* The prelude `String` constructor tags (std/string.bl declaration order: `empty` then `push`). */
#define BL_STRING_EMPTY_TAG 0u
#define BL_STRING_PUSH_TAG 1u
/* Allocate a packed `String` from `n` codepoints (a contiguous run, codepoint `i` = `cps[i]`). The
 * codepoints are copied into a program-lifetime intern buffer (never freed, never GC-traced), and the
 * returned BL_STRING object holds a pointer to it in `header.aux`. Observationally identical to the
 * `push cp0 (push cp1 … empty)` cons-list. `n == 0` yields a packed empty string. */
BlValue bl_string_from_codepoints(const uint64_t *cps, uint64_t n);
/* The codepoint count of any `String`-shaped value: O(1) for a BL_STRING, or counting the
 * `empty`/`push` spine otherwise. */
uint64_t bl_string_len_of_value(BlValue v);
/* Read codepoint `i` of any `String`-shaped value (O(1) for a BL_STRING; walks the spine otherwise).
 * Returns 0 if `i` is out of range — total, never traps. */
uint64_t bl_string_codepoint_at(BlValue v, uint64_t i);
/* Materialize ONE inductive layer of a packed `String` for a generic destructuring reader: an empty
 * packed string becomes `empty` (tag 0, 0 fields); a non-empty one becomes `push cp rest` (tag 1, 2
 * fields: field[0] = the head codepoint as a fast Nat; field[1] = the BL_STRING tail). A value that
 * is already an `empty`/`push` Con is returned unchanged. This is what `emit_case`/`load_field` call
 * so a packed String flowing into generic code behaves exactly like the cons-list. */
BlValue bl_string_to_con(BlValue v);


int64_t bl_int_val(BlValue v);
/* Construct a machine integer (`BL_INT`), returning a tagged immediate when it fits (M21). */
BlValue bl_int(int64_t n);
BlValue bl_con(uint64_t ctor_index, uint32_t nfields);

/* ---- UNVERIFIED IEEE-754 `F64` escape hatch (numeric.c, L2, Design B / spec §7.6) ---- */
/* `F64` is an opaque `foreign` postulate (std/f64.bl): the kernel trusts these C symbols and the
 * independent re-checker DECLINES any program mentioning them (unlike `Float`/std/float.bl's
 * verified fixed-point rational, Design C — see std/f64.bl's header for the full tradeoff). A
 * boxed `F64` value is, bit-for-bit, a `BL_INT` box whose `int64_t` payload is the `double`'s raw
 * IEEE-754 bit pattern (`bl_int`/`bl_int_val` already round-trip an arbitrary 64-bit pattern
 * exactly, immediate or heap-boxed, so no new GC tag is needed). A binary op's argument is one
 * `(Pair F64 F64)` value (field 0 / field 1), matching the `std/bytes.bl` packed-argument
 * convention `lower.rs`'s single-argument `Cir::Foreign` relies on. */
BlValue bl_f64_of_int(BlValue i); /* Int -> F64 : numeric conversion (n.0), not a bit reinterpret */
BlValue bl_f64_round(BlValue x);  /* F64 -> Int : round to the nearest i64, ties away from zero */
BlValue bl_f64_add(BlValue pair); /* (Pair F64 F64) -> F64 */
BlValue bl_f64_sub(BlValue pair); /* (Pair F64 F64) -> F64 */
BlValue bl_f64_mul(BlValue pair); /* (Pair F64 F64) -> F64 */
BlValue bl_f64_div(BlValue pair); /* (Pair F64 F64) -> F64 */
BlValue bl_f64_neg(BlValue x);    /* F64 -> F64 */
BlValue bl_f64_lt(BlValue pair);  /* (Pair F64 F64) -> Int : 1/0 flag, mirrors std/int.bl `int-lt` */
BlValue bl_f64_eq(BlValue pair);  /* (Pair F64 F64) -> Int : 1/0 flag, mirrors std/int.bl `int-eq` */

/* Print a `String` value (std/string.bl: `empty`/`push` cons-list of `Nat` codepoints) as text,
 * followed by a newline. Used by the host-authored `main` for a `String`-typed program. */
void bl_print_string(BlValue s);

/* Print a non-`String` result (Nat numeral / INT / tuple / constructor index) followed by a
 * newline — the historical numeric printer, exported for the host-authored `main`. */
void bl_print_default(BlValue v);

#endif /* BLIGHT_RT_H */
