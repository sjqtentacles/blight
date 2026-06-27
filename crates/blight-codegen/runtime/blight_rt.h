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
  BL_FWD = 7       /* GC forwarding pointer (used only during collection) */
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

/* A Blight value is a pointer to a heap object (all values are boxed in this subset). */
typedef struct BlObj {
  BlHeader header;
  struct BlObj *fields[];
} BlObj;

typedef BlObj *BlValue;

/* ---- allocation + GC (gc.c) ---- */
void bl_gc_init(size_t heap_bytes);
BlValue bl_alloc(BlTag tag, uint32_t nfields, uint64_t aux);
/* A GC safepoint poll, emitted by codegen at loop back-edges and function entry (never right
 * before a tail call). Runs a collection if the heap is under pressure. */
void bl_gc_poll(void);
/* Push/pop a stack of GC roots (the codegen-emitted shadow stack of live pointers). */
void bl_gc_push_root(BlValue *slot);
void bl_gc_pop_roots(size_t n);
/* Statistics for tests. */
size_t bl_gc_collections(void);
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


/* ---- segmented stack (stack.c) ---- */
void bl_stack_init(void);
/* Ensure at least `bytes` of contiguous stack headroom, growing (segmenting) if needed. */
void *bl_stack_grow(size_t bytes);

/* ---- delay trampoline (delay.c) ---- */
/* Force a Delay value: repeatedly step BL_LATER thunks until a BL_NOW, returning its payload.
 * Runs in bounded C stack regardless of recursion depth (the headline million-deep path). */
BlValue bl_force(BlValue delay);

/* ---- effect trampoline (effects.c) ---- */
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

/* OpNode-aware data construction (spec §4.3): after a Con/Tuple is built eagerly, this bubbles any
 * effectful field so `Succ (perform op a)` suspends with continuation `λn. Succ n`. Pure objects are
 * returned unchanged. */
BlValue bl_con_bubble(BlValue obj);

/* Native top-level `Console` handler (std/io.bl): drive a bubbling `Console` OpNode tree against
 * real stdio (`print` -> stdout, `read` -> stdin line), returning the pure result. The build driver
 * installs this as `main`'s interpreter when `main : (! Console A)`. */
BlValue bl_run_console(BlValue comp);

/* ---- constructors used by the prelude/tests (prelude_rt.c) ---- */
BlValue bl_int(int64_t n);
int64_t bl_int_val(BlValue v);
BlValue bl_con(uint64_t ctor_index, uint32_t nfields);

/* Print a `String` value (std/string.bl: `empty`/`push` cons-list of `Nat` codepoints) as text,
 * followed by a newline. Used by the host-authored `main` for a `String`-typed program. */
void bl_print_string(BlValue s);

/* Print a non-`String` result (Nat numeral / INT / tuple / constructor index) followed by a
 * newline — the historical numeric printer, exported for the host-authored `main`. */
void bl_print_default(BlValue v);

#endif /* BLIGHT_RT_H */
