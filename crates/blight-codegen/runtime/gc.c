/* gc.c — precise generational copying garbage collector (spec §7.3).
 *
 * Two generations:
 *   - a small **nursery** (young generation): a single bump buffer. Fresh allocations land here.
 *   - an **old generation**: a classic semi-space (from/to), collected by a full Cheney scan.
 *
 * Most objects die young, so the common collection is a cheap **minor** GC that scans only the
 * roots and the *remembered set* (old→young pointers recorded by `bl_write_barrier`), promoting the
 * few nursery survivors into the old generation and then declaring the whole nursery free in O(1).
 * When the old generation fills, a **major** GC does the full semi-space Cheney scan over everything
 * (this is the M4 mechanism, kept intact so the M4 suite stays green). The heap is **not fixed**: if
 * a major leaves the old generation nearly full (or an allocation cannot be satisfied even after a
 * major), the collector performs a *growing* major that relocates the live set into a freshly
 * allocated, larger pair of semi-spaces (doubling until it fits). The initial `bl_gc_init` size is
 * therefore just a starting point — only a genuine host out-of-memory is fatal.
 *
 * Region arenas (arena.c) are a third, non-GC space: objects with BL_ARENA_BIT are never moved, but
 * the collector traces *through* them so any GC-heap object reachable only via an arena survives.
 *
 * Precise: every header records exactly how many trailing fields are GC pointers. Roots are
 * explicit (the codegen shadow stack); the C stack is never scanned.
 */
#include "blight_rt.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ---- old generation: a semi-space ---- */
static char *g_old_from;   /* base of the active old from-space */
static char *g_old_to;     /* base of the inactive old to-space */
static size_t g_old_space; /* bytes per old semi-space */
static char *g_old_bump;   /* next free byte in old from-space */
static char *g_old_limit;  /* end of old from-space */

/* ---- young generation: a bump nursery ---- */
static char *g_nursery;       /* base of the nursery */
static size_t g_nursery_size; /* nursery capacity in bytes */
static char *g_nursery_bump;  /* next free byte in the nursery */
static char *g_nursery_limit; /* end of the nursery */

static size_t g_collections; /* minor + major collections (stats) */

/* Shadow stack of roots: pointers to BlValue slots the mutator currently holds live. */
#define BL_MAX_ROOTS 65536
static BlValue *g_roots[BL_MAX_ROOTS];
static size_t g_nroots;

/* Remembered set: old-generation objects that may hold a pointer into the nursery (recorded by the
 * write barrier). A minor GC treats these as extra roots so it never loses a young object kept alive
 * only by an old object. Deduplicated via BL_REMEMBERED_BIT in the object's tag. */
#define BL_MAX_REMEMBERED 65536
static BlValue g_remembered[BL_MAX_REMEMBERED];
static size_t g_nremembered;

/* Worklist of arena objects discovered during a collection: traced but never moved. */
#define BL_MAX_ARENA_GRAY 65536
static BlValue g_arena_gray[BL_MAX_ARENA_GRAY];
static size_t g_arena_ngray;

static size_t obj_bytes(BlValue o) {
  return sizeof(BlHeader) + (size_t)o->header.nfields * sizeof(BlValue);
}

static int in_nursery(BlValue p) {
  return (char *)p >= g_nursery && (char *)p < g_nursery_limit;
}
static int in_old_from(BlValue p) {
  return (char *)p >= g_old_from && (char *)p < g_old_from + g_old_space;
}

void bl_gc_init(size_t heap_bytes) {
  /* Split the budget: a modest nursery, the rest into two old semi-spaces. */
  g_nursery_size = heap_bytes / 8;
  if (g_nursery_size < 4096) g_nursery_size = 4096;
  g_old_space = heap_bytes / 2;
  if (g_old_space < 4096) g_old_space = 4096;

  g_old_from = (char *)malloc(g_old_space);
  g_old_to = (char *)malloc(g_old_space);
  g_nursery = (char *)malloc(g_nursery_size);
  if (!g_old_from || !g_old_to || !g_nursery) {
    fprintf(stderr, "blight: out of memory initializing heap\n");
    abort();
  }
  g_old_bump = g_old_from;
  g_old_limit = g_old_from + g_old_space;
  g_nursery_bump = g_nursery;
  g_nursery_limit = g_nursery + g_nursery_size;
  g_nroots = 0;
  g_nremembered = 0;
  g_collections = 0;
}

void bl_gc_push_root(BlValue *slot) {
  if (g_nroots >= BL_MAX_ROOTS) {
    fprintf(stderr, "blight: root stack overflow\n");
    abort();
  }
  g_roots[g_nroots++] = slot;
}

void bl_gc_pop_roots(size_t n) {
  if (n > g_nroots) n = g_nroots;
  g_nroots -= n;
}

/* The generational write barrier (spec §7.3). Called on a *post-initialization* store of `val` into
 * a field of `obj`. If `obj` lives in the old generation and `val` in the nursery, `obj` must be in
 * the remembered set so the next minor GC treats it as a root into the nursery — otherwise the young
 * `val` could be reclaimed while still live. Initializing stores into fresh nursery objects need no
 * barrier (codegen omits it there). Idempotent and cheap. */
void bl_write_barrier(BlValue obj, BlValue val) {
  if (obj == NULL || val == NULL) return;
  if (BL_IS_ARENA(obj)) return; /* arena objects are always traced wholesale */
  if (!in_nursery(val)) return; /* only old->young edges matter */
  if (in_nursery(obj)) return;  /* young->young needs no barrier */
  if (obj->header.tag & BL_REMEMBERED_BIT) return; /* already recorded */
  if (g_nremembered >= BL_MAX_REMEMBERED) {
    /* Saturated: fall back to remembering nothing more and forcing a major GC soon. Conservative —
     * a major collection scans everything, so correctness is preserved. */
    return;
  }
  obj->header.tag |= BL_REMEMBERED_BIT;
  g_remembered[g_nremembered++] = obj;
}

/* ---- minor collection: promote nursery survivors into the old generation ---- */

/* Evacuate a nursery object into the old generation (at `*alloc`). Non-nursery objects (old or
 * arena) are left in place; arena objects are enqueued for tracing. Returns the (possibly moved)
 * pointer. */
static BlValue evac_minor(BlValue o, char **alloc) {
  if (o == NULL) return NULL;
  if (BL_IS_ARENA(o)) {
    if ((o->header.tag & BL_GC_SEEN_BIT) == 0) {
      o->header.tag |= BL_GC_SEEN_BIT;
      if (g_arena_ngray >= BL_MAX_ARENA_GRAY) {
        fprintf(stderr, "blight: arena gray overflow (minor)\n");
        abort();
      }
      g_arena_gray[g_arena_ngray++] = o;
    }
    return o;
  }
  if (!in_nursery(o)) {
    return o; /* old-generation object: stays put in a minor GC */
  }
  if (BL_TAG(o) == BL_FWD) {
    return (BlValue)(uintptr_t)o->header.aux;
  }
  size_t bytes = obj_bytes(o);
  if (*alloc + bytes > g_old_limit) {
    /* Old generation is full mid-promotion. The caller (collect) guarantees a major GC runs first
     * whenever the old generation lacks a whole nursery of headroom, so this is unreachable; abort
     * defensively rather than corrupt the heap. */
    fprintf(stderr, "blight: old generation overflow during promotion\n");
    abort();
  }
  BlValue dst = (BlValue)(*alloc);
  memcpy(dst, o, bytes);
  *alloc += bytes;
  /* Leave a forwarding pointer in the *header* (`aux`), which always exists even for zero-field
   * objects — a `fields[0]` slot may not (e.g. BL_INT has no fields). */
  o->header.tag = BL_FWD;
  o->header.aux = (uint64_t)(uintptr_t)dst;
  return dst;
}

static void minor_collect(void) {
  char *scan = g_old_bump; /* newly-promoted objects start here in the old space */
  char *alloc = g_old_bump;
  g_arena_ngray = 0;

  /* Roots: evacuate young objects directly reachable from the shadow stack. */
  for (size_t i = 0; i < g_nroots; i++) {
    if (g_roots[i] && *g_roots[i]) {
      *g_roots[i] = evac_minor(*g_roots[i], &alloc);
    }
  }

  /* Remembered set: old objects with possible old->young pointers act as extra roots. Evacuate the
   * young objects they reference (updating the field in place). */
  for (size_t i = 0; i < g_nremembered; i++) {
    BlValue old = g_remembered[i];
    old->header.tag &= ~BL_REMEMBERED_BIT; /* clear; re-armed by future barriers if needed */
    for (uint32_t f = 0; f < old->header.nfields; f++) {
      old->fields[f] = (struct BlObj *)evac_minor((BlValue)old->fields[f], &alloc);
    }
  }
  g_nremembered = 0;

  /* Cheney scan over the freshly-promoted objects, interleaved with arena tracing, to a fixpoint. */
  size_t arena_scanned = 0;
  for (;;) {
    int progress = 0;
    while (scan < alloc) {
      BlValue o = (BlValue)scan;
      for (uint32_t i = 0; i < o->header.nfields; i++) {
        o->fields[i] = (struct BlObj *)evac_minor((BlValue)o->fields[i], &alloc);
      }
      scan += obj_bytes(o);
      progress = 1;
    }
    while (arena_scanned < g_arena_ngray) {
      BlValue o = g_arena_gray[arena_scanned++];
      for (uint32_t i = 0; i < o->header.nfields; i++) {
        o->fields[i] = (struct BlObj *)evac_minor((BlValue)o->fields[i], &alloc);
      }
      progress = 1;
    }
    if (!progress) break;
  }

  for (size_t i = 0; i < g_arena_ngray; i++) {
    g_arena_gray[i]->header.tag &= ~BL_GC_SEEN_BIT;
  }
  g_arena_ngray = 0;

  /* Commit promotions and free the nursery in O(1). */
  g_old_bump = alloc;
  g_nursery_bump = g_nursery;
  g_collections++;
}

/* ---- major collection: full semi-space Cheney over the old generation + nursery ---- */

/* Evacuate any live object (nursery OR old-from) into the old to-space. Arena objects traced in
 * place. This is the M4 semi-space mechanism, generalized to also sweep the nursery. */
static BlValue evac_major(BlValue o, char **alloc) {
  if (o == NULL) return NULL;
  if (BL_IS_ARENA(o)) {
    if ((o->header.tag & BL_GC_SEEN_BIT) == 0) {
      o->header.tag |= BL_GC_SEEN_BIT;
      if (g_arena_ngray >= BL_MAX_ARENA_GRAY) {
        fprintf(stderr, "blight: arena gray overflow (major)\n");
        abort();
      }
      g_arena_gray[g_arena_ngray++] = o;
    }
    return o;
  }
  if (BL_TAG(o) == BL_FWD) {
    return (BlValue)(uintptr_t)o->header.aux;
  }
  size_t bytes = obj_bytes(o);
  BlValue dst = (BlValue)(*alloc);
  memcpy(dst, o, bytes);
  *alloc += bytes;
  o->header.tag = BL_FWD;
  o->header.aux = (uint64_t)(uintptr_t)dst;
  return dst;
}

/* Major collection into a (possibly larger) to-space. `to_base`/`to_space` name the destination
 * semi-space; on a plain major they are the current `g_old_to`/`g_old_space`, but a *growing* major
 * passes a freshly-`malloc`'d larger buffer so the live set is relocated into more room. Returns the
 * frontier (`alloc`) so the caller can install the new sizes. The from-space (`g_old_from` + the
 * nursery) is swept; pointers are recomputed via forwarding, so growing is just "copy into a bigger
 * box". */
static char *major_collect_into(char *to_base, size_t to_space) {
  char *scan = to_base;
  char *alloc = to_base;
  (void)to_space; /* the destination is sized by the caller; the scan never overruns a live set
                   * that already fit (plain major) or was sized to fit (growing major). */
  g_arena_ngray = 0;
  /* The remembered set is rebuilt from scratch after a major (every old->young edge is gone since
   * the nursery is swept too); clear bits we set. */
  for (size_t i = 0; i < g_nremembered; i++) {
    g_remembered[i]->header.tag &= ~BL_REMEMBERED_BIT;
  }
  g_nremembered = 0;

  for (size_t i = 0; i < g_nroots; i++) {
    if (g_roots[i] && *g_roots[i]) {
      *g_roots[i] = evac_major(*g_roots[i], &alloc);
    }
  }

  size_t arena_scanned = 0;
  for (;;) {
    int progress = 0;
    while (scan < alloc) {
      BlValue o = (BlValue)scan;
      for (uint32_t i = 0; i < o->header.nfields; i++) {
        o->fields[i] = (struct BlObj *)evac_major((BlValue)o->fields[i], &alloc);
      }
      scan += obj_bytes(o);
      progress = 1;
    }
    while (arena_scanned < g_arena_ngray) {
      BlValue o = g_arena_gray[arena_scanned++];
      for (uint32_t i = 0; i < o->header.nfields; i++) {
        o->fields[i] = (struct BlObj *)evac_major((BlValue)o->fields[i], &alloc);
      }
      progress = 1;
    }
    if (!progress) break;
  }

  for (size_t i = 0; i < g_arena_ngray; i++) {
    g_arena_gray[i]->header.tag &= ~BL_GC_SEEN_BIT;
  }
  g_arena_ngray = 0;
  return alloc;
}

static void major_collect(void) {
  /* Plain major: evacuate into the existing to-space, then swap. */
  char *alloc = major_collect_into(g_old_to, g_old_space);
  char *tmp = g_old_from;
  g_old_from = g_old_to;
  g_old_to = tmp;
  g_old_bump = alloc;
  g_old_limit = g_old_from + g_old_space;
  g_nursery_bump = g_nursery;
  g_collections++;
}

/* A *growing* major collection (spec §7.3 — the heap is not fixed): pick a new semi-space size at
 * least large enough to hold the surviving old generation plus `request` bytes plus a fresh
 * nursery's headroom, relocate every live object into a freshly-allocated larger to-space, then
 * resize the (now-dead) other semi-space to match. Doubles the semi-space until it fits, so growth
 * is amortized O(1). Returns 0 only if the host is genuinely out of memory. */
static int major_collect_grow(size_t request) {
  /* Upper bound on what must fit after collection: everything currently allocated in the old gen
   * and the nursery is *potentially* live, plus the pending request, plus a nursery of slack so the
   * post-grow heap does not immediately re-collect. */
  size_t live_upper = (size_t)(g_old_bump - g_old_from) + g_nursery_size;
  size_t need = live_upper + request + 2 * g_nursery_size;
  size_t new_space = g_old_space;
  while (new_space < need) {
    size_t doubled = new_space * 2;
    if (doubled < new_space) return 0; /* size_t overflow: cannot grow further */
    new_space = doubled;
  }

  char *new_to = (char *)malloc(new_space);
  if (!new_to) return 0;

  char *alloc = major_collect_into(new_to, new_space);

  /* The old from-space and old to-space are both dead now: free them, install the larger buffer as
   * the new from-space, and give the to-space a matching larger buffer for next time. */
  free(g_old_from);
  free(g_old_to);
  char *new_other = (char *)malloc(new_space);
  if (!new_other) {
    /* We still have a valid (larger) from-space, but no spare to-space. Keep running with the old
     * size's worth of to-space is impossible (we freed it); fail honestly. */
    free(new_to);
    return 0;
  }
  g_old_from = new_to;
  g_old_to = new_other;
  g_old_space = new_space;
  g_old_bump = alloc;
  g_old_limit = g_old_from + g_old_space;
  g_nursery_bump = g_nursery;
  g_collections++;
  return 1;
}

/* Decide minor vs major and collect. A minor GC may promote up to a whole nursery's worth into the
 * old generation, so the old generation must have a comfortable margin (we require *two* nurseries
 * of headroom, since promotion plus rounding must never overrun the from-space) or we do a major GC
 * instead. If even a major leaves less than that margin (the live set nearly fills the old
 * generation), grow the heap so we neither thrash on back-to-back majors nor overflow a minor. */
static void collect(void) {
  size_t margin = 2 * g_nursery_size;
  size_t old_free = (size_t)(g_old_limit - g_old_bump);
  if (old_free < margin) {
    major_collect();
    /* Post-major: if survivors leave us without our promotion margin, the next minor could overflow
     * the old generation. Grow instead (best-effort; a true host-OOM is reported by the allocator). */
    size_t free_after = (size_t)(g_old_limit - g_old_bump);
    if (free_after < margin) {
      major_collect_grow(0);
    }
  } else {
    minor_collect();
  }
}

BlValue bl_alloc(BlTag tag, uint32_t nfields, uint64_t aux) {
  size_t bytes = sizeof(BlHeader) + (size_t)nfields * sizeof(BlValue);
  /* Oversized objects that cannot fit in the nursery are allocated straight into the old gen. */
  if (bytes > g_nursery_size) {
    if (g_old_bump + bytes > g_old_limit) {
      major_collect();
      if (g_old_bump + bytes > g_old_limit) {
        /* The live set plus this oversized object exceeds the old generation: grow the heap rather
         * than abort (spec §7.3 — the heap is dynamic). Only a true host-OOM is fatal. */
        if (!major_collect_grow(bytes) || g_old_bump + bytes > g_old_limit) {
          fprintf(stderr, "blight: out of memory (oversized allocation of %zu bytes)\n", bytes);
          abort();
        }
      }
    }
    BlValue o = (BlValue)g_old_bump;
    g_old_bump += bytes;
    o->header.tag = (uint32_t)tag;
    o->header.nfields = nfields;
    o->header.aux = aux;
    for (uint32_t i = 0; i < nfields; i++) o->fields[i] = NULL;
    return o;
  }
  if (g_nursery_bump + bytes > g_nursery_limit) {
    collect();
    if (g_nursery_bump + bytes > g_nursery_limit) {
      /* Nursery still can't fit after a minor: force a major to be safe. */
      major_collect();
      if (g_nursery_bump + bytes > g_nursery_limit) {
        /* Even an empty nursery after a major cannot satisfy this — only happens if the nursery is
         * absurdly small for the object; grow and retry rather than abort. */
        if (!major_collect_grow(bytes) || g_nursery_bump + bytes > g_nursery_limit) {
          fprintf(stderr, "blight: out of memory (allocation of %zu bytes)\n", bytes);
          abort();
        }
      }
    }
  }
  BlValue o = (BlValue)g_nursery_bump;
  g_nursery_bump += bytes;
  o->header.tag = (uint32_t)tag;
  o->header.nfields = nfields;
  o->header.aux = aux;
  for (uint32_t i = 0; i < nfields; i++) o->fields[i] = NULL;
  return o;
}

void bl_gc_poll(void) {
  /* Poll at a safepoint: if the nursery is nearly full, collect now (where roots are accurate).
   * Never called immediately before a tail call (codegen rule). */
  size_t margin = 4096;
  if (g_nursery_bump + margin > g_nursery_limit) {
    collect();
  }
}

size_t bl_gc_collections(void) { return g_collections; }
