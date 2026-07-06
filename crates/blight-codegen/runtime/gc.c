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
/* All collector state is `BL_THREAD_LOCAL` (spec §7.3 + M15 share-nothing): each worker thread owns
 * its own heap, so the existing single-mutator collector runs unchanged per worker with no locks. */
static BL_THREAD_LOCAL char *g_old_from;   /* base of the active old from-space */
static BL_THREAD_LOCAL char *g_old_to;     /* base of the inactive old to-space */
static BL_THREAD_LOCAL size_t g_old_space; /* bytes per old semi-space */
static BL_THREAD_LOCAL char *g_old_bump;   /* next free byte in old from-space */
static BL_THREAD_LOCAL char *g_old_limit;  /* end of old from-space */

/* ---- young generation: a bump nursery ---- */
static BL_THREAD_LOCAL char *g_nursery;       /* base of the nursery */
static BL_THREAD_LOCAL size_t g_nursery_size; /* nursery capacity in bytes */
static BL_THREAD_LOCAL char *g_nursery_bump;  /* next free byte in the nursery */
static BL_THREAD_LOCAL char *g_nursery_limit; /* end of the nursery */

static BL_THREAD_LOCAL size_t g_collections;    /* minor + major collections (stats) */
static BL_THREAD_LOCAL size_t g_minor;          /* minor collections */
static BL_THREAD_LOCAL size_t g_major;          /* major collections (incl. growing) */
static BL_THREAD_LOCAL size_t g_grows;          /* heap-growing majors */
static BL_THREAD_LOCAL size_t g_promoted_bytes; /* bytes promoted nursery->old (minor GCs) */
static BL_THREAD_LOCAL size_t g_bytes_allocated; /* total GC-heap bytes requested via bl_alloc (stats) */

/* ---- env-tunable sizing knobs (A4). Defaults match the historical fixed split. ---- */
/* `BL_GC_NURSERY_DIV` : nursery = heap / DIV (default 8).  `BL_GC_OLD_DIV` : old semi-space = heap /
 * DIV (default 2).  `BL_GC_NURSERY_BYTES` / `BL_GC_OLD_BYTES` : absolute overrides (win over the
 * divisors).  `BL_GC_MARGIN_NURSERIES` : promotion-headroom margin, in nurseries (default 2). All are
 * read once in bl_gc_init; an unset/invalid var keeps the default. UNTRUSTED runtime tuning only —
 * the collector's *semantics* (and thus observable results) are independent of these. */
static BL_THREAD_LOCAL size_t g_margin_nurseries = 2;

/* P4.1 mark-compact old generation, ON BY DEFAULT since C2 (Blight Arc II). The old generation is a
 * single region reclaimed by a copying compaction into a freshly right-sized region (peak ~1x live),
 * instead of the legacy two-space semi-space (peak ~2x live). `BL_GC_OLDGEN=semispace` opts back into
 * the legacy mode; `BL_GC_OLDGEN=compact` remains accepted as a no-op restating the (now-default)
 * behavior, so every script/test that pinned it explicitly keeps working unchanged. The collector's
 * *semantics* — and thus every observable result — are identical in both modes (verified by
 * `gc_diff.c`'s cross-mode checksum and the `oldgen_modes_identical_*` example corpus); this is
 * UNTRUSTED runtime memory tuning. C2 measured the switch throughput-neutral: at realistic heap sizes
 * old-gen majors are rare enough that the mode never matters, and under a deliberately tiny heap
 * forcing dozens of majors, compaction ran within noise of the semi-space (~1.05x either direction
 * across repeated trials) while reserving roughly half the memory. */
static BL_THREAD_LOCAL int g_oldgen_compact = 1;

/* P4.2 adaptive heap sizing. After a compacting major reclaims dead old objects, if the surviving live
 * set occupies only a small fraction of the (possibly long-ago-grown) region, the region is shrunk to
 * a right-sized buffer with growth slack. `g_shrink_band` (knob `BL_GC_SHRINK_BAND`, default 2) is the
 * anti-oscillation hysteresis: a shrink fires only when the current capacity exceeds the right-sized
 * target by more than this factor, and the right-sized target itself carries ~50% growth slack, so a
 * stable or moderately-fluctuating live set never triggers repeated grow/shrink churn. */
static BL_THREAD_LOCAL size_t g_shrink_band = 2;
static BL_THREAD_LOCAL size_t g_shrinks = 0; /* collections that shrank the old region (stats) */
/* P4.3 accounting: high-water mark of old-generation bytes *reserved* (incl. the semi-space's second
 * region), the headline footprint the mark-compact work moves toward ~1x-live. Updated whenever the
 * old region is (re)sized. */
static BL_THREAD_LOCAL size_t g_peak_old_reserved = 0;

static BL_ALWAYS_INLINE size_t old_reserved_now(void) {
  return g_oldgen_compact ? g_old_space : 2 * g_old_space;
}
static BL_ALWAYS_INLINE void note_peak(void) {
  size_t r = old_reserved_now();
  if (r > g_peak_old_reserved) g_peak_old_reserved = r;
}

static size_t env_size(const char *name, size_t fallback) {
  const char *v = getenv(name);
  if (!v || !*v) return fallback;
  char *end = NULL;
  unsigned long long n = strtoull(v, &end, 10);
  if (end == v || n == 0) return fallback; /* unparseable or zero → keep default */
  return (size_t)n;
}

/* Shadow stack of roots: pointers to BlValue slots the mutator currently holds live. The stack is
 * heap-backed and *grows on demand* (doubling): deep non-tail recursion that pins O(depth) live
 * frames (e.g. the slow-path `treesum` reference with every fast path off) must not hit a hard
 * ceiling and abort. Only a genuine host out-of-memory while growing is fatal. (The spec §7.4
 * segmented *call* stack in stack.c is a separate, larger follow-up and is currently unused by
 * codegen; this only removes the fixed root-stack ceiling.) */
#define BL_ROOTS_INIT 65536
static BL_THREAD_LOCAL BlValue **g_roots;
static BL_THREAD_LOCAL size_t g_nroots;
static BL_THREAD_LOCAL size_t g_roots_cap;

/* Remembered set: old-generation objects that may hold a pointer into the nursery (recorded by the
 * write barrier). A minor GC treats these as extra roots so it never loses a young object kept alive
 * only by an old object. Deduplicated via BL_REMEMBERED_BIT in the object's tag. */
#define BL_MAX_REMEMBERED 65536
static BL_THREAD_LOCAL BlValue g_remembered[BL_MAX_REMEMBERED];
static BL_THREAD_LOCAL size_t g_nremembered;

/* Worklist of arena objects discovered during a collection: traced but never moved. */
#define BL_MAX_ARENA_GRAY 65536
static BL_THREAD_LOCAL BlValue g_arena_gray[BL_MAX_ARENA_GRAY];
static BL_THREAD_LOCAL size_t g_arena_ngray;

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
  fprintf(stderr, "[rt] gc_init enter (heap=%zu)\n", heap_bytes); fflush(stderr); /* TEMP: localize Linux segfault */
  /* Split the budget: a modest nursery, the rest into two old semi-spaces. The divisors and absolute
   * sizes are env-tunable (A4); see the knob documentation above. */
  size_t nursery_div = env_size("BL_GC_NURSERY_DIV", 8);
  size_t old_div = env_size("BL_GC_OLD_DIV", 2);
  g_margin_nurseries = env_size("BL_GC_MARGIN_NURSERIES", 2);

  g_nursery_size = env_size("BL_GC_NURSERY_BYTES", heap_bytes / nursery_div);
  if (g_nursery_size < 4096) g_nursery_size = 4096;
  g_old_space = env_size("BL_GC_OLD_BYTES", heap_bytes / old_div);
  if (g_old_space < 4096) g_old_space = 4096;

  /* P4.1/C2: the old generation runs as a single compacting region by default. `BL_GC_OLDGEN=semispace`
   * is the only recognized opt-out, reverting to the legacy two-space semi-space; every other value
   * (unset, "compact", or anything unrecognized) keeps the default compacting mode. */
  const char *oldgen = getenv("BL_GC_OLDGEN");
  g_oldgen_compact = (oldgen && strcmp(oldgen, "semispace") == 0) ? 0 : 1;
  g_shrink_band = env_size("BL_GC_SHRINK_BAND", 2);
  if (g_shrink_band < 2) g_shrink_band = 2; /* a band below 2 would risk grow/shrink oscillation */

  g_old_from = (char *)malloc(g_old_space);
  /* The semi-space keeps a second (to-)region; compaction keeps only the one. */
  g_old_to = g_oldgen_compact ? NULL : (char *)malloc(g_old_space);
  g_nursery = (char *)malloc(g_nursery_size);
  if (!g_old_from || (!g_oldgen_compact && !g_old_to) || !g_nursery) {
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
  g_minor = 0;
  g_major = 0;
  g_grows = 0;
  g_promoted_bytes = 0;
  g_bytes_allocated = 0;
  g_shrinks = 0;
  g_peak_old_reserved = 0;
  note_peak();
}

void bl_gc_push_root(BlValue *slot) {
  if (g_nroots >= g_roots_cap) {
    /* Lazy first allocation, then doubling growth. Thread-local, so each worker grows its own. */
    size_t newcap = g_roots_cap ? g_roots_cap * 2u : (size_t)BL_ROOTS_INIT;
    BlValue **grown = (BlValue **)realloc(g_roots, newcap * sizeof(BlValue *));
    if (!grown) {
      fprintf(stderr, "blight: out of memory growing root stack to %zu slots\n", newcap);
      abort();
    }
    g_roots = grown;
    g_roots_cap = newcap;
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
  if (bl_is_imm(obj) || bl_is_imm(val)) return; /* immediates are not heap edges */
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
  if (bl_is_imm(o)) return o; /* a tagged immediate is not a heap pointer: nothing to trace/copy */
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

  /* Boxed-array handle table (P1, A3b): each live handle's backing object is an off-heap edge the
   * tracer would otherwise never see, so it is scanned as an extra root exactly like a shadow-stack
   * slot (boxed_array.c's header comment has the full rationale). */
  bl_boxed_array_gc_roots(evac_minor, &alloc);

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
  g_promoted_bytes += (size_t)(alloc - g_old_bump);
  g_old_bump = alloc;
  g_nursery_bump = g_nursery;
  g_collections++;
  g_minor++;
}

/* ---- major collection: full semi-space Cheney over the old generation + nursery ---- */

/* Evacuate any live object (nursery OR old-from) into the old to-space. Arena objects traced in
 * place. This is the M4 semi-space mechanism, generalized to also sweep the nursery. */
static BlValue evac_major(BlValue o, char **alloc) {
  if (o == NULL) return NULL;
  if (bl_is_imm(o)) return o; /* a tagged immediate is not a heap pointer: nothing to trace/copy */
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

  /* Boxed-array handle table (P1, A3b): see the matching call in minor_collect above. Every major
   * relocates the entire old generation (semi-space or compacting), so this entry MUST be rewritten
   * here regardless of whether the backing object was already promoted. */
  bl_boxed_array_gc_roots(evac_major, &alloc);

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
  g_major++;
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
  g_major++;
  g_grows++;
  note_peak();
  return 1;
}

/* ---- P4.1 compacting major: a single old region, relocated into a freshly right-sized buffer ----
 *
 * The compacting old generation holds ONE region (no to-space). A major reclaims it by evacuating the
 * entire live set — roots, nursery survivors, and live old objects, exactly as the semi-space major
 * does, reusing the proven `major_collect_into`/`evac_major` machinery — into a freshly `malloc`'d
 * region sized to (live upper bound + the pending request + a promotion margin). The (now-dead) source
 * region is then freed and the new buffer adopted as the single old region. Because the destination is
 * sized to the live set rather than to a fixed capacity, the steady-state reserved footprint is ~1x
 * the live set (one region), versus the semi-space's ~2x (two fixed regions) — the P4.1 win. Pointer
 * relocation is the identical, battle-tested forwarding the semi-space uses, so the compaction adds no
 * new use-after-free surface (gated under ASan). Returns 0 only on a genuine host out-of-memory. */
/* Relocate the entire live set into a freshly-`malloc`'d old region of `new_size` bytes (clamped to a
 * useful floor), via the proven `major_collect_into`/`evac_major` forwarding, then free the source
 * region and adopt the new one. The caller guarantees `new_size` holds the live set (it is sized from
 * a current-occupancy upper bound, or — when shrinking — from the live set already compacted into the
 * region being replaced). Returns 0 only on host out-of-memory. Does NOT touch the collection stat
 * counters; callers attribute the relocation (major / shrink). */
static int relocate_into(size_t new_size) {
  if (new_size < g_nursery_size) new_size = g_nursery_size;
  char *new_region = (char *)malloc(new_size);
  if (!new_region) return 0;
  char *alloc = major_collect_into(new_region, new_size);
  free(g_old_from); /* the source region is fully evacuated and dead */
  g_old_from = new_region;
  g_old_space = new_size;
  g_old_bump = alloc;
  g_old_limit = new_region + new_size;
  g_nursery_bump = g_nursery;
  note_peak();
  return 1;
}

/* The right-sized target capacity for a live set of `live` bytes plus a pending `request`: the live
 * set, the request, and ~50% growth slack (at least the promotion margin). The slack is the lower half
 * of the anti-oscillation hysteresis (a stable live set never re-grows right after a shrink). */
static size_t compact_target(size_t live, size_t request) {
  size_t margin = g_margin_nurseries * g_nursery_size;
  size_t slack = live / 2 > margin ? live / 2 : margin;
  return live + request + slack;
}

static int compact_collect(size_t request) {
  size_t live_upper = (size_t)(g_old_bump - g_old_from) + (size_t)(g_nursery_bump - g_nursery);
  size_t margin = g_margin_nurseries * g_nursery_size;
  size_t prev_space = g_old_space;

  /* First pass: relocate into a region sized to the current occupancy (an upper bound on the live set,
   * since dead old objects are not yet reclaimed) plus the request and a margin. */
  if (!relocate_into(live_upper + request + margin)) return 0;
  g_collections++;
  g_major++;
  if (g_old_space > prev_space) g_grows++;

  /* P4.2 adaptive shrink: now that the dead objects are gone, `g_old_bump - g_old_from` is the *true*
   * live set. If the region is over-provisioned by more than the hysteresis band relative to the
   * right-sized target, shrink to it. The first pass over-sizes whenever the collection reclaimed a
   * lot of garbage (low occupancy); the band + the target's growth slack prevent oscillation under a
   * stable or moderately-varying live set. */
  size_t real_live = (size_t)(g_old_bump - g_old_from);
  size_t target = compact_target(real_live, request);
  if (g_old_space > target * g_shrink_band) {
    if (relocate_into(target)) g_shrinks++;
  }
  return 1;
}

/* Decide minor vs major and collect. A minor GC may promote up to a whole nursery's worth into the
 * old generation, so the old generation must have a comfortable margin (we require *two* nurseries
 * of headroom, since promotion plus rounding must never overrun the from-space) or we do a major GC
 * instead. If even a major leaves less than that margin (the live set nearly fills the old
 * generation), grow the heap so we neither thrash on back-to-back majors nor overflow a minor. */
static void collect(void) {
  size_t margin = g_margin_nurseries * g_nursery_size;
  size_t old_free = (size_t)(g_old_limit - g_old_bump);
  if (old_free < margin) {
    if (g_oldgen_compact) {
      /* One compacting pass reclaims and right-sizes the single region in one step (it always
       * leaves at least `margin` headroom), so there is no separate post-major grow. */
      if (!compact_collect(0)) {
        fprintf(stderr, "blight: out of memory during compacting major\n");
        abort();
      }
      return;
    }
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

/* Initialize a freshly bump-allocated object's header and null its fields. Shared by the nursery and
 * old-gen allocation paths. (Fields are nulled so a collection triggered before the mutator fills
 * them in never traces a garbage pointer — the precise tracer reads `nfields` slots unconditionally.) */
static BL_ALWAYS_INLINE void init_obj(BlValue o, BlTag tag, uint32_t nfields, uint64_t aux) {
  o->header.tag = (uint32_t)tag;
  o->header.nfields = nfields;
  o->header.aux = aux;
  for (uint32_t i = 0; i < nfields; i++) o->fields[i] = NULL;
}

/* Cold allocation slow path: the object does not fit the current nursery frontier, either because it
 * is oversized (bigger than the whole nursery → lives in the old gen) or the nursery is full (collect,
 * then retry; escalate to a major / heap-grow if still short). Factored out of `bl_alloc` and marked
 * `BL_COLD`/noinline so the LTO inliner inlines only the hot bump path into compiled Blight code and
 * leaves this rare machinery out of line. Behavior is byte-for-byte the previous monolithic path. */
static BL_COLD BlValue alloc_slow(BlTag tag, uint32_t nfields, uint64_t aux, size_t bytes) {
  /* Oversized objects that cannot fit in the nursery are allocated straight into the old gen. */
  if (bytes > g_nursery_size) {
    if (g_old_bump + bytes > g_old_limit) {
      if (g_oldgen_compact) {
        /* A compacting major sized to hold the live set plus this oversized request. */
        if (!compact_collect(bytes) || g_old_bump + bytes > g_old_limit) {
          fprintf(stderr, "blight: out of memory (oversized allocation of %zu bytes)\n", bytes);
          abort();
        }
      } else {
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
    }
    BlValue o = (BlValue)g_old_bump;
    g_old_bump += bytes;
    init_obj(o, tag, nfields, aux);
    return o;
  }
  /* Nursery is full: collect (minor, escalating as needed) and retry the bump. */
  collect();
  if (g_nursery_bump + bytes > g_nursery_limit) {
    /* Nursery still can't fit after a minor: force a major to be safe. */
    if (g_oldgen_compact) {
      if (!compact_collect(0) || g_nursery_bump + bytes > g_nursery_limit) {
        fprintf(stderr, "blight: out of memory (allocation of %zu bytes)\n", bytes);
        abort();
      }
    } else {
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
  init_obj(o, tag, nfields, aux);
  return o;
}

/* The allocation fast path: bump the nursery frontier and initialize the object. This is the only
 * code the LTO inliner needs to splice into a compiled `Con`/`Tuple`/`MkClosure` site — a single
 * compare-and-branch plus a pointer bump. Anything that doesn't fit (full nursery, oversized object)
 * is a `BL_UNLIKELY` branch into the out-of-line `alloc_slow`. */
BL_HOT BlValue bl_alloc(BlTag tag, uint32_t nfields, uint64_t aux) {
  size_t bytes = sizeof(BlHeader) + (size_t)nfields * sizeof(BlValue);
  /* Stats only (BL_GC_STATS): total GC-heap bytes the program requests. Counted once per object here
   * (the single allocation entry point) so it covers both the fast bump and the alloc_slow path; GC
   * promotion copies and arena allocations are deliberately excluded. Does not affect any output. */
  g_bytes_allocated += bytes;
  char *bump = g_nursery_bump;
  char *next = bump + bytes;
  if (BL_UNLIKELY(next > g_nursery_limit)) {
    return alloc_slow(tag, nfields, aux, bytes);
  }
  g_nursery_bump = next;
  BlValue o = (BlValue)bump;
  init_obj(o, tag, nfields, aux);
  return o;
}

BL_HOT void bl_gc_poll(void) {
  /* Poll at a safepoint: if the nursery is nearly full, collect now (where roots are accurate).
   * Never called immediately before a tail call (codegen rule). */
  size_t margin = 4096;
  if (BL_UNLIKELY(g_nursery_bump + margin > g_nursery_limit)) {
    collect();
  }
}

size_t bl_gc_collections(void) { return g_collections; }
size_t bl_gc_minor(void) { return g_minor; }
size_t bl_gc_major(void) { return g_major; }
size_t bl_gc_grows(void) { return g_grows; }
size_t bl_gc_promoted_bytes(void) { return g_promoted_bytes; }
size_t bl_gc_bytes_allocated(void) { return g_bytes_allocated; }

int bl_gc_oldgen_compacting(void) { return g_oldgen_compact; }
size_t bl_gc_old_capacity(void) { return g_old_space; }
size_t bl_gc_old_reserved_bytes(void) {
  /* Semi-space reserves two equal regions (from + to); compaction keeps a single region. */
  return g_oldgen_compact ? g_old_space : 2 * g_old_space;
}
size_t bl_gc_old_live_bytes(void) { return (size_t)(g_old_bump - g_old_from); }
size_t bl_gc_old_shrinks(void) { return g_shrinks; }
size_t bl_gc_peak_old_reserved_bytes(void) { return g_peak_old_reserved; }

void bl_gc_force_collect(void) {
  if (g_oldgen_compact) {
    if (!compact_collect(0)) {
      fprintf(stderr, "blight: out of memory during forced compacting collection\n");
      abort();
    }
  } else {
    major_collect();
  }
}

/* Initialize the calling thread's thread-local runtime: its own heap and segmented stack. Each
 * share-nothing worker (M15+) calls this once on entry. Because all collector and stack state is
 * `BL_THREAD_LOCAL`, this gives the worker a fully independent heap that the existing single-mutator
 * collector manages with no locks and no interaction with any other worker. */
void bl_runtime_init(size_t heap_bytes) {
  bl_gc_init(heap_bytes);
  bl_stack_init();
}
