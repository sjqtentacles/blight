/* arena.c — region bump-pointer arenas (spec §3.5 / §7.3) — UNTRUSTED runtime.
 *
 * A region scope `(region r …)` is bracketed by `bl_arena_enter()` / `bl_arena_leave(mark)`. Inside
 * the scope, allocations the backend escape analysis ([`crate::region`]) proved non-escaping are
 * routed to `bl_arena_alloc`, which bump-allocates in the current arena. At `bl_arena_leave` the
 * whole arena is reclaimed in O(1) — the GC never sees these objects, so a region-disciplined
 * workload keeps `bl_gc_collections()` at zero (the M5 headline).
 *
 * Structure: a stack of fixed-size chunks. `bl_arena_enter` records a mark (the current stack depth
 * and bump offset in the top chunk). Each region scope conceptually owns the chunks allocated after
 * its mark; `bl_arena_leave(mark)` rewinds the bump pointer / frees chunks pushed since the mark.
 * Nesting works because marks are a stack: an inner leave never crosses an outer mark.
 *
 * Memory-safety note: routing an *escaping* value here would be a use-after-free — but that is the
 * (untrusted) analysis's responsibility to prevent; arena.c is a dumb, fast allocator. Arena
 * objects carry BL_ARENA_BIT so the GC traces through them without moving them.
 */
#include "blight_rt.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

/* One arena chunk: a bump buffer. We keep a singly-linked stack of chunks (newest on top). */
typedef struct BlArenaChunk {
  struct BlArenaChunk *prev; /* the chunk below this one on the stack */
  char *base;                /* start of the usable buffer */
  size_t bump;               /* next free offset within the buffer */
  size_t cap;                /* buffer capacity in bytes */
} BlArenaChunk;

#define BL_ARENA_CHUNK_BYTES (64 * 1024)

static BlArenaChunk *g_top;   /* top of the chunk stack (NULL when no region is open) */
static uint32_t g_depth;      /* number of chunks currently on the stack */
static size_t g_alloc_count;  /* total arena allocations (stats) */

/* Internal stack of region marks: each `bl_arena_enter` snapshots the current frontier; the paired
 * `bl_arena_leave` rewinds to it. Region scopes nest lexically, so this is a simple stack. */
typedef struct { uint32_t depth; size_t bump; } BlMark;
#define BL_MAX_REGIONS 4096
static BlMark g_marks[BL_MAX_REGIONS];
static size_t g_nmarks;

static BlArenaChunk *push_chunk(size_t min_bytes) {
  size_t cap = BL_ARENA_CHUNK_BYTES;
  if (min_bytes > cap) cap = min_bytes; /* oversized object: dedicated chunk */
  BlArenaChunk *c = (BlArenaChunk *)malloc(sizeof(BlArenaChunk));
  if (!c) { fprintf(stderr, "blight: arena chunk header OOM\n"); abort(); }
  c->base = (char *)malloc(cap);
  if (!c->base) { fprintf(stderr, "blight: arena chunk buffer OOM\n"); abort(); }
  c->bump = 0;
  c->cap = cap;
  c->prev = g_top;
  g_top = c;
  g_depth++;
  return c;
}

static void pop_chunk(void) {
  BlArenaChunk *c = g_top;
  if (!c) return;
  g_top = c->prev;
  g_depth--;
  free(c->base);
  free(c);
}

void bl_arena_enter(void) {
  /* Ensure there is a chunk to allocate into, then snapshot the current frontier onto the mark
   * stack. A region's objects all live at-or-after this mark; the paired leave rewinds to here. */
  if (!g_top) push_chunk(0);
  if (g_nmarks >= BL_MAX_REGIONS) {
    fprintf(stderr, "blight: region nesting too deep\n");
    abort();
  }
  g_marks[g_nmarks].depth = g_depth;
  g_marks[g_nmarks].bump = g_top->bump;
  g_nmarks++;
}

BlValue bl_arena_alloc(BlTag tag, uint32_t nfields, uint64_t aux) {
  size_t bytes = sizeof(BlHeader) + (size_t)nfields * sizeof(BlValue);
  if (!g_top || g_top->bump + bytes > g_top->cap) {
    push_chunk(bytes);
  }
  BlValue o = (BlValue)(g_top->base + g_top->bump);
  g_top->bump += bytes;
  /* Mark the object as arena-resident so the GC traces but never moves it. */
  o->header.tag = (uint32_t)tag | BL_ARENA_BIT;
  o->header.nfields = nfields;
  o->header.aux = aux;
  for (uint32_t i = 0; i < nfields; i++) o->fields[i] = NULL;
  g_alloc_count++;
  return o;
}

void bl_arena_leave(void) {
  /* Pop the most-recent region mark and rewind to it: free every chunk pushed since the mark, then
   * restore the surviving top chunk's bump pointer. O(chunks-since-mark), O(1) in the common case. */
  if (g_nmarks == 0) {
    fprintf(stderr, "blight: bl_arena_leave without matching enter\n");
    abort();
  }
  BlMark mark = g_marks[--g_nmarks];
  while (g_depth > mark.depth) {
    pop_chunk();
  }
  if (g_top && g_depth == mark.depth) {
    g_top->bump = mark.bump;
  }
}

size_t bl_arena_live_bytes(void) {
  size_t total = 0;
  for (BlArenaChunk *c = g_top; c; c = c->prev) total += c->bump;
  return total;
}

size_t bl_arena_alloc_count(void) { return g_alloc_count; }
