/* stack.c — segmented / growable stack (spec §7.4).
 *
 * Deep *non-tail* recursion and captured continuations must not hit a fixed OS-stack limit. We
 * provide a heap-backed auxiliary stack that grows in segments (Go-early style). The codegen uses
 * the OS stack for ordinary frames but spills large/unbounded activation chains here, and the
 * effect machinery stores reified continuation frames in segments so capture/resume is cheap.
 *
 * This M4 implementation provides the growth primitive and segment bookkeeping; the deep-recursion
 * acceptance test reaches unbounded depth through the *delay trampoline* (delay.c), which is the
 * core's only unbounded-recursion shape, so this stack primarily backs continuation reification.
 */
#include "blight_rt.h"
#include <stdlib.h>
#include <stdio.h>

typedef struct Segment {
  char *base;
  size_t size;
  char *top;
  struct Segment *prev;
} Segment;

static BL_THREAD_LOCAL Segment *g_seg;
static const size_t g_seg_default = 1 << 16; /* 64 KiB initial segment (shared, never mutated) */

static Segment *new_segment(size_t size, Segment *prev) {
  Segment *s = (Segment *)malloc(sizeof(Segment));
  if (!s) { fprintf(stderr, "blight: stack OOM\n"); abort(); }
  s->base = (char *)malloc(size);
  if (!s->base) { fprintf(stderr, "blight: stack OOM\n"); abort(); }
  s->size = size;
  s->top = s->base;
  s->prev = prev;
  return s;
}

void bl_stack_init(void) {
  fprintf(stderr, "[rt] stack_init enter\n"); fflush(stderr); /* TEMP: localize Linux segfault */
  g_seg = new_segment(g_seg_default, NULL);
  fprintf(stderr, "[rt] stack_init ok\n"); fflush(stderr); /* TEMP */
}

void *bl_stack_grow(size_t bytes) {
  if (!g_seg) bl_stack_init();
  /* If the request doesn't fit the current segment, chain a new (at least as large) one. */
  if (g_seg->top + bytes > g_seg->base + g_seg->size) {
    size_t size = g_seg->size;
    while (size < bytes) size *= 2;
    g_seg = new_segment(size, g_seg);
  }
  void *p = g_seg->top;
  g_seg->top += bytes;
  return p;
}
