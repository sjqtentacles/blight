/* graphics_test.c — standalone C test for the `Graphics` native handler (roadmap Wave 10 / P2,
 * docs/design-wave4-gobars.md §5 item 4's "deterministic sequence of polled synthetic events in a
 * headless/test SDL driver" requirement).
 *
 * Drives `bl_run_graphics` directly (bypassing the full Blight compiler pipeline, exactly like
 * `effects_test.c` drives `bl_handle`) over a hand-built OpNode chain: `init-window`, then two
 * `poll-input`s. Between the `init-window` resume and the first `poll-input`, the test's own
 * continuation closure calls `SDL_PushEvent` directly to enqueue two synthetic events (a keydown and
 * a quit) — since this test links SDL2 itself, it can inject events the same way a real input device
 * would, with no window/display required (`SDL_VIDEODRIVER=dummy`, set by the Rust harness). The two
 * `poll-input`s must observe them in order: `1` (Up) then `0` (Quit).
 *
 * Built and run by the Rust harness in `runtime.rs`, only when the `graphics` cargo feature test
 * variant is invoked (needs SDL2 dev headers).
 */
#include "blight_rt.h"
#include <SDL.h>
#include <stdio.h>
#include <stdlib.h>

static BlValue mkclo(void *fn, BlValue *caps, uint32_t n) {
  BlValue c = bl_alloc(BL_CLOSURE, n, (uint64_t)(uintptr_t)fn);
  for (uint32_t i = 0; i < n; i++) c->fields[i] = caps ? caps[i] : NULL;
  return c;
}

static BlValue apply1(BlValue clo, BlValue arg) {
  typedef BlValue (*Fn1)(BlValue, BlValue);
  Fn1 fn = (Fn1)(void *)(uintptr_t)clo->header.aux;
  return fn(clo, arg);
}

static BlValue opnode(const char *effect, const char *op, BlValue arg, BlValue kont) {
  BlValue node = bl_perform(effect, op, arg);
  node->fields[1] = kont;
  return node;
}

/* A Pair encoded the same way `mk-pair` would: a 2-field object, generic fields[0]/[1] — the tag/aux
 * value is never inspected by `graphics.c`'s `bl_obj_field` reads, only the field slots are. */
static BlValue mkpair(BlValue x, BlValue y) {
  BlValue p = bl_alloc(BL_CON, 2, 0);
  p->fields[0] = x;
  p->fields[1] = y;
  return p;
}

/* k3: resumed with the second poll-input's result. Must be 0 (SDL_QUIT). Combine with the first
 * result (captured in self->fields[0]) into a single checkable Int: first*10 + second. */
static BlValue k3(BlValue self, BlValue second) {
  int64_t first = bl_int_val(self->fields[0]);
  return bl_int(first * 10 + bl_int_val(second));
}

/* k2: resumed with the first poll-input's result. Must be 1 (Up). Capture it and issue the second
 * poll-input. */
static BlValue k2(BlValue self, BlValue first) {
  (void)self;
  BlValue caps[1] = { first };
  BlValue kont3 = mkclo((void *)k3, caps, 1);
  return opnode("Graphics", "poll-input", bl_alloc(BL_CON, 0, 0), kont3);
}

/* k1: resumed with init-window's Unit result. Inject the two synthetic events, then poll. */
static BlValue k1(BlValue self, BlValue unit_result) {
  (void)self;
  (void)unit_result;
  SDL_Event up = {0};
  up.type = SDL_KEYDOWN;
  up.key.keysym.sym = SDLK_UP;
  if (SDL_PushEvent(&up) < 0) {
    fprintf(stderr, "graphics_test: SDL_PushEvent(up) failed: %s\n", SDL_GetError());
    exit(1);
  }
  SDL_Event quit = {0};
  quit.type = SDL_QUIT;
  if (SDL_PushEvent(&quit) < 0) {
    fprintf(stderr, "graphics_test: SDL_PushEvent(quit) failed: %s\n", SDL_GetError());
    exit(1);
  }
  BlValue kont2 = mkclo((void *)k2, NULL, 0);
  return opnode("Graphics", "poll-input", bl_alloc(BL_CON, 0, 0), kont2);
}

static int test_poll_input_observes_synthetic_events_in_order(void) {
  BlValue dims = mkpair(bl_int(64), bl_int(48));
  BlValue kont1 = mkclo((void *)k1, NULL, 0);
  BlValue body = opnode("Graphics", "init-window", dims, kont1);
  BlValue result = bl_run_graphics(body);
  if (result == NULL || bl_obj_tag(result) != BL_INT || bl_int_val(result) != 10) {
    fprintf(stderr,
            "poll_input_observes_synthetic_events_in_order: expected 10 (Up=1 then Quit=0), got %s\n",
            result ? "wrong value" : "null");
    return 1;
  }
  return 0;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();
  int rc = test_poll_input_observes_synthetic_events_in_order();
  if (rc == 0) printf("GRAPHICS_OK\n");
  return rc;
}
