/* graphics.c — the `Graphics` effect's native handler (roadmap Wave 10 / P2,
 * docs/design-wave4-gobars.md §5).
 *
 * Design B (the go-bar's recommendation, chosen over Design A's raw `foreign` SDL bindings): the
 * entire SDL2 dependency is hidden behind five small, purpose-built, single-Pair-packed-argument
 * ops — exactly the shape `Console`/`Bytes`/`Arrays` already ship (`effects.c`'s `bl_run_console`).
 * `bl_run_graphics` mirrors that loop exactly: root `comp`, while it is a bubbling `BL_OPNODE`,
 * dispatch on `bl_op_name_of`, perform the real SDL side effect, then resume via `bl_apply1`. Window/
 * renderer state is thread-local (mirrors `g_arrays`/`g_bytes` in effects.c) and NEVER exposed to
 * Blight code as a raw pointer — a Blight program only ever sees `Unit`/`Int` crossing this boundary,
 * so there is no Blight-visible "is this handle still valid" question to get wrong (the exact runtime
 * safety gap Design A could not close).
 *
 * Only compiled/linked when the `graphics` cargo feature is enabled (`driver.rs` adds this file plus
 * `-lSDL2` only then); the ordinary build and CI's default jobs stay entirely SDL-free. The one CI job
 * that DOES build this runs every op under `SDL_VIDEODRIVER=dummy` (SDL's headless, windowless video
 * backend), which is why every op here degrades harmlessly rather than crashing when there is no real
 * display — the same "total, never traps" discipline every other native-effect handler in this
 * runtime follows.
 */
#include "blight_rt.h"
#include <SDL.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static BL_THREAD_LOCAL SDL_Window *g_window = NULL;
static BL_THREAD_LOCAL SDL_Renderer *g_renderer = NULL;
static BL_THREAD_LOCAL int g_sdl_inited = 0;

static void bl_graphics_ensure_sdl(void) {
  if (g_sdl_inited) return;
  if (SDL_Init(SDL_INIT_VIDEO) != 0) {
    fprintf(stderr, "blight: SDL_Init failed: %s\n", SDL_GetError());
    exit(1);
  }
  g_sdl_inited = 1;
}

/* init-window : (Pair Int Int) -> Unit = (width, height). A second `init-window` while a window is
 * already open is a no-op: `mono.rs`'s double-init inlining guard is the compile-time half of this
 * defense (an effectful op used twice is never silently duplicated by inlining), and this is the
 * runtime half, so even a hand-built OpNode tree that calls it twice cannot leak/duplicate windows. */
static void bl_graphics_init_window(int64_t w, int64_t h) {
  bl_graphics_ensure_sdl();
  if (g_window != NULL) return;
  g_window = SDL_CreateWindow("blight", SDL_WINDOWPOS_UNDEFINED, SDL_WINDOWPOS_UNDEFINED, (int)w,
                               (int)h, SDL_WINDOW_SHOWN);
  if (g_window == NULL) {
    fprintf(stderr, "blight: SDL_CreateWindow failed: %s\n", SDL_GetError());
    exit(1);
  }
  /* Prefer accelerated+vsync; the dummy driver (and some CI/headless hosts) cannot provide either,
   * so fall back to a plain software renderer rather than failing the whole program outright. */
  g_renderer =
      SDL_CreateRenderer(g_window, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);
  if (g_renderer == NULL) g_renderer = SDL_CreateRenderer(g_window, -1, SDL_RENDERER_SOFTWARE);
  if (g_renderer == NULL) {
    fprintf(stderr, "blight: SDL_CreateRenderer failed: %s\n", SDL_GetError());
    exit(1);
  }
  /* Window creation itself queues housekeeping events (SDL_WINDOWEVENT_SHOWN/EXPOSED, and on some
   * backends a synthetic focus event) that would otherwise be the very first thing a program's own
   * `poll-input` observes — burning a real frame's input slot on an event this handler does not even
   * interpret (it already falls through to -1 for any non-quit/non-key type, but only after
   * *consuming* one queue entry). Drain them here, once, right after the window/renderer exist, so
   * the first `poll-input` a Blight program calls only ever sees genuine post-window-open input. */
  SDL_PumpEvents();
  SDL_Event drain;
  while (SDL_PollEvent(&drain)) { /* discard */ }
}

/* poll-input : Unit -> Int. Encodes AT MOST ONE pending SDL event per call (never blocks — a
 * `snake`/`pong`-class frame loop calls this once per frame and must never stall waiting for input):
 *   -1 : no event pending
 *    0 : quit requested (SDL_QUIT — the window close button, or a synthetic test event)
 *    1 : Up/W key pressed         2 : Down/S key pressed
 *    3 : Left/A key pressed       4 : Right/D key pressed
 *   10 : any other key pressed (an escape hatch so no keypress is silently swallowed)
 * This is deliberately the go-bar's explicit minimal scope ("sized to make a snake/pong-class
 * real-time game buildable, not a full 2D-graphics API"), not a general SDL event API. */
static int64_t bl_graphics_poll_input(void) {
  bl_graphics_ensure_sdl();
  SDL_Event ev;
  if (!SDL_PollEvent(&ev)) return -1;
  if (ev.type == SDL_QUIT) return 0;
  if (ev.type == SDL_KEYDOWN) {
    switch (ev.key.keysym.sym) {
      case SDLK_UP:
      case SDLK_w:
        return 1;
      case SDLK_DOWN:
      case SDLK_s:
        return 2;
      case SDLK_LEFT:
      case SDLK_a:
        return 3;
      case SDLK_RIGHT:
      case SDLK_d:
        return 4;
      default:
        return 10;
    }
  }
  return -1;
}

/* clear : Unit -> Unit. Clears the whole frame to black. A no-op before `open-window` (no renderer
 * yet) rather than a crash, matching every other native effect's out-of-range-is-a-no-op discipline. */
static void bl_graphics_clear(void) {
  if (g_renderer == NULL) return;
  SDL_SetRenderDrawColor(g_renderer, 0, 0, 0, 255);
  SDL_RenderClear(g_renderer);
}

/* draw-rect : (Pair Int (Pair Int (Pair Int Int))) -> Unit = (x, (y, (w, h))). Always fills white —
 * a single fixed draw color is the honest minimal scope of this go-bar (no color argument yet; a
 * natural follow-up, not required to make `snake`/`pong` buildable). */
static void bl_graphics_draw_rect(int64_t x, int64_t y, int64_t w, int64_t h) {
  if (g_renderer == NULL) return;
  SDL_Rect r = {(int)x, (int)y, (int)w, (int)h};
  SDL_SetRenderDrawColor(g_renderer, 255, 255, 255, 255);
  SDL_RenderFillRect(g_renderer, &r);
}

/* present : Unit -> Unit. Flips the back buffer to the window (or, under the dummy driver, simply
 * completes with no visible effect — SDL still tracks the call). */
static void bl_graphics_present(void) {
  if (g_renderer == NULL) return;
  SDL_RenderPresent(g_renderer);
}

/* `is_opnode`/`bl_apply1` mirror the identically-named `static` helpers in `effects.c` exactly
 * (effects.c's copies are file-private, and this is a separate translation unit) — the same
 * duplication `runtime/tests/effects_test.c` already uses for its own hand-built OpNode trees. Both
 * are trivial, defined only in terms of the public `BlValue`/`BlHeader` layout, so there is nothing
 * meaningfully "shared logic" to factor out. */
static int bl_gfx_is_opnode(BlValue v) { return v != NULL && !bl_is_imm(v) && BL_TAG(v) == BL_OPNODE; }

static BlValue bl_gfx_apply1(BlValue clo, BlValue arg) {
  /* Route through bl_call_tailcc (lifted code is tailcc on native; a direct C call is the wrong ABI
   * on x86_64 and segfaults). See blight_rt.h. */
  return bl_call_tailcc((void *)(uintptr_t)clo->header.aux, clo, arg);
}

BlValue bl_run_graphics(BlValue comp) {
  bl_gc_push_root(&comp);
  for (;;) {
    if (!bl_gfx_is_opnode(comp)) {
      bl_gc_pop_roots(1);
      return comp; /* pure result */
    }
    const char *opn = bl_op_name_of(comp->header.aux);
    BlValue arg = comp->fields[0];
    BlValue kont = comp->fields[1];
    if (strcmp(opn, "init-window") == 0) {
      int64_t w = bl_int_val(bl_obj_field(arg, 0));
      int64_t h = bl_int_val(bl_obj_field(arg, 1));
      bl_graphics_init_window(w, h);
      BlValue u = bl_alloc(BL_CON, 0, 0);
      comp = (kont == NULL) ? u : bl_gfx_apply1(kont, u);
    } else if (strcmp(opn, "poll-input") == 0) {
      BlValue r = bl_int(bl_graphics_poll_input());
      bl_gc_push_root(&r);
      comp = (kont == NULL) ? r : bl_gfx_apply1(kont, r);
      bl_gc_pop_roots(1);
    } else if (strcmp(opn, "clear") == 0) {
      bl_graphics_clear();
      BlValue u = bl_alloc(BL_CON, 0, 0);
      comp = (kont == NULL) ? u : bl_gfx_apply1(kont, u);
    } else if (strcmp(opn, "draw-rect") == 0) {
      int64_t x = bl_int_val(bl_obj_field(arg, 0));
      BlValue rest = bl_obj_field(arg, 1);
      int64_t y = bl_int_val(bl_obj_field(rest, 0));
      BlValue rest2 = bl_obj_field(rest, 1);
      int64_t w = bl_int_val(bl_obj_field(rest2, 0));
      int64_t h = bl_int_val(bl_obj_field(rest2, 1));
      bl_graphics_draw_rect(x, y, w, h);
      BlValue u = bl_alloc(BL_CON, 0, 0);
      comp = (kont == NULL) ? u : bl_gfx_apply1(kont, u);
    } else if (strcmp(opn, "present") == 0) {
      bl_graphics_present();
      BlValue u = bl_alloc(BL_CON, 0, 0);
      comp = (kont == NULL) ? u : bl_gfx_apply1(kont, u);
    } else {
      /* An operation we do not interpret bubbled to the top: report and stop (mirrors
       * bl_run_console's fallback). */
      fprintf(stderr, "blight: unhandled Graphics operation %s\n", opn);
      bl_gc_pop_roots(1);
      return comp;
    }
  }
}
