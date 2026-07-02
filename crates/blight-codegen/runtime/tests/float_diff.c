/* float_diff.c — the differential gate for the M23 fixed-point `Float` helpers (numeric.c).
 *
 * The autism invariant (mirrors numeric_diff.c for `Nat`): the fast `bl_float_*` helpers must be
 * observationally identical to the *checked* meaning of std/float.bl — exact base-10 fixed-point
 * rational arithmetic on the scaled `Int` mantissa (`mkfloat (mantissa Int)`, SCALE = 10^6). This
 * harness computes every recognized op (`add`/`sub`/`mul`/`div`/`neg`) BOTH ways over a fuzzed grid
 * and asserts bit-identical mantissas:
 *
 *   - the FAST path: a `(mkfloat m)` value, the op is the O(1) `bl_float_*` runtime helper;
 *   - the REFERENCE: the same fixed-point arithmetic computed locally in `int64_t`/`__int128` exactly
 *     as std/float.bl specifies (`int+`, `int-`, `int/ (int* x y) SCALE`, …).
 *
 * If a fast op ever disagrees with the reference, the build fails. We deliberately do NOT compare
 * against IEEE `double`: a hardware double cannot be bit-identical to the library's exact base-10
 * fixed point, so a double helper would *fail its own gate* — the whole point of keeping `Float`
 * untrusted library data is that its fast path reproduces the checked rational semantics exactly.
 *
 * We also build the `mkfloat` operands BOTH with a boxed `BL_INT` field and (via the `bl_int`
 * immediate path) a tagged-immediate field, and require the helper to agree for both — the
 * representation-coherence check that mirrors numeric_diff's chain-vs-word mixing.
 *
 * Built and run by the Rust harness in runtime.rs. Prints `FLOAT_DIFF_OK` on success.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdint.h>

#define SCALE 1000000LL

/* The fast helpers live in numeric.c. */
extern BlValue bl_float_add(BlValue, BlValue);
extern BlValue bl_float_sub(BlValue, BlValue);
extern BlValue bl_float_mul(BlValue, BlValue);
extern BlValue bl_float_div(BlValue, BlValue);
extern BlValue bl_float_neg(BlValue);

/* Build `(mkfloat m)`: a BL_CON, ctor index 0, one field = the scaled Int mantissa. The field is the
 * `Int` `m`; `bl_int` returns a tagged immediate when `m` fits, else a boxed BL_INT — so this
 * exercises both field representations across the fuzz set. The field is rooted across the alloc. */
static BlValue mkfloat(int64_t m) {
  BlValue field = bl_int(m);
  bl_gc_push_root(&field);
  BlValue obj = bl_alloc(BL_CON, 1, 0);
  obj->fields[0] = field;
  bl_gc_pop_roots(1);
  return obj;
}

/* Read the scaled mantissa back out of a `(mkfloat m)` value (immediate-safe via bl_int_val). */
static int64_t mant(BlValue v) { return bl_int_val(bl_obj_field(v, 0)); }

/* Reference fixed-point semantics, exactly std/float.bl on the scaled mantissa. */
static int64_t ref_add(int64_t a, int64_t b) { return a + b; }
static int64_t ref_sub(int64_t a, int64_t b) { return a - b; }
static int64_t ref_mul(int64_t a, int64_t b) { return (int64_t)(((__int128)a * (__int128)b) / SCALE); }
static int64_t ref_div(int64_t a, int64_t b) { return (int64_t)(((__int128)a * (__int128)SCALE) / b); }
static int64_t ref_neg(int64_t a) { return -a; }

static int check_binary(const char *name, int64_t a, int64_t b, int64_t expected,
                        BlValue (*op)(BlValue, BlValue)) {
  BlValue fa = mkfloat(a);
  bl_gc_push_root(&fa);
  BlValue fb = mkfloat(b);
  bl_gc_push_root(&fb);
  int64_t fast = mant(op(fa, fb));
  bl_gc_pop_roots(2);
  if (fast != expected) {
    fprintf(stderr, "%s(%lld,%lld): fast=%lld expected=%lld\n", name, (long long)a, (long long)b,
            (long long)fast, (long long)expected);
    return 0;
  }
  return 1;
}

static int check_neg(int64_t a) {
  BlValue fa = mkfloat(a);
  bl_gc_push_root(&fa);
  int64_t fast = mant(bl_float_neg(fa));
  bl_gc_pop_roots(1);
  if (fast != ref_neg(a)) {
    fprintf(stderr, "neg(%lld): fast=%lld expected=%lld\n", (long long)a, (long long)fast,
            (long long)ref_neg(a));
    return 0;
  }
  return 1;
}

int main(void) {
  bl_gc_init(8 * 1024 * 1024);
  bl_stack_init();

  /* A deterministic but wide fuzz over scaled mantissas: whole numbers, fractions, and negatives,
   * plus values large enough to stress the __int128 mul/div intermediate (but within the i64
   * mantissa range so the reference and helper share the exact same arithmetic). */
  static const int64_t pts[] = {
      0,        1,         SCALE,        -SCALE,      2 * SCALE,   3500000,    -3500000,
      500000,   -500000,   1500000,      10 * SCALE,  -10 * SCALE, 123456789,  -123456789,
      999999,   -999999,   7 * SCALE,    1000000000LL,
  };
  const int N = (int)(sizeof(pts) / sizeof(pts[0]));

  for (int i = 0; i < N; i++) {
    if (!check_neg(pts[i])) return 1;
    for (int j = 0; j < N; j++) {
      int64_t a = pts[i], b = pts[j];
      if (!check_binary("add", a, b, ref_add(a, b), bl_float_add)) return 1;
      if (!check_binary("sub", a, b, ref_sub(a, b), bl_float_sub)) return 1;
      if (!check_binary("mul", a, b, ref_mul(a, b), bl_float_mul)) return 1;
      if (b != 0 && !check_binary("div", a, b, ref_div(a, b), bl_float_div)) return 1;
    }
  }

  printf("FLOAT_DIFF_OK\n");
  return 0;
}
