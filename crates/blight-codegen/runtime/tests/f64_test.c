/* f64_test.c — sanity/regression check for the L2 `F64` foreign hatch (numeric.c, std/f64.bl).
 *
 * Unlike float_diff.c/numeric_diff.c, this is NOT a differential gate: `F64` is a deliberately
 * UNVERIFIED escape hatch (spec §7.6, Design B) with no independent reference to diff against — a
 * hardware `double` IS the ground truth here, there is no second implementation to disagree with.
 * This harness instead pins the observable behavior of every `bl_f64_*` symbol against literal C
 * `double` arithmetic, so a future refactor of numeric.c cannot silently break the hatch.
 *
 * Also exercises the representation contract from std/f64.bl's header directly: a boxed `F64` must
 * be bit-for-bit a `bl_int` box of the `double`'s raw bit pattern (never a numeric truncation), for
 * BOTH the tagged-immediate and heap-boxed `BL_INT` cases.
 *
 * Built and run by the Rust harness in runtime.rs. Prints `F64_OK` on success.
 */
#include "blight_rt.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern BlValue bl_f64_of_int(BlValue);
extern BlValue bl_f64_round(BlValue);
extern BlValue bl_f64_add(BlValue);
extern BlValue bl_f64_sub(BlValue);
extern BlValue bl_f64_mul(BlValue);
extern BlValue bl_f64_div(BlValue);
extern BlValue bl_f64_neg(BlValue);
extern BlValue bl_f64_lt(BlValue);
extern BlValue bl_f64_eq(BlValue);

/* Mirrors std/f64.bl's representation contract exactly (independently reimplemented here, not
 * `#include`d from numeric.c, so this harness would catch numeric.c drifting off that contract). */
static BlValue f64_of(double d) {
  int64_t bits;
  memcpy(&bits, &d, sizeof(bits));
  return bl_int(bits);
}
static double f64_val(BlValue v) {
  int64_t bits = bl_int_val(v);
  double d;
  memcpy(&d, &bits, sizeof(d));
  return d;
}

/* Build a `(Pair F64 F64)`-shaped BL_CON (ctor index 0, two fields) — exactly what `mk-pair` builds
 * and what lower.rs packs a binary `foreign` op's two operands into (see numeric.c's file header). */
static BlValue pair_of(BlValue a, BlValue b) {
  bl_gc_push_root(&a);
  bl_gc_push_root(&b);
  BlValue obj = bl_alloc(BL_CON, 2, 0);
  obj->fields[0] = a;
  obj->fields[1] = b;
  bl_gc_pop_roots(2);
  return obj;
}

static int failed = 0;

static void expect_f64(const char *what, double got, double want) {
  if (got != want) {
    fprintf(stderr, "%s: got %.17g want %.17g\n", what, got, want);
    failed = 1;
  }
}

static void expect_int(const char *what, int64_t got, int64_t want) {
  if (got != want) {
    fprintf(stderr, "%s: got %lld want %lld\n", what, (long long)got, (long long)want);
    failed = 1;
  }
}

int main(void) {
  bl_gc_init(8 * 1024 * 1024);
  bl_stack_init();

  /* Conversion is a genuine numeric injection (5 -> 5.0), not a bit reinterpret: `bl_int(5)`'s
   * payload (the integer 5) must NOT equal `f64_of(5.0)`'s payload (5.0's IEEE bit pattern). */
  BlValue five_int = bl_int(5);
  BlValue five_f64 = bl_f64_of_int(five_int);
  expect_f64("f64_of_int(5)", f64_val(five_f64), 5.0);
  if (bl_int_val(five_int) == bl_int_val(five_f64)) {
    fprintf(stderr, "f64_of_int must NOT be a bit reinterpret of its Int argument\n");
    failed = 1;
  }

  /* Round-trip through round(): exact integers survive exactly. */
  expect_int("round(f64_of_int(5))", bl_int_val(bl_f64_round(five_f64)), 5);
  expect_int("round(f64_of_int(-7))", bl_int_val(bl_f64_round(bl_f64_of_int(bl_int(-7)))), -7);

  /* Arithmetic: exactly-representable values, checked against literal C double arithmetic. */
  expect_f64("add", f64_val(bl_f64_add(pair_of(f64_of(3.0), f64_of(4.5)))), 3.0 + 4.5);
  expect_f64("sub", f64_val(bl_f64_sub(pair_of(f64_of(10.0), f64_of(3.5)))), 10.0 - 3.5);
  expect_f64("mul", f64_val(bl_f64_mul(pair_of(f64_of(2.5), f64_of(4.0)))), 2.5 * 4.0);
  expect_f64("div", f64_val(bl_f64_div(pair_of(f64_of(7.0), f64_of(2.0)))), 7.0 / 2.0);
  expect_f64("neg", f64_val(bl_f64_neg(f64_of(3.5))), -3.5);

  /* IEEE-754 division-by-zero semantics: never a trap, always +-Inf per the hardware. */
  double inf_check = 1.0 / 0.0;
  expect_f64("div_by_zero", f64_val(bl_f64_div(pair_of(f64_of(1.0), f64_of(0.0)))), inf_check);

  /* Rounding: ties away from zero (std/f64.bl / numeric.c's documented convention). */
  expect_int("round(2.5)", bl_int_val(bl_f64_round(f64_of(2.5))), 3);
  expect_int("round(-2.5)", bl_int_val(bl_f64_round(f64_of(-2.5))), -3);
  expect_int("round(2.4)", bl_int_val(bl_f64_round(f64_of(2.4))), 2);
  expect_int("round(-2.4)", bl_int_val(bl_f64_round(f64_of(-2.4))), -2);

  /* Comparison flags are `Int` (1/0), never a Bool, mirroring std/int.bl. */
  expect_int("eq(3,3)", bl_int_val(bl_f64_eq(pair_of(f64_of(3.0), f64_of(3.0)))), 1);
  expect_int("eq(3,4)", bl_int_val(bl_f64_eq(pair_of(f64_of(3.0), f64_of(4.0)))), 0);
  expect_int("lt(3,4)", bl_int_val(bl_f64_lt(pair_of(f64_of(3.0), f64_of(4.0)))), 1);
  expect_int("lt(4,3)", bl_int_val(bl_f64_lt(pair_of(f64_of(4.0), f64_of(3.0)))), 0);

  /* IEEE equality: NaN != NaN, unlike the fixed-point `Float`'s exact-mantissa equality. */
  double nan_bits_d;
  {
    int64_t raw = (int64_t)0x7ff8000000000000ULL; /* a canonical quiet NaN bit pattern */
    memcpy(&nan_bits_d, &raw, sizeof(nan_bits_d));
  }
  BlValue nan_val = f64_of(nan_bits_d);
  expect_int("eq(NaN,NaN)", bl_int_val(bl_f64_eq(pair_of(nan_val, nan_val))), 0);

  /* Representation contract: the SAME bit pattern round-trips whether the box is a tagged immediate
   * or heap-allocated (`bl_int`/`bl_int_val` already guarantee this generically; pin it here too so a
   * future change to that guarantee cannot silently break `F64` specifically). A small integral
   * double's bit pattern is itself a small (positive) i64, so it is very likely an immediate; a
   * fractional double's bit pattern is a large i64 essentially guaranteed to be heap-boxed. */
  expect_f64("small (likely-immediate) round-trip", f64_val(f64_of(1.0)), 1.0);
  expect_f64("large (heap-boxed) round-trip", f64_val(f64_of(0.1)), 0.1);

  if (failed) {
    fprintf(stderr, "F64 test FAILED\n");
    return 1;
  }
  printf("F64_OK\n");
  return 0;
}
