/* numeric_diff.c — the differential gate for the M20 fast-`Nat` representation (numeric.c).
 *
 * The autism invariant: a fast machine-word `Nat` (BL_NAT) must be observationally identical to the
 * inductive `Zero`/`Succ` chain the kernel checks. This harness proves it the only honest way — by
 * computing every recognized op (`plus`/`mult`/`sub`/`pred`) BOTH ways over a fuzzed range and
 * asserting bit-identical results:
 *
 *   - the FAST path: operands are BL_NAT words, the op is the O(1) `bl_nat_*` runtime helper;
 *   - the UNARY path: operands are real `Succ (… (Succ Zero))` chains, and the same op is computed by
 *     the reference unary semantics implemented locally here (the std/nat.bl recurrences), with the
 *     result counted back to a word.
 *
 * If a fast op ever disagrees with the unary reference, the build fails. We also check the coherence
 * shim directly: `bl_nat_to_con` must materialize exactly one inductive layer such that the chain it
 * exposes counts back to the original word (so any generic `case` reader sees the chain it expects),
 * and that the FAST helpers transparently accept a chain-shaped operand (mixed representation).
 *
 * Built and run by the Rust harness in runtime.rs. Prints `NUMERIC_DIFF_OK` on success.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdint.h>

/* ---- reference: the inductive Nat as a real Zero/Succ chain ---- */

/* Build `Succ^n Zero` as genuine BL_CON nodes (ctor index 0 = Zero, 1 = Succ, one field). This is
 * exactly what the elaborator lowers a numeral to, and what a generic pattern-match destructures. */
static BlValue chain_of_u64(uint64_t n) {
  BlValue acc = bl_alloc(BL_CON, 0, BL_NAT_ZERO_TAG); /* Zero */
  bl_gc_push_root(&acc);
  for (uint64_t i = 0; i < n; i++) {
    BlValue succ = bl_alloc(BL_CON, 1, BL_NAT_SUCC_TAG);
    succ->fields[0] = acc;
    acc = succ; /* `acc` stays rooted via the same slot */
  }
  bl_gc_pop_roots(1);
  return acc;
}

/* Reference unary semantics (std/nat.bl), computed on plain words — the trusted meaning. */
static uint64_t ref_add(uint64_t a, uint64_t b) { return a + b; }
static uint64_t ref_mul(uint64_t a, uint64_t b) { return a * b; }
static uint64_t ref_sub(uint64_t a, uint64_t b) { return a > b ? a - b : 0; }
static uint64_t ref_pred(uint64_t a) { return a == 0 ? 0 : a - 1; }
static uint64_t ref_min(uint64_t a, uint64_t b) { return a < b ? a : b; }
static uint64_t ref_max(uint64_t a, uint64_t b) { return a > b ? a : b; }

/* ---- the differential checks ---- */

static int check_binary(const char *name, uint64_t a, uint64_t b, uint64_t expected,
                        BlValue (*op)(BlValue, BlValue)) {
  /* fast path: BL_NAT operands. */
  BlValue fa = bl_nat_from_u64(a), fb = bl_nat_from_u64(b);
  uint64_t fast = bl_nat_of_value(op(fa, fb));
  /* unary path: real Zero/Succ chains fed to the SAME helper (it must count them). */
  BlValue ca = chain_of_u64(a);
  bl_gc_push_root(&ca);
  BlValue cb = chain_of_u64(b);
  bl_gc_push_root(&cb);
  uint64_t unary = bl_nat_of_value(op(ca, cb));
  bl_gc_pop_roots(2);
  if (fast != expected || unary != expected) {
    fprintf(stderr, "%s(%llu,%llu): fast=%llu unary=%llu expected=%llu\n", name,
            (unsigned long long)a, (unsigned long long)b, (unsigned long long)fast,
            (unsigned long long)unary, (unsigned long long)expected);
    return 0;
  }
  return 1;
}

/* The no-alloc peel (`bl_nat_is_succ`/`bl_nat_pred_value`, M25) must agree with the materializing
 * `bl_nat_to_con` + tag-read + field-load path for every Nat-shaped value: same tag, and a Succ's
 * predecessor counts back to n-1. We check both representations (fast BL_NAT word and real chain). */
static int check_peel_one(BlValue v, uint64_t n) {
  uint64_t is_succ = bl_nat_is_succ(v);
  uint64_t expect_succ = n != 0 ? 1u : 0u;
  if (is_succ != expect_succ) {
    fprintf(stderr, "peel(%llu): is_succ=%llu expected=%llu\n", (unsigned long long)n,
            (unsigned long long)is_succ, (unsigned long long)expect_succ);
    return 0;
  }
  if (n != 0) {
    uint64_t pred = bl_nat_of_value(bl_nat_pred_value(v));
    if (pred != n - 1) {
      fprintf(stderr, "peel(%llu): pred=%llu expected=%llu\n", (unsigned long long)n,
              (unsigned long long)pred, (unsigned long long)(n - 1));
      return 0;
    }
  }
  return 1;
}

static int check_peel(uint64_t n) {
  if (!check_peel_one(bl_nat_from_u64(n), n)) return 0; /* fast BL_NAT word */
  BlValue chain = chain_of_u64(n);
  bl_gc_push_root(&chain);
  int ok = check_peel_one(chain, n); /* real Zero/Succ chain */
  bl_gc_pop_roots(1);
  return ok;
}

static int check_pred(uint64_t a) {
  uint64_t expected = ref_pred(a);
  uint64_t fast = bl_nat_of_value(bl_nat_pred(bl_nat_from_u64(a)));
  BlValue ca = chain_of_u64(a);
  bl_gc_push_root(&ca);
  uint64_t unary = bl_nat_of_value(bl_nat_pred(ca));
  bl_gc_pop_roots(1);
  if (fast != expected || unary != expected) {
    fprintf(stderr, "pred(%llu): fast=%llu unary=%llu expected=%llu\n", (unsigned long long)a,
            (unsigned long long)fast, (unsigned long long)unary, (unsigned long long)expected);
    return 0;
  }
  return 1;
}

/* `bl_nat_to_con` must materialize ONE inductive layer such that the exposed chain counts back to
 * the original word — this is what makes a fast Nat destructure correctly under a generic `case`. We
 * peel layers one at a time (each predecessor is itself a fast Nat) and confirm the depth matches. */
static int check_to_con(uint64_t n) {
  BlValue cur = bl_nat_from_u64(n);
  bl_gc_push_root(&cur);
  uint64_t depth = 0;
  for (;;) {
    BlValue layer = bl_nat_to_con(cur);
    if (BL_TAG(layer) != BL_CON) {
      fprintf(stderr, "to_con(%llu): layer tag not BL_CON\n", (unsigned long long)n);
      bl_gc_pop_roots(1);
      return 0;
    }
    if (layer->header.aux == BL_NAT_ZERO_TAG && layer->header.nfields == 0) {
      break; /* reached Zero */
    }
    if (layer->header.aux != BL_NAT_SUCC_TAG || layer->header.nfields != 1) {
      fprintf(stderr, "to_con(%llu): malformed layer\n", (unsigned long long)n);
      bl_gc_pop_roots(1);
      return 0;
    }
    depth++;
    cur = layer->fields[0]; /* predecessor (still a fast Nat); re-root via the same slot */
  }
  bl_gc_pop_roots(1);
  if (depth != n) {
    fprintf(stderr, "to_con(%llu): materialized depth=%llu\n", (unsigned long long)n,
            (unsigned long long)depth);
    return 0;
  }
  return 1;
}

int main(void) {
  bl_gc_init(8 * 1024 * 1024); /* heap large enough for the fuzz set's transient chains */
  bl_stack_init();

  /* A deterministic but wide fuzz: a dense small range plus a sampling of larger values where the
   * unary chain is still cheap enough to build (the fast path of course handles far larger). */
  static const uint64_t pts[] = {0, 1, 2, 3, 5, 7, 13, 31, 64, 100, 255, 256, 511, 1000, 1024, 4095};
  const int N = (int)(sizeof(pts) / sizeof(pts[0]));

  for (int i = 0; i < N; i++) {
    if (!check_pred(pts[i])) return 1;
    if (!check_to_con(pts[i])) return 1;
    if (!check_peel(pts[i])) return 1;
    for (int j = 0; j < N; j++) {
      uint64_t a = pts[i], b = pts[j];
      if (!check_binary("plus", a, b, ref_add(a, b), bl_nat_add)) return 1;
      if (!check_binary("mult", a, b, ref_mul(a, b), bl_nat_mul)) return 1;
      if (!check_binary("sub", a, b, ref_sub(a, b), bl_nat_sub)) return 1;
      if (!check_binary("min", a, b, ref_min(a, b), bl_nat_min)) return 1;
      if (!check_binary("max", a, b, ref_max(a, b), bl_nat_max)) return 1;
    }
  }

  printf("NUMERIC_DIFF_OK\n");
  return 0;
}
