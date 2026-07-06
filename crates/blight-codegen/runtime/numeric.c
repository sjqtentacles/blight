/* numeric.c — machine-word natural numbers (M20, zero-TCB performance).
 *
 * The kernel and re-checker only ever know the inductive `Nat` (`Zero`/`Succ`, std/nat.bl): every
 * proof and every `--recheck` is against that unary semantics, so nothing here is *trusted*. This
 * file is a pure *backend representation* optimization living entirely in the untrusted runtime: a
 * `Nat` value can be carried as a single machine word (a BL_NAT object, value in `header.aux`, zero
 * fields) instead of an `n`-deep `Succ` chain, turning `plus`/`mult`/`sub`/`pred` from O(n)
 * allocation into O(1) register arithmetic.
 *
 * The one invariant that makes this safe is OBSERVATIONAL IDENTITY: a BL_NAT must be
 * indistinguishable from the corresponding `Zero`/`Succ` chain to every observer.
 *   - The garbage collector observes only `tag`/`nfields`/`aux`. A BL_NAT has `nfields == 0`, so the
 *     precise collector traces it exactly as it traces BL_INT (no fields to trace) and copies it by
 *     size. No collector change is required.
 *   - The only observers that *destructure* a Nat are the codegen's pattern-match readers
 *     (`emit_case` reads the constructor tag, `load_field` reads a constructor's fields). Those call
 *     `bl_nat_to_con` first, which materializes exactly one inductive layer (`Zero`, or `Succ` of the
 *     fast Nat `n-1`) so the match sees precisely the chain it expects.
 *   - Reading a Nat back to a word (`bl_nat_of_value`) accepts BOTH a BL_NAT (O(1)) and a real chain
 *     (counted), so a fast op fed a chain-shaped argument (e.g. one a foreign function built, or a
 *     user value the recognizer did not produce) still computes the right answer.
 *
 * Correctness is gated by a differential fuzz test (runtime/tests/numeric_diff.c) that runs every op
 * both ways over a wide range and asserts bit-identical results; a divergence fails the build. The
 * trusted kernel gains zero lines.
 */
#include "blight_rt.h"
#include <stdlib.h>
#include <string.h>

/* Core value constructors that the codegen emits at every link site (so they live here in the
 * always-linked numeric unit rather than the optional prelude_rt.c). Each returns a tagged immediate
 * (M21 unboxing) when the payload fits — no heap box, no GC work — and falls back to a heap object
 * otherwise. Observationally identical to a box: `bl_obj_tag`/`bl_obj_aux` agree for both forms. */
BlValue bl_int(int64_t n) {
  uint64_t bits = (uint64_t)n;
  if (bl_imm_fits(bits)) return bl_make_imm(BL_IMM_INT, bits);
  return bl_alloc(BL_INT, 0, bits);
}

int64_t bl_int_val(BlValue v) {
  return (int64_t)bl_obj_aux(v);
}

BlValue bl_con(uint64_t ctor_index, uint32_t nfields) {
  if (nfields == 0 && bl_imm_fits(ctor_index)) return bl_make_imm(BL_IMM_CON, ctor_index);
  return bl_alloc(BL_CON, nfields, ctor_index);
}

BlValue bl_nat_from_u64(uint64_t n) {
  /* Prefer a tagged immediate (no heap box, no GC work): a fast Nat whose count fits in the 60-bit
   * immediate payload rides in the pointer itself. Only an astronomically large count (>= 2^60)
   * falls back to a zero-field BL_NAT heap object — still GC-safe (traced/copied exactly like
   * BL_INT). Observationally identical either way: `bl_obj_tag` reports BL_NAT and `bl_obj_aux`
   * reports `n` for both forms. */
  if (bl_imm_fits(n)) return bl_make_imm(BL_IMM_NAT, n);
  return bl_alloc(BL_NAT, 0, n);
}

uint64_t bl_nat_of_value(BlValue v) {
  if (v == NULL) return 0;
  /* A fast Nat (immediate or boxed BL_NAT) reads its count in O(1). */
  if (bl_obj_tag(v) == BL_NAT) {
    return bl_obj_aux(v);
  }
  /* Fall back to counting a real `Zero`/`Succ` chain (Succ = ctor index 1, one field). This is the
   * O(n) path, taken only for genuinely chain-shaped inputs; the recognizer keeps hot data in a
   * fast Nat so this is rare. */
  uint64_t n = 0;
  BlValue cur = v;
  while (cur && bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == BL_NAT_SUCC_TAG &&
         bl_obj_nfields(cur) == 1) {
    n++;
    cur = bl_obj_field(cur, 0);
  }
  return n;
}

BlValue bl_nat_add(BlValue a, BlValue b) {
  return bl_nat_from_u64(bl_nat_of_value(a) + bl_nat_of_value(b));
}

BlValue bl_nat_mul(BlValue a, BlValue b) {
  return bl_nat_from_u64(bl_nat_of_value(a) * bl_nat_of_value(b));
}

BlValue bl_nat_sub(BlValue a, BlValue b) {
  uint64_t x = bl_nat_of_value(a);
  uint64_t y = bl_nat_of_value(b);
  return bl_nat_from_u64(x > y ? x - y : 0); /* truncated subtraction, matches std/nat.bl `sub` */
}

BlValue bl_nat_pred(BlValue a) {
  uint64_t x = bl_nat_of_value(a);
  return bl_nat_from_u64(x == 0 ? 0 : x - 1); /* truncated predecessor, matches `pred` */
}

BlValue bl_nat_min(BlValue a, BlValue b) {
  uint64_t x = bl_nat_of_value(a);
  uint64_t y = bl_nat_of_value(b);
  return bl_nat_from_u64(x < y ? x : y); /* matches std/nat.bl `min` */
}

BlValue bl_nat_max(BlValue a, BlValue b) {
  uint64_t x = bl_nat_of_value(a);
  uint64_t y = bl_nat_of_value(b);
  return bl_nat_from_u64(x > y ? x : y); /* matches std/nat.bl `max` */
}

/* Peel one inductive layer of a Nat-shaped value WITHOUT materializing a heap `Succ` cell (M25).
 *
 * `bl_nat_is_succ` is the *tag* a generic `case` would switch on (Succ = ctor index 1, Zero = 0),
 * and `bl_nat_pred_value` is the `Succ` arm's single field (the predecessor). Together they let the
 * codegen destructure a fast-`Nat` loop driver (`match fuel [Zero … ][Succ f …]`) by reading/decre-
 * menting the machine word directly — zero allocation per iteration — instead of `bl_nat_to_con`
 * (which allocates a `Succ` box every step). They are observationally identical to the
 * `bl_nat_to_con` + tag-read + field-load path for every Nat-shaped value:
 *   - a fast Nat (immediate or boxed BL_NAT): is-succ iff word > 0; predecessor is the word minus one
 *     as a fresh fast Nat (an immediate for any in-range count — no heap, no GC);
 *   - a real `Zero`/`Succ` chain: is-succ iff the tag is BL_NAT_SUCC_TAG; predecessor is field 0.
 * Anything not Nat-shaped is treated as `Zero` (is-succ 0), matching `bl_nat_of_value`'s totality.
 * The differential gate (numeric_diff.c `check_peel`) proves the peel agrees with `bl_nat_to_con`. */
uint64_t bl_nat_is_succ(BlValue v) {
  if (v == NULL) return 0;
  if (bl_obj_tag(v) == BL_NAT) return bl_obj_aux(v) != 0 ? 1u : 0u;
  /* A real chain: `Succ` is BL_CON, ctor index 1, one field. */
  if (bl_obj_tag(v) == BL_CON && bl_obj_aux(v) == BL_NAT_SUCC_TAG && bl_obj_nfields(v) == 1) {
    return 1u;
  }
  return 0u;
}

BlValue bl_nat_pred_value(BlValue v) {
  if (v == NULL) return bl_nat_from_u64(0);
  if (bl_obj_tag(v) == BL_NAT) {
    uint64_t n = bl_obj_aux(v);
    return bl_nat_from_u64(n == 0 ? 0 : n - 1); /* a fast Nat: predecessor word, no allocation */
  }
  /* A real `Succ` chain node: the predecessor is its single field (already a value). */
  if (bl_obj_tag(v) == BL_CON && bl_obj_aux(v) == BL_NAT_SUCC_TAG && bl_obj_nfields(v) == 1) {
    return bl_obj_field(v, 0);
  }
  return bl_nat_from_u64(0);
}

BlValue bl_nat_to_con(BlValue v) {
  if (v == NULL) return v;
  if (bl_is_imm(v)) {
    /* An immediate flowing into a generic destructuring reader (codegen `emit_case`/`load_field`,
     * which GEP into a real pointer) must be materialized into a heap object first, since those
     * readers dereference raw offsets. Decode the immediate's synthesized header into a boxed object:
     *   - BL_IMM_NAT : one inductive `Zero`/`Succ` layer (see below);
     *   - BL_IMM_CON : the nullary constructor it stands for (a real BL_CON, 0 fields);
     *   - BL_IMM_INT : a boxed BL_INT carrying the same payload.
     * The materialized object is a normal heap value the reader can GEP into; for a fast Nat its
     * predecessor stays a (fast) Nat so matching still peels one layer at a time. */
    switch (bl_imm_kind(v)) {
      case BL_IMM_CON:
        return bl_alloc(BL_CON, 0, bl_imm_payload(v));
      case BL_IMM_INT:
        return bl_alloc(BL_INT, 0, bl_imm_payload(v));
      case BL_IMM_NAT:
        break; /* fall through to the Nat materialization below */
    }
  } else if (BL_TAG(v) != BL_NAT) {
    /* A real boxed `Zero`/`Succ` Con (or any other boxed value) is already in the shape a
     * destructuring reader expects. */
    return v;
  }
  uint64_t n = bl_obj_aux(v);
  if (n == 0) {
    /* Zero: ctor index 0, no fields. Return a *boxed* Con (not an immediate) so the caller can GEP
     * into it. */
    return bl_alloc(BL_CON, 0, BL_NAT_ZERO_TAG);
  }
  /* Succ: ctor index 1, one field = the fast Nat `n-1`. Build the predecessor first and keep it
   * rooted across the second allocation so a collection mid-build cannot free it. Only ONE layer is
   * materialized; the predecessor stays a fast Nat, so repeated matching peels one layer at a time
   * and never forces the whole chain. (`pred` may be an immediate, which is harmless to root: a GC
   * root slot holding an immediate is skipped by the collector.) */
  BlValue pred = bl_nat_from_u64(n - 1);
  bl_gc_push_root(&pred);
  BlValue succ = bl_alloc(BL_CON, 1, BL_NAT_SUCC_TAG);
  succ->fields[0] = pred;
  bl_gc_pop_roots(1);
  return succ;
}

/* ---- fixed-point Float helpers (M23, std/float.bl) ----
 *
 * A `Float` is the UNTRUSTED library type `(defdata Float () (mkfloat (mantissa Int)))`: a one-field
 * constructor (ctor index 0, one field) whose field is an `Int` holding the value scaled by
 * `BL_FLOAT_SCALE = 10^6` (six fractional decimal digits). The kernel and re-checker only ever see
 * that inductive `Data` over the trusted `Int` base — nothing here is trusted.
 *
 * These helpers are the fast path the recognizer (recognize.rs) rewrites the `float-*` wrappers to.
 * They are *not* IEEE hardware doubles: an IEEE `double` cannot be bit-identical to the library's
 * exact base-10 fixed-point rational, so a double path would fail the differential gate that every
 * optimization here must pass. Instead each helper performs the SAME exact `Int` arithmetic on the
 * scaled mantissa that std/float.bl specifies (so the differential test in float_diff.c agrees
 * bit-for-bit), while collapsing the wrapper's `match … match … mkfloat (int op)` tower — two
 * projections plus a box — into one call. The win is the eliminated allocations/branches, not a
 * change of numeric meaning; correctness stays *checked*, never *trusted*.
 *
 * Mantissa arithmetic is plain `int64_t` (matching the kernel's `Int` primitives, which are i64).
 * Multiply uses `__int128` to divide the 10^12-scaled product back down without intermediate
 * overflow; this matches `int/ (int* x y) float-scale` exactly on the representable range. */
#define BL_FLOAT_SCALE 1000000LL

/* Read the scaled `Int` mantissa out of a `(mkfloat m)` value. Field 0 is the `Int`; `bl_int_val`
 * decodes both a boxed BL_INT and a tagged immediate. */
static int64_t bl_float_mantissa_of(BlValue v) {
  return bl_int_val(bl_obj_field(v, 0));
}

/* Build `(mkfloat (int m))`: a one-field `Float` constructor over the scaled mantissa. The boxed
 * `Int` field is kept rooted across the constructor allocation so a GC mid-build cannot free it. */
static BlValue bl_float_of_mantissa(int64_t m) {
  BlValue field = bl_int(m);
  bl_gc_push_root(&field);
  BlValue obj = bl_alloc(BL_CON, 1, 0 /* mkfloat ctor index */);
  obj->fields[0] = field;
  bl_gc_pop_roots(1);
  return obj;
}

BlValue bl_float_add(BlValue a, BlValue b) {
  return bl_float_of_mantissa(bl_float_mantissa_of(a) + bl_float_mantissa_of(b));
}

BlValue bl_float_sub(BlValue a, BlValue b) {
  return bl_float_of_mantissa(bl_float_mantissa_of(a) - bl_float_mantissa_of(b));
}

BlValue bl_float_mul(BlValue a, BlValue b) {
  __int128 prod = (__int128)bl_float_mantissa_of(a) * (__int128)bl_float_mantissa_of(b);
  return bl_float_of_mantissa((int64_t)(prod / BL_FLOAT_SCALE)); /* (x*y)/SCALE */
}

BlValue bl_float_div(BlValue a, BlValue b) {
  __int128 num = (__int128)bl_float_mantissa_of(a) * (__int128)BL_FLOAT_SCALE;
  return bl_float_of_mantissa((int64_t)(num / bl_float_mantissa_of(b))); /* (x*SCALE)/y */
}

BlValue bl_float_neg(BlValue a) {
  return bl_float_of_mantissa(-bl_float_mantissa_of(a)); /* 0 - x */
}

/* ---- UNVERIFIED IEEE-754 `F64` escape hatch (L2, Design B / spec §7.6, std/f64.bl) ----
 *
 * Unlike `Float` above (an ordinary trusted-`Int`-backed `Data` the kernel fully understands), `F64`
 * is a `foreign` postulate: the kernel takes these C symbols on faith and the independent re-checker
 * honestly DECLINES any program mentioning them (see std/f64.bl's header for the full trade-off).
 * There is consequently no differential gate here (there is no independent reference to diff
 * against — that IS the cost of Design B) — correctness rests on this file alone.
 *
 * Representation: a boxed `F64` is bit-for-bit a `BL_INT` box (`bl_int`/`bl_int_val`, already exact
 * for any 64-bit pattern whether immediate or heap-allocated) whose `int64_t` payload is the raw
 * IEEE-754 bit pattern of the `double`, reinterpreted via `memcpy` (never `(int64_t)` cast, which
 * would truncate/round the *value* instead of copying its bits). This needs no new GC tag: a
 * `BL_INT` already has zero fields, so the precise collector traces/copies it exactly like every
 * other opaque machine word.
 *
 * A binary op (`f64-add`/…) receives ONE argument atom carrying a `(Pair F64 F64)` — `lower.rs`
 * packs every multi-operand `foreign` this way (mirrors the `std/bytes.bl` multi-arg-effect-op
 * convention; see `ir.rs`'s `Cir::Foreign` doc comment) — so `bl_obj_field(pair, 0)`/`(pair, 1)` read
 * the two operands exactly as `effects.c`'s `get-byte`/`set-byte` branches do. No rooting is needed
 * anywhere below: every op reads its (non-allocating) `double` operand(s) out to C locals *before*
 * its one `bl_int` allocation, so there is never more than one live heap value in flight — the same
 * shape as `bl_float_add` above. */

/* Reinterpret a boxed `F64`'s raw bit pattern as a `double` (bit-for-bit; never a numeric cast). */
static double bl_f64_bits_of(BlValue v) {
  int64_t bits = bl_int_val(v);
  double d;
  memcpy(&d, &bits, sizeof(d));
  return d;
}

/* Box a `double`'s raw bit pattern as an `F64` (bit-for-bit; never a numeric cast). */
static BlValue bl_f64_of_bits(double d) {
  int64_t bits;
  memcpy(&bits, &d, sizeof(bits));
  return bl_int(bits);
}

BlValue bl_f64_of_int(BlValue i) {
  /* A genuine numeric conversion (5 -> 5.0), NOT a bit reinterpret. */
  return bl_f64_of_bits((double)bl_int_val(i));
}

BlValue bl_f64_round(BlValue x) {
  /* Round-to-nearest, ties away from zero (deliberately not `llround`/<math.h>: every other symbol
   * in this file links with zero extra libraries, and a plain `+/- 0.5` truncate needs none either).
   * Out-of-`int64_t`-range inputs (NaN/Inf/huge magnitude) are UB territory for a real cast in C, but
   * this hatch is explicitly unverified — see the file/module header. */
  double d = bl_f64_bits_of(x);
  return bl_int((int64_t)(d + (d >= 0.0 ? 0.5 : -0.5)));
}

BlValue bl_f64_add(BlValue pair) {
  double a = bl_f64_bits_of(bl_obj_field(pair, 0));
  double b = bl_f64_bits_of(bl_obj_field(pair, 1));
  return bl_f64_of_bits(a + b);
}

BlValue bl_f64_sub(BlValue pair) {
  double a = bl_f64_bits_of(bl_obj_field(pair, 0));
  double b = bl_f64_bits_of(bl_obj_field(pair, 1));
  return bl_f64_of_bits(a - b);
}

BlValue bl_f64_mul(BlValue pair) {
  double a = bl_f64_bits_of(bl_obj_field(pair, 0));
  double b = bl_f64_bits_of(bl_obj_field(pair, 1));
  return bl_f64_of_bits(a * b);
}

BlValue bl_f64_div(BlValue pair) {
  double a = bl_f64_bits_of(bl_obj_field(pair, 0));
  double b = bl_f64_bits_of(bl_obj_field(pair, 1));
  return bl_f64_of_bits(a / b); /* IEEE-754 semantics: b == 0.0 yields +-Inf or NaN, never a trap */
}

BlValue bl_f64_neg(BlValue x) {
  return bl_f64_of_bits(-bl_f64_bits_of(x));
}

BlValue bl_f64_lt(BlValue pair) {
  double a = bl_f64_bits_of(bl_obj_field(pair, 0));
  double b = bl_f64_bits_of(bl_obj_field(pair, 1));
  return bl_int(a < b ? 1 : 0); /* an Int flag, not Bool — mirrors std/int.bl's `int-lt` */
}

BlValue bl_f64_eq(BlValue pair) {
  double a = bl_f64_bits_of(bl_obj_field(pair, 0));
  double b = bl_f64_bits_of(bl_obj_field(pair, 1));
  return bl_int(a == b ? 1 : 0); /* IEEE equality: NaN = NaN is 0, as real IEEE-754 demands */
}

/* ---- packed `String` (A2) ----
 *
 * Like BL_NAT, a packed `String` is a backend representation choice that is OBSERVATIONALLY identical
 * to the inductive `empty`/`push` cons-list std/string.bl defines — the kernel and re-checker only
 * ever see that inductive, so nothing here is trusted; correctness is gated differentially.
 *
 * Storage: a BL_STRING object is a zero-field heap value (so the precise GC copies it by size and
 * traces nothing, exactly like BL_NAT — no collector change). Its `header.aux` points at a
 * `BlStrData` view: a base codepoint array plus the index of this string's head within it and a
 * length. A view's `cps` base is a program-lifetime intern buffer (never freed, never GC-traced);
 * the `bl_string_to_con` tail shares the same base advanced by one, so walking the spine allocates
 * only tiny view structs on the rare generic-destructuring path (mirroring `bl_nat_to_con`'s one
 * `Succ` box per peeled layer). The common consumer (`bl_print_string`) reads the packed buffer
 * directly in O(1)/codepoint and never materializes. */
typedef struct BlStrData {
  const uint64_t *cps; /* shared, program-lifetime codepoint base (interned, never freed) */
  uint64_t off;        /* index of this string's first codepoint within `cps` */
  uint64_t len;        /* number of codepoints from `off` */
} BlStrData;

static BlValue bl_string_from_view(const uint64_t *cps, uint64_t off, uint64_t len) {
  BlStrData *d = (BlStrData *)malloc(sizeof(BlStrData));
  /* The view struct hangs off `header.aux` of a zero-field BL_STRING the GC copies but never traces,
   * so it is intentionally immortal (freeing it would dangle the aux pointer). Tell LSan so. */
  BL_LSAN_IGNORE(d);
  d->cps = cps;
  d->off = off;
  d->len = len;
  BlValue o = bl_alloc(BL_STRING, 0, (uint64_t)(uintptr_t)d);
  return o;
}

BlValue bl_string_from_codepoints(const uint64_t *cps, uint64_t n) {
  /* Intern the codepoints into a program-lifetime buffer so the BlStrData base is stable for the
   * whole run (the literal never changes and is shared by every tail view). */
  uint64_t *buf = NULL;
  if (n != 0) {
    buf = (uint64_t *)malloc((size_t)n * sizeof(uint64_t));
    memcpy(buf, cps, (size_t)n * sizeof(uint64_t));
    BL_LSAN_IGNORE(buf); /* program-lifetime intern buffer, never freed by design (see above) */
  }
  return bl_string_from_view(buf, 0, n);
}

/* Read the BlStrData view of a BL_STRING (NULL for any non-BL_STRING value). */
static BlStrData *bl_string_data(BlValue v) {
  if (v == NULL || bl_is_imm(v) || BL_TAG(v) != BL_STRING) return NULL;
  return (BlStrData *)(uintptr_t)bl_obj_aux(v);
}

uint64_t bl_string_len_of_value(BlValue v) {
  /* Count codepoints, tolerating a *mixed* spine: inductive `push` cells whose tail is eventually a
   * packed BL_STRING (as `string-append`'s `(empty) t` arm can splice one in). */
  uint64_t n = 0;
  BlValue cur = v;
  for (;;) {
    BlStrData *d = bl_string_data(cur);
    if (d != NULL) return n + d->len;
    if (!(cur && bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == BL_STRING_PUSH_TAG &&
          bl_obj_nfields(cur) == 2)) {
      return n;
    }
    n++;
    cur = bl_obj_field(cur, 1);
  }
}

uint64_t bl_string_codepoint_at(BlValue v, uint64_t i) {
  /* Index into a possibly-mixed spine (inductive `push` cells terminating in a packed BL_STRING). */
  BlValue cur = v;
  for (;;) {
    BlStrData *d = bl_string_data(cur);
    if (d != NULL) {
      if (i >= d->len) return 0;
      return d->cps[d->off + i];
    }
    if (!(cur && bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == BL_STRING_PUSH_TAG &&
          bl_obj_nfields(cur) == 2)) {
      return 0;
    }
    if (i == 0) return bl_nat_of_value(bl_obj_field(cur, 0));
    i--;
    cur = bl_obj_field(cur, 1);
  }
}

BlValue bl_string_to_con(BlValue v) {
  BlStrData *d = bl_string_data(v);
  if (d == NULL) {
    /* Already a real `empty`/`push` Con (or some other boxed value): the destructuring reader can
     * GEP into it as-is. */
    return v;
  }
  if (d->len == 0) {
    /* empty: ctor index 0, no fields (a boxed Con so the caller can GEP into it). */
    return bl_alloc(BL_CON, 0, BL_STRING_EMPTY_TAG);
  }
  /* push cp rest: ctor index 1, two fields — field[0] = head codepoint as a fast Nat, field[1] = the
   * BL_STRING tail (same base, advanced by one). Build the children first and keep them rooted across
   * the parent allocation so a collection mid-build cannot free them. Only ONE layer is materialized;
   * the tail stays packed, so repeated matching peels one layer at a time. */
  BlValue head = bl_nat_from_u64(d->cps[d->off]);
  bl_gc_push_root(&head);
  BlValue tail = bl_string_from_view(d->cps, d->off + 1, d->len - 1);
  bl_gc_push_root(&tail);
  BlValue push = bl_alloc(BL_CON, 2, BL_STRING_PUSH_TAG);
  push->fields[0] = head;
  push->fields[1] = tail;
  bl_gc_pop_roots(2);
  return push;
}
