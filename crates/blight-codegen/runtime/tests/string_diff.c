/* string_diff.c — the differential gate for the A2 packed-`String` representation (numeric.c).
 *
 * The autism invariant: a packed `String` (BL_STRING) must be observationally identical to the
 * inductive `empty`/`push` cons-list of `Nat` codepoints the kernel checks (std/string.bl). This
 * harness proves it the only honest way — by building the SAME codepoint sequence BOTH ways and
 * asserting every observation agrees bit-for-bit:
 *
 *   - the PACKED path: a single BL_STRING built by `bl_string_from_codepoints`;
 *   - the INDUCTIVE path: a real `push cp0 (push cp1 … empty)` chain of BL_CON nodes whose head
 *     fields are `Nat` codepoints (exactly what the elaborator lowers a string literal to, and what
 *     a generic pattern-match destructures).
 *
 * Checks:
 *   - length (`bl_string_len_of_value`) agrees on both reprs;
 *   - every codepoint (`bl_string_codepoint_at`) agrees on both reprs;
 *   - the coherence shim `bl_string_to_con` materializes exactly one `empty`/`push` layer such that
 *     peeling it (head codepoint Nat + packed tail) reconstructs the original sequence — so any
 *     generic `case` reader sees the cons-list it expects;
 *   - `bl_string_to_con` is the identity on a real `empty`/`push` chain (so chaining it after
 *     `bl_nat_to_con` in the generic destructuring shim is always safe).
 *
 * Built and run by the Rust harness in runtime.rs. Prints `STRING_DIFF_OK` on success.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdint.h>

/* Build the inductive `push cp0 (push cp1 … empty)` chain of `Nat` codepoints — exactly the
 * std/string.bl encoding (empty = ctor 0, 0 fields; push = ctor 1, 2 fields: head Nat, tail String).
 * Built head-last so codepoint `i` ends up at spine depth `i`, matching `bl_string_from_codepoints`. */
static BlValue chain_of_cps(const uint64_t *cps, uint64_t n) {
  BlValue acc = bl_alloc(BL_CON, 0, BL_STRING_EMPTY_TAG); /* empty */
  bl_gc_push_root(&acc);
  for (uint64_t k = 0; k < n; k++) {
    uint64_t i = n - 1 - k; /* prepend from the end so cp[0] is the outermost push */
    BlValue head = bl_nat_from_u64(cps[i]);
    bl_gc_push_root(&head);
    BlValue push = bl_alloc(BL_CON, 2, BL_STRING_PUSH_TAG);
    push->fields[0] = head;
    push->fields[1] = acc;
    bl_gc_pop_roots(1); /* head now reachable via push */
    acc = push;         /* stays rooted via the same slot */
  }
  bl_gc_pop_roots(1);
  return acc;
}

/* Build a *mixed* spine: `prefix` inductive `push` cells (the first `prefix` codepoints) terminating
 * in a packed BL_STRING for the remaining `n - prefix` codepoints. This is exactly what
 * `string-append "lit" rest` produces — the `(empty) t` arm splices the packed second operand `t` in
 * verbatim as a cons tail. Every direct runtime spine-walker (print/emit/to-cstr) must tolerate it. */
static BlValue mixed_spine(const uint64_t *cps, uint64_t n, uint64_t prefix) {
  if (prefix > n) prefix = n;
  BlValue acc = bl_string_from_codepoints(cps + prefix, n - prefix); /* packed tail */
  bl_gc_push_root(&acc);
  for (uint64_t k = 0; k < prefix; k++) {
    uint64_t i = prefix - 1 - k;
    BlValue head = bl_nat_from_u64(cps[i]);
    bl_gc_push_root(&head);
    BlValue push = bl_alloc(BL_CON, 2, BL_STRING_PUSH_TAG);
    push->fields[0] = head;
    push->fields[1] = acc;
    bl_gc_pop_roots(1);
    acc = push;
  }
  bl_gc_pop_roots(1);
  return acc;
}

static int check_observations(const char *which, BlValue s, const uint64_t *cps, uint64_t n) {
  uint64_t len = bl_string_len_of_value(s);
  if (len != n) {
    fprintf(stderr, "%s: len=%llu expected=%llu\n", which, (unsigned long long)len,
            (unsigned long long)n);
    return 0;
  }
  for (uint64_t i = 0; i < n; i++) {
    uint64_t got = bl_string_codepoint_at(s, i);
    if (got != cps[i]) {
      fprintf(stderr, "%s: cp[%llu]=%llu expected=%llu\n", which, (unsigned long long)i,
              (unsigned long long)got, (unsigned long long)cps[i]);
      return 0;
    }
  }
  /* out-of-range index is total: returns 0, never traps. */
  if (bl_string_codepoint_at(s, n) != 0) {
    fprintf(stderr, "%s: cp[len] not 0 (out-of-range)\n", which);
    return 0;
  }
  return 1;
}

/* `bl_string_to_con` must materialize ONE `empty`/`push` layer such that walking the exposed spine
 * (head Nat + packed tail, peeled one layer at a time) reconstructs the original codepoints. */
static int check_to_con(BlValue s, const uint64_t *cps, uint64_t n) {
  BlValue cur = s;
  bl_gc_push_root(&cur);
  uint64_t depth = 0;
  for (;;) {
    BlValue layer = bl_string_to_con(cur);
    if (BL_TAG(layer) != BL_CON) {
      fprintf(stderr, "to_con: layer tag not BL_CON at depth %llu\n", (unsigned long long)depth);
      bl_gc_pop_roots(1);
      return 0;
    }
    if (layer->header.aux == BL_STRING_EMPTY_TAG && layer->header.nfields == 0) {
      break; /* reached empty */
    }
    if (layer->header.aux != BL_STRING_PUSH_TAG || layer->header.nfields != 2) {
      fprintf(stderr, "to_con: malformed layer at depth %llu\n", (unsigned long long)depth);
      bl_gc_pop_roots(1);
      return 0;
    }
    if (depth >= n) {
      fprintf(stderr, "to_con: spine longer than %llu\n", (unsigned long long)n);
      bl_gc_pop_roots(1);
      return 0;
    }
    uint64_t head = bl_nat_of_value(layer->fields[0]);
    if (head != cps[depth]) {
      fprintf(stderr, "to_con: head[%llu]=%llu expected=%llu\n", (unsigned long long)depth,
              (unsigned long long)head, (unsigned long long)cps[depth]);
      bl_gc_pop_roots(1);
      return 0;
    }
    depth++;
    cur = layer->fields[1]; /* tail (still packed); re-root via the same slot */
  }
  bl_gc_pop_roots(1);
  if (depth != n) {
    fprintf(stderr, "to_con: materialized depth=%llu expected=%llu\n", (unsigned long long)depth,
            (unsigned long long)n);
    return 0;
  }
  return 1;
}

static int check_seq(const uint64_t *cps, uint64_t n) {
  BlValue packed = bl_string_from_codepoints(cps, n);
  bl_gc_push_root(&packed);
  BlValue chain = chain_of_cps(cps, n);
  bl_gc_push_root(&chain);

  int ok = check_observations("packed", packed, cps, n) &&
           check_observations("chain", chain, cps, n) && check_to_con(packed, cps, n);

  /* `bl_string_to_con` is the identity on a real chain (so the generic shim composes). */
  if (ok && bl_string_to_con(chain) != chain) {
    fprintf(stderr, "to_con: not identity on a real empty/push chain\n");
    ok = 0;
  }

  /* Mixed spines: every prefix split (inductive head + packed tail, as `string-append` builds) must
   * observe identically and `to_con`-peel back to the full sequence. */
  for (uint64_t p = 0; ok && p <= n; p++) {
    BlValue mixed = mixed_spine(cps, n, p);
    bl_gc_push_root(&mixed);
    if (!check_observations("mixed", mixed, cps, n) || !check_to_con(mixed, cps, n)) {
      fprintf(stderr, "mixed: failed at prefix=%llu\n", (unsigned long long)p);
      ok = 0;
    }
    bl_gc_pop_roots(1);
  }

  bl_gc_pop_roots(2);
  return ok;
}

int main(void) {
  bl_gc_init(8 * 1024 * 1024);
  bl_stack_init();

  /* empty, single, ascii, multi-byte codepoints, and a longer mixed run. */
  static const uint64_t empty[] = {0};
  static const uint64_t one[] = {65};
  static const uint64_t hi[] = {72, 105};
  static const uint64_t mixed[] = {0, 1, 65, 90, 97, 122, 128, 255, 256, 0x1F600, 1114111};

  if (!check_seq(empty, 0)) return 1;
  if (!check_seq(one, 1)) return 1;
  if (!check_seq(hi, 2)) return 1;
  if (!check_seq(mixed, (uint64_t)(sizeof(mixed) / sizeof(mixed[0])))) return 1;

  /* a wide deterministic run to exercise the buffer and repeated peeling. */
  static uint64_t big[512];
  for (uint64_t i = 0; i < 512; i++) big[i] = (i * 2654435761u) & 0x1FFFFF; /* up to 21-bit cps */
  if (!check_seq(big, 512)) return 1;

  printf("STRING_DIFF_OK\n");
  return 0;
}
