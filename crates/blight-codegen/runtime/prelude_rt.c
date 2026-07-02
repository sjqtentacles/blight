/* prelude_rt.c — runtime entry shim and primitive value constructors (spec §7).
 *
 * Provides the C `main` that initializes the heap and stack, calls the compiled program's entry
 * (`bl_program_entry`, emitted by codegen), and prints the resulting value. Also the small set of
 * value constructors the codegen and tests rely on (boxed integers, constructors) and the value
 * printers.
 *
 * The `main` definition is guarded by `BL_NO_MAIN` so the host driver can compile this file purely
 * for its constructors/printers (`-DBL_NO_MAIN`) and supply its own result-type-aware `main`
 * (e.g. calling `bl_print_string` for a `String`-typed program). When `BL_NO_MAIN` is undefined
 * (the default), the historical 64 MiB-heap numeric `main` is emitted, so existing link sites are
 * unaffected.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

/* Decode a unary `Nat` (`Zero`=ctor 0 / `Succ`=ctor 1) to its integer value, counting Succ depth
 * iteratively. Non-Nat or malformed chains return the accumulated count so far. */
static uint64_t bl_nat_to_u64(BlValue v) {
  if (v && bl_obj_tag(v) == BL_NAT) return bl_obj_aux(v);
  uint64_t n = 0;
  BlValue cur = v;
  while (cur && bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == 1 && bl_obj_nfields(cur) == 1) {
    n++;
    cur = bl_obj_field(cur, 0);
  }
  /* A recognized `Nat` materializes lazily: `bl_nat_to_con` peels one `Succ` whose predecessor is a
   * fast `Nat`, so a partially-walked chain can terminate at a fast Nat carrying the rest. */
  if (cur && bl_obj_tag(cur) == BL_NAT) n += bl_obj_aux(cur);
  return n;
}

/* Print a value for the test harness: a Nat (Zero/Succ chain) is printed as its numeral; an INT as
 * its integer; otherwise the constructor index. Counts Succ depth iteratively. */
static void bl_print(BlValue v) {
  if (v == NULL) { printf("<null>\n"); return; }
  switch (bl_obj_tag(v)) {
    case BL_INT:
      printf("%" PRId64 "\n", (int64_t)bl_obj_aux(v));
      return;
    case BL_NAT:
      /* A fast machine-word Nat (numeric.c, M20; immediate or boxed): numeral lives in `aux`. */
      printf("%" PRIu64 "\n", bl_obj_aux(v));
      return;
    case BL_CON: {
      /* Convention: constructor index 0 = Zero (0 fields), index 1 = Succ (1 field). */
      uint64_t n = 0;
      BlValue cur = v;
      while (bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == 1 && bl_obj_nfields(cur) == 1) {
        n++;
        cur = bl_obj_field(cur, 0);
      }
      if (bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == 0) {
        printf("%" PRIu64 "\n", n);
      } else if (bl_obj_tag(cur) == BL_NAT) {
        /* A recognized `Nat`: `bl_nat_to_con` peels one `Succ` whose predecessor is a fast `Nat`,
         * so the chain can terminate at a fast Nat carrying the remaining count (M20 coherence). */
        printf("%" PRIu64 "\n", n + bl_obj_aux(cur));
      } else {
        printf("con#%" PRIu64 "\n", bl_obj_aux(v));
      }
      return;
    }
    case BL_TUPLE: {
      printf("(");
      for (uint32_t i = 0; i < bl_obj_nfields(v); i++) {
        if (i) printf(", ");
        BlValue f = bl_obj_field(v, i);
        if (f && bl_obj_tag(f) == BL_INT) printf("%" PRId64, (int64_t)bl_obj_aux(f));
        else if (f && bl_obj_tag(f) == BL_NAT) printf("%" PRIu64, bl_obj_aux(f));
        else if (f && bl_obj_tag(f) == BL_CON) printf("con#%" PRIu64, bl_obj_aux(f));
        else printf("?");
      }
      printf(")\n");
      return;
    }
    default:
      printf("<value tag %u>\n", bl_obj_tag(v));
  }
}

/* Print a `String` (std/string.bl) as text. A `String` is a cons-list with `empty` = ctor index 0
 * (0 fields) and `push` = ctor index 1 (2 fields: a codepoint `Nat` in field[0], the rest in
 * field[1]). Walk the spine, decode each codepoint Nat to a byte, and write it. A trailing newline
 * is emitted so the output is line-terminated like the numeric printer. Codepoints are written as
 * raw bytes (so ASCII renders directly); values >255 are truncated to a byte, which is sufficient
 * for the ASCII fragment the language currently models. */
void bl_print_string(BlValue s) {
  /* A packed BL_STRING is read directly from its codepoint buffer (O(1)/codepoint, no spine
   * materialization); a packed value may also appear as a *tail* spliced in by `string-append`
   * (whose `(empty) t` arm returns the second operand verbatim), so we re-check each step.
   * Observationally identical to fully walking the `empty`/`push` cons-list. */
  BlValue cur = s;
  for (;;) {
    if (cur && !bl_is_imm(cur) && bl_obj_tag(cur) == BL_STRING) {
      uint64_t n = bl_string_len_of_value(cur);
      for (uint64_t i = 0; i < n; i++) {
        putchar((int)(unsigned char)bl_string_codepoint_at(cur, i));
      }
      break;
    }
    if (!(cur && bl_obj_tag(cur) == BL_CON && bl_obj_aux(cur) == 1 && bl_obj_nfields(cur) == 2)) {
      break;
    }
    putchar((int)(unsigned char)bl_nat_to_u64(bl_obj_field(cur, 0)));
    cur = bl_obj_field(cur, 1);
  }
  putchar('\n');
}

/* Exported wrapper around the (static) numeric/constructor printer, so a host-authored `main`
 * (driver.rs) can select it for non-`String` results without `bl_print` itself being linkable. */
void bl_print_default(BlValue v) {
  bl_print(v);
}

/* ---- foreign FFI demo (spec §7.6) ---- *
 * `bl_foreign_answer` is the C symbol behind the example `(foreign answer Nat "bl_foreign_answer")`.
 * It builds and returns the unary `Nat` 42 (Zero = ctor 0, Succ = ctor 1 over one field), proving
 * that a trusted external C function can hand a fully-formed Blight value back to compiled code. The
 * partial Succ-chain is kept rooted across each `bl_alloc` so a collection triggered mid-build never
 * frees the in-progress value. */
BlValue bl_foreign_answer(void) {
  BlValue acc = bl_alloc(BL_CON, 0, 0); /* Zero */
  bl_gc_push_root(&acc);
  for (int i = 0; i < 42; i++) {
    BlValue succ = bl_alloc(BL_CON, 1, 1); /* Succ _ */
    succ->fields[0] = acc;
    acc = succ;
  }
  bl_gc_pop_roots(1);
  return acc;
}

/* The compiled program's entry point, emitted by codegen. Returns the program's result value. */
extern BlValue bl_program_entry(void);

#ifndef BL_NO_MAIN
int main(void) {
  bl_gc_init(64 * 1024 * 1024); /* 64 MiB heap */
  bl_stack_init();
  BlValue result = bl_program_entry();
  bl_print(result);
  /* Opt-in GC churn signal for the bench harness. Gated behind BL_GC_STATS so it is off by default;
   * written to stderr so it never contaminates stdout (the correctness golden). */
  if (getenv("BL_GC_STATS")) {
    fprintf(stderr,
            "BL_GC_STATS collections=%zu minor=%zu major=%zu grows=%zu promoted_bytes=%zu "
            "bytes_allocated=%zu compacting=%d shrinks=%zu old_capacity=%zu old_live=%zu "
            "peak_old_reserved=%zu\n",
            bl_gc_collections(), bl_gc_minor(), bl_gc_major(), bl_gc_grows(),
            bl_gc_promoted_bytes(), bl_gc_bytes_allocated(), bl_gc_oldgen_compacting(),
            bl_gc_old_shrinks(), bl_gc_old_capacity(), bl_gc_old_live_bytes(),
            bl_gc_peak_old_reserved_bytes());
  }
  return 0;
}
#endif /* BL_NO_MAIN */
