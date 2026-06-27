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
#include <inttypes.h>

BlValue bl_int(int64_t n) {
  BlValue v = bl_alloc(BL_INT, 0, (uint64_t)n);
  return v;
}

int64_t bl_int_val(BlValue v) {
  return (int64_t)v->header.aux;
}

BlValue bl_con(uint64_t ctor_index, uint32_t nfields) {
  return bl_alloc(BL_CON, nfields, ctor_index);
}

/* Decode a unary `Nat` (`Zero`=ctor 0 / `Succ`=ctor 1) to its integer value, counting Succ depth
 * iteratively. Non-Nat or malformed chains return the accumulated count so far. */
static uint64_t bl_nat_to_u64(BlValue v) {
  uint64_t n = 0;
  BlValue cur = v;
  while (cur && cur->header.tag == BL_CON && cur->header.aux == 1 && cur->header.nfields == 1) {
    n++;
    cur = cur->fields[0];
  }
  return n;
}

/* Print a value for the test harness: a Nat (Zero/Succ chain) is printed as its numeral; an INT as
 * its integer; otherwise the constructor index. Counts Succ depth iteratively. */
static void bl_print(BlValue v) {
  if (v == NULL) { printf("<null>\n"); return; }
  switch (v->header.tag) {
    case BL_INT:
      printf("%" PRId64 "\n", (int64_t)v->header.aux);
      return;
    case BL_CON: {
      /* Convention: constructor index 0 = Zero (0 fields), index 1 = Succ (1 field). */
      uint64_t n = 0;
      BlValue cur = v;
      while (cur->header.tag == BL_CON && cur->header.aux == 1 && cur->header.nfields == 1) {
        n++;
        cur = cur->fields[0];
      }
      if (cur->header.tag == BL_CON && cur->header.aux == 0) {
        printf("%" PRIu64 "\n", n);
      } else {
        printf("con#%" PRIu64 "\n", v->header.aux);
      }
      return;
    }
    case BL_TUPLE: {
      printf("(");
      for (uint32_t i = 0; i < v->header.nfields; i++) {
        if (i) printf(", ");
        BlValue f = v->fields[i];
        if (f && f->header.tag == BL_INT) printf("%" PRId64, (int64_t)f->header.aux);
        else if (f && f->header.tag == BL_CON) printf("con#%" PRIu64, f->header.aux);
        else printf("?");
      }
      printf(")\n");
      return;
    }
    default:
      printf("<value tag %u>\n", v->header.tag);
  }
}

/* Print a `String` (std/string.bl) as text. A `String` is a cons-list with `empty` = ctor index 0
 * (0 fields) and `push` = ctor index 1 (2 fields: a codepoint `Nat` in field[0], the rest in
 * field[1]). Walk the spine, decode each codepoint Nat to a byte, and write it. A trailing newline
 * is emitted so the output is line-terminated like the numeric printer. Codepoints are written as
 * raw bytes (so ASCII renders directly); values >255 are truncated to a byte, which is sufficient
 * for the ASCII fragment the language currently models. */
void bl_print_string(BlValue s) {
  BlValue cur = s;
  while (cur && cur->header.tag == BL_CON && cur->header.aux == 1 && cur->header.nfields == 2) {
    uint64_t cp = bl_nat_to_u64(cur->fields[0]);
    putchar((int)(unsigned char)cp);
    cur = cur->fields[1];
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
  return 0;
}
#endif /* BL_NO_MAIN */
