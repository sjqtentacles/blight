/* string_test.c — standalone C test for `bl_print_string` (Workstream A, string output).
 *
 * Builds a `String` value by hand using the std/string.bl representation — a cons-list with
 * `empty` = constructor index 0 (0 fields) and `push` = constructor index 1 (2 fields: a codepoint
 * `Nat` in field[0] and the rest of the string in field[1]) — then prints it with the runtime's
 * `bl_print_string` and checks the bytes hit stdout. The codepoint `Nat` is the unary `Zero`/`Succ`
 * encoding (`Zero` = ctor 0, `Succ` = ctor 1).
 *
 * `bl_print_string` lives in prelude_rt.c, which is linked here compiled with `-DBL_NO_MAIN` so its
 * own `main` is suppressed and this file's `main` drives the test. The Rust harness in runtime.rs
 * arranges that compile flag.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>

/* `bl_con`/`bl_int` and `bl_print_string` all come from prelude_rt.c (compiled with -DBL_NO_MAIN
 * so its `main` is suppressed and this file's `main` drives the test). */

/* Build a unary Nat for codepoint `cp`. */
static BlValue make_nat(uint64_t cp) {
  BlValue n = bl_con(0, 0); /* Zero */
  bl_gc_push_root(&n);
  for (uint64_t i = 0; i < cp; i++) {
    BlValue s = bl_con(1, 1); /* Succ */
    s->fields[0] = n;
    n = s;
  }
  bl_gc_pop_roots(1);
  return n;
}

/* Build a String from a NUL-terminated C string (ASCII), as a `push`/`empty` chain. */
static BlValue make_string(const char *bytes) {
  /* Build right-to-left so the head is the first character. */
  size_t len = 0;
  while (bytes[len]) len++;
  BlValue s = bl_con(0, 0); /* empty */
  bl_gc_push_root(&s);
  for (size_t i = len; i > 0; i--) {
    BlValue cp = make_nat((unsigned char)bytes[i - 1]);
    bl_gc_push_root(&cp);
    BlValue node = bl_con(1, 2); /* push */
    node->fields[0] = cp;
    node->fields[1] = s;
    s = node;
    bl_gc_pop_roots(1);
  }
  bl_gc_pop_roots(1);
  return s;
}

int main(void) {
  bl_gc_init(8 * 1024 * 1024);
  bl_stack_init();

  /* Redirect stdout to a pipe-like temp file so we can read back exactly what bl_print_string wrote. */
  char tmpl[] = "/tmp/blight_str_test_XXXXXX";
  int fd = mkstemp(tmpl);
  if (fd < 0) { fprintf(stderr, "mkstemp failed\n"); return 1; }
  FILE *saved = stdout;
  FILE *f = fdopen(fd, "w+");
  if (!f) { fprintf(stderr, "fdopen failed\n"); return 1; }
  stdout = f;

  BlValue hello = make_string("hello");
  bl_print_string(hello);
  fflush(f);

  stdout = saved;

  /* Read back the file and compare. */
  rewind(f);
  char buf[64];
  size_t got = fread(buf, 1, sizeof(buf) - 1, f);
  buf[got] = '\0';
  fclose(f);
  remove(tmpl);

  if (got != 6 /* "hello\n" */ ||
      buf[0] != 'h' || buf[1] != 'e' || buf[2] != 'l' || buf[3] != 'l' ||
      buf[4] != 'o' || buf[5] != '\n') {
    fprintf(stderr, "string_test: wrong output: got %zu bytes \"%s\"\n", got, buf);
    return 1;
  }

  printf("STRING_OK\n");
  return 0;
}
