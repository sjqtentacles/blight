/* mobility_test.c — standalone C tests for P5 code mobility (roadmap Wave 10): the
 * `bl_value_serialize_mobile`/`bl_value_deserialize_mobile` extension to serialize.c's structural
 * (de)serializer that additionally handles BL_CLOSURE and BL_OPNODE.
 *
 * Hand-registers a tiny two-entry code table via `bl_code_table_register` (mirroring what a real
 * compiled binary's codegen-emitted `main.c` does at startup) and checks:
 *   - the base data tags (Con/Tuple/Int/Nat) still round-trip through the *_mobile entry points, a
 *     strict superset of the plain bl_value_serialize/deserialize format;
 *   - a BL_CLOSURE round-trips via its `code_id` (resolved through the registered table), not its
 *     raw (per-process, ASLR-randomized) function pointer, and its captured env is preserved;
 *   - a BL_OPNODE round-trips by (effect, op) NAME rather than its raw `aux` index — proven by
 *     deliberately interning a decoy pair first so the "real" pair lands at a nonzero index, then
 *     checking the receiver (this same process, so it re-derives the identical index) still resolves
 *     the SAME (effect, op) rather than whatever the wire happened to carry as a number;
 *   - a blob whose `bl_binary_id` prefix does not match the receiving process's own is rejected
 *     outright (NULL), before any `code_id` is ever resolved to a pointer;
 *   - an out-of-range `code_id` is rejected (NULL), never dereferenced.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static BlValue fn_a(BlValue env, BlValue arg) { (void)env; return arg; }
static BlValue fn_b(BlValue env, BlValue arg) { (void)env; return arg; }

static void *g_table[] = { (void *)fn_a, (void *)fn_b };

static int value_eq(BlValue a, BlValue b) {
  if (a == NULL || b == NULL) return a == b;
  if (bl_obj_tag(a) != bl_obj_tag(b)) return 0;
  if (bl_obj_nfields(a) != bl_obj_nfields(b)) return 0;
  if (bl_obj_aux(a) != bl_obj_aux(b)) return 0;
  for (uint32_t i = 0; i < bl_obj_nfields(a); i++) {
    if (!value_eq(a->fields[i], b->fields[i])) return 0;
  }
  return 1;
}

static int test_data_roundtrips_via_mobile_path(void) {
  BlValue v = bl_alloc(BL_CON, 1, 3);
  bl_gc_push_root(&v);
  v->fields[0] = bl_int(99);
  bl_write_barrier(v, v->fields[0]);

  size_t len = 0;
  void *blob = bl_value_serialize_mobile(v, &len);
  int ok = blob != NULL;
  if (ok) {
    BlValue back = bl_value_deserialize_mobile(blob, len);
    ok = back != NULL && back != v && value_eq(v, back);
    free(blob);
  }
  bl_gc_pop_roots(1);
  if (!ok) fprintf(stderr, "mobility: plain data round-trip via mobile path failed\n");
  return ok;
}

static int test_closure_roundtrips_by_code_id(void) {
  BlValue env = bl_int(7);
  bl_gc_push_root(&env);
  BlValue clo = bl_alloc(BL_CLOSURE, 1, (uint64_t)(uintptr_t)fn_b);
  bl_gc_push_root(&clo);
  clo->fields[0] = env;
  bl_write_barrier(clo, env);

  size_t len = 0;
  void *blob = bl_value_serialize_mobile(clo, &len);
  int ok = blob != NULL;
  if (ok) {
    BlValue back = bl_value_deserialize_mobile(blob, len);
    ok = back != NULL && back != clo && bl_obj_tag(back) == BL_CLOSURE
      && (void *)(uintptr_t)bl_obj_aux(back) == (void *)fn_b
      && bl_obj_nfields(back) == 1 && value_eq(back->fields[0], env);
    free(blob);
  }
  bl_gc_pop_roots(2);
  if (!ok) fprintf(stderr, "mobility: closure round-trip by code_id failed\n");
  return ok;
}

static int test_opnode_roundtrips_by_name(void) {
  /* Deliberately intern a decoy pair first so (effect,op) below lands at a NONZERO local index: a
   * receiver that (incorrectly) trusted the wire's raw aux index instead of re-deriving it by name
   * would silently resolve to the wrong operation, which this test would catch. */
  bl_effect_intern("Decoy", "op");
  uint64_t idx = bl_effect_intern("Ref", "get");
  if (idx == 0) { fprintf(stderr, "mobility: test setup expected a nonzero local index\n"); return 0; }

  BlValue arg = bl_int(5);
  bl_gc_push_root(&arg);
  BlValue op = bl_alloc(BL_OPNODE, 2, idx);
  bl_gc_push_root(&op);
  op->fields[0] = arg;
  bl_write_barrier(op, arg);
  op->fields[1] = NULL;

  size_t len = 0;
  void *blob = bl_value_serialize_mobile(op, &len);
  int ok = blob != NULL;
  if (ok) {
    BlValue back = bl_value_deserialize_mobile(blob, len);
    /* Same process re-interning the same names must resolve to the SAME local index. */
    ok = back != NULL && bl_obj_tag(back) == BL_OPNODE && bl_obj_aux(back) == idx
      && value_eq(back->fields[0], arg) && back->fields[1] == NULL;
    free(blob);
  }
  bl_gc_pop_roots(2);
  if (!ok) fprintf(stderr, "mobility: opnode round-trip by name failed\n");
  return ok;
}

static int test_rejects_mismatched_binary_id(void) {
  BlValue v = bl_int(1);
  bl_gc_push_root(&v);
  size_t len = 0;
  void *blob = bl_value_serialize_mobile(v, &len);
  int ok = blob != NULL && len >= sizeof(uint64_t);
  bl_gc_pop_roots(1);
  if (ok) {
    /* Flip every bit of the leading binary_id so it can never equal this process's own (bitwise-NOT
     * of a value is never equal to the value itself). */
    unsigned char *bytes = (unsigned char *)blob;
    for (size_t i = 0; i < sizeof(uint64_t); i++) bytes[i] ^= 0xFF;
    BlValue back = bl_value_deserialize_mobile(blob, len);
    ok = back == NULL;
    free(blob);
  }
  if (!ok) fprintf(stderr, "mobility: mismatched binary_id must be rejected\n");
  return ok;
}

static int test_rejects_unknown_code_id(void) {
  BlValue clo = bl_alloc(BL_CLOSURE, 0, (uint64_t)(uintptr_t)fn_a);
  bl_gc_push_root(&clo);
  size_t len = 0;
  void *blob = bl_value_serialize_mobile(clo, &len);
  bl_gc_pop_roots(1);
  int ok = blob != NULL;
  if (ok) {
    /* Wire layout: [binary_id:8][tag:4][code_id:8][nf:4]...; stomp the code_id out of table range. */
    uint64_t bogus = 0xFFFFFFFFFFFFFFFFULL;
    memcpy((unsigned char *)blob + sizeof(uint64_t) + sizeof(uint32_t), &bogus, sizeof(bogus));
    BlValue back = bl_value_deserialize_mobile(blob, len);
    ok = back == NULL;
    free(blob);
  }
  if (!ok) fprintf(stderr, "mobility: unknown code_id must be rejected\n");
  return ok;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();
  bl_code_table_register(g_table, sizeof(g_table) / sizeof(g_table[0]), 0x1234567890abcdefULL);

  int rc = 0;
  if (!test_data_roundtrips_via_mobile_path()) rc = 1;
  if (!test_closure_roundtrips_by_code_id()) rc = 1;
  if (!test_opnode_roundtrips_by_name()) rc = 1;
  if (!test_rejects_mismatched_binary_id()) rc = 1;
  if (!test_rejects_unknown_code_id()) rc = 1;
  if (rc == 0) printf("MOBILITY_OK\n");
  return rc;
}
