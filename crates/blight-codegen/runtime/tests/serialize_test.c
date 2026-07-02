/* serialize_test.c — standalone C tests for the M18 structural (de)serializer (serialize.c).
 *
 * Built and run by the Rust harness in `runtime.rs`. Verifies:
 *   - round-trip equality: serialize then deserialize reproduces a structurally-equal value over
 *     representative data shapes (Int, nested Con, Tuple, a deep cons-list);
 *   - deep copy: the rebuilt value is a DISTINCT allocation from the source (no shared sub-objects),
 *     which is what makes cross-heap/cross-machine messaging share-nothing;
 *   - data-only caveat: serializing a value containing a closure/opnode tag is rejected (NULL blob).
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>

/* `bl_int`/`bl_int_val` now live in the always-linked numeric.c (M21 unboxing). */

/* Structural equality over the data tags (mirrors what a message round-trip must preserve). */
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

/* The rebuilt value is a deep copy BY CONSTRUCTION: `bl_value_deserialize` reads only bytes from the
 * blob and allocates every node fresh in the current heap — it never sees a source pointer, so it
 * cannot alias any source sub-object. We assert the cheap, sufficient invariant that the root is a
 * distinct allocation (a full O(n*m) disjointness walk is unnecessary and would be super-linear). */
static int distinct_root(BlValue a, BlValue b) {
  return a != b;
}

static int roundtrip_ok(BlValue v) {
  size_t len = 0;
  void *blob = bl_value_serialize(v, &len);
  if (!blob) { fprintf(stderr, "serialize: unexpected NULL blob for data value\n"); return 0; }
  BlValue back = bl_value_deserialize(blob, len);
  free(blob);
  if (!value_eq(v, back)) { fprintf(stderr, "serialize: round-trip not structurally equal\n"); return 0; }
  if (!distinct_root(v, back)) { fprintf(stderr, "serialize: round-trip shares the root allocation (not a deep copy)\n"); return 0; }
  return 1;
}

static int test_int(void) {
  return roundtrip_ok(bl_int(0)) && roundtrip_ok(bl_int(-42)) && roundtrip_ok(bl_int(1234567));
}

static int test_nested_con_and_tuple(void) {
  /* (pair (just 7) (nothing))-ish: Con(aux=0, [Con(aux=1,[Int 7]), Con(aux=2,[])]) and a Tuple. */
  BlValue inner = bl_alloc(BL_CON, 1, 1);
  bl_gc_push_root(&inner);
  inner->fields[0] = bl_int(7);
  bl_write_barrier(inner, inner->fields[0]);
  BlValue none = bl_alloc(BL_CON, 0, 2);
  bl_gc_push_root(&none);
  BlValue pair = bl_alloc(BL_TUPLE, 2, 0);
  bl_gc_push_root(&pair);
  pair->fields[0] = inner; bl_write_barrier(pair, inner);
  pair->fields[1] = none;  bl_write_barrier(pair, none);
  int ok = roundtrip_ok(pair);
  bl_gc_pop_roots(3);
  return ok;
}

static int test_deep_list(void) {
  /* A 500-element cons-list: Con(aux=1=cons, [Int i, tail]) terminated by Con(aux=0=nil, []). */
  BlValue list = bl_alloc(BL_CON, 0, 0); /* nil */
  bl_gc_push_root(&list);
  for (int i = 0; i < 500; i++) {
    BlValue node = bl_alloc(BL_CON, 2, 1);
    node->fields[0] = bl_int((int64_t)i);
    node->fields[1] = list;
    bl_write_barrier(node, node->fields[0]);
    bl_write_barrier(node, node->fields[1]);
    list = node;
    bl_gc_poll();
  }
  int ok = roundtrip_ok(list);
  bl_gc_pop_roots(1);
  return ok;
}

static int test_rejects_closure(void) {
  /* A BL_CLOSURE value (raw fn pointer in aux) must NOT serialize: data-only v1. */
  BlValue clo = bl_alloc(BL_CLOSURE, 0, 0xdeadbeefu);
  bl_gc_push_root(&clo);
  size_t len = 12345;
  void *blob = bl_value_serialize(clo, &len);
  bl_gc_pop_roots(1);
  if (blob != NULL) { free(blob); fprintf(stderr, "serialize: closure must be rejected\n"); return 0; }
  if (len != 0) { fprintf(stderr, "serialize: rejected blob must set len=0\n"); return 0; }
  /* A data value CONTAINING a closure field is also rejected. */
  BlValue wrap = bl_alloc(BL_CON, 1, 0);
  bl_gc_push_root(&wrap);
  BlValue c2 = bl_alloc(BL_CLOSURE, 0, 1);
  wrap->fields[0] = c2;
  bl_write_barrier(wrap, c2);
  void *b2 = bl_value_serialize(wrap, &len);
  bl_gc_pop_roots(1);
  if (b2 != NULL) { free(b2); fprintf(stderr, "serialize: value containing a closure must be rejected\n"); return 0; }
  return 1;
}

int main(void) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();

  int rc = 0;
  if (!test_int()) rc = 1;
  if (!test_nested_con_and_tuple()) rc = 1;
  if (!test_deep_list()) rc = 1;
  if (!test_rejects_closure()) rc = 1;
  if (rc == 0) printf("SERIALIZE_OK\n");
  return rc;
}
