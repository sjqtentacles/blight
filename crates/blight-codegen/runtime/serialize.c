/* serialize.c — structural (de)serialization of Blight values over the 7-tag layout (M18) —
 * UNTRUSTED runtime.
 *
 * Flattens an immutable Blight value to a self-contained byte blob and rebuilds it in the CURRENT
 * thread's heap. This is the boundary primitive for share-nothing messaging: the worker pool (M17)
 * copies arguments/results across thread-local heaps, and the distributed transport (M19) ships the
 * same blobs over a socket. Because Blight values are immutable persistent structures — no cycles,
 * no aliasing, no in-place mutation — a value is a finite tree and (de)serialization is a simple
 * pre-order structural walk.
 *
 * Wire format (little-endian host bytes; same-architecture transport in v1): a pre-order walk
 * emitting, per node, {tag:u32, nfields:u32, aux:u64} followed by its `nfields` children. A NULL
 * child is the sentinel tag 0xFFFFFFFF. Rebuilding allocates fresh objects in the current heap, so
 * the result shares nothing with the source.
 *
 * DATA-ONLY caveat (deliberate, v1 = the Erlang model): only first-order data tags are serializable
 * via `bl_value_serialize`/`bl_value_deserialize` — BL_CON (constructors), BL_TUPLE (products),
 * BL_INT (machine integers), BL_NAT. BL_CLOSURE and BL_OPNODE carry a raw function pointer
 * (`blight_rt.h` BL_CLOSURE/BL_OPNODE) that is meaningful only within one process's address space, so
 * these two functions still reject them (NULL blob) — a transport must reject such a message rather
 * than ship a pointer that would be garbage on the other side. BL_NOW/BL_LATER wrap closures (delay
 * thunks) and remain out of scope entirely.
 *
 * Code/continuation mobility (P5, roadmap Wave 10) IS now implemented, as a SEPARATE, explicitly-
 * opted-into pair of entry points below: `bl_value_serialize_mobile`/`bl_value_deserialize_mobile`
 * additionally accept BL_CLOSURE/BL_OPNODE, resolved through a codegen-emitted stable function-index
 * table (`bl_code_table_register`) and a same-binary-identity check (`bl_binary_id`) rather than
 * shipping raw pointers — see that section's header comment and `docs/design-code-mobility.md` for
 * the full design and security model. The base data-only path above is UNCHANGED by this addition
 * (kept as the default for `bl_pool_submit`'s existing data-only worker transfer, M17/M19), so
 * nothing that already depends on "closures never cross this boundary" is affected.
 */
#include "blight_rt.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#define BL_BLOB_NULL_TAG 0xFFFFFFFFu

typedef struct { unsigned char *buf; size_t len; size_t cap; } Blob;

static void blob_put(Blob *b, const void *p, size_t n) {
  if (b->len + n > b->cap) {
    size_t cap = b->cap ? b->cap * 2 : 256;
    while (cap < b->len + n) cap *= 2;
    b->buf = (unsigned char *)realloc(b->buf, cap);
    if (!b->buf) { fprintf(stderr, "blight: serialize blob OOM\n"); abort(); }
    b->cap = cap;
  }
  memcpy(b->buf + b->len, p, n);
  b->len += n;
}

int bl_value_is_serializable_tag(BlTag t) {
  /* BL_NAT is first-order data (a machine-word Nat, value in aux, zero fields) — it round-trips
   * trivially and is observationally a `Nat`, so it ships like BL_INT/BL_CON/BL_TUPLE. */
  return t == BL_CON || t == BL_TUPLE || t == BL_INT || t == BL_NAT;
}

/* Recursively serialize `v` into `b`. Returns 0 on success, nonzero if a non-data tag is hit. */
static int blob_write(Blob *b, BlValue v) {
  if (v == NULL) {
    uint32_t nil = BL_BLOB_NULL_TAG;
    blob_put(b, &nil, sizeof(nil));
    return 0;
  }
  /* Read through the generic accessors so a tagged immediate (M21) serializes as the header it
   * stands for (tag/nfields=0/aux) — observationally identical to the box it elides. */
  BlTag tag = bl_obj_tag(v);
  if (!bl_value_is_serializable_tag(tag)) return 1;
  uint32_t t = (uint32_t)tag;
  uint32_t nf = bl_obj_nfields(v);
  uint64_t aux = bl_obj_aux(v);
  blob_put(b, &t, sizeof(t));
  blob_put(b, &nf, sizeof(nf));
  blob_put(b, &aux, sizeof(aux));
  for (uint32_t i = 0; i < nf; i++) {
    if (blob_write(b, bl_obj_field(v, i)) != 0) return 1;
  }
  return 0;
}

void *bl_value_serialize(BlValue v, size_t *out_len) {
  Blob b = {0};
  if (blob_write(&b, v) != 0) { free(b.buf); *out_len = 0; return NULL; }
  *out_len = b.len;
  /* Always return non-NULL on success, even for an empty blob (NULL value → one sentinel). */
  return b.buf;
}

/* Rebuild a value from a blob into the CURRENT thread's heap. `*pos` advances. */
static BlValue blob_read(const unsigned char *buf, size_t len, size_t *pos) {
  uint32_t t;
  if (*pos + sizeof(t) > len) { fprintf(stderr, "blight: deserialize blob underrun\n"); abort(); }
  memcpy(&t, buf + *pos, sizeof(t));
  if (t == BL_BLOB_NULL_TAG) { *pos += sizeof(t); return NULL; }
  *pos += sizeof(t);
  uint32_t nf; uint64_t aux;
  if (*pos + sizeof(nf) + sizeof(aux) > len) {
    fprintf(stderr, "blight: deserialize blob underrun\n"); abort();
  }
  memcpy(&nf, buf + *pos, sizeof(nf)); *pos += sizeof(nf);
  memcpy(&aux, buf + *pos, sizeof(aux)); *pos += sizeof(aux);
  /* Rebuild a zero-field fast `Nat` through `bl_nat_from_u64` (numeric.c, always linked) so it
   * round-trips to a tagged immediate (M21). Zero-field BL_INT / nullary BL_CON are rebuilt boxed
   * via `bl_alloc`; that is observationally identical to the immediate form (`bl_obj_tag`/`bl_obj_aux`
   * agree), so the data-only round-trip stays correct without depending on the higher-level
   * constructors (`bl_con`/`bl_int`) that not every link site provides. */
  if (nf == 0 && (BlTag)t == BL_NAT) {
    return bl_nat_from_u64(aux);
  }
  /* Allocate in this thread's heap; root it while filling children (they may allocate and GC). */
  BlValue o = bl_alloc((BlTag)t, nf, aux);
  bl_gc_push_root(&o);
  for (uint32_t i = 0; i < nf; i++) {
    BlValue child = blob_read(buf, len, pos);
    o->fields[i] = child;
    if (child) bl_write_barrier(o, child);
  }
  bl_gc_pop_roots(1);
  return o;
}

BlValue bl_value_deserialize(const void *buf, size_t len) {
  size_t pos = 0;
  return blob_read((const unsigned char *)buf, len, &pos);
}

/* ===================================================================================================
 * P5 code mobility (roadmap Wave 10): mobile (de)serialization of BL_CLOSURE / BL_OPNODE.
 *
 * See `docs/design-code-mobility.md` for the full design and security model. Summary: a closure's
 * `header.aux` (a raw C function pointer) is meaningless outside the process that allocated it, and
 * doubly so under ASLR — this extension resolves it to/from a small `code_id` through a table the
 * codegen-emitted binary registers at startup (`bl_code_table_register`, see blight_rt.h). An
 * OpNode's `header.aux` (a LOCAL first-use-order index into `effects.c`'s `g_ops`) is even less
 * portable than a closure's pointer — it is not even stable across two runs of the identical
 * binary if the two processes intern operations in different orders — so an OpNode instead ships its
 * (effect, op) NAME pair and the receiver re-derives its own local index via `bl_effect_intern`.
 *
 * Every mobile blob is prefixed with the sender's `bl_binary_id` (see registration above), checked
 * BEFORE any `code_id` is resolved to a pointer: a mismatch is a hard reject (`bl_value_deserialize_
 * mobile` returns NULL), never a dereference into a foreign process's function-pointer space. This is
 * the one deliberate scope boundary: mobility works only same-binary-to-same-binary.
 * ===================================================================================================
 */

static void *const *g_code_table;
static uint64_t g_code_table_len;
static uint64_t g_binary_id;

void bl_code_table_register(void *const *table, uint64_t len, uint64_t binary_id) {
  g_code_table = table;
  g_code_table_len = len;
  g_binary_id = binary_id;
}

/* Linear scan: the registered table is the whole program's lifted-function count, typically tens to
 * low hundreds of entries — the same "small and append-only, no hot path" scale as effects.c's
 * `g_ops`, so no hash table is warranted. Returns `(uint64_t)-1` if `fn` is not in the table (never
 * the case for a genuine closure built by this same compiled binary; it IS the case for a closure
 * hand-built by a `foreign`-adjacent or test harness that never registered a table). */
static uint64_t bl_code_id_of(void *fn) {
  for (uint64_t i = 0; i < g_code_table_len; i++) {
    if (g_code_table[i] == fn) return i;
  }
  return (uint64_t)-1;
}

/* Bounds-checked reverse lookup. Returns NULL (never an out-of-bounds read) for an invalid id. */
static void *bl_code_ptr_of(uint64_t id) {
  if (id >= g_code_table_len) return NULL;
  return (void *)g_code_table[id];
}

/* Public wrapper around `bl_code_ptr_of` for OTHER translation units that need to resolve a `code_id`
 * against this same registered table — currently only `worker.c`'s `bl_pool_submit_code` (P4, roadmap
 * Wave 10 / auto-parallelism), which hands a lifted Blight function to a worker by id rather than by
 * raw pointer. Kept as a thin public wrapper (not `bl_code_ptr_of` itself made non-static) so the
 * table's storage stays private to serialize.c, mirroring `bl_op_name_of`'s relationship to
 * `effects.c`'s private `g_ops`. */
void *bl_code_table_resolve(uint64_t code_id) { return bl_code_ptr_of(code_id); }

int bl_value_is_mobile_tag(BlTag t) {
  return bl_value_is_serializable_tag(t) || t == BL_CLOSURE || t == BL_OPNODE;
}

/* A short length-prefixed byte string (used for the OpNode wire format's effect/op names). */
static void blob_put_str(Blob *b, const char *s) {
  uint32_t n = (uint32_t)strlen(s);
  blob_put(b, &n, sizeof(n));
  blob_put(b, s, n);
}

/* Recursively serialize `v` into `b`, extending `blob_write`'s format with BL_CLOSURE/BL_OPNODE
 * branches. Returns 0 on success, nonzero if a tag outside `bl_value_is_mobile_tag` is hit (e.g. a
 * BL_NOW/BL_LATER delay thunk — still out of scope, same as the base data-only serializer) OR a
 * closure's function pointer is not in the registered table (a closure this binary did not itself
 * create — refuse to ship an id that would not resolve to anything sane on the far side). */
static int blob_write_mobile(Blob *b, BlValue v) {
  if (v == NULL) {
    uint32_t nil = BL_BLOB_NULL_TAG;
    blob_put(b, &nil, sizeof(nil));
    return 0;
  }
  BlTag tag = bl_obj_tag(v);
  if (tag == BL_CLOSURE) {
    void *fn = (void *)(uintptr_t)bl_obj_aux(v);
    uint64_t code_id = bl_code_id_of(fn);
    if (code_id == (uint64_t)-1) return 1;
    uint32_t t = (uint32_t)BL_CLOSURE;
    uint32_t nf = bl_obj_nfields(v);
    blob_put(b, &t, sizeof(t));
    blob_put(b, &code_id, sizeof(code_id));
    blob_put(b, &nf, sizeof(nf));
    for (uint32_t i = 0; i < nf; i++) {
      if (blob_write_mobile(b, bl_obj_field(v, i)) != 0) return 1;
    }
    return 0;
  }
  if (tag == BL_OPNODE) {
    const char *effect = bl_effect_name_of(bl_obj_aux(v));
    const char *op = bl_op_name_of(bl_obj_aux(v));
    uint32_t t = (uint32_t)BL_OPNODE;
    blob_put(b, &t, sizeof(t));
    blob_put_str(b, effect);
    blob_put_str(b, op);
    /* Always exactly 2 fields (arg, continuation) by construction (bl_perform/bl_app); the
     * continuation may be NULL (the identity continuation), handled by the NULL sentinel above. */
    if (blob_write_mobile(b, bl_obj_field(v, 0)) != 0) return 1;
    if (blob_write_mobile(b, bl_obj_field(v, 1)) != 0) return 1;
    return 0;
  }
  if (!bl_value_is_serializable_tag(tag)) return 1;
  uint32_t t = (uint32_t)tag;
  uint32_t nf = bl_obj_nfields(v);
  uint64_t aux = bl_obj_aux(v);
  blob_put(b, &t, sizeof(t));
  blob_put(b, &nf, sizeof(nf));
  blob_put(b, &aux, sizeof(aux));
  for (uint32_t i = 0; i < nf; i++) {
    if (blob_write_mobile(b, bl_obj_field(v, i)) != 0) return 1;
  }
  return 0;
}

void *bl_value_serialize_mobile(BlValue v, size_t *out_len) {
  Blob b = {0};
  blob_put(&b, &g_binary_id, sizeof(g_binary_id));
  if (blob_write_mobile(&b, v) != 0) { free(b.buf); *out_len = 0; return NULL; }
  *out_len = b.len;
  return b.buf;
}

/* Read a length-prefixed string out of the blob into a fresh NUL-terminated malloc'd buffer (caller
 * frees). Aborts on underrun, mirroring `blob_read`'s existing discipline for the base format. */
static char *blob_get_str(const unsigned char *buf, size_t len, size_t *pos) {
  uint32_t n;
  if (*pos + sizeof(n) > len) { fprintf(stderr, "blight: deserialize blob underrun\n"); abort(); }
  memcpy(&n, buf + *pos, sizeof(n)); *pos += sizeof(n);
  if (*pos + n > len) { fprintf(stderr, "blight: deserialize blob underrun\n"); abort(); }
  char *s = (char *)malloc((size_t)n + 1);
  if (!s) { fprintf(stderr, "blight: deserialize blob OOM\n"); abort(); }
  memcpy(s, buf + *pos, n);
  s[n] = '\0';
  *pos += n;
  return s;
}

/* Rebuild a value from a mobile-format blob. `*pos` advances. Returns a sentinel via `*reject` (set
 * to 1) rather than aborting for the two REJECTABLE conditions this format introduces — an unknown
 * `code_id` — since those are legitimate "the far side sent us something we cannot safely resolve"
 * outcomes (e.g. cross-binary mobility, deliberately out of scope), not a malformed-blob bug; a
 * truncated/malformed blob still aborts, exactly like the base `blob_read`, since that indicates
 * actual data corruption rather than a scope boundary. */
static BlValue blob_read_mobile(const unsigned char *buf, size_t len, size_t *pos, int *reject) {
  uint32_t t;
  if (*pos + sizeof(t) > len) { fprintf(stderr, "blight: deserialize blob underrun\n"); abort(); }
  memcpy(&t, buf + *pos, sizeof(t));
  if (t == BL_BLOB_NULL_TAG) { *pos += sizeof(t); return NULL; }
  *pos += sizeof(t);
  if ((BlTag)t == BL_CLOSURE) {
    uint64_t code_id; uint32_t nf;
    if (*pos + sizeof(code_id) + sizeof(nf) > len) {
      fprintf(stderr, "blight: deserialize blob underrun\n"); abort();
    }
    memcpy(&code_id, buf + *pos, sizeof(code_id)); *pos += sizeof(code_id);
    memcpy(&nf, buf + *pos, sizeof(nf)); *pos += sizeof(nf);
    void *fn = bl_code_ptr_of(code_id);
    if (fn == NULL) {
      /* Reject BEFORE allocating/resolving anything further — still must consume the bytes so a
       * caller that wants to skip-and-continue could (not needed today; we always propagate reject
       * to the top and discard the partial result). */
      *reject = 1;
      for (uint32_t i = 0; i < nf; i++) (void)blob_read_mobile(buf, len, pos, reject);
      return NULL;
    }
    BlValue o = bl_alloc(BL_CLOSURE, nf, (uint64_t)(uintptr_t)fn);
    bl_gc_push_root(&o);
    for (uint32_t i = 0; i < nf; i++) {
      BlValue child = blob_read_mobile(buf, len, pos, reject);
      o->fields[i] = child;
      if (child) bl_write_barrier(o, child);
    }
    bl_gc_pop_roots(1);
    return o;
  }
  if ((BlTag)t == BL_OPNODE) {
    char *effect = blob_get_str(buf, len, pos);
    char *op = blob_get_str(buf, len, pos);
    uint64_t idx = bl_effect_intern(effect, op);
    /* effects.c's `intern_op` stores the RAW pointers it is given (every other caller passes string
     * literals baked into the compiled program, which are valid for the process's entire lifetime) —
     * on a first-use miss it keeps `effect`/`op` themselves as the table entry, not a copy. Freeing
     * them here would leave a dangling pointer in `g_ops` for the rest of the process. So: intentionally
     * LEAK these two small malloc'd strings (at most once per distinct (effect,op) pair a process ever
     * deserializes — the same "tiny and append-only" budget `g_ops` itself already assumes). */
    BlValue o = bl_alloc(BL_OPNODE, 2, idx);
    bl_gc_push_root(&o);
    BlValue arg = blob_read_mobile(buf, len, pos, reject);
    o->fields[0] = arg;
    if (arg) bl_write_barrier(o, arg);
    BlValue kont = blob_read_mobile(buf, len, pos, reject);
    o->fields[1] = kont;
    if (kont) bl_write_barrier(o, kont);
    bl_gc_pop_roots(1);
    return o;
  }
  uint32_t nf; uint64_t aux;
  if (*pos + sizeof(nf) + sizeof(aux) > len) {
    fprintf(stderr, "blight: deserialize blob underrun\n"); abort();
  }
  memcpy(&nf, buf + *pos, sizeof(nf)); *pos += sizeof(nf);
  memcpy(&aux, buf + *pos, sizeof(aux)); *pos += sizeof(aux);
  if (nf == 0 && (BlTag)t == BL_NAT) {
    return bl_nat_from_u64(aux);
  }
  BlValue o = bl_alloc((BlTag)t, nf, aux);
  bl_gc_push_root(&o);
  for (uint32_t i = 0; i < nf; i++) {
    BlValue child = blob_read_mobile(buf, len, pos, reject);
    o->fields[i] = child;
    if (child) bl_write_barrier(o, child);
  }
  bl_gc_pop_roots(1);
  return o;
}

BlValue bl_value_deserialize_mobile(const void *buf, size_t len) {
  const unsigned char *b = (const unsigned char *)buf;
  size_t pos = 0;
  uint64_t sender_id;
  if (pos + sizeof(sender_id) > len) { fprintf(stderr, "blight: deserialize blob underrun\n"); abort(); }
  memcpy(&sender_id, b + pos, sizeof(sender_id)); pos += sizeof(sender_id);
  if (sender_id != g_binary_id) {
    /* Reject BEFORE touching a single byte of the value tree — no code_id is ever resolved for a
     * blob whose binary identity does not match this process's own (docs/design-code-mobility.md). */
    return NULL;
  }
  int reject = 0;
  BlValue v = blob_read_mobile(b, len, &pos, &reject);
  if (reject) return NULL;
  return v;
}
