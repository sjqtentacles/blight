# P5 go-bar: code mobility (closure + continuation serialization + security model)

**Status: SHIPPED** (roadmap Arc II, Wave 10 / P5). This document is the go-bar that gated P5; every
checklist item below is cleared. The shippable target locked in from the start — **same-binary
mobility only** — is exactly what shipped: a `BL_CLOSURE`/`BL_OPNODE` can cross a heap, a thread, or a
real OS process boundary, but only ever back into a copy of the *identical compiled binary*. Shipping
a closure to a different build (even one built from a trivially edited source) is a documented,
enforced non-goal, not a silent unsoundness — see "Security model" below.

## Why this needed a go-bar at all

`crates/blight-codegen/runtime/serialize.c` (M18) already flattens an immutable `BlValue` tree to a
byte blob and rebuilds it in a possibly-different heap, but only for the **data-only** tags:
`BL_CON`/`BL_TUPLE`/`BL_INT`/`BL_NAT` (`bl_value_is_serializable_tag`). Two blockers kept
`BL_CLOSURE`/`BL_OPNODE` out of that format:

### Blocker 1 — a closure's `header.aux` is a raw, per-process function pointer

`BL_CLOSURE`'s `header.aux` is a live C function pointer (`blight_rt.h`'s `BlHeader` doc comment) —
meaningful only within the address space that allocated it, and doubly so under ASLR (ping and pong
processes of the *same* binary still load their `.text` segment at different base addresses). There
was, before this change, no stable identifier a receiving process could use to resolve "the function
this closure pointed to" back to its own copy of that same function.

### Blocker 2 — an OpNode's `header.aux` is a runtime, first-use-order-assigned index

`BL_OPNODE`'s `header.aux` is an index into `effects.c`'s `g_ops` intern table (`bl_effect_intern`),
assigned in whatever order a process happens to first *use* each `(effect, op)` pair
(`effects.c`'s header comment, the M15 share-nothing multicore design). Unlike a lifted function's
identity (fixed at **compile** time — see below), this index is not even guaranteed stable across two
runs of the identical binary if the two runs happen to exercise their effects in a different order.
Shipping the raw index would be a ticking correctness bug, not merely a portability gap.

## Design (mirrors `effects.c`'s `g_ops` precedent)

The precedent already in the runtime is exactly the right shape: `effects.c`'s `g_ops` intern table
already assigns small stable `uint64_t` ids to `(effect, op)` pairs. P5 reuses that idea twice, once
for each blocker, and does not touch `blight-kernel`/`blight-elab`/`blight-recheck` at all (zero new
kernel lines, zero new `foreign` axioms) — this is a pure tower/runtime feature:

- **Closures — a compile-time function-index table.** `driver.rs`'s `code_table_source_for` emits a
  small, separate generated C translation unit (`code_table.c`) per compiled binary: it declares an
  `extern` for every lifted top-level function in `AnfProgram.funcs` order (the *same* order
  `llvm.rs`'s `emit_program` assigns LLVM function values in — a property fixed at codegen time, not
  by runtime behavior), packs their addresses into a `static void *const[]` table, and registers that
  table with `serialize.c` via `bl_code_table_register` from an `__attribute__((constructor))` that
  runs before `main`. A closure serializes as `(code_id, captured env fields)`, where `code_id` is
  the table index found by a reverse (address → index) scan (`bl_code_id_of`); the receiver resolves
  `code_id` back to a pointer with a single bounds-checked table read (`bl_code_ptr_of`) — never an
  out-of-bounds dereference for a bad index.
- **OpNodes — ship the name, not the index.** An OpNode instead serializes its `(effect, op)` as two
  length-prefixed strings (`bl_effect_name_of`/`bl_op_name_of`, both read-only accessors into the
  existing `g_ops` table); the *receiving* process re-derives its own local index via
  `bl_effect_intern` (append-on-miss, exactly like any other first-use interning) rather than ever
  trusting a number that was only ever meaningful relative to the sender's own first-use order.
- **Registration, not a direct `extern` reference.** `serialize.c` never references
  `code_table.c`'s globals directly (no `extern void *bl_code_table[];`); `code_table.c` instead
  *calls into* `serialize.c` at startup. This deliberately keeps `serialize.c` linkable, with an
  always-valid (simply *empty*) table, into every existing C-only runtime test harness
  (`runtime.rs`'s `build_and_run_harness*`), none of which link an actual compiled Blight
  `program.o` — an `extern` in the other direction would leave every one of those harnesses with an
  unresolved symbol at link time.

## Security model

Every mobile blob (`bl_value_serialize_mobile`'s output) is prefixed with `bl_binary_id`: an FNV-1a
hash (`driver.rs`'s `fnv1a_binary_id`) over the ordered list of lifted function names — a compile-time
content fingerprint of "the exact set of functions this program's `code_id`s can mean, in this exact
order." `bl_value_deserialize_mobile` checks the blob's leading `bl_binary_id` against the receiving
process's own **before touching a single further byte of the value tree**: a mismatch is a hard
reject (`NULL`), never a dereference into a foreign process's function-pointer space. An out-of-range
`code_id` (a corrupted blob, or a binary-id collision — astronomically unlikely for FNV-1a-64 but not
cryptographically ruled out) is a second, independent reject inside `bl_code_ptr_of`'s bounds check,
so a bad id can never resolve to a wild pointer even in that residual case.

This is **not** a cryptographic authentication tag — FNV-1a has no collision resistance guarantees,
and there is no signature or trust anchor here. The property being enforced is narrower and matches
the shippable scope exactly: "this blob almost certainly came from (or agrees with) a process running
the identical compiled binary," which is all `code_id` resolution ever needs. **Cross-binary or
untrusted-peer code mobility is explicitly out of scope** — deserializing a mobile blob from a
different binary, or from an adversarial peer that does not share source, is a documented sharpened
negative: it is designed to reject cleanly (mismatched `bl_binary_id` ⇒ `NULL`), not to be safe to
attempt. A future cross-binary story (if ever wanted) would need a real content-addressed code
identity and a trust/signing model — deliberately not attempted here.

## Wire format (extends M18's, `serialize.c`'s header comment has the full byte layout)

Same pre-order walk as the data-only format, with two new per-node tag branches:

- `BL_CLOSURE`: `{tag: u32, code_id: u64, nfields: u32}` then `nfields` children (the captured env,
  recursively — itself may contain further closures/opnodes/data).
- `BL_OPNODE`: `{tag: u32, effect_len: u32, effect_bytes, op_len: u32, op_bytes}` then exactly 2
  children (`arg`, `continuation`; the continuation may be the `NULL` sentinel).

The base data-only format (`bl_value_serialize`/`bl_value_deserialize`) is **completely unchanged** —
the mobile extension lives entirely in the separate `bl_value_serialize_mobile`/
`bl_value_deserialize_mobile` entry points, so the worker pool (M17) and `blight-net`'s distributed
transport (M19), which both deliberately want to stay data-only (the Erlang model), are unaffected.

## Go-bar checklist (all items required before P5 was considered shipped)

1. ✅ **Red-first**: `runtime/tests/serialize_test.c`'s existing data-only round-trip/rejection tests
   were the pre-existing green baseline; the new mobile-format tests were written and run failing
   (no `bl_value_serialize_mobile` symbol) before `serialize.c`'s extension was implemented.
2. ✅ **Closure + continuation round-trip** (serialize → deserialize → apply → same result), in one
   process: `runtime/tests/mobility_test.c`
   (`code_mobility_round_trips_closures_and_opnodes`, `crates/blight-codegen/src/runtime.rs`) —
   round-trips plain data via the mobile path, a closure with a captured env by `code_id`, and an
   OpNode by `(effect, op)` name (using a deliberately nonzero local index, so a receiver that
   incorrectly trusted the raw wire index instead of re-deriving it by name would be caught).
3. ✅ **Cross-process mobility test**: `runtime/tests/mobility_pingpong.c` +
   `code_mobility_ships_a_closure_across_a_process_boundary`
   (`crates/blight-codegen/src/runtime.rs`) — the C-runtime-level analogue of `blight-net`'s
   `pingpong.rs`: two independently-spawned OS processes of the identical compiled test binary ship a
   real `BL_CLOSURE` across a loopback TCP socket; the receiver applies it and both sides confirm the
   result.
4. ✅ **Security model documented and enforced**: this document, plus
   `test_rejects_mismatched_binary_id` / `test_rejects_unknown_code_id`
   (`runtime/tests/mobility_test.c`) — a mismatched `bl_binary_id` or an out-of-range `code_id` is
   rejected (`NULL`) before any pointer is ever resolved or dereferenced.
5. ✅ **Zero kernel/elaborator/re-checker lines**: `git diff crates/blight-kernel crates/blight-elab
   crates/blight-recheck` for this feature is empty — P5 is entirely `blight-codegen`
   (`driver.rs`/`llvm.rs`'s doc-comment-only note) and the runtime (`serialize.c`, `blight_rt.h`).
6. ✅ **Every real `blight build` binary carries the table**: `serialize.c` and the generated
   `code_table.c` are unconditionally linked by both `build_objects` and `build_lto` (`driver.rs`),
   so `bl_code_table_register` runs at startup for every compiled program, not just ones that use
   mobility — an unused table costs a few static bytes and one constructor call.
7. ✅ **Existing differential/e2e corpus unaffected**: the full example-program build/run suite
   (`crates/blight-repl`'s `example_*_builds_and_runs` tests) still passes with `serialize.c` +
   `code_table.c` now linked into every binary, both via the `-flto` cross-object path and the
   `BL_NO_LTO` object-file fallback path.

All seven items are checked. P5 is the prerequisite P4 (auto-parallelism) consumes: a work-stealing
pool needs to hand a lifted function to a worker *by id*, which is exactly what this table provides.

## Cross-references

- Capability table: `docs/roadmap.md`.
- Wire format base case (data-only) and the effect-op intern precedent this mirrors:
  `crates/blight-codegen/runtime/serialize.c`, `crates/blight-codegen/runtime/effects.c`.
- Function-index table generation: `crates/blight-codegen/src/driver.rs`
  (`code_table_source_for`, `fnv1a_binary_id`).
- `blight-net`'s deliberately-data-only distributed transport (unaffected by this change, and not
  extended to carry code — see its own module doc for why that boundary is intentional):
  `crates/blight-net/src/lib.rs`.
- P4 (auto-parallelism, depends on this table): `docs/roadmap.md`'s Wave 10 section.
