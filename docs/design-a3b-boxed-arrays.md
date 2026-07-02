# A3b go-bar: generic/boxed arrays

**Status: SHIPPED** (roadmap Arc II, Wave 10 / P1). This document was the go-bar gating A3b; every
checklist item below is now cleared and Design 1 (the recommendation) is implemented:
`runtime/boxed_array.c` (the rooted handle table + write barrier), two new root-scanning call sites
in `gc.c` (`bl_boxed_array_gc_roots`, from both `minor_collect` and `major_collect_into`), four new
op-name branches in `effects.c`'s `bl_run_console`, and the parameterized `Array A` effect in
`std/array.bl` (riding the already-shipped Wave 7/E2 parameterized-effects kernel feature). Red
tests: `runtime/tests/gc_test.c`'s `test_boxed_array_survives_minor_and_major_gc_structurally` /
`test_boxed_array_write_barrier_old_to_young` (both ASan-clean via
`boxed_array_survives_gc_and_write_barrier_under_asan`, `crates/blight-codegen/src/runtime.rs`);
end-to-end: `examples/boxed_array_scratch.bl` (`example_boxed_array_scratch_builds_and_runs`), part
of the full `BL_NO_*` differential bit-identity corpus. See `docs/implementation.md` for the
consolidated writeup. The design history below is retained as the record of what was decided and
why.

## Why this needs a go-bar at all

A3a (`std/array.bl`) works, unmodified, for `Int` because of one property: a `malloc`'d table of
raw `int64_t` can never contain a stale or moved GC pointer, since it never contains a pointer at
all. A generic array of arbitrary boxed `BlValue`s — the actually-useful feature people mean by
"arrays" — loses that property twice over, independently:

### Blocker 1 — effect operations cannot be polymorphic

`OpSig` (`crates/blight-kernel/src/signature.rs`) stores each operation's parameter and result
types as **closed** kernel `Term`s, elaborated once at the `(effect …)` declaration
(`crates/blight-elab/src/elab.rs`, `declare_effect`). `DefEffect` has no parameter telescope —
unlike `defdata`, which does. So there is no surface form today that can express
`(effect Array (get-elem (Pair (Array-handle A) Nat) A) …)` for a type variable `A`: the kernel
representation of an effect's ops has nowhere to put `A`. `(perform op arg)` always yields the one
fixed `result_ty` recorded at declaration time (only *value*-dependence `B[a/x]` is supported;
`check.rs`). This is a hard wall, not a missing convenience function.

### Blocker 2 — an off-heap `BlValue[]` is GC-unsafe

The collector is precise and **moving** (a two-space/generational Cheney copy;
`crates/blight-codegen/runtime/gc.c`). It discovers every live object by walking a fixed root set —
the shadow stack (`g_roots`) plus the remembered set of old→young pointers recorded by
`bl_write_barrier` — and only ever traces `BlValue` objects reachable from those roots, using each
object's `header.nfields` to know how many pointer-sized fields to walk/relocate. A `malloc`'d
buffer of `BlValue` slots that the tracer does not know about is invisible to it: any `BlValue`
stored there is (a) never marked reachable, so it can be *collected* out from under the array even
while the handle is still live, and (b) if some other root happens to keep it alive, its address
still gets *relocated* by a copying collection without the array's copy ever being updated — so the
array ends up holding a dangling pointer into free space. There is currently no "register this
external buffer as an extra root set" API in `gc.c` at all; every rooted structure today is either
on the shadow stack or is itself a traced heap object.

## Candidate designs

### Design 1 — GC-object backing (recommended default if/when this opens)

Back the array with a real heap object using the *existing* tuple representation: allocate it via
`bl_alloc(BL_TUPLE, len, 0)` so `header.nfields == len` and the precise tracer already walks and
relocates every slot with zero changes to `gc.c`'s tracing code. The array "handle" a Blight program
holds is not a raw pointer (which a GC copy would invalidate under the mutator's feet) but an index
into a **rooted handle table** — a new, small, `g_boxed_arrays`-style side table, analogous to
`g_arrays`/`g_bytes` in `effects.c`, except that *this* table's slots are themselves GC roots that
must be included in every root-scanning phase (`mark_roots`/the shadow-stack walk in `gc.c`), not
just `g_roots`. `set-elem` on a slot that may hold an old-generation array with a new (nursery)
value **must** call `bl_write_barrier(array, val)` (`gc.c`, already used elsewhere for exactly this
purpose) or the minor-GC remembered-set invariant silently breaks and the young value can be
reclaimed while still reachable through the (unrecorded) old array.

This design is still bound by Blocker 1: it does not add a polymorphic effect. What it buys is a
**monomorphic-per-instantiation** array of *one specific* boxed type, generated the same way
monomorphization already specializes other polymorphic code today (`crates/blight-codegen/src/
mono.rs`) — i.e. `(effect ArrayOfNatTree …)` declared per concrete element type the program actually
needs, or a `defdata`-style effect-instantiation mechanism that emits one concrete `(effect …)` per
use site before elaboration. This keeps the *kernel* completely unchanged (no telescope, no new
term former) at the cost of needing a tower-level specialization step to generate the per-type
effect declarations. It is the smaller, lower-risk of the two designs and does not touch the TCB.

### Design 2 — parameterized effects (language feature)

Extend `DefEffect` with a parameter telescope, the same shape `defdata` already has, and thread a
type parameter through `OpSig` and through `perform`'s instantiation at the call site. This is a
genuine elaborator **and** kernel-signature change: `OpSig` stops being closed, `declare_effect`
needs telescope elaboration mirroring `declare_data`, and `perform`'s typing rule
(`crates/blight-kernel/src/check.rs`) needs to substitute the instantiation's argument into both
`param_ty` and `result_ty` before checking, not just apply value-dependence. Every place that
currently treats `OpSig` as closed (`blight-kernel`, `blight-recheck`'s independent op-signature
model, `blight-elab`'s effect-row bookkeeping) needs a matching, reviewed update, and the
independent re-checker's copy of the typing rule needs to be extended **in lockstep** — a real,
audited TCB-adjacent change (the re-checker already checks effect programs at the type level per
`docs/implementation.md`'s coverage matrix; that parity is exactly what would need re-establishing).
This is strictly larger and higher-risk than Design 1, and is only worth it if generic effects
(not just generic arrays) are wanted as a first-class language feature — e.g. a future `Channel A`
or `Ref A` effect would reuse the same telescope machinery. Do not choose this design for arrays
alone; choose it only if the broader "generic effects" capability is independently justified.

### Recommendation

Start with **Design 1** if/when the go-bar below is cleared. It is strictly additive to the tower
and the runtime (a new rooted side table + a `bl_write_barrier` call site), touches zero kernel
code, and directly reuses the existing `BL_TUPLE` representation and tracer. Revisit Design 2 only
if a second, independent use case for generic effects shows up (at which point the amortized cost
of the kernel change is worth it across more than one feature).

## Go-bar checklist (all items required before A3b implementation work starts)

1. ✅ **This design doc** exists and a design (1 vs 2) has been chosen for the specific attempt about
   to be made — **Design 1**, per the recommendation above (Blocker 1 turned out to already be
   closed for free by the time this was picked up: Wave 7/E2 shipped parameterized effects in the
   interim, so `Array`'s telescope needed zero kernel/elaborator work at all).
2. ✅ **A rooted-handle-table root-scanning design note**, for Design 1 specifically: `gc.c`'s
   `minor_collect` and `major_collect_into` each gained one call to `bl_boxed_array_gc_roots`
   (`boxed_array.c`), placed immediately after the existing shadow-stack roots loop in both
   functions. No race is possible: this runtime is single-mutator per (thread-local) heap
   (spec §7.3's share-nothing multicore model), so at most one collection is ever scanning the
   table, and every entry point that can trigger a collection (`bl_alloc`'s slow path,
   `bl_gc_force_collect`) routes through exactly these two functions — there is no third
   collection-triggering path that could skip the new call.
3. ✅ **An ASan test proving no use-after-free / no stale-pointer read** across at least one real
   collection cycle while a boxed array is live:
   `test_boxed_array_survives_minor_and_major_gc_structurally` (`runtime/tests/gc_test.c`) stores a
   freshly-consed `Con` (with its own `Int` child) and a plain `Int` into a boxed array, forces heavy
   churn plus an explicit `bl_gc_force_collect()` (guaranteeing both a minor and a major fire), then
   reads both slots back and asserts each is structurally identical to what was stored — checked by
   value, not just by the sanitizer's absence of a fault. Run under ASan by
   `boxed_array_survives_gc_and_write_barrier_under_asan` (`crates/blight-codegen/src/runtime.rs`).
4. ✅ **A write-barrier regression test**: `test_boxed_array_write_barrier_old_to_young`
   (`runtime/tests/gc_test.c`) promotes a boxed array's backing object into the old generation via
   churn, stores a fresh nursery value into one of its slots via `bl_boxed_array_set` (which calls
   `bl_write_barrier`) *without* touching the array handle again afterward, forces a **minor-only**
   collection (deliberately never `bl_gc_force_collect`, which would go major and mask a missing
   barrier), and asserts the value is still intact — the exact bug class the barrier exists to
   prevent.
5. N/A — Design 2 was not chosen; no kernel/re-checker parity change was needed (parameterized
   effects, including their type-level re-checker coverage, already existed as of Wave 7/E2).
6. ✅ Blocker 1 (closed `OpSig`) and Blocker 2 (off-heap `BlValue[]` vs the moving GC) are each
   concretely closed by Design 1, not worked around for one element type: `Array`'s parameter `A` is
   genuinely instantiated per call site (`(perform op (T) arg)`, `std/array.bl`), and every boxed
   array's backing object is a real GC-heap `BL_TUPLE` the precise tracer already walks, referenced
   through a table that is itself a root source — see `runtime/boxed_array.c`'s header comment.
   `std/array.bl`'s `Array A` effect (`boxed-array-new`/`-length`/`-get`/`-set`) is the shipped
   boxed counterpart; `examples/boxed_array_scratch.bl` is the runtime-execution proof.

All six items are now checked (item 5 vacuously, by not needing Design 2). Ordinary inductive
`List`/`Vec`/tree structures remain the right choice for collections that do not need O(1) random
mutable access — see `std/tree.bl` and the Wave 2 `L1` stdlib-breadth plan's hash map/set, which
deliberately routes through the tree rather than an array for exactly that reason — but `Array A` is
now available where mutable random access genuinely is the requirement.

## Cross-references

- Capability table: `docs/roadmap.md` ("Mutable arrays (generic/boxed)" row).
- A3a (shipped, the non-gated sibling this design mirrors up to the two blockers):
  `docs/implementation.md`, section D6.
- Effect-signature closedness (Blocker 1): `crates/blight-kernel/src/signature.rs`,
  `crates/blight-elab/src/elab.rs` (`declare_effect`).
- Moving/precise collector internals (Blocker 2): `crates/blight-codegen/runtime/gc.c`.
- Re-checker's independent effect-typing model (relevant to Design 2 only):
  `crates/blight-recheck/src/typecheck.rs`.
