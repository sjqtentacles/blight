# Wave 4 go-bars: SN/canonicity, RC-reuse, arenas, auto-parallelism, graphics FFI

**Status: none of these are open.** Every Wave 4 item in the roadmap
(`blight_full-arc_roadmap_3d438c0d.plan.md`, task `w4-gobars`) is gated behind its own falsifiable
go-bar before implementation work may start — matching the discipline `docs/design-a3b-boxed-arrays.md`
already established for boxed arrays. This document is the single index for all five, so "what would
it take" is answered once per item rather than re-litigated. Three of the five (RC + in-place reuse,
interprocedural arena cloning, auto-parallelism) were already investigated as research go/no-gos in
[`docs/roadmap-post-m6.md`](roadmap-post-m6.md) (Grand Arc — Perf Frontier II, P5.1/P5.2/P8); this
document summarizes their dispositions and points at the primary source rather than duplicating it.
The other two (SN/canonicity mechanization, graphics FFI) have not had a go-bar written yet — both are
now unblocked by work landed this pass (M5+M6 for the former, L2's `F64` hatch for the latter) — so
this document gives them the full treatment.

| Item | Disposition | Go-bar detail |
|---|---|---|
| SN/canonicity mechanization | **Unblocked, not started** — go-bar below | this document, §1 |
| RC + in-place reuse | **Deferred, sharpened** (Arc II Wave 10 / P6: committed red test) | `docs/design-rc-reuse.md`; `roadmap-post-m6.md` P5.1; summarized §2 |
| Interprocedural arena cloning | **Deferred**; linearity substrate landed (Wave 6 C3) | `roadmap-post-m6.md` P5.2; summarized §3 |
| Auto-parallelism | **No-go for now** on the rewrite; detection half **SHIPPED** (Arc II Wave 10 / P4) | `roadmap-post-m6.md` P8; summarized §4 |
| Graphics FFI | **SHIPPED** (Arc II Wave 10 / P2) | this document, §5 |

---

## 1. SN / canonicity mechanization

**Why this needs a go-bar.** This is the plan's original "going for gold" ambition — a
machine-checked strong-normalization (every reduction sequence terminates) and canonicity (every
closed term of a base type, e.g. `Bool`, reduces to an actual canonical value, `tt` or `ff`, not just
"a value or a step" per-term) proof for the mechanized fragment. It was explicitly deferred in
`docs/metatheory-mechanized.md` pending M5 (Kan formers) + M6 (progress/preservation) landing first;
both are now done (this repo, this pass), so the prerequisite is met and this go-bar exists to scope
what "attempt it" actually means before starting.

**Current state (what M5/M6 already give us, precisely).** `BlightMeta/Progress.lean`'s `Step`
defines a deterministic, call-by-value small-step relation over `Tm` (STLC core + the constant-family
Kan formers); `progress` + `preservation` combine into `type_safety`. This is **not** SN: type safety
only says a well-typed closed term is a value or can take *one* step and stay well-typed after —
it says nothing about whether *repeated* stepping ever stops. Two facts bound how hard the remaining
work actually is:

- **There is no source of non-termination in this fragment.** `Tm` (`Calculus.lean`) has no
  general-recursion/fixpoint combinator, no unbounded-depth data (`Bool` has two nullary
  constructors; there is no `Nat`/`List` in this file's `Ty`), and every `Step` rule is structurally
  decreasing on some measure of the term (β-reduction strictly shrinks the redex; `ite_tt`/`ite_ff`/
  `transp_val`/`hcomp_true`/`hcomp_false`/`iabs_elim` all discard a subterm outright). So SN is
  **expected to hold and is not a live soundness risk** — this is not a "will it even be true"
  question the way M7's heterogeneous-grade probe was; it is a "formalize the well-understood
  argument" question.
- **The actual work is a reducibility-candidates (Tait-style logical relations) proof**, indexed by
  `Ty`, showing every well-typed term is reducible (hence, by the standard corollary, SN). This is
  the standard technique for exactly this class of calculus (simply-typed core + a handful of
  structural eliminators), but it is notoriously fiddly to mechanize: the `Pi`-case requires
  reducibility to be closed under application at *every* reducible argument (a higher-order
  quantification Lean's `induction` tactic cannot discharge directly — it needs the reducibility
  predicate defined by well-founded recursion on `Ty`'s structure, argued once up front), and every
  `Step` rule added by M5 (`iabs_elim`, `transp_val`, `hcomp_true`/`false`) needs its own reducibility
  preservation case threaded through the logical relation. None of this touches grades: `Step` and
  `Value` are already grade-erased (the `HasType` judgement's `σ`/`φ` never appear in `Step`'s
  indices), so the logical relation is a property of `Tm`/`Ty` alone — grades are orthogonal to this
  proof, not an extra dimension of it.
- **Canonicity is a short corollary once SN lands, not a second proof from scratch.** Given SN
  (every `Step` sequence from a well-typed closed term terminates), `Step`'s determinism (each
  `Tm` steps to at most one successor — provable by a direct case analysis on `Step`'s constructors,
  no new machinery), and `progress` (a non-value always steps), a closed term of type `Bool` must
  terminate at *some* value, and a canonical-forms lemma (a `Value` of type `Bool` is `tt` or `ff` by
  case analysis on `HasType`+`Value`, similarly `Pi` values are exactly `lam`) reads off canonicity
  directly.

**Go-bar checklist (all required before starting the SN attempt):**

1. **A written proof sketch** (on paper/in a scratch `.lean` file, not necessarily compiling) of the
   reducibility-candidates definition for this fragment's three type formers (`Bool`, `Pi`, and the
   Kan formers' shared type `Ty` — recall `Ty` is non-dependent here, so no new type former is
   actually introduced by `iabs`/`transp`/`hcomp`, only new `Tm` constructors and `Step` rules over
   the existing two `Ty`s), reviewed for the well-foundedness argument in the `Pi` case specifically
   (this is where reducibility proofs most commonly get stuck in a proof assistant).
2. **A worked reducibility-preservation case for every M5 `Step` rule** (`iabs_elim`, `transp_val`,
   `hcomp_true`, `hcomp_false`) in the sketch above — each is a "drop a subterm" rule, so the expected
   shape is "reducibility of the whole term already contains reducibility of the surviving subterm,"
   but this must be checked per-rule, not assumed by analogy to β/ι.
3. **A determinism lemma for `Step`** (`Step t t1 → Step t t2 → t1 = t2`) — needed for the canonicity
   corollary above and independently useful (it is not currently proved anywhere in `Progress.lean`).
4. **Zero `sorry`** in the landed proof, per this repo's existing CI gate
   (`.github/workflows/mechanization.yml`) — same bar as M5/M6, no exception for "SN is hard."
5. Explicit scope sign-off: SN/canonicity is proved for **exactly** the M5/M6 fragment (STLC core +
   constant-family Kan), not the fully heterogeneous fragment M7 left open — extending the type
   system further (a real dependent `Ty`, the heterogeneous Kan corner) is out of scope for this
   go-bar and would need its own follow-up scoping pass.

Until this checklist is met, `docs/metatheory-mechanized.md`'s "What's not covered" section
accurately states the boundary: type safety (M6) is mechanized, SN/canonicity is not.

**Cross-references:** `mechanization/BlightMeta/Progress.lean` (`Value`, `Step`, `progress`,
`preservation`); `mechanization/BlightMeta/Calculus.lean` (`Tm`/`Ty`, no fixpoint combinator);
`docs/metatheory-mechanized.md` ("What's not covered").

---

## 2. RC + in-place reuse — summarized (full go-bar: `roadmap-post-m6.md` P5.1)

**Disposition: no-go for now.** *Go-bar:* (1) a measured allocation drop on a reuse-shaped workload
(e.g. `map` reusing a cons spine); (2) zero UAF under ASan + the full differential matrix + the
fuzzer; (3) the reference count segregated from the Cheney/compaction evacuation so reuse cannot race
a move; (4) a sound RC→GC hybrid with proven root discipline for shared/cyclic/overflowed-count
objects. *Finding:* three structural obstacles, any one decisive — Blight's collector **moves**
objects (Cheney/compaction), which Perceus-style slot reuse assumes it does not; the ownership-typed
`dup`/`drop`/`reuse` IR pass needed is large, near-TCB-adjacent codegen surface where a misplaced
`drop` is a UAF the differential harness cannot reliably catch; and the headline motivating win
(functional-update reuse on a freshly-built-then-consumed list) is already captured by **P7
deforestation/fusion** (shipped) at a fraction of the risk, with no moving-GC conflict and no new
ownership discipline. **Prerequisite if ever revisited:** a non-moving heap mode (or a pinned-reuse
safepoint protocol) plus an ownership analysis behind a `*_diff.c` gate and the ASan/fuzzer bar above.
See `roadmap-post-m6.md`'s "P5.1 RC + in-place reuse — no-go for now" for the full writeup. **Update
(Wave 6 C3):** the prerequisite ownership/linearity analysis this item's "if ever revisited" clause
asks for now exists as a substrate ([`crate::linearity`](../crates/blight-codegen/src/linearity.rs));
see §3's update below for what it does and does not change about this disposition.

**Update (Arc II Wave 10 / P6): the moving-collector objection is revised for a narrower shape, but the
disposition is still deferred.** Full go-bar, finding, and the committed red test:
[`docs/design-rc-reuse.md`](design-rc-reuse.md). Summary: this pass distinguishes **general** Perceus
reuse (an opaque, untyped reuse-token address threaded across arbitrary control flow before a later
`alloc` claims it) — which genuinely does race Blight's moving Cheney/compaction collector exactly as
the original finding says — from a **narrower, purely-static "same-arm" reuse** (the dying value stays
an ordinary GC-traced, rooted `BlValue` from its last read to the point its fields are overwritten, all
within one eliminator arm, using the same write-barrier discipline every other in-place mutation in
this runtime already relies on). The narrow shape does **not**, by itself, race a move — so a
non-moving GC mode is *not* actually the prerequisite for it. The reason it is still deferred is
different: implementing it soundly needs a new correctness-critical ANF construct + emitter path, a
real shape-matching consumer pass (not just `is_transiently_consumed`'s classification), and proof it
composes correctly with every intervening backend pass — a large investment for a win **P7
deforestation/fusion** (shipped) has already mostly captured on the textbook motivating case. The
committed failing test is `crates/blight-codegen/runtime/tests/rc_diff.c`
(`runtime::tests::in_place_reuse_is_observationally_identical`, `#[ignore]`d, fails today with a clear
"undeclared function `bl_gc_reused_bytes`" compile error) — see the design doc for the full go-bar
items it pins and what a future implementer needs to build to turn it green.

## 3. Interprocedural region/arena cloning — summarized (full go-bar: `roadmap-post-m6.md` P5.2)

**Disposition: deferred**, unchanged from A5's original deferral. *Go-bar:* a sound, checkable
transient-consumption (linearity) analysis proving a target allocation site's result is fully
consumed before its enclosing arena is released, a measured allocation drop, and zero-UAF under ASan.
*Finding:* the gating work is the linearity analysis itself (a research-sized proof obligation), not
the arena plumbing — the QTT grades already in the kernel are the natural substrate for it, which is
why this is the one Wave 4 item where the Language and Performance fronts could share a mechanism (a
sound transient/linear-usage analysis would also directly inform obligation 1.3.2-style reasoning
about grade-preserving transformations). Building that analysis soundly, and only then arena-izing
on top of it, is the disposition. See `roadmap-post-m6.md`'s "P5.2 interprocedural region cloning —
deferred" for the full writeup.

**Update (Wave 6 C3): the linearity substrate now exists; arena-izing on top of it remains deferred.**
[`crate::linearity`](../crates/blight-codegen/src/linearity.rs) is a standalone, whole-function-local
analysis over the untrusted ANF that classifies each `let`-bound allocation site's uses into
`Dead`/`Linear`/`Shared` — `Linear` meaning exactly one, non-retaining (consuming) occurrence, the
structural analogue of "grade 1" the erased QTT grades cannot express past codegen (grades are
stripped by `blight_kernel::erase` before `blight-codegen` ever sees a term, so the analysis
re-derives the judgement from ANF shape rather than threading grades through). It is intentionally
conservative in the two ways P5.2's go-bar cares about most: it never looks inside a callee (any
value crossing a call boundary — argument, capture, effect payload, handler clause — is `Shared`,
full stop), and it does not chase `let`-alias re-bindings. Today it is wired into the pipeline as a
**pure self-check** (`linearity::analyze_gated`, gated `BL_NO_LINEARITY`, diagnosable via
`BL_LINEARITY_STATS`): it classifies and optionally reports, but is the identity transform on the
program — proven by ANF structural equality (`crate::linearity`'s own unit corpus plus
`driver::bench_sanity_tests::linearity_analysis_is_observationally_invisible`, which classifies a real
compiled `.bl` program, confirms it exercises a genuine `Linear` site, and asserts `analyze_gated`
returns a byte-for-byte-equal `AnfProgram`). **What this does not do:** it does not arena-ize
`treesum`'s `build`, does not touch a single `Alloc` tag, and is not measured against P5.2's "measured
allocation drop" or "zero-UAF under ASan" bars — those apply to a *consumer* pass (synthesizing an
arena-allocating clone at a proven-`Linear` site) that does not exist yet. Because the substrate
itself never changes what a program computes or where anything is allocated, there is no runtime
memory behavior to ASan-gate; the ASan/measured-win bar remains the acceptance criterion for the
*next* step (an actual P5.1/P5.2 consumer built on top of `is_transiently_consumed`), which stays
deferred exactly as before. See `roadmap-post-m6.md`'s "P5.2 interprocedural region cloning —
deferred" for the full writeup.

## 4. Auto-parallelism — summarized (full go-bar: `roadmap-post-m6.md` P8)

**Disposition: no-go for now on the rewrite** (a narrow fib-shaped fragment aside); **the detection
half SHIPPED** (Arc II Wave 10 / P4). *Go-bar:* (1) measured speedup on a realistic divide-and-conquer
workload above a granularity cutoff with no speeddown below it; (2) bit-identical output under the
`BL_NO_AUTOPAR` differential A/B; (3) ThreadSanitizer-clean; (4) deadlock-free under arbitrary
recursion depth. *Finding:* two structural obstacles — `worker.c`'s fixed-`N`-thread pool with a
**blocking** join has no help-on-join/work-stealing, so naive recursive fork-join can deadlock a
bounded pool by parking every worker in a blocking join while their own unrun subtasks sit in the
queue; and cross-heap task arguments/results are copied by structural serialization (O(message size)),
so the win is workload-shaped — genuinely parallelizable for `Int`-shaped workloads like `fibrec`, but
for data-heavy splits (`treesum`/sort) the copy cost matches the compute saved unless a shared-heap
read-only fork-join pivot is built, which itself needs a no-collect-during-parallel-region discipline
against the moving collector. **Prerequisite if ever revisited:** a help-on-join (or bounded
thread-per-split) pool rewrite of `worker.c`, plus the shared-heap-vs-copy decision for data-heavy
splits, both behind the `BL_NO_AUTOPAR` + TSan bar above. See `roadmap-post-m6.md`'s "P8
auto-parallelism" for the full writeup and finding.

**What Arc II Wave 10 / P4 shipped instead:** the sound, checkable *detection* half, as a pure
analysis pass — [`crate::autopar`](../crates/blight-codegen/src/autopar.rs), run right after the P3
elim-loop transform over the lowered `Cir`. It recognizes exactly the shape neither `build_elim_loop`
(3a) nor `build_elim_worklist` (3b) can loop-ify: a constructor arm whose induction hypothesis is used
`fanout >= 2` times (a genuine tree-shaped fold, e.g. `tree-sum`'s `node l x r`), reusing `elimloop`'s
own `(CtorShape, method)` recovery rather than re-deriving it, and flags whether the combining method
is effect-free. It **never rewrites** the `Cir` it scans (`BL_NO_AUTOPAR` is bit-identical by
construction, and is now a real flag in the B1 `DIFF_FLAGS` matrix, not just a named-in-advance
placeholder) — turning a candidate into an actual `bl_pool_submit_code` rewrite still needs the two
obstacles above resolved *plus* a fan-out-budget-threading codegen rewrite, none of which exist. P5
code mobility (`docs/design-code-mobility.md`) landed the other prerequisite the rewrite (not the
detector) would need: a stable `code_id` so a worker could be handed a Blight closure at all.

---

## 5. Graphics FFI (real-time games)

**Status: SHIPPED (Arc II Wave 10 / P2).** Design B below was implemented exactly as recommended:
`std/graphics.bl` declares the `Graphics` effect (`init-window`/`poll-input`/`clear`/`draw-rect`/
`present`) and `runtime/graphics.c` is its native handler, linked against SDL2 behind the `graphics`
cargo feature (off by default; `driver.rs`'s `build_objects`/`build_lto` shell out to `pkg-config
sdl2` for compiler/linker flags, with `SDL2_CFLAGS`/`SDL2_LIBS` env overrides). Every item on the
go-bar checklist below is satisfied: (1) the five-op signature shipped verbatim; (2) SDL2 links
cleanly via the existing `clang` pipeline with only linker-flag additions; (3)
`runtime/graphics.c`'s header comment is the native handler design note; (4) the four-layer TDD all
exists — `std_graphics_loads_in_isolation` (`crates/blight-repl/tests/stdlib.rs`),
`examples/graphics_scratch.bl` + `graphics_scratch_example_loads`
(`crates/blight-repl/tests/examples.rs`), `example_graphics_scratch_builds_and_runs`
(`crates/blight-repl/src/main.rs`, gated behind `graphics`, running the built binary under headless
`SDL_VIDEODRIVER=dummy`) plus a dedicated C-level `runtime/tests/graphics_test.c` harness
(`graphics_handler_observes_synthetic_input_events_in_order`, `runtime.rs`) that injects two
synthetic `SDL_PushEvent`s and asserts `poll-input` observes them in the exact order pushed, and
`mono::tests::effectful_init_window_used_twice_is_not_inlined` (the double-`init-window` safety
regression); (5) confirmed — zero kernel change, `git diff --stat crates/blight-kernel` for this
feature is empty. A dedicated `graphics` CI job (`.github/workflows/ci.yml`) installs `libsdl2-dev`
and runs the whole suite under `SDL_VIDEODRIVER=dummy`, kept separate from the default `llvm` job so
the ordinary build/CI matrix never needs SDL2. See `docs/roadmap.md`'s "Can we build games?" section
for the user-facing summary. The rest of this section is the original go-bar, kept verbatim as the
design record.

**Why this is now feasible to scope.** `docs/roadmap.md`'s "Can we build games?" section identifies
graphics FFI as the one remaining brick for *real-time* games (turn-based, text-rendered games are
already fully buildable on shipped bricks: the `Console` effect + native handler (M7), string output,
and native `Int` (M10)). Two prerequisites this brick needs have **both** shipped since that section
was written: the `foreign` FFI hatch (M8, untrusted, re-checker-declined) and a `Float`/`F64` numeric
type for real-valued coordinates/physics (`std/float.bl`'s verified fixed-point default, and — this
plan's Wave 2 L2 — `std/f64.bl`'s unverified IEEE-754 hatch for real hardware rounding). Nothing about
graphics FFI would touch `crates/blight-kernel` under either design below; it is tower-only, same as
every prior FFI-adjacent milestone (M7/M8/M9/A3a).

**The actual design question is not "can we call SDL," it is "how does Blight code see it."** Two
candidate designs, mirroring the A3b go-bar's structure:

### Design A — raw `foreign` bindings directly to SDL (the literal reading of the one-line plan note)

Declare each needed SDL entry point as a `foreign` postulate exactly like `std/f64.bl`'s `bl_f64_add`
etc., with an opaque `foreign GfxHandle (Type 0) "bl_gfx_handle_ty_witness"` for window/renderer
pointers (representable as a boxed `Int` holding the raw pointer bits, the *exact* trick `F64` already
uses to smuggle a non-`BlValue` payload through the `Int` box — no new runtime representation needed).
**Problems this design inherits, not fixed by anything shipped so far:**

- `foreign` calls are strictly **one argument** (multi-operand calls pack into a `Pair`, per
  `ir.rs`'s `Cir::Foreign` convention `std/f64.bl` already uses for binary ops). `SDL_CreateWindow`
  (6 heterogeneous arguments) or `SDL_RenderFillRect` (a rect struct) would need deeply nested
  `Pair`-packing on both the Blight and the C glue side for every call — mechanical but genuinely
  awkward, and a new, bespoke packing/unpacking C shim is needed **per SDL function**, not once.
- A `foreign`-returned pointer's validity (was the window actually created? was it already
  destroyed? is this handle from the right SDL context?) is **entirely unchecked** — the kernel takes
  every `foreign` declaration on faith already (spec §7.6), but here the *runtime* safety property
  ("this `Int` is a live pointer of the claimed shape") also has zero enforcement anywhere, tower or
  kernel. A stale/wrong handle is a C-level use-after-free or type confusion, not a caught Blight
  error.
- The event loop shape is left to whoever calls these `foreign` functions — nothing here gives a
  Blight program a *driving* frame loop the way `Console`'s native handler does; the program would
  have to hand-roll its own `SDL_PollEvent`/`SDL_Delay`/`SDL_RenderPresent` loop as a sequence of raw
  `foreign` calls with no vsync-pacing or input-handling structure to reuse.

### Design B — a `Graphics`/`Window` **effect** + native runtime handler (recommended default)

Mirror the pattern already shipped **three times** (`Console` M7, `Bytes`/`Arrays` A3a, and L1's
planned `Clock`): declare a small, purpose-built effect (e.g. `(effect Graphics (init-window (Pair
Int Int) Unit) (poll-input Unit Int) (draw-rect (Pair Int (Pair Int (Pair Int Int))) Unit) (present
Unit Unit) ...)`), and hide **every** actual SDL call inside a new `runtime/graphics.c`'s native
handler (analogous to `bl_run_console`), added to the `console_inner` row check in `driver.rs`
alongside `Console`/`FileIO`/`Bytes`/`Arrays`/`Clock`. This sidesteps every Design A problem at once:

- No n-ary argument-packing pain leaks into Blight code: `effects.c` already owns full C-level
  freedom to call whatever multi-argument SDL functions it needs internally; only the small,
  purpose-built op signatures (single `Pair`-packed argument each, exactly A3a's convention) cross
  the Blight/C boundary.
- No raw pointer ever reaches Blight code at all — the window/renderer handle lives entirely inside
  `graphics.c`'s own state (a thread-local, mirroring `g_bytes`/`g_arrays`), so there is no
  Blight-visible "is this handle still valid" question to get wrong.
- The frame loop is **native-driven**, which is the architecturally correct shape for vsync-paced
  real-time rendering: `bl_run_console`'s existing design already *is* "a native C loop resumes a
  Blight continuation once per turn, performing real I/O between resumptions" (the CPS deep-handler
  trampoline, `runtime/effects.c`) — a `Graphics` handler is the same shape with the native loop
  paced by `SDL_Delay`/vsync instead of blocking on `stdin`, calling back into the (already-shipped,
  already-tested) multi-shot continuation-resume machinery once per frame.
- Zero kernel change, same as A3a: the re-checker already type-checks arbitrary effect programs with
  no decline (`crates/blight-recheck/src/typecheck.rs` ~397-438, cited by A3a's own go-bar
  precedent), so a `Graphics` effect needs no re-checker change either, only a new op-signature
  declaration.

### Recommendation

**Design B.** It has strictly smaller Blight-facing API surface, no raw-pointer safety gap, reuses
the exact effect + native-handler + `console_inner` pattern this repo has now shipped three times
(`Console`, `Arrays`, `Clock`), and gives a correctly-paced frame loop for free from the existing CPS
trampoline. Design A remains available as an *internal implementation detail* inside `graphics.c`
itself (the handler's own C code is free to use raw `foreign`-style SDL calls, or simply link SDL
directly since `graphics.c` is already untrusted runtime C) — the distinction that matters is that
Design A's rough edges never need to be **Blight-facing** API surface once wrapped this way.

### Go-bar checklist (all items required before graphics FFI implementation work starts)

1. **A concrete `Graphics` effect signature** (op names, argument/result shapes, one Pair-packed
   argument per op per A3a's convention) covering at minimum: window creation, polling one input
   event per frame, clearing/filling a rectangle, and presenting a frame — sized to make a
   `snake`/`pong`-class real-time game buildable, not a full 2D-graphics API.
2. **A chosen concrete C library** (SDL2 is the natural default, matching every prior mention in this
   repo's docs) and confirmation it links cleanly via the existing `clang` build pipeline
   (`driver.rs`'s `build_binary`) without a new build-system dependency beyond a linker flag.
3. **A native handler design note** for `graphics.c`, mirroring `bl_run_console`'s doc comments:
   exactly how the native frame loop resumes the Blight continuation once per `present`, and how
   window/input state is threaded across resumptions (thread-local table, per A3a's `g_arrays`).
4. **Four-layer TDD**, mirroring A3a exactly: `std_graphics_loads_in_isolation`; an
   `examples/graphics_scratch.bl` scratch program; an end-to-end `builds_and_runs` test asserting a
   concrete observable result (e.g. a deterministic sequence of polled synthetic events in a
   headless/test SDL driver, not a human watching a window); and a `mono.rs` inlining regression
   confirming an effectful op used twice is not inlined (double-`init-window` safety, mirroring
   A3a's double-allocation guard).
5. Explicit acknowledgment that this brick, like the `F64` hatch, does not enlarge the trusted kernel
   at all — the honest cost is entirely in the untrusted tower (a new runtime handler + a linked C
   library), matching `foreign`'s existing "unchecked but not un-sound" TCB accounting.

Until this checklist is met, real-time graphical games remain out of reach; deterministic,
turn-based, text-rendered games (the `Console`-effect frame-loop pattern, M7) are already fully
buildable today and are the right target for anything not specifically motivated by pixel output.

**Cross-references:** `docs/roadmap.md` ("Can we build games?", capability table's "Frame loop /
real-time games" row); `crates/blight-prelude/std/f64.bl` (the `foreign`-postulate + boxed-`Int`
pattern this go-bar reuses for opaque handles); `crates/blight-codegen/src/driver.rs`'s
`console_inner` (the effect-row dispatch this go-bar extends); `crates/blight-codegen/runtime/
effects.c` (`bl_run_console`, the native-loop-resumes-continuation shape this go-bar's Design B
reuses); A3a's four-layer TDD precedent (`docs/implementation.md`, the `Arrays` effect section).
