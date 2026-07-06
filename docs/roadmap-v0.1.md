# Blight roadmap — the v0.1 program (arcs E / S / P / R)

The bootstrap is complete: M0–M30 and the proof track (see
[roadmap-post-m6.md](roadmap-post-m6.md)) delivered the graded cubical kernel, the independent
re-checker, the native/WASM backend, the share-nothing multicore runtime, the max-performance
sweep, and a sorry-free Lean mechanization of the graded core. The binding constraints are now:

1. **Surface ergonomics** — no numeric literals, hand-written fuel for every non-structural
   recursion, a spartan record story, thin diagnostics.
2. **Self-hosting Stage-1** — the `.bl`-written front end (lexer → parser → elaborator → ANF)
   exists and is kernel-certified over a toy STLC, but nothing yet closes the loop where the
   Rust kernel independently re-checks what the Blight-written front end *produces*.
3. **The open metatheory corners** — quantities × cubical, and operational semantics for graded
   handlers.
4. **Distribution** — version 0.0.0, no releases, no playground.

This roadmap defines four arcs — **E** (Ergonomics), **S** (Self-hosting Stage-1), **P** (Proof
track), **R** (Release v0.1) — every milestone with red-commit-first acceptance tests, exit
criteria, and TCB accounting.

## Governance (applies to every milestone)

- **TCB rule** — unchanged from M15–M30: the kernel diff must be empty or test-only unless the
  milestone says otherwise. Exactly one milestone below (S3, `Box→Rc`) touches kernel
  *representation*, under its own pre-registered protocol.
- **Red-first TDD protocol** — each milestone lands in (at least) two commits. Commit 1
  (`<id> red: <name>`) lands the acceptance tests guarded `#[ignore = "<id>: pending"]` (Rust)
  or as commented-out corpus entries (`.bl` goldens), plus scaffolding; CI stays green. The
  final green commit removes the guards — the flip must be visible in the diff. Negative tests
  (must-reject) land *unguarded* in the red commit when rejection is already current behavior:
  they pin the boundary before the feature widens it.
- **Differential rule** (inherited) — any backend-visible change must be bit-identical on the
  `DIFF_CORPUS` under the `BL_NO_*` flag matrix.
- **Oracle rule** — desugaring bugs are *meaning* bugs the codegen differential cannot catch
  (both paths compile the same wrong term). Every surface-sugar milestone (E1/E4/E5/E6) must add
  its rewritten or new examples to the kernel-normalizer oracle corpus
  ([crates/blight-repl/tests/oracle.rs](../crates/blight-repl/tests/oracle.rs)), pinning
  *compiled output == intended value == kernel normal form*.
- **Docs rule** — every green commit flips this file's status marker and updates the CHANGELOG.

Status markers: `[ ]` planned · `[~]` in progress · `[x]` shipped.

---

## Arc E — Ergonomics sweep (all tower/elaborator; zero TCB)

Ordering within the arc: E1 → E2 → E3 → E5 → E6 → E4 → E7 → E8. Literals unblock everything's
readability; E3's coverage pass is a dependency of E5's equation coverage; E6 builds on E5's
desugaring path; E7/E8 sweep last, once messages and formatting are stable.

### [x] E1 — Numeric literals

Bare decimal atoms parse as literals via a new `Surface::NatLit(u64)` variant (not immediate
Succ-chain expansion at parse time), elaborated to the existing `nat_to_surface` chain. v1 rule:
a bare decimal is always `Nat` sugar; `(int n)` stays the `Int` form. The reader is unchanged
(digits already read as atoms). The pretty-printer re-sugars canonical `Succ` chains to decimals
so REPL output round-trips.

**Known hazard (verified):** binder grades are parsed through `parse_surface`, and `parse_grade`
matches `Surface::Var("0"|"1")` — naive digit literals would break every graded binder
`(x A 0)`/`(x A 1)` in the corpus. The `NatLit` variant makes the fix one arm: `parse_grade`
additionally accepts `NatLit(0) → Zero`, `NatLit(1) → One`. `(Type 0)` levels are safe (parsed
from raw atom text).

- **Red tests** (`crates/blight-elab/tests/literals.rs`): `bare_decimal_parses_as_nat_literal`,
  `decimal_in_defdata_index_position_checks` (`Vec Nat 3`), `negative_decimal_rejected_cleanly`,
  `non_numeric_atom_still_symbol` (`x2`, `2x` stay symbols — unguarded pin),
  `graded_binders_still_parse_with_literal_grades` (the hazard test);
  plus `repl_prints_canonical_nat_as_decimal` (blight-repl tests).
- **Exit:** `examples/hello_nat.bl` + 3 more examples rewritten with decimals; example goldens
  byte-identical. Migration sweep of examples/ + std/ where decimals improve clarity (keep Peano
  forms in tutorial §1 for pedagogy). Oracle-corpus additions per the oracle rule.

### [x] E2 — Stdlib implicitization + unsolved-meta diagnostics

Use the *existing* brace-implicit machinery
([crates/blight-elab/src/meta.rs](../crates/blight-elab/src/meta.rs)) across the stdlib so call
sites drop explicit type/index arguments: `(safe-head sample)`, not `(safe-head Nat one sample)`.
Grade-0 leading Pi binders in std signatures become `{…}` implicits **where first-order
unification can solve them** — where it can't (higher-order motive positions), binders stay
explicit, and the milestone documents that rule. Unsolved-meta and ambiguous-meta errors must
name the binder, the definition, and the call-site span (caret diagnostic).

Implicitizing changes call arity, so this is a **breaking surface change** (fine pre-1.0): the
sweep must update every in-repo call site (std, examples, spore*, bench games) in the same
milestone, with the full example corpus + `DIFF_CORPUS` as the completeness gate.

- **Red tests:** `implicit_index_solved_from_vec_argument`,
  `implicit_unsolved_reports_binder_name_and_span`, `ambiguous_meta_reports_both_candidates`.
- **Exit:** std/vec, std/list, std/maybe, std/either, std/pair implicitized; vec_head/safe_head/
  zip_vec call sites shrink; README snippet updated.

**As-built notes (findings not anticipated in the plan):**
- *Implicit-ness and grade are independent.* The first attempt bundled a grade change
  (`ω`→`0`/erased) into the implicit binders, which segfaulted the built binaries — changing an
  eliminator argument's grade alters codegen. Implicitized binders keep their original `ω` grade;
  erasure is a separate optimization, out of scope for an ergonomics-only milestone.
- *Self-call priority on idempotent re-load.* When a module is `(load …)`ed a second time (e.g.
  `mergesort.bl` loads both `std/list.bl` and `std/list_extra.bl`, the latter re-loading the
  former), the function being re-elaborated already exists as a global carrying its implicit spec,
  so its own body's `(self A …)` self-call was mis-routed through the implicit-app path. Fixed by
  making the recursive-self-call check take priority in `Surface::App` — inside a recursive
  definition the self-name always denotes the recursion.
- *Effect subsumption in the unifier.* Solving an implicit type argument from an *effectful*
  computation's type `(! E T)` (e.g. `append`'s element type at a `parser.bl` call site whose
  argument is `(! Bytes (List Token))`) required the first-order unifier to strip the effect row
  and unify against `T`, mirroring the kernel's subsumption that made the old explicit form work.
- *`Ambiguous`-with-both-candidates is mostly defensive.* `unify` forces solved metas before
  dispatch, so a real conflict surfaces as `Mismatch` at the leaf (reported as "expected X, got
  Y" with both types re-sugared); the two-candidate `Ambiguous` path fires only for a directly
  re-solved bare meta.
- *Call sites needing an ascription.* A bare lambda parameter or a `match`-bound field variable
  has no synthesizable type, so an implicit solved from it needs a `(the T x)` ascription — a
  handful of sites (std/map, std/test, rle, map_scratch, spore_codegen_meta) carry one.

### [x] E3 — Match coverage diagnostics

Exhaustiveness is currently enforced implicitly by `Elim` construction; missing-constructor
errors surface as elaboration internals. Add an explicit coverage pre-pass over parsed clauses
(constructor set from the scrutinee's inductive signature) with a "missing cases: …" diagnostic,
including for nested patterns (column-wise, mirroring the existing lowering), plus a
warning-grade diagnostic for duplicate/unreachable arms.

- **Red tests:** `missing_constructor_names_the_gap` (Ordering with 2 arms → "missing: eq"),
  `nested_missing_case_reported_with_path` (`(Maybe (Maybe A))` missing `(just (nothing))`),
  `unreachable_duplicate_arm_flagged`; unguarded pins that exhaustive matches elaborate
  unchanged.
- **Exit:** error text in the tutorial troubleshooting section.

### [x] E4 — Records: named fields over a single-constructor `defdata`

**Design re-verified 2026-07-03** (the original "over Sigma" premise was overturned by the
pre-implementation code check, seven code-cited reasons): `(defrecord Point ((x Nat) (y Nat)))`
is sexpr-level sugar (per the [defn.rs](../crates/blight-elab/src/defn.rs)/
[measure.rs](../crates/blight-elab/src/measure.rs) precedent) lowering to a **single-constructor
`defdata`** — nominal type `Point`, constructor `mk-Point`, projection `deftotal`s
`Point-x`/`Point-y` (match-based), and `(Point-with p (y 5))` functional update rewriting to
`(mk-Point (Point-x p) 5)`. Why not Sigma: dependent match refinement decomposes `Con`-valued
indices but goes stuck on `Pair`-valued ones (check.rs `solvable_index`) — records-as-Sigma
would fail this milestone's own dependent-position test; global inlining makes a Sigma alias
structural, not nominal; spore.rs asserts the parser state is an inductive; codegen unbox/SRA
optimizes one n-field `Con`, not n−1 nested pairs; a grade-1 record is unusable through
projection chains but consumable once via match; and match/E3-coverage/E5-`defn` over records
come free. Forfeited and documented: definitional record eta (a neutral `p` is not convertible
with its repacking — v1 limitation).

Spec details (from the same check): exact 3-item shape enforced, parameterized records reserved
for v2 (the field list is binder-list-shaped and would be ambiguous with a parameter telescope);
dependent field types supported (later fields may mention earlier ones — defdata telescopes
already elaborate this); projections are real global `deftotal`s so E2's synth reads their
result types and bare `(Point-x p)` needs no ascription; `-with` is an expression-position
elaborator rewrite with a dedicated unknown-field diagnostic; hygiene guards reject duplicate
fields and generated-name collisions (`mk-Name`, `Name-field`, `Name-with`), failing atomically
via the existing run_form snapshot. No pretty-printer/LSP work (values already print as
`(mk-Point …)` via constructor resugaring; residual polish is E7's). No anonymous records, no
row polymorphism in v1.

- **Red tests** (`crates/blight-repl/tests/records.rs`):
  `defrecord_declares_type_ctor_and_projections`, `field_update_rebuilds_constructor_application`,
  `unknown_field_in_update_rejected`, `record_in_dependent_position_checks` (the
  Con-refinement property that drove the design), `defrecord_rejects_malformed_shape`,
  `generated_name_collision_rejected`, `record_constructor_match_and_coverage` (match + E3 +
  E5 `defn` over `mk-Point` patterns), `dependent_field_types_check`; a new
  `examples/records_demo.bl` in the corpus.
- **Exit:** stdlib adoption in **std/test.bl** (true stdlib, textbook record shapes, outside
  DIFF_CORPUS and the self-host closure; the spec's former std/graphics "config" target does not
  exist, and std/parser's PState is a post-E4 stretch item gated on re-blessing the verdict
  golden and preserving the S1 stdout pin). Oracle-corpus additions per the oracle rule.

**As-built notes (2026-07-03):**
- *Landed as specified post-re-verification; 8/9 tests green on the first full run.* New
  `crates/blight-elab/src/records.rs` (parse + emit + the `RecordEnv` registry + the
  `rewrite_updates` walk); `Program` gains the registry with the same snapshot discipline as the
  macro table; the `-with` rewrite runs at the top of `run_form` on every non-`define-macro`
  form, so updates work in any expression position including inside `defn`/`deftotal` bodies.
- *Idempotent re-declaration:* an identical `defrecord` re-runs cleanly (the `(load …)`
  re-splice pattern); hygiene collisions only fire on genuinely new names. Emitted forms process
  atomically (snapshot/rollback around the whole batch).
- *std/test.bl adoption:* `TestCase`/`TestSuite` became `defrecord`s; constructors renamed to the
  generated `mk-TestCase`/`mk-TestSuite` (7 in-module sites + 3 example call sites). The verdict
  golden re-blessed: the only drift is the four new projections re-verified `Ok` in every closure
  loading std/test.bl, plus records_demo.bl's globals — zero `Rejected` movement.
- *Documented v1 limitations, as pre-registered:* no definitional record eta (a neutral record
  is not convertible with its repacking); a field whose type mentions earlier fields gets no
  projection (access via `match`; `-with` names the field in its diagnostic if asked to rebuild
  around it); the update duplicates the record expression once per kept field (pure language —
  a cost, not a semantics change).

### [x] E5 — Equation-style definitions (`defn`)

`(defn name T [(pat1 … patn) body] …)` — top-level pattern-equation sugar. Arity from the Pi
telescope; desugars (sexpr→sexpr) to
`(define-rec name T (lam (x1..xn) (matchx (x1 .. xn) [(pats) body] …)))`, reusing the existing
Pattern infrastructure, nested-pattern lowering, and multi-scrutinee `matchx`. First-match
semantics; exhaustiveness via the E3 pass. Composes with E6: optional `(measure e)`/`(default e)`
clauses before the first equation route the output through the E6 lowering.

- **Red tests** (`crates/blight-repl/tests/defn.rs`): `defn_equations_desugar_and_check`,
  `defn_nested_constructor_patterns_check`, `defn_wrong_arity_clause_is_clear_error`,
  `defn_non_exhaustive_reports_missing_case` (needs E3), `defn_with_measure_clause_composes`
  (lands ignored until E6); parse_negative.rs additions.
- **Exit:** 2–3 examples rewritten in equation style (e.g. list_sum, minmax); tutorial section;
  oracle-corpus additions.

**As-built notes (deviations from the plan):**
- *Single-scrutinee `match`, not `matchx`.* The plan targeted multi-scrutinee `matchx`, but a
  hand-written `matchx`-based recursion is *not* recognized by the structural-recursion recognizer
  (it fails to infer, falling to the partial lane). So `defn` finds the single column that carries
  constructor patterns and desugars to a single-scrutinee `match` on *that* argument (which may be
  any argument — `len` matches on its `xs`, not `A`). v1 supports exactly one matched column; the
  others must be plain variables named consistently across clauses (the body references them as the
  lambda's own parameters — a `let` alias would break recursion recognition, since a self-call's
  leading argument must be the *literal* parameter). Multi-column matching stays an explicit
  `define-rec` + `match`.
- *E3 duplicate-check fix.* Nested-pattern `defn`s (e.g. `(just (nothing))` and `(just (just x))`)
  produce a single `match` with two `just`-headed arms, which the E3 duplicate check wrongly
  flagged. Fixed E3 to only flag a *saturating* repeat — a constructor arm whose sub-patterns are
  all variables/wildcards, which genuinely subsumes a later same-constructor arm — so legitimate
  nested refinements pass. (A latent E3 false positive that only `defn` surfaced.)

### [x] E6 — Measure-based totality (auto-fuel)

The headline ergonomics milestone: automate the fuel pattern that quicksort/mergesort/gcd and
the self-host readers hand-write today.

```scheme
(deftotal f (Pi ((x1 T1) ... (xn Tn)) R)
  (measure e_m)   ; e_m : Nat, over the lam binder names
  (default e_d)   ; e_d : R — REQUIRED with measure; the fuel-exhaustion value
  (lam (x1 ... xn) BODY))
```

No reader changes; recognition is positional (a 6-item `deftotal` is currently a hard error, so
no existing program changes meaning). Lowering: new `crates/blight-elab/src/measure.rs`
(`desugar_measured`, sexpr→sexpr, hooked in `program.rs::run_form` beside the `mutual` dispatch).
Emits:

1. `msr_fueled_<name>` — fuel as **parameter 0** (all real args become trailing and free to vary
   at self-calls, which is exactly what the structural recognizer permits), body
   `(match msr_fuel [(Zero) e_d] [(Succ msr_k) BODY'])` where `BODY'` rewrites every saturated
   self-call `(f a1..an)` → `(msr_fueled_f msr_k a1..an)` with a shadowing-aware traversal;
2. the wrapper `f`, seeding `(msr_fueled_f (Succ e_m) x1..xn)`.

Invariant: with fuel `k ≥ measure+1` the default arm is dead code iff the user's decrease claim
holds. Hard errors: measure without default; unsaturated self-reference (suggests
eta-expansion); self-call inside `e_m`/`e_d`; a measured definition with no self-calls; a binder
named `msr_fuel`/`msr_k`; implicit binders in the telescope (v1).

**The honest contract (documented and test-pinned):** the kernel certifies **totality
unconditionally** — the helper is a genuine structural `Elim` over `Nat`, and nothing about the
rewrite is trusted. Measure **adequacy** is *not* checked: a wrong measure yields "total but
returns the default", never unsoundness — and the semantics stays exact, because `f` *is* the
fueled unfolding, so every in-language proof about `f` is about the real function including its
default arm. Deferred extensions, recorded here: lexicographic `(measure e1 e2)` via nested
helpers (v2); `(measure e :proved p)` per-call-site tactic obligations (v3).

- **Red tests** (`crates/blight-repl/tests/measure.rs` + unit tests + parse negatives):
  `measured_quicksort_declares_total` (no `Later` in the elaborated term),
  `measured_quicksort_computes_by_refl` (the kernel certifies behavior end-to-end),
  `measured_definition_rechecks_ok` (re-checker `Ok` on both emitted globals),
  `wrong_measure_is_total_but_returns_default` (the contract, pinned),
  `measure_without_default_is_clear_error`, `measure_on_body_without_self_calls_is_error`,
  `unsaturated_self_reference_is_clear_error`, `deftotal_measure_clause_shapes_rejected`,
  `desugar_measured_emits_helper_and_wrapper` + `shadowed_self_name_not_rewritten` (unit
  goldens).
- **Migration (exit):** quicksort.bl (`(measure (length xs)) (default xs)` — deletes the four-helper
  fuel scaffold), mergesort.bl (both `merge` and `msort` measured), gcd.bl (`(measure (plus a b))
  (default a)`). All are in `DIFF_CORPUS` and re-verified bit-identical (fast==slow) with the same
  output. **Deliberately kept on hand fuel,** with comments saying why: collatz_steps.bl (no measure
  exists — that is the conjecture; its exhaustion arm is semantically live — the pedagogical
  contrast case) and std/lexer.bl + std/parser.bl (effectful and performance-sensitive).

**As-built notes:**
- *`spore_reader.bl` migration deferred.* The plan listed migrating the self-host reader's
  `resolve-ty`/`resolve-term`, but they are load-bearing for the S1 self-host demo and use a subtle
  `bsexp-size` fuel; migrating them is a follow-up once the mechanism has soaked (the sorting
  examples fully demonstrate the exit criterion).
- *E5×E6 composition implemented.* A `defn` with leading `(measure e)`/`(default e)` clauses emits a
  *measured* `deftotal` (re-dispatched through `desugar_measured`). The measured-`defn` path names
  the lambda parameters after the *type's* binders (so the measure expression, written over those
  names, resolves) and `let`-aliases any differently-named non-matched clause variable — safe
  *because the E6 helper recurses on the synthesized fuel, not on any argument*, so an argument
  alias cannot break recursion recognition (unlike the plain `defn` path, where it would).
- *Totality is witnessed structurally.* `measured_definition_is_total_no_later` checks the emitted
  helper's elaborated term is `Later`-free — i.e. it compiled to a structural `Elim`, not the
  partial lane — which is the operational meaning of "the kernel certifies it total".

### [x] E7 — Diagnostics quality pass

Systematic error-message audit: every `ElabError::BadForm` gets a form-specific message + span;
kernel `TypeError` rendering gains expected/actual type highlighting (re-sugared, decimals
post-E1); "did you mean" suggestions for unbound names (edit distance over scope + globals).

- **Red tests** (`crates/blight-elab/tests/diagnostics.rs`): golden rendered output for an
  unbound-var typo (suggests), a lam arity error, a type mismatch in `the` (both types
  re-sugared), and a non-structural `deftotal` (suggests `(measure …)`).
- **Exit:** goldens documented in [testing.md](testing.md).

**As-built notes (2026-07-03):** all four landed as specified — did-you-mean via Levenshtein
over locals+constructors+datatypes+globals (suggestion appended to the `Unbound` payload;
`narrow_span` splits on whitespace so LSP spans survive); lam-arity detected structurally in
`kernel_check_def` (leading-`Lam` vs leading-`Pi` counts, type via `pretty_term`); the one
kernel-side change is message-only (the constructor-mismatch strings render `` `Nat` ``, not
`DataName("Nat")` — rendering is exactly what the spec authorized); the `deftotal` message now
teaches the E6 measure clause. Suite 853/853; the "every BadForm gets a form-specific message +
span" ambition beyond these four shapes is folded into E9/R-era polish rather than blocking
here.

### [x] E8 — Formatter + LSP surface polish

Wire the existing formatter (`crates/blight-elab/src/fmt.rs` — correctness already pinned by the
fmt_corpus idempotence + semantics test) through LSP `textDocument/formatting` and a `blight fmt`
CLI subcommand; this milestone is exposure only. Add LSP completion (globals, constructors,
keywords, std module paths after `(load "`).

- **Red tests:** `lsp_formatting_returns_fmt_output`, `completion_lists_globals_and_keywords`
  (blight-lsp inline harness); `blight_fmt_rewrites_file_in_place_idempotently` (CLI).
- **Exit:** VS Code extension bumped; README LSP feature table updated.

**As-built (2026-07-03):** red at 0a2e007 (the pre-named tests plus an extra
`completion_lists_std_modules_after_load` — the `(load "` context is detected *lexically*, since
a mid-keystroke buffer is unreadable and the definitions index empty exactly when path completion
is wanted). The CLI half was already live (Wave 9/T2), so its roadmap-named test landed as an
un-ignored idempotence pin. Green: `formatting_edits` (None on lexically-malformed text / empty
on canonical / one whole-document edit otherwise) and `completions_at` (definitions index +
curated keyword set, or embedded std paths inside a load string) as pure helpers in the inline-
harness style; capabilities advertised; `blight_prelude_embed::module_names()` added via a
macro so the lookup and the enumeration share one list. Wire-protocol test covers both methods
end-to-end. Extension 0.2.0 → 0.3.0; its README feature list updated (also un-rotted: rename for
local binders shipped in T1 but was still listed as "not yet implemented").

---

## Arc S — Self-hosting Stage-1 (bridge + scale)

Context: the `.bl` pipeline String → BSexp → BSurf → (Σ a. BTm g a) → BAnf is complete and
kernel-certified over a toy STLC (spore_reader/elab/compile/pipeline.bl over std/lexer +
std/parser), with the pure parts re-verified `Ok` by the independent re-checker, and an
in-process verdict-level differential (D10) already green. What Stage-1 adds: a compiled native
proposer, the string front end under test, and the kernel re-checking *terms*, not booleans.

### [x] S1 — End-to-end self-host demo

A ~30–50 line buildable `examples/selfhost_check.bl`: `read-file` (C1) → `bcheck-string` →
print verdict + ANF size fingerprint, with `main : (! ⟨Console Bytes⟩ Unit)` (the combined-row
pattern of std/io.bl).

- **Red test** (llvm-gated, main.rs test module): builds + runs it on a good and a bad input
  file, asserting the two verdict lines.

### [x] S2 — Proposer/disposer bridge (the kernel re-checks the Blight front end's output)

**Marshalling:** canonical Blight *surface text* on stdout, sentinel-prefixed
(`BRIDGE <i> ACCEPT (the ⟦a⟧ ⟦tm⟧)` / `BRIDGE <i> REJECT`), printed by a new
`crates/blight-prelude/spore_print.bl` (`bty-print`/`btm-print`/`bsig-print`) from the
**BSig/BTm layer before `bcompile`** (BAnf is the wrong layer to round-trip). The embedding
⟦·⟧ maps the toy theory into the real one: `Base ↦ (defdata Base () (b0))`,
`Arr a b ↦ (Pi ((v ⟦a⟧)) ⟦b⟧)`, TVar/TLam/TApp ↦ named var/lam/application — every lam fully
`the`-annotated (BTm's intrinsic indices supply dom/cod at every node) so the payload stays in
checking mode. The Rust host runs `(defdata Base () (b0))` + payload through the **unmodified**
reader → elaborator → kernel and demands `Checked`: the trusted kernel checks the real-theory
judgement. Type-preservation of ⟦·⟧ is documented informally in the example header — a wrong
embedding surfaces as a differential failure, never as unsoundness. The printer is the natural
first consumer of E6 (`(measure (btm-size t))`).

Rejected alternatives, for the record: blight-net binary values (new untrusted decode on the
Rust side, no reuse of the existing door); evaluating the pipeline in the Rust NbE evaluator
(blocked by the O(n²) `Term::clone` cost and adds no implementation independence).

- **Differential:** ~12 toy-fragment *source strings* baked into `examples/selfhost_bridge.bl`
  (the D10 corpus programs as strings, plus string-level-only cases: reader garbage, an unbound
  name, shadowing `λx.λx.x`, a domain mismatch under a binder, an Arr-typed argument). A
  Rust-side `Case` table pairs each with verdict + expected type; both directions must agree; a
  corpus-shape guard asserts both verdicts occur.
- **Red tests:** `bridge_printer_loads` (no llvm; printer globals exist, re-checker `Ok`),
  `bridge_printer_output_checks_for_demo_id` (no llvm; refl-pins the printed string at
  spore_pipeline scale — if that env is over the perf cliff, downgrade to llvm-gated and say
  so), `bridge_kernel_rejects_tampered_payload` (no llvm; a forged
  `(the (Pi ((v0 Base)) Base) (lam (v0) (v0 v0)))` **must** error — the disposer-has-teeth
  test), `example_selfhost_bridge_builds_and_runs_and_kernel_rechecks` (llvm; the full
  differential), `selfhost_bridge_corpus_covers_reject_shapes`.
- **Files:** new spore_print.bl; new examples/selfhost_bridge.bl; spore.rs; the main.rs test
  module (generalize `build_and_run_example_opts` to return stdout); fix the stale D10 doc note
  about the string front end.

**As-built notes (deviation from the plan):**
- *Print the source `BSurf`, not the intrinsic `BTm`.* The plan called for a dependent
  `btm-print`/`bsig-print` over the intrinsic `BTm`, fully annotating every lam. That is a large,
  dependent-match-heavy pretty-printer. The as-built printer is much simpler and equally faithful:
  since `belaborate` is structure-preserving and the *source* `BSurf` already carries each lam's
  domain, `spore_print.bl` renders the source at the elaborator-inferred type `a`, wrapped in a
  single top-level `(the ⟦a⟧ …)`. That top-level ascription puts the whole term in checking mode,
  so inner lams need no annotation — the corpus is redex-free (no application whose head is a lam),
  which makes checking-mode propagation sufficient. `bty-print`/`bsurf-print` are plain,
  non-dependent structural recursions (re-verified `Ok` by the independent re-checker). Printing
  from `BTm` to also cover beta-redexes (per-node annotation) is a documented follow-up.
- *Hand-built `BSurf` corpus, not the string reader.* The corpus is 7 hand-built `BSurf` values
  (id, higher-order id, application, const/shadowing — ACCEPT; self-application, unbound variable,
  domain mismatch — REJECT), keeping the bridge program pure (`Console` only, no `Bytes`). The
  string front end (reader → parser) is separately exercised end-to-end by S1's `selfhost_check.bl`;
  the novel thing S2 adds is the kernel re-checking a *term* the elaborator produced, which this
  fully delivers. The `bridge_printer_output_checks_for_demo_id` refl-at-scale test is deferred to
  S3 (the in-kernel `refl` over the printed pipeline needs the Box→Rc perf fix).

### [x] S3 — Term representation: Box→Rc (refl-at-scale; TCB-adjacent)

Sequenced **after** S2 — the bridge doesn't need it (the proposer runs natively compiled; the
kernel checks only the small emitted judgement). Payoff: the deferred `reader-demo-refl`
(spore_reader.bl's documented go-bar) goes live — in-process, kernel-certified refl agreement
over `bcheck-string` — and the 40-line blocker comment is deleted.

Scope: mechanical `Box<Term>` → `Rc<Term>` (42 Box fields in kernel term.rs; ~2300 sites across
kernel/elab/recheck/codegen). Protocol, all gates pre-registered in the red commit:

- (a) representation-only rule — no signature/logic changes beyond Box→Rc; audit every `*x` move
  → `Rc::try_unwrap`-with-clone-fallback (behavior identical; only sharing changes);
- (b) full workspace suite green;
- (c) verdict differential: a harness recording per-global (kernel verdict, recheck
  Ok/Declined/Rejected) over the entire stdlib + examples + spore corpus, captured on main,
  byte-identical after;
- (d) `differential_fast_paths_are_bit_identical` stays bit-identical;
- (e) criterion benches within 5%, plus the spore_reader refl re-measure (the go-bar's own
  success metric);
- (f) kernel diff reviewed line-by-line + cargo-mutants over the touched kernel files.

- **Red:** `reader-demo-refl` added to spore_reader.bl (commented/guarded) + the
  verdict-differential harness landing green on main first.

**As-built notes:**
- *All gates passed; the payoff prediction did not.* The conversion itself was clean: (a) the
  kernel diff is Box↔Rc plus imports plus one audited helper (`term::unshare`, the
  `Rc::try_unwrap`-with-shallow-clone-fallback the protocol prescribed — the compiler surfaced
  **zero** move-out sites inside the kernel itself; all 18 were in elab/tests); (b) 835/835 tests;
  (c) the corpus verdict report byte-identical; (d) the full `BL_NO_*` matrix bit-identical;
  (e) all 50 criterion points within ±5% (worst confirmed regression +2.5%, two >5%
  *improvements*); (f) cargo-mutants scoped to `term.rs` — the one kernel file with new logic —
  found exactly one mutant (`unshare` → `Default::default()`), and it is *unviable* (`Term` has
  no `Default`), so the mutation gate is vacuous for this diff, stated honestly: `unshare`'s
  behavioral coverage comes from its 18 call sites under the full suite plus gates (c)/(d), not
  from mutation testing. (A kernel-wide sweep incidentally run during this milestone surfaced
  ~38 pre-existing uncaught mutants in `check.rs` — main-branch test-coverage gaps unrelated to
  this diff, being triaged in their own session.)
  But the go-bar itself did **not** open: `reader-demo-refl`, re-enabled and re-measured post-Rc,
  was killed at ~15 CPU-min in release (pre-S3: killed at ~7 — both censored kills of the same
  effectively non-terminating computation). The O(n²) closure-clone cost the N1 comment blamed
  was real but not dominant; the post-S3 adversarial review identified the actual mechanism —
  `do_elim`'s eager computation of *discarded* induction hypotheses, ~2^min(codepoints) steps
  per `nat-eq`, shared at parity by both engines, with the "kernel is fast on these" appearance
  being the elaborator's deliberate ground-value gate — see arc N (milestones N5-N7; numbered past the historical Wave-track N1 ValueChain / N2 metering / N4) for the code-cited findings
  and the fix plan. The refl stays commented in spore_reader.bl with the corrected analysis.
- *`Send` fallout was confined to tests plus one audited assertion.* `Rc` makes `Term` `!Send`;
  production code needed exactly one change — the llvm-gated backend driver hands `&Term` to its
  big-stack worker thread under an `AssertSend` wrapper with a documented safety argument (the
  parent blocks on `join` inside the same scope, so access is strictly serialized — the only
  `unsafe` in the milestone). Five test files that returned `ElabEnv`/`Outcome` values across
  `join()` were restructured to run assertions on the worker thread (closure-passing helpers);
  the pipeline bench got a hand-rolled `main` running the whole criterion harness on one
  64 MiB-stack thread so elaborated terms never cross a thread boundary.
- *The red-phase harness paid for itself before the change landed.* Capturing the golden on main
  surfaced: four examples whose re-check is over the perf cliff (RECHECK_SKIP, with a
  `BL_VERDICT_DISCOVER` watchdog mode for finding such units); **two pre-existing false
  `Rejected` verdicts** (flat_esc.bl `main` — nested `Pair`-match inference; spore_codegen_meta's
  `aeval-k-correct` — trans-chain rhs boundary), both re-checker bugs filed separately and
  deliberately pinned as-is in the golden; a stdlib coverage-guard gap (std/graphics.bl); and an
  unrunnable pipeline bench (reader nesting limit + missed E2 arity sweep), fixed on main first.

### [ ] S4 — Grow the self-hosted fragment

Toy STLC (Base/Arr) → a real Blight fragment, one sub-milestone per feature, each re-running the
S2 bridge differential and growing its corpus by ≥5 cases:

- **S4a** — Nat literals + a second base type (post-E1). **[x] DONE (2026-07-05).** `BTy` gains
  `NatT` (name distinct from spore.bl's `Nat` datatype); intrinsic `BTm` gains `TZero`/`TSuc`;
  `BSurf` gains `su-zero`/`su-succ`; the reader parses the `Nat` type keyword, the `(succ …)` form,
  and numeric literals (a digit-atom desugars to a nested `su-succ` — detected with `nat-eq` ONLY,
  never `nat-lt` on a codepoint, which re-triggers the discarded-IH blowup N5 fixed). The S2 bridge
  differential grew by 7 Nat cases (kernel-`refl`-certified accord with the Rust front end);
  `selfhost_bridge.bl` (+4 Nat cases, kernel re-checks each `(the Nat …)` payload) and
  `selfhost_check.bl` (numeral + Nat successor read from disk, native run) both extended.
- **S4b** — user inductives: BTy gains declared datatypes; `belaborate` gains constructors +
  match on non-indexed inductives. **[x] DONE (2026-07-05).** Two representative non-indexed
  inductives baked into the object language: `BoolT` (nullary `TTrue`/`TFalse` + the two-branch
  eliminator `TIf`) and the sum `Sum l r` (data-carrying `TInl`/`TInr` + the variable-BINDING
  eliminator `TCase`, whose branch-binder types `l`/`r` are recovered from the scrutinee's
  runtime-discovered type via a `split-sum` view + `bty-coerce`). Full pipeline (intrinsic/elab/
  compile/print/reader); the reader's head dispatch was refactored to a flat `classify-head` to
  absorb six special forms without deep `(match is-X …)` nesting. Differential grew +12 cases
  (6 Bool, 6 Sum; kernel-`refl`), the bridge +7 (real-kernel disposer re-checks each `match`/`inl`/
  `inr` payload), `selfhost_check.bl` +2 sources (the Bool `if` and the Sum `case`, read from disk
  and run natively). A general *user-declared* datatype mechanism (arbitrary inductives via an
  object-level datatype environment) remains a deeper follow-up.
- **S4c** — dependent Pi (BTy indexed by context; the intrinsic two-index machinery is already
  proven by `spore_intrinsic.bl`).

Each sub-milestone extends BSurf/BTy/BTm + `belaborate` + spore_print + the ⟦·⟧ embedding, and
keeps everything re-checker-`Ok`.

### [ ] S5 — Stage-1 declaration

**Exit:** the Blight-written front end checks a designated corpus subset (≥10 real examples
inside the S4 fragment) with 100% kernel agreement via the S2 bridge;
[implementation.md](implementation.md)'s Stage table updated. This is the go/no-go gate for a
future Stage-2 (the self-hosted checker as the primary front end).

---

## Arc N — The eliminator cliff (post-S3; mechanism identified)

Context — what S3's follow-up review actually established (all claims code-cited and measured;
the adversarial review of 2026-07-03 falsified the first draft of this arc):

1. **Root cause, both engines, CONFIRMED: `do_elim` eagerly computes discarded induction
   hypotheses.** Every surface `match` compiles to the full dependent eliminator whose methods
   always bind an IH per recursive argument, and both evaluators compute that IH
   *unconditionally* (kernel [normalize.rs:793-798](../crates/blight-kernel/src/normalize.rs),
   recheck [normalize.rs:325-331](../crates/blight-recheck/src/normalize.rs)) even when the
   method body never references it. `nat-eq` therefore costs ~2^min(codepoints) eliminator
   steps: comparing two `'l'`s (codepoint 108) is ~2^108 steps. Measured slope ×~2.0 per +1
   codepoint on match-forced `nat-eq k k`, k=8..22, in **both** engines (parity ±10-15% at every
   k). The RECHECK_SKIP cliffs and the reader-demo-refl kill are all this one defect at 0%
   progress — palindrome dies comparing its *first* character; the refl dies inside `is-lam-kw`'s
   first `nat-eq(108,108)`. Fuel is innocent (the reader's fuel is 11).
2. **The "kernel fast / re-checker slow" asymmetry was a workload-selection artifact.** The
   elaborator *deliberately gates* ground-value conclusions away from the kernel
   ([elab.rs:3158-3175](../crates/blight-elab/src/elab.rs), doc at :164-175 naming "the
   palindrome/mergesort/quicksort blowup"), while `--recheck` feeds every typed global to
   `recheck_judgement` ungated ([main.rs:588-604](../crates/blight-repl/src/main.rs)). Fed the
   identical judgement via `check_top_with`, the kernel diverges identically. There is no fast
   twin to copy from; there is one defect in two deliberately mirrored implementations.
3. **Secondary, real, bounded:** (a) `Value` trees have no structural sharing — `do_elim`
   deep-clones constructor arguments twice per iota level and `Var` lookup deep-clones values,
   a Θ(k)-per-level polynomial multiplier on the exponential; (b) blight-recheck's `RTerm` never
   got S3's Box→Rc treatment (its closures deep-copy binder bodies) — bounded to ~15% by the
   measured parity, so hygiene, not the cliff; (c) refl/Path checking evaluates the goal ~3×
   (both endpoints + PLam boundary + define-by re-check).
4. **Dead hypotheses (do not re-litigate):** a global-value cache (globals are inlined at
   elaboration — [elab.rs:1789-1796](../crates/blight-elab/src/elab.rs); no Global variant
   exists in either term type); conv-strategy divergence (both engines quote neutrals; conv ≈ 0
   samples in stuck profiles); literal fast-path asymmetry (both consume identical Con trees);
   deep-chain env lookup (impossible under global inlining — eval-time depth is lexical);
   "S3 regressed the kernel 7→15 min" (both numbers are manual kills of a 2^100+-step
   computation — censored data, no throughput signal).

Method rules (amended by the review):
- **Instrumented evidence before fixes** — counters *and* profilers (the sampled `do_elim`
  towers cracked this case at zero commit cost). Feature-gated counters land first:
  `ih_computed`/`ih_discarded` at the two do_elim IH sites, hung off the kernel's existing
  `tick()` infrastructure, plus an allocation counter (counting `#[global_allocator]`).
- **Slopes, not timeouts.** The unit of measurement is a fitted scaling exponent on a
  size-parameterized micro-reproducer, never pass/fail under a kill budget (a censored
  observation distinguishes nothing). Rung 0 of the ladder: match-forced `nat-eq k k`, k=8..24
  (pre-fix slope ×~2.0/unit; post-fix target: polynomial, slope-fit flat).
- **One variable at a time**, kernel fixes flag-gated (`BL_NO_*`) into the differential matrix;
  full S3 gate protocol (verdict golden, bit-identity, benches, mutants) per kernel-touching fix
  — the S3 infrastructure is the reusable asset here.
- **Independence constraint (hard):** blight-recheck may copy the *idea* of a fix, never kernel
  code.

### [x] N5 — Eliminate eager discarded induction hypotheses (both engines; TCB-touching)

The mechanism-fix milestone. **Opens with a half-day design spike** (a lesson bought twice on
2026-07-03: optimistic labels don't get to sit in documents): the panel's "IH-free case trees
are elaborator-only, zero TCB" claim does not type-check against the kernel grammar — `Elim`'s
typing rule fixes method arities to include IH binders and no non-recursive `Case` form exists,
so genuinely IH-free terms mean a new kernel variant or changed arities (TCB-touching either
way; the `mono.rs` precedent lives in the *untrusted* backend and does not transfer). The spike
decides among, cheapest-plausible first:
1. **Dead-IH detection in `do_elim` (kernel-internal, no grammar change):** occurs-check whether
   the method body references the IH binder (cacheable per method closure); if dead, pass a
   stuck dummy neutral — O(1), never forced. ~Dozen lines under the full S3 gate protocol, then
   an independent mirror in recheck.
2. **Lazy IH (evaluator-only):** thunk the IH at the do_elim site; force on first use. Same
   values, deferred work; heavier (the `Value` domain grows a thunk form) but covers exotic
   cases where deadness is not syntactically visible.
3. **Kernel `Case` variant + elaborator emission (grammar + typing rule change):** the
   Agda-shaped long-term answer; largest TCB delta, only if (1)/(2) leave measured residue
   (e.g. through higher-order motives).
Whichever lands, emitted-term changes (if any) are additionally gated by the oracle corpus +
DIFF_CORPUS; evaluator-only changes are gated by the byte-identical verdict golden.

- **Red:** the `ih_computed`/`ih_discarded` counters + the rung-0 micro-reproducer harness with
  its pre-fix slope pinned as a golden (the regression test is the *slope*, not a timing).
- **Exit (re-annotated ladder, in order):** rung-0 slope flat → 1-char palindrome variant
  (codepoint-parameterized — codepoint *value* is the exponent, string length is irrelevant) →
  RECHECK_SKIP emptied + verdict golden re-blessed (the four units flip `Skipped → Ok`/
  `Declined`, reviewed line-by-line, nothing else drifts) → json_scratch (>68 min baseline) →
  `reader-demo-refl` uncommented and green in suite time (the original go-bar; the spore_reader
  blocker NOTE deleted, not amended) → the S2-deferred
  `bridge_printer_output_checks_for_demo_id` re-attempted.
- **Pre-registered fork:** if the fix family cannot clear the gates, the alternative exit is
  *policy alignment* — gate ground-value judgements in `recheck_before_emit` exactly as the
  elaborator gates the kernel, making RECHECK_SKIP a documented policy rather than a bug — and
  N7 fires.

**As-built notes (2026-07-03):**
- *The spike picked candidate (1) and it sufficed alone.* `uses_binder` (a shifted occurs-check
  whose binder map mirrors each engine's own `shift` exactly — the kernel's in `check.rs`, the
  re-checker's `shift_free_cut`; `System` treated conservatively as "used" since kernel `shift`
  scopes it out) + a stuck sentinel `Neutral::Var(usize::MAX)` for dead binders, behind
  `BL_NO_DEAD_IH=1`. ~Dozen live lines per engine, independently implemented. Lazy-IH thunks and
  kernel `Case` trees were never needed.
- *The ladder fell end to end.* Rung 0: kernel IH counts on match-forced `nat-eq k k` went from
  [361, 618, 1131, 2156, 4205] (×~2.0/step) to [7..11] over baseline (+1/step, exactly linear);
  recheck [8..12], same law, independently counted — the flipped nbe_scaling pins now hold both
  engines to it. The RECHECK_SKIP corpus: palindrome >120 s → **0.1 s**, map_scratch >60 s →
  2.5 s, json_scratch >68 min → **26.5 s**, regex_scratch >60 s → 30.8 s; the list is now empty
  and the verdict golden re-blessed (89 `Skipped → Ok`; the two pinned false-`Rejected` lines
  deliberately unchanged — separate fixes in flight). `reader-demo-refl` — the go-bar N1 and S3
  both predicted and missed — is **live and green in 5.96 s in a debug build** (was 29 debug-min
  / 15+ release-CPU-min, killed); the 40-line spore_reader blocker NOTE is deleted. The
  S2-deferred `bridge_printer_output_checks_for_demo_id` refl-at-scale pin is authored and live:
  the kernel runs the whole self-hosted proposer pipeline (belaborate ▷ verdict ▷ printers ▷
  string concat) inside conversion and pins its exact output string (needed the 64 MiB-stack
  treatment in debug builds).
- *json/regex at ~30 s are the N6 signal:* feasible but slow — consistent with the predicted
  Θ(k)-per-level `Value` deep-clone polynomial multiplier. N6's value-sharing item has its
  measured justification; the other two N6 items still await theirs.

### [~] N6 — Constant-factor hygiene (post-N5, measured-in, each optional)

Only what the post-N5 ladder still needs, in measured order of leverage:
- [x] **Value-tree sharing** (kernel + recheck): `Rc` children in `Value` / interned `ConName` —
  kills the Θ(k)-per-level deep clones (the polynomial multiplier). S3-shaped protocol.
  *Landed 2026-07-03 under an amended pre-registration — see the as-built note below.*
- [ ] **RTerm Box→Rc** (recheck only): S3-for-recheck; parity bounds the win at ~15% on eliminator
  workloads, more on closure-heavy ones. Verdict golden byte-identical.
- [ ] **Refl endpoint sharing / re-evaluation churn** (kernel + recheck): stop re-evaluating the
  witness/endpoints ~3× (PathP eager endpoint eval + PLam boundary + define-by re-check);
  measured target ~3-10× constant on refl-heavy goldens. *Now holds the scale-pair quadratic's
  measured justification (the Value-sharing profile below): eval/do_elim materialize a fresh
  O(level) chain per level and drop it — representation sharing cannot reach it.*

**Pre-registration (2026-07-03, Value-tree sharing — the item with two measured justifications:
json/regex re-checks at 26.5/30.8 s and the depth scale-pair at ~19.6× for 4×):** mechanical
`Box<Value>`/`Box<Neutral>` → `Rc` in kernel `value.rs` (27 fields) + `normalize.rs` sites, and
independently in recheck `value.rs` (6 fields); one audited `unshare`-style helper per engine if
moves exist; `ConName` interning explicitly deferred (API-shaped, needs its own justification).
No new `Send` fallout is possible (`Value` already holds `Rc<Term>` since S3). Gates: full
suite; verdict golden byte-identical; llvm bit-identity; criterion vs a fresh `pre-n6` baseline
(±5%, isolated re-measure arbiter); mutants over any new logic. Payoff targets, pre-registered:
the scale-pair ratio drops from ~19.6× toward the linear ~4–6× band (then tighten its bound from
35× to 10×), and json/regex re-checks drop meaningfully below ~30 s. Kill criterion: if the
ratio does not drop below 12×, the sharing hypothesis is wrong — revert and re-profile instead
of keeping speculative churn.

**As-built (2026-07-03, kill criterion fired → pre-registration amended, user decision):** the
conversion landed complete (zero `Box<Value>`/`Box<Neutral>` remnants, audited `unshare_value`/
`unshare_args` per engine) and every safety gate held: suite 858/858, verdict golden
byte-identical, B1 llvm bit-identity matrix green, mutants over the diff 129 tested / every
viable mutant killed (one initially missed — recheck `unify_index`'s `(Data, Data)` arm — now
mutation-pinned by `unify_index_data_arm_decomposes_and_clashes`; the `#[ignore]`d corpus gates
don't run in the mutants oracle, so arm-level behavior needs direct probes). Payoffs, measured
as same-machine paired stash-twins: json_scratch 17.2 → **8.7 s** (2.0×), regex_scratch 24.7 →
**5.3 s** (4.7×), whole verdict corpus 49.4 → 20.4 s (2.4×), scale-pair absolute 1.37 s →
0.73 s (~1.9×) — but the scale-pair *ratio* only 16.6× → 15.3× (five runs each, tight), above
the pre-registered 12× kill line. The re-profile (kill protocol) re-attributed the quadratic:
the hot frames are recursive `drop_in_place`/`clone`/`Vec::from_iter` under `eval`/`do_elim` —
freshly *materialized* O(level) chains (refcount 1, sharing never engages), i.e. re-evaluation
churn, item 3's territory, its measured justification. Decision: keep — the deep-clone
hypothesis for the ratio is falsified, but the change decisively meets the other pre-registered
target on the workloads that motivated N6; the ratio bound tightened 35× → **20×** (earned from
15.3 measured, not the unearned 10×; item 3 must earn the rest). Recorded cost: pipeline
`end_to_end` criterion rows regressed ~4–5% (isolated arbiter confirmed; µs-scale Rc constant
overhead on tiny terms) — runtime benches flat-to-improved. `ConName` interning stays deferred.

### [x] N7 — Decision checkpoint (fires only on N5 fork) — closed without firing

N5 cleared every gate and the full ladder on 2026-07-03, so the fork (policy-alignment fallback)
never triggered. Recorded as closed rather than deleted so the pre-registration stays auditable.
The original trigger text follows for the record.

Trigger (named, P4-style): the N5 fix family fails the S3 gate protocol, or fails to flip the
rung-0 slope + RECHECK_SKIP rungs, within two milestone-sessions of effort. Then: adopt the
policy-alignment exit permanently; record in [implementation.md](implementation.md)'s Stage
table that Stage-1 certification is the S2 verdict-level bridge (delivered, scaling) and that
whole-pipeline in-kernel refl is out of scope for v0.1; keep the rung-0 slope harness as the
standing measurement so the question stays falsifiable for v0.2. No code.

---

## Arc P — Proof track continuation (Lean; external, zero TCB)

Red-commit protocol for Lean (where `sorry` is CI-banned and a theorem cannot be stated without
a proof): the red commit lands the obligations as **Prop-valued definitions**
(`def preservation_stmt : Prop := ∀ …`) in a new Obligations module — buildable, sorry-free,
pinning the exact statements. The green commit adds `theorem preservation : preservation_stmt`
etc. and wires the module into the root import.

### [x] P1 — Effects operational semantics

Extend [BlightMeta/Effects.lean](../mechanization/BlightMeta/Effects.lean) from the static
discipline to a small-step semantics with evaluation contexts for perform/handle (delimited
continuation capture), proving preservation and the resume-once theorem *operationally*.

- **DONE (2026-07-04) — settled with a sharp negative result, machine-verified (all headline
  theorems `#print axioms`-clean, no `sorryAx`; landed via a 4-way worktree fan-out, every claim
  rebuilt + axiom-checked in the main repo):**
  - **Proved:** the deep-handler small-step `Step` (one-hole `ECtx`, `handle_perform` capturing
    `k = lam (handle E[var 0] retC opC)`) + the `Effects.Tm` substitution stack; `progress` (closed
    pure-rowed → value or step); `preservation_core` (the type-preserving fragment `StepC` = every
    step **except** `handle_perform`, incl. `handle_ret`, preserves type + ambient and only weakens
    the row, at runtime ambient `σ ∈ {ω,0}`); and the **operational resume-once** trio
    (`resume_once_operational`/`never_resumes_operational`/`cont_slot_demand_after_arg_subst`) —
    `handle_linear_at_most_once` upgraded to the actual `handle_perform` redex.
  - **Refuted (machine-checked):** `handle_perform_not_preserving` — the deep-handler step does NOT
    preserve types against this static presentation, because the static `handle` rule types the
    continuation binder at `opCod` (a value), not `opCod → B` (a function); a faithful deep handler
    substitutes a `lam` there, so `handle (perform tt) (var 0) (var 0) : bool` steps to a `lam`
    (`lam_not_bool`: no typing at `bool`). The grade discipline stays sound; the continuation
    *typing* is the blocker. Recovering subject reduction needs `handle` to bind `k` at `opCod → B`.
  - Not attempted: multi-op rows (the crux refutation was the headline; single-op suffices for it).
- **Exit — MET:** metatheory-mechanized.md + metatheory.md §2 updated with the operational evidence
  and the negative result.

### [x] P2 — Dependent.lean substitution + preservation

**Settled + machine-verified.** The substitution lemma is **proved**; `preservation` is **proved
false** for this fragment (a real metatheoretic finding, not a gap). Both questions the milestone
posed are now definitively answered with zero-`sorryAx` Lean.

- **Prerequisite (2026-07-04, `10596c9`):** `Expr.subst_subst_comm`, the substitution/substitution
  commutation lemma, plus its cancellation helper. `#print axioms` = `[propext, Quot.sound]`, no
  `sorryAx`.
- **Substitution lemma DONE (2026-07-04):** the full dependent substitution lemma — `subst_lemma`
  (the `k=0` public form `HasType (A'::Γ) e B σ φ → φ.get 0 ≤ π → ∃ φ', HasType Γ (subst0 a e)
  (subst0 a B) σ φ'`) + its telescope workhorse `subst_lemma_tele` + the helper ladder. `#print
  axioms subst_lemma` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Found en route (via
  a 5-way independent worktree fan-out): the `ctxInsert` formulation provably cannot do the `lam`
  case (it head-shifts the domain), so the lemma is stated over an explicit telescope `Δ ++ A'::Γ`.
- **`preservation` — PROVED FALSE (2026-07-04):** `preservation_false` in `Dependent.lean`, `#print
  axioms` = `[propext, Quot.sound]`, no `sorryAx`. Subject reduction genuinely fails for this
  syntax-directed, conversion-free `HasType` via the `app2` (argument-congruence) case. Settling it
  took **two adversarial fan-outs plus hand-verification**, because the question is subtle:
  - Fan-out #1 said "false" with a *wrong* counterexample — **refuted** (machine-checked): `lam` has
    no domain annotation, so a value's `pi`-codomain is non-unique and `app2`'s `Value f` is always a
    `lam`; a *lam-headed* body lets the stepped term recover the original type (`app (lam (lam tt)) tt`
    checks at `pi 1 (app (lam tt) tt) bool`). I initially concluded from this that preservation was
    probably *true* — also wrong.
  - Fan-out #2 (adversarial, provers vs refuters) found the *real* counterexample: with
    `Γ = [Π(x:bool).x]` (a dependent function in the context), `f = lam (app (var 1) (var 0)) :
    Π ρ bool (var 0)` has a **rigid, var/app-headed** body, so its codomain is forced;
    `app f (ite tt tt ff) : ite tt tt ff` steps to `app f tt : tt ≠ ite tt tt ff`, and the domain
    (via `tt`) + codomain (lam-free body) are both pinned, so no flexibility rescues it.
  Recovering subject reduction needs a conversion rule (or type well-formedness restricting such
  contexts) — a real result, arguably more informative than a bare preservation proof would have been.
- **Exit — MET:** substitution lemma proved + `preservation` question settled (false), both zero
  `sorryAx`; `Dependent.lean`'s header updated.

### [x] P3 — Dependent Kan increment (scoped)

Constant-family Kan (Calculus.lean) → one genuinely dependent case: `transp` over a Π line with
a graded binder — the mechanized twin of the kernel probes
`transp_heterogeneous_pi_grade_glue_line_{rejected,accepted}` (the remaining half of obligation
1.3.2).

- **DONE (2026-07-04):** `HasTranspLine` in `GradeSkeleton.lean` — an actual *typing rule* for a
  heterogeneous transp along a genuinely two-endpoint type line `A0 ⇝ A1` (past `Calculus.lean`'s
  constant family), gated by the grade-skeleton guard. Twins `hasTranspLine_grade_heterogeneous_
  rejected` (no derivation for a `Π_ω ⇝ Π_1` line) / `hasTranspLine_grade_homogeneous_accepted`
  mirror the kernel probes at the transp-term level; `hasTranspLine_preserves_pi_grade` is the rule's
  soundness. All three `#print axioms` = `[propext]` only, no `sorryAx`. Standalone (no
  `Calculus.HasType` ripple). The prior grade-skeleton *guard* mechanization
  (`grade_skeleton_preserved_by_transp` et al.) was already in place; this lifts it to the transp
  level. The underlying `Glue`/`ua` line remains the deliberately-deferred cubical corner.
- **Exit — MET:** [metatheory.md](metatheory.md) §1.3 now cites the Lean lemma (`HasTranspLine` +
  its twins), not only kernel tests.

### [x] P4 — Decision checkpoint: the fused-theory bet

Timeboxed review after P1–P3: if the quantities × cubical corner (obligation 1.3.1 / spec §10.3)
has resisted two consecutive proof-track milestones, implement the spec's own documented
fallback — stratify — rather than carrying the open bet into v0.2. Deliverable: a metatheory.md
rewrite stating exactly what is proved, pinned, or stratified away. No code.

- **DECIDED (2026-07-04): adopt the stratified theory** — [metatheory.md](metatheory.md) §2.6 (the
  fused-theory checkpoint). The decision is *data-driven*, not a time-out: the proof track produced
  **two machine-checked negative results** that pinpoint why the unified fusion fails as stated —
  P2's `preservation_false` (dependent subject reduction needs a conversion rule) and P1's
  `handle_perform_not_preserving` (deep-handler subject reduction needs a first-class continuation
  type). What stands (all zero-`sorryAx`): SN + canonicity for the constant-family+graded fragment,
  the grade-skeleton × cubical corner (obligation 1.3.2, P3), dependent-`Π` substitution (P2), effect
  grade-safety + operational progress/resume-once (P1). Obligation 1.3.1 is retired from "open bet"
  to "stratified, with the obstruction machine-characterized" — and §2.6 records exactly what a v0.2
  unified-theory attempt would have to add first.
- **Exit — MET:** metatheory.md §2.6 written; the fused-theory bet resolved to the committed
  stratification with machine-checked justification.

---

## Arc R — Release v0.1

### [x] R1 — wasm-clean checker (`ureq` feature gate)

`blight-elab` gains a `net` cargo feature gating registry.rs's HTTP fetch (git deps + publish):
default ON for the CLI, OFF for a wasm profile. CI adds
`cargo check -p blight-elab -p blight-kernel -p blight-recheck --no-default-features --target
wasm32-unknown-unknown`.

- **Red:** the CI job lands first (allowed-to-fail matrix row, required after green).

**As-built notes (2026-07-03):** compiler-adjudicated premises first: blight-kernel and
blight-recheck were *already* wasm32-clean; blight-elab was blocked by exactly ureq's transitive
`getrandom` — plus one genuine 32-bit bug the spec never anticipated and nothing else could have
found: `META_BASE: usize = 1 << 40` is a compile-time overflow on wasm32. Fixed width-portably
(`1 << (usize::BITS - 1)` — further from real indices on 64-bit than before, 2^31 on wasm32).
The two registry HTTP branches are cfg-gated with clear no-`net` diagnostics; the CI row is
required. Suite 858/858 (one perf-guard failure during the sweep was the wall-clock instrument,
not the change — both N1 guards are now machine-independent ratios, landed separately).

### [x] R2 — Browser playground

A static page (GitHub Pages) embedding the checker compiled to wasm (R1) via wasm-bindgen or a
thin C-ABI export: source in, elaborate + kernel-check + re-check verdicts out (the type of
`main`, errors with carets). **Not** running compiled programs in v0.1 (wasm_rt has no
Console/GC — documented out of scope). Examples dropdown seeded from examples/.

- **Red tests:** a headless smoke test (wasmtime or node) invoking the wasm checker export on
  hello_nat.bl source and asserting the checked type; the page CI-built and link-checked.

**As-built notes (2026-07-03):** `crates/blight-playground` exports the checker over a thin
C ABI (`bp_alloc`/`bp_check`/`bp_free_*`, length-prefixed UTF-8 reports) — **no wasm-bindgen, no
bundler, no npm**: the page's Web Worker instantiates the raw cdylib. The report is the full
two-checker story: form/proof counts, `main`'s re-sugared type, and the independent re-checker's
verified/declined/rejected tally (a rejection renders as a SOUNDNESS ALARM, first). Checker
panics are caught, never abort the instance; the page runs checks in a killable worker with a
20 s watchdog, so divergent input cannot wedge the tab. `playground/build.sh` bakes a curated
pure-checkable examples dropdown into `dist/`; CI builds the wasm, runs the node smoke
(hello_nat: `main : Nat`, 17 globals re-verified), assembles the page, and link-checks every
asset. Deployment is a deliberate act: `pages.yml` is workflow_dispatch-only until the project
wants every merge live. Deferred per spec: running compiled programs (wasm_rt has no Console/GC
in v0.1).

### [x] R3 — Release engineering

`release.yml`: tag-triggered matrix build (macOS arm64/x86_64, Linux x86_64) of `blight-repl`
(+llvm where the toolchain is available; a check-only binary otherwise), artifacts attached to
the GitHub release. Version 0.0.0 → 0.1.0; CHANGELOG "0.1.0" section; README install section;
`blight --version`.

- **Red:** a release.yml dry-run job on push (build artifacts, no publish) lands first.

**As built (2026-07-04).** Red-first: `crates/blight-repl/tests/version.rs` pins `blight
--version`/`-V` → `blight 0.1.0` and the workspace version, both red before the change (flag fell
through to the REPL; version was `0.0.0`). Green: a `--version`/`-V` branch in `main.rs`
(`println!("blight {}", env!("CARGO_PKG_VERSION"))`); workspace version + `blight-playground` bumped
`0.0.0` → `0.1.0`; CHANGELOG cut a `[0.1.0] — 2026-07-04` section (folding the arc work + adding
E8/N6/the soundness pass); README grew an `## Install` section (from-source + release-artifact paths,
`blight --version` verify). `release.yml` builds the check-only `blight` across the three-platform
matrix, smoke-tests `--version`, and always uploads a workflow artifact (the **dry-run** deliverable
— runs on every push/PR without publishing); the GitHub-release attach is a tag-gated `if:` step on
top of the same build. Gates: clippy clean, fmt-clean for the new files, workspace suite 885/885.
**Known, out-of-scope for R3:** the CI `fmt --check` gate is red on ~1750 lines of *pre-existing*
repo-wide drift (the deferred `style_edition=2021` reformat, `e73c904`) across files R3 never
touched — resolving it needs the worktree-branch merge coordination and is an R4-tag prerequisite,
not an R3 change.

### [ ] R4 — v0.1 content freeze + docs truth pass

README status extended through the arcs actually landed; tutorial refreshed post-E1/E2 (decimals
+ implicits change every snippet); examples/README regenerated; this file's statuses flipped;
tag `v0.1.0`.

- **Exit:** a fresh-clone quickstart (README only) succeeds on a clean machine, scripted in CI
  (`quickstart.yml` running the README commands verbatim).

---

## Cross-arc ordering (recommended for a single stream)

E1 → E2 → E3 → S1 → E5 → E6 → S2 → S3 → N5 ✓ → **E4 → E7 → E9 → R1 → R2** → N6 → E8 → S4 →
P1 → P2 → S5 → R3 → P3 → P4 → R4

(Re-sequenced 2026-07-03 after N5, adopting the panel review's release-first correction: the
project's biggest deficit is that nobody outside can try it, and N5 removed the blocker that
made a playground irresponsible — so R1/R2 move directly behind the diagnostics pass (E7) and
the new E9 first-session bundle, with N6 now measured-in *behind* them (the ~30 s json/regex
re-checks justify its Value-sharing item but nothing user-facing blocks on it) and E8/S4/P*/R3
following. The two re-checker false-`Rejected` fixes, the ground-value-gate fix, and the
do_handle/metatheory reconciliation run as independent parallel sessions outside this ordering.)

### [x] E9 — First-session bundle (pre-playground; all tower, zero TCB)

The four verified first-ten-minutes bounce points from the 2026-07-03 panel review, fixed
together before anything is public: (1) `(do …)` sequencing sugar (kills effectful let-chain
soup); (2) the REPL prints *values* (`5`, not a core elim term) — re-sugared via the existing
pretty-printer; (3) typed holes: `?name` elaborates to a hole that reports its expected type and
context instead of an unsolved-meta error; (4) a stdlib self-consistency sweep (E1/E2 completion:
decimals and implicits everywhere the stdlib still contradicts its own shipped features, plus a
`Show`-to-`String` bridge). Each item is elaborator/REPL-level; red tests per item; oracle-corpus
additions per the oracle rule.

**As-built notes (2026-07-03):**
- *(do …) sugar:* `(do step … last)` with `(<- x e)` binders desugars in `parse_surface` to the
  right-nested `let` chain the corpus writes by hand; unbound steps bind unmentionable `%doN`
  names. Meaning refl-pinned in tests and oracle-pinned (`kernel_normal_form_matches_intended_value`
  gains an inline do case).
- *REPL values:* a bare expression at the prompt evaluates and prints re-sugared
  (`(plus 2 3)` ⇒ `5`) via new `blight_elab::eval_value_str` — infer first (never evaluate
  ill-typed input), evaluate under the N2 metering budget (divergence reports instead of
  hanging), pretty-print the quoted normal form. Only the driver's exact "bare term must be
  ascribed" refusal falls through to this path; files stay strict.
- *Typed holes:* `?` or `?name` (≥2 chars — single-char stays the char literal, boundary pinned
  by an unguarded test) reports the hole's expected type and the local context. Display-only
  domain threading: when an argument of a typed global is syntactically a hole, the head's Pi
  domain for that position is handed to the hole (dependent domains render unsubstituted);
  non-hole arguments elaborate exactly as before.
- *Stdlib sweep:* all 21 Peano `Succ`-chain value definitions across std/{nat,char,test,json,
  lexer}.bl replaced with decimals; the verdict golden is **byte-identical** after the sweep —
  the empirical confirmation of E1's identical-elaborated-terms guarantee at stdlib scale.
  Deferred, named honestly: a further implicits sweep beyond E2's (no contradictions surfaced by
  the suite) and the `Show`-to-`String` REPL bridge (belongs with R-era polish; `show` exists in
  std/order and the value printer now covers the common case).

Rationale: E1–E3 are small and every later arc's code and docs benefit; S1 is tiny and proves
the substrate early; E6 lands before S2 because spore_print is the measure clause's natural
first consumer; S2 lands before S3 because the bridge does not need Box→Rc and de-risks its
payoff test; E5+E6 land before S4 because the growing self-host fragment wants equations and
measures; P interleaves as independent Lean work; R1/R2 come early enough that the playground
exists while S and P complete; R4 is last. P and R items can run in parallel with S work — the
linear order is the default for a single stream.

## Milestone sizing (rough)

| Size | Milestones |
|---|---|
| Small (≈1 session) | E1, E3, E8, S1, R1, R3, P4, N7 |
| Medium (1–3 sessions) | E2, E4, E5, E7, S2, P1, P3, R2, R4, S5, N5 (counters land fast; the fix is the unknown) |
| Large (3+ sessions) | E6, S3 (the Box→Rc audit), S4 (three sub-milestones), P2, N6 (kernel-side, full gate protocol per fix) |

## Cross-references

- Bootstrap milestones M0–M6: [implementation.md](implementation.md) and spec §9.
- Post-M6 milestones M7–M30 + proof track: [roadmap-post-m6.md](roadmap-post-m6.md).
- Capability axis (TCB vs tower): [roadmap.md](roadmap.md).
- Metatheory evidence and open obligations: [metatheory.md](metatheory.md),
  [metatheory-mechanized.md](metatheory-mechanized.md).
