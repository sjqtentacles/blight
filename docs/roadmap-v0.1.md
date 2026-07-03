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

### [ ] E4 — Records: named fields over Sigma

Sexpr-level sugar (mirroring [mutual.rs](../crates/blight-elab/src/mutual.rs)'s
lower-before-elaborate precedent): `(defrecord Point ((x Nat) (y Nat)))` → Sigma type +
constructor + per-field projections (fst/snd chains) + `(Point-with p (y 5))` functional update.
Field access `(Point-x p)`. No anonymous record types, no row polymorphism in v1.

- **Red tests:** `defrecord_declares_type_ctor_and_projections`,
  `field_update_rebuilds_pair_chain`, `unknown_field_in_update_rejected`,
  `record_in_dependent_position_checks`; a new `examples/records_demo.bl` in the corpus.
- **Exit:** one stdlib adoption (std/parser parse-state or std/graphics config) proving it
  composes. Oracle-corpus additions.

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

### [ ] E7 — Diagnostics quality pass

Systematic error-message audit: every `ElabError::BadForm` gets a form-specific message + span;
kernel `TypeError` rendering gains expected/actual type highlighting (re-sugared, decimals
post-E1); "did you mean" suggestions for unbound names (edit distance over scope + globals).

- **Red tests** (`crates/blight-elab/tests/diagnostics.rs`): golden rendered output for an
  unbound-var typo (suggests), a lam arity error, a type mismatch in `the` (both types
  re-sugared), and a non-structural `deftotal` (suggests `(measure …)`).
- **Exit:** goldens documented in [testing.md](testing.md).

### [ ] E8 — Formatter + LSP surface polish

Wire the existing formatter (`crates/blight-elab/src/fmt.rs` — correctness already pinned by the
fmt_corpus idempotence + semantics test) through LSP `textDocument/formatting` and a `blight fmt`
CLI subcommand; this milestone is exposure only. Add LSP completion (globals, constructors,
keywords, std module paths after `(load "`).

- **Red tests:** `lsp_formatting_returns_fmt_output`, `completion_lists_globals_and_keywords`
  (blight-lsp inline harness); `blight_fmt_rewrites_file_in_place_idempotently` (CLI).
- **Exit:** VS Code extension bumped; README LSP feature table updated.

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

### [ ] S3 — Term representation: Box→Rc (refl-at-scale; TCB-adjacent)

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

### [ ] S4 — Grow the self-hosted fragment

Toy STLC (Base/Arr) → a real Blight fragment, one sub-milestone per feature, each re-running the
S2 bridge differential and growing its corpus by ≥5 cases:

- **S4a** — Nat literals + a second base type (post-E1).
- **S4b** — user inductives: BTy gains declared datatypes; `belaborate` gains constructors +
  match on non-indexed inductives.
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

## Arc P — Proof track continuation (Lean; external, zero TCB)

Red-commit protocol for Lean (where `sorry` is CI-banned and a theorem cannot be stated without
a proof): the red commit lands the obligations as **Prop-valued definitions**
(`def preservation_stmt : Prop := ∀ …`) in a new Obligations module — buildable, sorry-free,
pinning the exact statements. The green commit adds `theorem preservation : preservation_stmt`
etc. and wires the module into the root import.

### [ ] P1 — Effects operational semantics

Extend [BlightMeta/Effects.lean](../mechanization/BlightMeta/Effects.lean) from the static
discipline to a small-step semantics with evaluation contexts for perform/handle (delimited
continuation capture), proving preservation and the resume-once theorem *operationally*
(`handle_linear_at_most_once` upgraded from static to operational). Multi-operation rows
(`Row : Option Grade` → a per-op map).

- **Exit:** [metatheory-mechanized.md](metatheory-mechanized.md) checklist rows flip;
  metatheory.md §2 evidence upgraded.

### [ ] P2 — Dependent.lean substitution + preservation

The acknowledged "comparably-sized effort": the substitution lemma + preservation for the
dependent-Π fragment (requires a conversion relation). Same red protocol.

- **Exit:** closes the stated gap in Dependent.lean's header; checklist updated.

### [ ] P3 — Dependent Kan increment (scoped)

Constant-family Kan (Calculus.lean) → one genuinely dependent case: `transp` over a Π line with
a graded binder — the mechanized twin of the kernel probes
`transp_heterogeneous_pi_grade_glue_line_{rejected,accepted}` (the remaining half of obligation
1.3.2).

- **Exit:** the obligation table in [metatheory.md](metatheory.md) §1.3 cites the Lean lemma,
  not only kernel tests.

### [ ] P4 — Decision checkpoint: the fused-theory bet

Timeboxed review after P1–P3: if the quantities × cubical corner (obligation 1.3.1 / spec §10.3)
has resisted two consecutive proof-track milestones, implement the spec's own documented
fallback — stratify: interval variables carry no grade (already the kernel's measured behavior,
per `interval_var_carries_no_grade_in_usage_vector`), and document the stratified theory as
*the* theory, retiring the open obligation — rather than carrying the open bet into v0.2.
Deliverable either way: a metatheory.md §10 rewrite stating exactly what is proved, pinned, or
stratified away. No code.

---

## Arc R — Release v0.1

### [ ] R1 — wasm-clean checker (`ureq` feature gate)

`blight-elab` gains a `net` cargo feature gating registry.rs's HTTP fetch (git deps + publish):
default ON for the CLI, OFF for a wasm profile. CI adds
`cargo check -p blight-elab -p blight-kernel -p blight-recheck --no-default-features --target
wasm32-unknown-unknown`.

- **Red:** the CI job lands first (allowed-to-fail matrix row, required after green).

### [ ] R2 — Browser playground

A static page (GitHub Pages) embedding the checker compiled to wasm (R1) via wasm-bindgen or a
thin C-ABI export: source in, elaborate + kernel-check + re-check verdicts out (the type of
`main`, errors with carets). **Not** running compiled programs in v0.1 (wasm_rt has no
Console/GC — documented out of scope). Examples dropdown seeded from examples/.

- **Red tests:** a headless smoke test (wasmtime or node) invoking the wasm checker export on
  hello_nat.bl source and asserting the checked type; the page CI-built and link-checked.

### [ ] R3 — Release engineering

`release.yml`: tag-triggered matrix build (macOS arm64/x86_64, Linux x86_64) of `blight-repl`
(+llvm where the toolchain is available; a check-only binary otherwise), artifacts attached to
the GitHub release. Version 0.0.0 → 0.1.0; CHANGELOG "0.1.0" section; README install section;
`blight --version`.

- **Red:** a release.yml dry-run job on push (build artifacts, no publish) lands first.

### [ ] R4 — v0.1 content freeze + docs truth pass

README status extended through the arcs actually landed; tutorial refreshed post-E1/E2 (decimals
+ implicits change every snippet); examples/README regenerated; this file's statuses flipped;
tag `v0.1.0`.

- **Exit:** a fresh-clone quickstart (README only) succeeds on a clean machine, scripted in CI
  (`quickstart.yml` running the README commands verbatim).

---

## Cross-arc ordering (recommended for a single stream)

E1 → E2 → E3 → S1 → E5 → E6 → S2 → S3 → E4 → E7 → E8 → S4 → P1 → R1 → R2 → P2 → S5 → P3 → R3 →
P4 → R4

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
| Small (≈1 session) | E1, E3, E8, S1, R1, R3, P4 |
| Medium (1–3 sessions) | E2, E4, E5, E7, S2, P1, P3, R2, R4, S5 |
| Large (3+ sessions) | E6, S3 (the Box→Rc audit), S4 (three sub-milestones), P2 |

## Cross-references

- Bootstrap milestones M0–M6: [implementation.md](implementation.md) and spec §9.
- Post-M6 milestones M7–M30 + proof track: [roadmap-post-m6.md](roadmap-post-m6.md).
- Capability axis (TCB vs tower): [roadmap.md](roadmap.md).
- Metatheory evidence and open obligations: [metatheory.md](metatheory.md),
  [metatheory-mechanized.md](metatheory-mechanized.md).
