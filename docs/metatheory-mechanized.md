# External mechanization — Track M4 checklist

This tracks the **machine-checked** (Lean 4) mechanization in [`mechanization/`](../mechanization),
the "going for gold" deliverable named in the metatheory plan: a formal, independently-checkable
witness for a scoped fragment of the theory [docs/metatheory.md](metatheory.md) documents only by
kernel-behavior evidence. It is **not** a replacement for that evidence — the kernel/re-checker pair
remains the actual trusted implementation — it is a second, wholly independent piece of proof
engineering (a fresh implementation of the typing judgement, checked by Lean's kernel, not
Blight's) that the design is mathematically coherent.

## Why Lean 4

Agda and Lean 4 were both viable; Lean 4 was chosen for its more automated tactic mode (`omega`,
`simp`, `decide`) which keeps the arithmetic side-conditions on de Bruijn indices and usage-vector
lengths tractable without hand-writing every step. Nothing here depends on a Lean-specific axiom —
the development is axiom-free (`#print axioms` on any theorem below reports none beyond
`propext`/`Classical.choice`/`Quot.sound`, which the file set never actually needs since everything
is constructive `Prop`/`Decidable` reasoning over inductive types).

## Scope of the fragment

QTT resource grading (`{0, 1, ω}`, spec §10.3) over a simply-typed core with `Bool` and `Π`-types,
plus (Wave 3 / M5) the **constant-family** corner of the cubical Kan fragment: `iabs`/`transp`/
`hcomp`, restricted to a type "line" that does not actually vary across the interval (this
fragment's `Ty` is non-dependent, so a genuine `PathP`/`Glue`/heterogeneous `comp` is out of scope
— see "What's not covered" below, and M7 in the roadmap for the open heterogeneous corner). This is
deliberately the same scoping discipline as the rest of the repo: land a fully-proven fragment
rather than an admitted/`sorry`d whole theory.

Build: `cd mechanization && lake build` (pinned toolchain in `lean-toolchain`; no Mathlib dependency
— every lemma, including semiring/list-algebra facts, is proved from scratch in `Grade.lean`/
`Usage.lean` so the development has no external proof-assistant-library trust dependency either).
CI: [`.github/workflows/mechanization.yml`](../.github/workflows/mechanization.yml) builds this on
every push/PR and fails if any file needs `sorry` (see below) or fails to compile.

## Correspondence table (mechanized lemma ↔ kernel evidence)

Each row pairs a Lean theorem with the `blight-kernel`/`blight-recheck` test(s) that pin the *same*
claim operationally. If a kernel-side change ever breaks the cited test, treat it as a signal that
the mechanized lemma's assumptions (`BlightMeta/Calculus.lean`'s `HasType` transcription) may need
re-auditing against the new `check.rs` rule — the pairing is the regression guard the plan asks for.

| Lean file : theorem | Statement | Kernel/re-checker correspondence |
|---|---|---|
| `Grade.lean` : `add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `mul_add` (distributivity), `zero_add`/`add_zero`, `one_mul`/`mul_one` | `{0,1,ω}` forms a commutative semiring under the kernel's grade `add`/`mul` tables | `blight-kernel/src/semiring.rs` (the `Grade` type + its `add`/`mul` impls, exercised throughout `check.rs`'s usage accounting) |
| `Grade.lean` : `le_refl`, `le_trans`, `zero_le`, `self_le_add_left/right`, `self_le_mul_omega` | the demand order `0 < 1 < ω`, and its interaction with `add`/`mul`, is a genuine preorder with `0` least and `ω` absorbing | same `semiring.rs`; operationally the order the kernel's `demand ≤ declared` usage checks compare against (`check.rs`'s `Var`/`Lam` rules) |
| `Usage.lean` : `get_add`, `get_scale`, `add_assoc`/`add_comm`, `scale_add_grade`, `le_get`/`le_of_forall_get` | usage vectors (`List Grade`) and their pointwise order form the expected additive/scalar structure, and the vector order is exactly "check every slot" | `blight-kernel/src/usage.rs` (`Usage` + its `add`/`scale`/`Le`) |
| `Weakening.lean` : `weaken` | inserting an unused (0-demand) binder anywhere into a well-typed context preserves typability, term shifted by `Tm.shiftAbove`, usage by `insertUsage` | the kernel never re-derives this explicitly (it re-elaborates from scratch each time), but it is the standard justification for why `check.rs`'s de Bruijn context-extension in `Lam`/`Pi-Intro` is sound; also the shape `blight-recheck`'s independent context handling must respect for kernel/re-checker agreement (`recheck.rs`'s shared-context conformance tests) |
| `Weakening.lean` : `demote`, `demote_scaled` | a term checked at ambient grade `σ` also checks at any `σ' ≤ σ`, with usage `Le`-bounded (resp. bounded by `scale σ' φ`) | the grade-order monotonicity `check.rs`'s `Var` rule relies on implicitly (checking at a smaller ambient demand never needs *more* resource); probed by the kernel's `grades-cubical-stress` demand-order tests (`transp_family_use_keeps_grade0_var_erased` et al., §1.1 of [docs/metatheory.md](metatheory.md)) |
| `Substitution.lean` : `subst_lemma` (public form of `subst_lemma_aux`) | substituting a well-typed term `a` (checked at grade `π`, usage `φa`) for a variable removed from a context preserves typability, with the result's usage bounded by the original usage (that slot dropped) plus `scale (φ.get k) φa` — the substituted term's usage scaled by exactly how much the removed variable was demanded | the mechanized form of [docs/metatheory.md](metatheory.md) §1.2's "usage is preserved under reduction" sketch; the kernel/re-checker never state this as a standalone lemma (substitution is baked into `normalize.rs`'s evaluator), so this is the one lemma in this file set with **no direct kernel test pairing** — it is a foundational fact the informal sketch *assumes*, now proved rather than assumed. Closing this gap is exactly the "going for gold" contribution: the informal §1.2 sketch is now backed by a machine-checked proof of its core step. |
| `Calculus.lean` : `HasType.iabs`/`transp`/`hcomp` + `iabs_preserves_context_and_usage`, `transp_reflects_base` | (M5) the constant-family Kan fragment: opening a dimension binder (`iabs`) is a no-op on `Γ`/`σ`/`φ`; `transp` on a constant family charges its base at the ambient rate unchanged; `hcomp` sums base and tube demand, exactly like `ite` | `crates/blight-kernel/src/kan.rs`'s `transp_constant_family_is_identity`/`hcomp_total_cofib_picks_tube`/`hcomp_empty_cofib_picks_base`, and `check.rs`'s graded `Transp`/`HComp`/`IAbs` rules; the four concrete `example`s immediately below `HasType` in `Calculus.lean` mirror `transp_base_omega_var_accepted`, `transp_base_charges_demand_erased_base_rejected`, `hcomp_base_and_tube_sum_demand_linear_rejected`, and `interval_var_carries_no_grade_in_usage_vector` verbatim |
| `Weakening.lean` : `dim_weaken`, `dim_change` | a derivation's dimension-binder count `d` is pure well-scoping bookkeeping: `dim_weaken` shows validity is preserved going from `d` to `d + 1` (needed by `Substitution.lean`'s `iabs` case); `dim_change` shows the stronger fact that `d`'s exact value never matters at all (needed by `Progress.lean`'s `iabs` reduction step, which moves the opposite direction, `d + 1` back down to `d`) | no single kernel test pins this directly — it is the mechanized form of the kernel's dimension context being pure bookkeeping that no `check.rs` rule branches on |
| `Progress.lean` : `Value`, `Step`, `progress`, `preservation`, `type_safety` | (M6) a well-typed *closed* term of this fragment (STLC core + constant-family Kan) is either a canonical value or can take a CBV step (`progress`); stepping never changes a term's type (`preservation`); combined, well-typed closed programs never get stuck (`type_safety`) | `Step`'s `app`/`ite` rules are the standard CBV STLC reduction rules; its `transp_val`/`hcomp_true`/`hcomp_false` rules are `kan.rs`'s `transp_constant_family_is_identity`/`hcomp_total_cofib_picks_tube`/`hcomp_empty_cofib_picks_base` read operationally (as reduction rules, not just value-level functions); `iabs_elim` (opening a dimension is a runtime no-op, not just a typing no-op) has no direct kernel-test pairing — it is a modeling choice this mechanization makes explicit (see `Progress.lean`'s module doc for the canonical-forms gotcha it closes) |
| `Reducibility.lean` : `Typed`, `fundamental`, `strong_normalization`, `step_deterministic`, `canonicity` | (M8, Wave 8) a grade-free re-derivation of typing (`Typed`, since `HasType.lam`'s declared-grade bound cannot be uniformly promoted to a single fixed grade) with its own progress/preservation, Tait-style reducibility candidates (`Reducible`) indexed by `Ty`, and the fundamental lemma (every `Typed`-well-typed term, closed against a reducible environment, is reducible) proved by induction with a case for *every* M5 `Step` rule (`Reducible_lam` for β, `Reducible_ite` for ι, `Reducible_transp`/`Reducible_hcomp`/`Reducible_iabs` for the Kan formers) | mechanizes [docs/design-wave4-gobars.md](design-wave4-gobars.md) §1's go-bar in full: `strong_normalization` and `canonicity` are stated for the full graded `HasType` (via `Typed.of_has_type`'s erasure) even though the reducibility argument itself is grade-independent, matching the go-bar's "grades are orthogonal to this proof" framing; no kernel test pins SN/canonicity directly (there is no bounded-fuel evaluator test that could observe non-termination), so this is a pure proof-engineering deliverable, not a kernel-behavior correspondence |
| `Dependent.lean` : `Expr`, `HasType`, `HasType.weaken`, `progress` | (M9, Wave 8) a second, independent core with a *bona fide* dependent `Π`: `Expr` unifies term and type syntax (so a `Π`'s codomain can mention the value its domain binds), with its own substitution algebra (`shiftBy`/`subst`/`subst0`), shift/substitution commutation (`shiftBy_subst_lt`/`_ge`, the standard TAPL §6.2.5 fact — needed here because a dependent type, not just a term, must shift correctly), rebasing-aware context operations (`ctxGet`/`ctxInsert`), the graded `HasType` (`app`'s conclusion type is `Expr.subst0 a B`, the one substantive change from `Calculus.lean`'s non-dependent `Ty.arr`), `weaken` (now shifting *both* the term and its type, since types can contain variables), and `progress` | broadens `Calculus.lean`'s structurally-non-dependent `Ty`/`Tm` split (flagged in that file's own module doc) toward `crates/blight-kernel`'s genuinely dependent `Value` — no kernel test pins this file directly (it is a from-scratch parallel core, not an extension of the `Calculus.lean` fragment the other rows correspond to); `Dependent.lean`'s own module doc states precisely what is and is not proved (dependent `Π` only; the general substitution lemma and `preservation` are honestly scoped out, see "What's not covered" below) |
| `GradeSkeleton.lean` : `kanLineGradeSkeletonEq`, `grade_skeleton_preserved_by_transp` | (M10, Wave 8) machine-checks [docs/metatheory.md](metatheory.md) §1.3 obligation 1.3.2 (Track M7): `kanLineGradeSkeletonEq` transcribes the check verbatim over `Calculus.Ty`, and `grade_skeleton_preserved_by_transp` proves its exact soundness content — whenever the check accepts two `Π`-formers as a Kan line's endpoints, their declared grades already coincide, which is precisely what rules out re-labeling a value's grade by crossing the line. `grade_skeleton_preserved_by_transp_nested` extends this to nested `Π`-under-`Π` positions; `kanLineGradeSkeletonEq_heterogeneous_pi_rejected`/`_homogeneous_pi_accepted` are `decide`-witnessed twins of the concrete pre-/post-fix behavior. **P3 (v0.1)** lifts this to the transp-typing level: `HasTranspLine` is an actual heterogeneous-transp typing rule along a two-endpoint line `A0 ⇝ A1` (past `Calculus.lean`'s constant family), gated by the grade skeleton, with `hasTranspLine_grade_heterogeneous_rejected`/`_homogeneous_accepted` (transp-term-level twins of the kernel probes) and `hasTranspLine_preserves_pi_grade` (the rule's soundness), all `[propext]`-only | `crates/blight-kernel/src/check.rs::kan_line_grade_skeleton_eq` (mirrored in `crates/blight-recheck/src/conv.rs`), which now cites this Lean theorem by name in its doc comment; operationally pinned by `transp_heterogeneous_pi_grade_glue_line_rejected`/`transp_homogeneous_pi_grade_glue_line_accepted`. This is the first obligation in this repo's metatheory notes to move from "test-pinned" to "machine-checked." |
| `Effects.lean` : `HasType` (with `perform`/`handle`), `handle_grade_safe`, `handle_abort_never_resumes`, `handle_linear_at_most_once` | (M10, Wave 8) a third, independent core mechanizing the graded effect-row discharge (spec §4.1/§4.3/§4.4): a single globally-fixed operation `op : opDom → opCod` at declared continuation-grade `opGrade`, `Row := Option Grade` (the single-label specialization of `row.rs`'s graded `BTreeMap`), and a `HasType` extended with `perform`/`handle` whose `handle` rule requires the op-clause's measured usage of its own captured continuation (`δk`) to satisfy `δk ≤ opGrade` — the exact transcription of `check.rs`'s `demand_k.leq(cont_grade)`. `handle_abort_never_resumes` and `handle_linear_at_most_once` derive the spec's own stated consequences (a `0`-graded handler's clause provably never uses `k`; a `1`-graded one's usage is provably `0` or `1`, never `ω`) as genuine corollaries of the grade order, not restatements of the rule's premise | `crates/blight-kernel/src/check.rs`'s `Handle` rule (`demand_k.leq(cont_grade)`, both `infer_g`/`check_g` copies) and `crates/blight-kernel/src/row.rs`'s graded `Row`; operationally pinned by `handle_discharges_label`/`handle_with_clause`-style tests. No kernel test previously had a Lean counterpart for this judgement at all — closing that gap is this row's contribution |

## What this buys, precisely

With `weaken` + `subst_lemma` both proved for the STLC core, and now (M5) the constant-family Kan
formers added to `Calculus.lean`/`Weakening.lean`/`Substitution.lean`, **M6 delivers full type
safety for the whole fragment**: `Progress.lean`'s `progress` (a well-typed closed term is a value
or steps) combines with `preservation` (stepping never changes the type) into `type_safety` — the
standard "well-typed closed programs never get stuck" guarantee, mechanized rather than assumed.
`preservation`'s one substantive case (β-reduction) is exactly the corollary `subst_lemma` was
built to unlock, discharging its `hget` side-condition via `Weakening.lean`'s `demand_le_scale`/
`ambient_zero_usage` — both written, per their own doc comments, in anticipation of this composition.

**A genuine mechanized gotcha, not present in the non-cubical core:** `HasType.iabs`'s conclusion
reuses its body's type `A` verbatim (this fragment has no `Line`/`PathP` type former to distinguish
"a line of `A`s" from "an `A`"), so `.iabs body` can inhabit an *arrow* type without being a `lam`.
Naively classifying `.iabs _` as a value (the "no eliminator exists yet" argument that correctly
makes `lam` a value) would leave `.app (.iabs body) a` well-typed but stuck — a genuine progress
hole introduced by the Kan extension. `Progress.lean` closes it not with an ad hoc "apply through
iabs" rule, but by extending `iabs`'s already-established typing transparency (§1.1(d), mechanized
by `dim_change`) to evaluation: `.iabs body` is never a value, and unconditionally steps to `body`.
See `Progress.lean`'s module doc for the full argument.

## What's not covered (honest scope boundary)

- **No heterogeneous/dependent cubical structure** (`PathP`/`Glue`/a genuinely dimension-varying
  type line, or a dimension-varying *grade*) — M5's Kan formers are scoped to the reachable,
  evidence-backed **constant-family** corner of `kan.rs` (this fragment's `Ty` is still
  non-dependent). The fully heterogeneous case (a graded type line whose grade itself varies across
  the dimension) is [docs/metatheory.md](metatheory.md) §1.3 obligation 2 / roadmap M7's "last open
  cubical-QTT corner," deliberately left as a separate probe-first go/no-go rather than folded in
  here. Broadening `Ty`/`HasType` past this fragment is the (separate, non-cubical) job
  `Dependent.lean` takes on — see below.
- **Strong normalization and canonicity are now proved** (Wave 8 / M8, `Reducibility.lean`) for
  this fragment (`Bool`/`Π` + the constant-family Kan formers), closing the go-bar
  [`docs/design-wave4-gobars.md`](design-wave4-gobars.md) §1 left open. The proof is grade-free
  (see `Reducibility.lean`'s module doc for why a fresh `Typed` judgement, not an existential over
  `HasType`'s own grades, is the right relation for a Tait-style logical-relations argument): it
  covers a *strictly bigger* class of terms than any single `HasType` grade assignment could, so
  `strong_normalization`/`canonicity` specialize to the graded fragment via one erasure lemma
  (`Typed.of_has_type`) rather than needing the reducibility argument to thread grades through at
  all.
- **The grade-skeleton fix (obligation 1.3.2) is now machine-checked, not just test-pinned**
  (Wave 8 / M10, `GradeSkeleton.lean`): `grade_skeleton_preserved_by_transp` proves
  `kan_line_grade_skeleton_eq`'s exact soundness content — see the correspondence table above.
  This is the first §1.3 obligation to move from "kernel-behavior evidence" to "independently
  proof-checked."
- **A genuine dependent `Π` is now mechanized** (Wave 8 / M9, `Dependent.lean`), in a second,
  independent core (`Expr`/`HasType`, distinct from `Calculus.lean`'s `Ty`/`Tm`) with complete
  proofs of `weaken` and `progress`. Honestly **not** covered by this file: dependent `Σ` and
  `PathP` (both need a real definitional-equality/conversion relation as a prerequisite — see
  `Dependent.lean`'s module doc for exactly where `Σ`'s `snd`-elimination β-case would need it and
  `Π`'s doesn't). The **general substitution lemma** for the dependent fragment is now **proved**
  (P2; `subst_subst_comm` prerequisite + `subst_lemma`/`subst_lemma_tele`, `#print axioms subst_lemma`
  = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) — over an explicit telescope `Δ ++ A'::Γ`,
  since the `ctxInsert` formulation provably cannot do the `lam` case (it head-shifts the domain).
  **`preservation` is proved FALSE** (`preservation_false`, `#print axioms` = `[propext, Quot.sound]`):
  subject reduction genuinely fails for this syntax-directed, conversion-free `HasType`. The
  counterexample (settled by an adversarial fan-out after a first, *wrong*, "false" counterexample was
  machine-refuted and a "probably true" reading was also wrong): with `Γ = [Π(x:bool).x]`,
  `f = lam (app (var 1) (var 0)) : Π ρ bool (var 0)` has a rigid var/app-headed body, so
  `app f (ite tt tt ff) : ite tt tt ff` steps to `app f tt : tt`, and both domain and codomain are
  pinned (no `lam`-flexibility rescue). Recovering it needs a conversion rule or type well-formedness —
  see `Dependent.lean`'s module doc.
- **Effect/handler grade safety (the graded-row discharge) is now mechanized in a scoped form**
  (Wave 8 / M10, `Effects.lean`): a single fixed operation, a single-label closed row, no row-
  variable effect polymorphism, and lambda bodies required pure (see that file's module doc for
  the full simplification list). `handle_grade_safe`/`handle_abort_never_resumes`/
  `handle_linear_at_most_once` mechanize spec §4.4's continuation-multiplicity claims as genuine
  corollaries of the grade order. Honestly **not** covered: multi-operation/multi-label rows, row
  variables (`ε`, spec §4.1), a row-carrying arrow type (so a value can latently carry an
  unresolved effect), and — the load-bearing gap, matching the pattern already set by `Dependent.
  lean`'s deferred substitution/preservation — genuine delimited-continuation *operational*
  semantics and preservation for `Handle`/`Op`; this file proves only the static discipline.
- **HITs, universe levels, and the `Int` primitive** remain out of scope for this fragment,
  matching the kernel's own layering (spec §10.4, [docs/metatheory.md](metatheory.md) §2).

## File map

| File | Contents |
|---|---|
| `BlightMeta/Grade.lean` | the `{0,1,ω}` grade semiring + its order |
| `BlightMeta/Usage.lean` | usage vectors (`List Grade`) and their `add`/`scale`/`Le` |
| `BlightMeta/Calculus.lean` | `Ty`, `Tm` (incl. M5's `iabs`/`transp`/`hcomp`), de Bruijn `shiftAbove`/`subst`, and the graded judgement `HasType` (with its dimension-count parameter `d`) |
| `BlightMeta/Weakening.lean` | context-insertion lemmas, `weaken`, `demote`/`demote_scaled`, `dim_weaken`/`dim_change` |
| `BlightMeta/Substitution.lean` | `subst_lemma_aux`/`subst_lemma`, the substitution lemma with its usage bound, extended to the Kan formers |
| `BlightMeta/Progress.lean` | (M6) `Value`, CBV `Step`, `progress`, `preservation`, `type_safety` |
| `BlightMeta/Reducibility.lean` | (M8) grade-free `Typed`, Tait-style `Reducible` candidates, the fundamental lemma, `strong_normalization`, `step_deterministic`, `canonicity` |
| `BlightMeta/Dependent.lean` | (M9) a second, independent core: `Expr` (unified term/type syntax), the substitution algebra and its shift/substitution commutation lemmas, `ctxGet`/`ctxInsert`, the graded dependent `HasType`, `weaken`, `Value`/`Step`, `progress` |
| `BlightMeta/GradeSkeleton.lean` | (M10) `kanLineGradeSkeletonEq` over `Calculus.Ty`, `grade_skeleton_preserved_by_transp` (obligation 1.3.2, machine-checked), `_nested`, accept/reject `decide` twins |
| `BlightMeta/Effects.lean` | (M10) a third, independent core: graded effect row (`Row := Option Grade`), `Tm`/`HasType` extended with `perform`/`handle`, `handle_grade_safe`, `handle_abort_never_resumes`, `handle_linear_at_most_once` |
| `BlightMeta.lean` | root module importing the above (the `lake build` default target) |

No file in this set contains `sorry`, `admit`, or `native_decide` — every theorem is a complete
proof term checked by Lean's own kernel (`lake build` fails the CI job otherwise).
