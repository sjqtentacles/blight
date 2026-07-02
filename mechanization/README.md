# BlightMeta — external Lean 4 mechanization

An independent, machine-checked companion to [`crates/blight-kernel`](../crates/blight-kernel)'s
metatheory notes ([docs/metatheory.md](../docs/metatheory.md)). This is a from-scratch Lean 4
development — a fresh implementation of the graded typing judgement, checked by Lean's own kernel,
not Blight's — for a scoped fragment of the theory: the QTT resource semiring (`{0, 1, ω}`), usage
vectors, a graded simply-typed calculus (`Bool`, `Π`-types), plus the constant-family corner of the
cubical Kan fragment (`iabs`/`transp`/`hcomp`), with complete (no `sorry`) proofs of weakening,
substitution, progress, preservation/type safety, step determinism, strong normalization, and
canonicity. A second, independent core (`BlightMeta/Dependent.lean`, Wave 8 / M9) develops a
*bona fide* dependent `Π`-type (unified term/type syntax, so the codomain can mention the value its
domain binds) with complete proofs of its own weakening and progress theorems; see that file's
module doc for the precise, honestly-bounded scope (dependent `Π` only, substitution/preservation
for that fragment deliberately not attempted). Wave 8 / M10 adds two more standalone pieces:
`BlightMeta/GradeSkeleton.lean` machine-checks `docs/metatheory.md` §1.3 obligation 1.3.2 (the
`kan_line_grade_skeleton_eq` fix) as `grade_skeleton_preserved_by_transp`, and
`BlightMeta/Effects.lean` mechanizes the graded effect-row discharge (spec §4.4) — a `handle`'s
op-clause usage of its captured continuation is provably bounded by the operation's declared
grade, with `handle_abort_never_resumes`/`handle_linear_at_most_once` as the headline corollaries.

See [docs/metatheory-mechanized.md](../docs/metatheory-mechanized.md) for the full scope, the
per-lemma correspondence to `blight-kernel`/`blight-recheck` tests, and what is deliberately not
covered yet (dependent `Σ`/`PathP`, fully heterogeneous/dependent cubical structure, effects/handlers,
HITs, universe levels, the `Int` primitive — see that file's "What's not covered" section).

## Build

```sh
lake build
```

Requires the [elan](https://github.com/leanprover/elan) toolchain manager; `lean-toolchain` pins the
exact Lean 4 version. No Mathlib or other external Lean library dependency — every lemma (including
basic semiring/list-algebra facts) is proved from scratch, so this development has no additional
proof-assistant-library trust dependency.

CI ([`.github/workflows/mechanization.yml`](../.github/workflows/mechanization.yml)) runs `lake build`
on every push/PR and independently greps for `sorry`/`admit`/`native_decide` so an incomplete proof
can never merge silently.

## Layout

- `BlightMeta/Grade.lean` — the grade semiring + its order.
- `BlightMeta/Usage.lean` — usage vectors (`List Grade`) and their `add`/`scale`/`Le`.
- `BlightMeta/Calculus.lean` — `Ty`, `Tm` (incl. `iabs`/`transp`/`hcomp`), de Bruijn
  shifting/substitution, the graded judgement `HasType`.
- `BlightMeta/Weakening.lean` — context-insertion lemmas, `weaken`, grade-demotion, dimension-count
  bookkeeping (`dim_weaken`/`dim_change`).
- `BlightMeta/Substitution.lean` — the substitution lemma with its usage bound.
- `BlightMeta/Progress.lean` — `Value`, CBV `Step`, `progress`, `preservation`, `type_safety`.
- `BlightMeta/Reducibility.lean` — a grade-free re-derivation of typing (`Typed`), Tait-style
  reducibility candidates, the fundamental lemma, `step_deterministic`, `strong_normalization`, and
  `canonicity`.
- `BlightMeta/Dependent.lean` — (M9) a second, independent core with a genuine dependent `Π`
  (`Expr`, unified term/type syntax), its own substitution algebra and shift/substitution
  commutation lemmas, dependent context operations (`ctxGet`/`ctxInsert`), the graded `HasType`,
  `weaken`, `Value`/`Step`, and `progress`.
- `BlightMeta/GradeSkeleton.lean` — (M10, part 1) `kanLineGradeSkeletonEq` over `Calculus.Ty`,
  `grade_skeleton_preserved_by_transp` (obligation 1.3.2, machine-checked), and the
  accept/reject/nested corollaries witnessing the fix's exact behavior.
- `BlightMeta/Effects.lean` — (M10, part 2) a graded effect row (`Row := Option Grade`), `Tm`/
  `HasType` extended with `perform`/`handle`, and the handler continuation-grade-safety corollaries
  `handle_grade_safe`/`handle_abort_never_resumes`/`handle_linear_at_most_once`.
- `BlightMeta.lean` — root module importing the above (the `lake build` default target).
