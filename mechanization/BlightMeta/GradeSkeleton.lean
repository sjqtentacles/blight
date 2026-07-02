/-
  Wave 8 / M10, part 1: a machine-checked mechanization of `kan_line_grade_skeleton_eq`
  (`crates/blight-kernel/src/check.rs`, mirrored in `crates/blight-recheck/src/conv.rs`) — the
  fix for [docs/metatheory.md](../../docs/metatheory.md) §1.3 obligation 1.3.2 (Track M7).

  ── The gap this mechanizes the fix for ──────────────────────────────────────────────────────
  A Kan operation (`transp`/`comp`) over a *non-constant* type line checks its base term **once**,
  against the line's source endpoint, and hands back the line's **target** endpoint as the whole
  expression's type — with no re-verification that the two endpoints agree. When both endpoints
  are `Π`-formers that differ only in their *declared grade* (e.g. `Π_ω A B` at one end, `Π_1 A B`
  at the other, connected via an inhabited `Glue`), this can "launder" a value whose body was
  checked to *need* `ω` into being re-labeled as `Π_1`'s "uses its argument at most once" promise
  — a genuine, reachable soundness gap (see `docs/metatheory.md`'s Track M7 narrative in full).

  `kan_line_grade_skeleton_eq` closes it: whenever a line's two endpoints are not already
  definitionally equal, any `Π`-formers occurring at corresponding structural positions in the two
  endpoints must still agree in declared grade (the type itself may differ across the line; its
  *quantitative skeleton* may not). This file mechanizes exactly that guarantee.

  ── Scope ─────────────────────────────────────────────────────────────────────────────────────
  This mechanizes the check's *content* — what it guarantees about grades wherever it accepts a
  pair of endpoints — directly over `Calculus.lean`'s non-dependent `Ty` (`Bool`/`Π`). It does not
  re-derive a full heterogeneous Kan-operation judgement (a "line of types" genuinely varying
  across a dimension needs a dependent `Ty`, exactly the fragment `Dependent.lean` deliberately
  does not extend this far — see that file's module doc). That is intentional: the check's entire
  correctness content is the purely *structural* fact proved below as
  `grade_skeleton_preserved_by_transp`, independent of any particular Kan-operation typing rule
  that consumes it — proving it once here, generically, covers every call site (`Transp`, `Comp`,
  and any future Kan-op that reuses the same guard) without needing to mechanize each one's typing
  rule individually.
-/

import BlightMeta.Calculus

namespace BlightMeta

/-- The grade-skeleton check (`crates/blight-kernel/src/check.rs::kan_line_grade_skeleton_eq`,
    mirrored in `crates/blight-recheck/src/conv.rs`), transcribed verbatim over this fragment's
    `Ty`: matching `Π`-formers must agree in declared grade *and* recurse into domain/codomain;
    `Bool` at both ends is trivially fine; mismatched head shapes (`Bool` vs `Π`) are untouched —
    they can only arise from a genuine `ua`-style line between unrelated types, which this check
    is not concerned with (the doc comment on the Rust original: "mismatched head shapes ... are
    untouched"). This fragment has no `Σ`-former (`Calculus.Ty` is `Bool`/`Π` only), so the
    Rust original's "`Σ`-formers recurse structurally with no constraint" clause has nothing to
    transcribe here. -/
def kanLineGradeSkeletonEq : Ty → Ty → Bool
  | .bool, .bool => true
  | .arr g0 d0 c0, .arr g1 d1 c1 =>
      decide (g0 = g1) && kanLineGradeSkeletonEq d0 d1 && kanLineGradeSkeletonEq c0 c1
  | .bool, .arr _ _ _ => true
  | .arr _ _ _, .bool => true

/-- Sanity check: the skeleton relation is reflexive — a line whose endpoints are syntactically
    identical (in particular, any *constant* family, which is all M5's `transp`/`hcomp` fragment
    ever transports along) trivially passes, matching the Rust doc comment's framing ("whenever a
    line's two endpoints are not already definitionally equal ... this constraint is imposed") —
    the check is a genuine *weakening* of full equality, never rejecting what conversion already
    accepts. -/
theorem kanLineGradeSkeletonEq_refl : ∀ a : Ty, kanLineGradeSkeletonEq a a = true
  | .bool => rfl
  | .arr g d c => by
      simp [kanLineGradeSkeletonEq, kanLineGradeSkeletonEq_refl d, kanLineGradeSkeletonEq_refl c]

/-- **The mechanization of docs/metatheory.md §1.3 obligation 1.3.2 (Track M7's fix), the exact
    soundness content `kan_line_grade_skeleton_eq` is relied on for.** Whenever the check accepts
    two `Π`-formers as a Kan line's endpoints, their *declared grades* already coincide. This is
    precisely what rules out the laundering attack: `Transp`/`Comp` check a base term once against
    the source endpoint's declared grade and hand back the target endpoint's declared grade with no
    re-verification, so if this theorem holds unconditionally of *which* endpoint's grade a
    downstream elimination (`app`) happens to read off, the two readings can never disagree — a
    value's usage-discipline grade cannot change by crossing the line. -/
theorem grade_skeleton_preserved_by_transp {ρ0 ρ1 : Grade} {dom0 cod0 dom1 cod1 : Ty}
    (hskel : kanLineGradeSkeletonEq (.arr ρ0 dom0 cod0) (.arr ρ1 dom1 cod1) = true) :
    ρ0 = ρ1 := by
  simp only [kanLineGradeSkeletonEq, Bool.and_eq_true, decide_eq_true_eq] at hskel
  exact hskel.1.1

/-- The general, structural form: `grade_skeleton_preserved_by_transp` is not just a fact about
    the two *top-level* endpoints — because the check recurses into domain/codomain, it applies
    equally to any nested `Π`-under-`Π` position the recursion actually visits (a `Π`-line whose
    domain or codomain is itself a further-nested `Π`). Unfolding `kanLineGradeSkeletonEq` one
    step exposes exactly the recursive call whose own success is a fresh instance of the same
    hypothesis, so no separate induction is needed: applying `grade_skeleton_preserved_by_transp`
    to that recursive call *is* the nested-position guarantee. This corollary makes that
    unfolding step explicit for the immediate domain/codomain case (the next rung down from the
    top-level pair). -/
theorem grade_skeleton_preserved_by_transp_nested {ρ0 ρ1 : Grade} {cod0 cod1 : Ty}
    {ρ0' ρ1' : Grade} {dom0' cod0' dom1' cod1' : Ty}
    (hskel : kanLineGradeSkeletonEq (.arr ρ0 (.arr ρ0' dom0' cod0') cod0)
      (.arr ρ1 (.arr ρ1' dom1' cod1') cod1) = true) :
    ρ0' = ρ1' := by
  simp only [kanLineGradeSkeletonEq, Bool.and_eq_true, decide_eq_true_eq] at hskel
  exact hskel.1.2.1.1

/-- The concrete pre-fix gap this check now rejects (`docs/metatheory.md`'s Track M7 narrative;
    mirrors the red state `transp_heterogeneous_pi_grade_glue_line_rejected`'s doc comment
    describes): grade-heterogeneous `Π` endpoints — identical domain/codomain shape, differing
    only in declared grade — are exactly the construction the check must decline. Witnessed by
    `decide` rather than merely asserted, so a future change to `kanLineGradeSkeletonEq` that
    accidentally started accepting this shape would fail to compile this file. -/
theorem kanLineGradeSkeletonEq_heterogeneous_pi_rejected :
    kanLineGradeSkeletonEq (.arr .omega .bool .bool) (.arr .one .bool .bool) = false := by
  decide

/-- The accept twin: the *same* `Π`-former shape at both ends, agreeing in grade, is accepted —
    confirming `grade_skeleton_preserved_by_transp`'s hypothesis is satisfiable and the rejection
    above is the grade *mismatch* discriminating, not `Π`-headed lines being rejected wholesale
    (mirrors `transp_homogeneous_pi_grade_glue_line_accepted`). -/
theorem kanLineGradeSkeletonEq_homogeneous_pi_accepted :
    kanLineGradeSkeletonEq (.arr .omega .bool .bool) (.arr .omega .bool .bool) = true := by
  decide

/-- Mismatched head shapes (a genuine `ua`-style line between a `Π` and a `Bool`, i.e. between
    unrelated types) are untouched by this check, matching the Rust original's documented
    behavior — the check only ever *adds* a restriction to matching `Π`-former positions, never to
    a line that changes type former entirely. -/
theorem kanLineGradeSkeletonEq_mismatched_heads_unconstrained (ρ : Grade) (dom cod : Ty) :
    kanLineGradeSkeletonEq .bool (.arr ρ dom cod) = true ∧
      kanLineGradeSkeletonEq (.arr ρ dom cod) .bool = true :=
  ⟨rfl, rfl⟩

end BlightMeta
