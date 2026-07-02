/-
  Structural lemmas about `HasType` needed before substitution/preservation: checking at ambient
  `0` forces all-zero usage (the mechanized form of §1.1(a)/(d)'s "erasure is total"), and general
  weakening (inserting a fresh, unused binder anywhere in the context) — the ingredient the
  substitution lemma (`Substitution.lean`) needs to shift the substituted term correctly when
  recursing under a binder, mirroring `subst`'s own `shiftAbove 0 s` call in the `lam` case.
-/

import BlightMeta.Calculus

namespace BlightMeta

/-- **Ambient-zero erasure is total**: if `e` is checked at ambient demand `0`, *every* variable's
    recorded usage is `0` — not just the ones lying in a type-formation/family position (§1.1(a)),
    but literally all of them, since at `σ = 0` the `Var` rule's unit contribution is `0`
    everywhere and no other rule scales usage back up. This is the fact that makes the
    substitution lemma close in the one case where the naive bound `δ ≤ ρ` isn't already enough
    on its own (`σ = 0`, where `σ · ρ = 0` regardless of `ρ`). -/
theorem ambient_zero_usage {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) : σ = Grade.zero → φ = Usage.zero Γ.length := by
  induction h with
  | var => intro hσ; subst hσ; exact Usage.unit_zero _ _
  | lam _ _ ih =>
    intro hσ
    have htail := ih hσ
    injection htail with _ ht
  | app hf ha ihf iha =>
    intro hσ
    subst hσ
    have hfz := ihf rfl
    have haz := iha rfl
    simp only [hfz, haz, Usage.add_zero_zero]
  | tt => intro _; rfl
  | ff => intro _; rfl
  | ite _ _ _ ihc iht ihe =>
    intro hσ
    subst hσ
    simp only [ihc rfl, iht rfl, ihe rfl, Usage.add_zero_zero]
  | iabs _ ihbody => intro hσ; exact ihbody hσ
  | transp _ ihbase => intro hσ; exact ihbase hσ
  | hcomp _ _ ihtube ihbase =>
    intro hσ
    subst hσ
    simp only [ihtube rfl, ihbase rfl, Usage.add_zero_zero]

/-- The grade arithmetic the substitution lemma's `app`/`lam` (β) case needs: a binder's
    *actual* demand `δ` (bounded by its *declared* grade `ρ` — `T-lam`'s own `hle`) never exceeds
    `σ · ρ`, the exact grade `T-app` checks the argument at. The one case where `δ ≤ ρ` doesn't
    already finish it (`σ = 0`, so `σ · ρ = 0` regardless of `ρ`) is exactly where
    `ambient_zero_usage` forces `δ = 0` too — so this is really "`δ ≤ ρ` plus the σ = 0 collapse,"
    combined by a case split on `σ`. This is the mechanized generalization of the "layered
    reading" §1.2 sketches for `hcomp`/`comp`'s additive accounting to the substitution step. -/
theorem demand_le_scale {σ ρ δ : Grade} (hle : δ ≤ ρ) (hzero : σ = Grade.zero → δ = Grade.zero) :
    δ ≤ σ.mul ρ := by
  cases σ with
  | zero => simp [hzero rfl, Grade.mul]
  | one => rw [Grade.one_mul]; exact hle
  | omega =>
    cases ρ with
    | zero =>
      have : δ = Grade.zero := by cases δ <;> simp_all [Grade.le_def, Grade.rank]
      simp [this, Grade.mul]
    | one => cases δ <;> decide
    | omega => cases δ <;> decide

/-- If a de Bruijn lookup succeeds, the index is in bounds. Plain induction rather than a library
    lemma, to not depend on the exact `List.getElem?` API surface of a given Lean version. -/
theorem lookup_lt {α : Type _} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.length_cons]
      have : l[i]? = some a := by simpa using h
      have := ih this
      omega

/-- `insertTy`/`shiftAbove` at position `c` commute with `List.get?` the way you'd expect: a
    lookup strictly below `c` (a binder more local than the insertion point) is untouched, and
    one at/above `c` shifts by 1 (it's now one binder further from the innermost end). -/
theorem insertTy_get_lt {Γ : List Ty} {c i : Nat} {X : Ty} (h : i < c) (hin : i < Γ.length) :
    (insertTy Γ c X)[i]? = Γ[i]? := by
  induction Γ generalizing c i with
  | nil => simp only [List.length_nil] at hin; omega
  | cons A Γ ih => cases c with
    | zero => omega
    | succ c => cases i with
      | zero => rfl
      | succ i =>
        have hin' : i < Γ.length := by simp only [List.length_cons] at hin; omega
        exact ih (by omega) hin'

/-- `insertTy`/`insertUsage` at position `0` unfold to a plain `cons`, for an *arbitrary* (not
    necessarily literal-`cons`) list — needed because the equation compiler's generated code
    matches on the list argument before the position, so `insertTy Γ 0 X` doesn't reduce via
    `rfl` alone unless `Γ`'s shape (`nil`/`cons`) is already known. -/
theorem insertTy_zero (Γ : List Ty) (X : Ty) : insertTy Γ 0 X = X :: Γ := by
  cases Γ <;> rfl

theorem insertTy_get_ge {Γ : List Ty} {c i : Nat} {X : Ty} (h : i ≥ c) :
    (insertTy Γ c X)[i + 1]? = Γ[i]? := by
  induction Γ generalizing c i with
  | nil => cases c with
    | zero => rfl
    | succ c => cases i with
      | zero => omega
      | succ i => rfl
  | cons A Γ ih => cases c with
    | zero => rfl
    | succ c => cases i with
      | zero => omega
      | succ i => exact ih (by omega)

/-- The freshly-inserted slot itself reads back as exactly what was inserted — the fact the
    substitution lemma's `var`-hits-the-substituted-slot case needs to identify the looked-up
    type `A` with `A'`. -/
theorem insertTy_get_eq {Γ : List Ty} {c : Nat} {X : Ty} (h : c ≤ Γ.length) :
    (insertTy Γ c X)[c]? = some X := by
  induction Γ generalizing c with
  | nil =>
    simp only [List.length_nil] at h
    have hc : c = 0 := Nat.le_zero.mp h
    subst hc; rfl
  | cons A Γ ih => cases c with
    | zero => rfl
    | succ c => exact ih (by simpa using h)

theorem insertTy_length {Γ : List Ty} {c : Nat} {X : Ty} :
    (insertTy Γ c X).length = Γ.length + 1 := by
  induction Γ generalizing c with
  | nil => cases c <;> rfl
  | cons A Γ ih => cases c with
    | zero => rfl
    | succ c => simp [insertTy, ih]

theorem insertUsage_cons_zero (u : Usage) : insertUsage u 0 = Grade.zero :: u := by
  cases u <;> rfl

theorem insertUsage_length {u : Usage} {c : Nat} : (insertUsage u c).length = u.length + 1 := by
  induction u generalizing c with
  | nil => cases c <;> rfl
  | cons g u ih => cases c with
    | zero => rfl
    | succ c => simp [insertUsage, ih]

/-- Inserting a fresh `0` slot anywhere in an all-`0` vector gives an all-`0` vector one longer. -/
theorem insertUsage_zero (n c : Nat) : insertUsage (Usage.zero n) c = Usage.zero (n + 1) := by
  induction n generalizing c with
  | zero => cases c <;> rfl
  | succ n ih =>
    cases c with
    | zero => rfl
    | succ c =>
      simp only [Usage.zero, insertUsage]
      congr 1
      exact ih c

/-- `insertUsage` distributes over `add`, provided the two summands are equal-length (they always
    are here — both come from `HasType` derivations over the same context, `usage_length`). -/
theorem insertUsage_add {u v : Usage} (hlen : u.length = v.length) (c : Nat) :
    insertUsage (Usage.add u v) c = Usage.add (insertUsage u c) (insertUsage v c) := by
  induction u generalizing v c with
  | nil => cases v with
    | nil => cases c <;> rfl
    | cons _ _ => simp_all
  | cons g u ih =>
    cases v with
    | nil => simp_all
    | cons h v =>
      cases c with
      | zero => rfl
      | succ c =>
        have hlen' : u.length = v.length := by simpa using hlen
        simp only [Usage.add, insertUsage]
        congr 1
        exact ih hlen' c

/-- `insertUsage` "shifts" a `unit` vector the same way `insertTy_get_lt`/`_ge` shift a lookup:
    inserting a fresh slot strictly above the demanded index leaves it in place; inserting at or
    below it moves it up by one. Needed by `weaken`'s `var` case. -/
theorem insertUsage_unit_lt {n c i : Nat} {g : Grade} (h : i < c) (hin : i < n) :
    insertUsage (Usage.unit i n g) c = Usage.unit i (n + 1) g := by
  induction n generalizing c i with
  | zero => omega
  | succ n ih =>
    cases c with
    | zero => omega
    | succ c =>
      cases i with
      | zero =>
        show insertUsage (g :: Usage.zero n) (c + 1) = g :: Usage.zero (n + 1)
        rw [show insertUsage (g :: Usage.zero n) (c + 1) = g :: insertUsage (Usage.zero n) c from rfl,
          insertUsage_zero]
      | succ i =>
        simp only [Usage.unit, insertUsage]
        congr 1
        exact ih (by omega) (by omega)

theorem insertUsage_unit_ge {n c i : Nat} {g : Grade} (h : i ≥ c) (hin : i < n) :
    insertUsage (Usage.unit i n g) c = Usage.unit (i + 1) (n + 1) g := by
  induction n generalizing c i with
  | zero => omega
  | succ n ih =>
    cases c with
    | zero =>
      cases i with
      | zero => rfl
      | succ i => rfl
    | succ c =>
      cases i with
      | zero => omega
      | succ i =>
        simp only [Usage.unit, insertUsage]
        congr 1
        exact ih (by omega) (by omega)

/-- `insertUsage` "shifts" `get` the same way it shifts `unit` (`insertUsage_unit_lt`/`_ge` above)
    and the same way `insertTy` shifts a type lookup: a slot strictly below the insertion point is
    untouched, the inserted slot itself reads back as the fresh `0`, and a slot at/above it shifts
    up by one. Needed by the substitution lemma (`Substitution.lean`) to relate its `insertUsage`-
    padded usage bound back to plain `get` facts about the un-padded result. -/
theorem insertUsage_get_lt {u : Usage} {c i : Nat} (h : i < c) :
    (insertUsage u c).get i = u.get i := by
  induction u generalizing c i with
  | nil => cases c with
    | zero => omega
    | succ c => cases i with
      | zero => rfl
      | succ i => rfl
  | cons g gs ih => cases c with
    | zero => omega
    | succ c => cases i with
      | zero => rfl
      | succ i =>
        simp only [insertUsage, Usage.get]
        exact ih (by omega)

theorem insertUsage_get_self (u : Usage) (c : Nat) : (insertUsage u c).get c = Grade.zero := by
  induction u generalizing c with
  | nil => cases c <;> rfl
  | cons g gs ih => cases c with
    | zero => rfl
    | succ c => simp only [insertUsage, Usage.get]; exact ih c

theorem insertUsage_get_ge {u : Usage} {c i : Nat} (h : i ≥ c) :
    (insertUsage u c).get (i + 1) = u.get i := by
  induction u generalizing c i with
  | nil => cases c with
    | zero => rfl
    | succ c => cases i with
      | zero => omega
      | succ i => rfl
  | cons g gs ih => cases c with
    | zero => rfl
    | succ c => cases i with
      | zero => omega
      | succ i =>
        simp only [insertUsage, Usage.get]
        exact ih (by omega)

/-- The usage vector produced by `HasType` always has one entry per context variable — a basic
    sanity invariant used throughout (e.g. to know `φf`/`φa` are equal-length before adding, and
    that `insertTy`/`insertUsage`'s lengths line up in `weaken`). -/
theorem usage_length {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) : φ.length = Γ.length := by
  induction h with
  | @var Γ d i A σ hlk => exact Usage.length_unit i Γ.length _ (lookup_lt hlk)
  | lam _ hle ih =>
    have := ih
    simp only [List.length_cons] at this
    omega
  | app _ _ ihf iha => simp [Usage.length_add, ihf, iha]
  | tt => simp
  | ff => simp
  | ite _ _ _ ihc iht ihe => simp [Usage.length_add, ihc, iht, ihe]
  | iabs _ ihbody => exact ihbody
  | transp _ ihbase => exact ihbase
  | hcomp _ _ ihtube ihbase => simp [Usage.length_add, ihtube, ihbase]

/-- **Grade demotion**: a term checked at ambient `σ` also checks at any *smaller* ambient `σ'`
    (`σ' ≤ σ`), with usage that only *shrinks* (`Usage.Le`). This is the mechanized form of §1.2's
    "the layered/erasure reading is exactly what standard metatheory predicts" for the general
    order `0 ≤ 1 ≤ ω`, not just the `0`-fragment `ambient_zero_usage` already isolates: using
    something *less* than originally licensed (fewer times, or not at all) is always sound. This
    is exactly what the substitution lemma's `var`-hits-the-substituted-slot case needs: the
    substituted term was checked once at some grade `π`, but is being spliced in at a (possibly
    smaller) occurrence-specific ambient `σ' ≤ π`. -/
theorem demote {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) :
    ∀ {σ' : Grade}, σ' ≤ σ → ∃ φ', HasType Γ d e A σ' φ' ∧ Usage.Le φ' φ := by
  induction h with
  | @var Γ d i A σ hlk =>
    intro σ' hσ'
    exact ⟨Usage.unit i Γ.length σ', HasType.var hlk, Usage.unit_le hσ'⟩
  | @lam Γ d body ρ σ δ A B rest hbody hle ihbody =>
    intro σ' hσ'
    obtain ⟨φ', hφ', hLe⟩ := ihbody hσ'
    have hlen : φ'.length = (A :: Γ).length := usage_length hφ'
    obtain ⟨δ', rest', hφ'eq⟩ : ∃ δ' rest', φ' = δ' :: rest' := by
      cases φ' with
      | nil => simp at hlen
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφ'eq
    obtain ⟨hδδ, hrestrest⟩ := hLe
    exact ⟨rest', HasType.lam hφ' (Grade.le_trans hδδ hle), hrestrest⟩
  | @app Γ d f a ρ σ A B φf φa hf ha ihf iha =>
    intro σ' hσ'
    obtain ⟨φf', hφf', hlef⟩ := ihf hσ'
    obtain ⟨φa', hφa', hlea⟩ := iha (Grade.mul_mono_left hσ' ρ)
    exact ⟨Usage.add φf' φa', HasType.app hφf' hφa', Usage.add_mono hlef hlea⟩
  | @tt Γ d σ =>
    intro σ' _
    exact ⟨Usage.zero Γ.length, HasType.tt, Usage.le_refl _⟩
  | @ff Γ d σ =>
    intro σ' _
    exact ⟨Usage.zero Γ.length, HasType.ff, Usage.le_refl _⟩
  | @ite Γ d cnd t e σ A φc φt φe hc ht he ihc iht ihe =>
    intro σ' hσ'
    obtain ⟨φc', hφc', hlec⟩ := ihc hσ'
    obtain ⟨φt', hφt', hlet⟩ := iht hσ'
    obtain ⟨φe', hφe', hlee⟩ := ihe hσ'
    exact ⟨Usage.add φc' (Usage.add φt' φe'), HasType.ite hφc' hφt' hφe',
      Usage.add_mono hlec (Usage.add_mono hlet hlee)⟩
  | @iabs Γ d body A σ φ hbody ihbody =>
    intro σ' hσ'
    obtain ⟨φ', hφ', hLe⟩ := ihbody hσ'
    exact ⟨φ', HasType.iabs hφ', hLe⟩
  | @transp Γ d A base σ φ hbase ihbase =>
    intro σ' hσ'
    obtain ⟨φ', hφ', hLe⟩ := ihbase hσ'
    exact ⟨φ', HasType.transp hφ', hLe⟩
  | @hcomp Γ d A phi tube base σ φtube φbase htube hbase ihtube ihbase =>
    intro σ' hσ'
    obtain ⟨φtube', hφtube', hletube⟩ := ihtube hσ'
    obtain ⟨φbase', hφbase', hlebase⟩ := ihbase hσ'
    exact ⟨Usage.add φtube' φbase', HasType.hcomp hφtube' hφbase',
      Usage.add_mono hletube hlebase⟩

/-- Combines two "substitution bound" facts (of the shape the substitution lemma produces at
    each `HasType` constructor: a padded result usage bounded by the original usage plus a
    `scale`d correction) additively — the fact `T-app`/`T-ite`'s summed sub-usages need to turn
    two per-branch bounds into one bound for the combined branch. Factored out here since `app`
    (two branches) and `ite` (three, via two applications of this) both need exactly this
    rearrangement. -/
theorem insertUsage_scale_add_bound {k : Nat} {u1 u2 u1' u2' X : Usage}
    (hlenu : u1.length = u2.length) (hlenu1X : u1.length = X.length)
    (hlenu' : u1'.length = u2'.length)
    (h1 : Usage.Le (insertUsage u1' k) (Usage.add u1 (Usage.scale (u1.get k) X)))
    (h2 : Usage.Le (insertUsage u2' k) (Usage.add u2 (Usage.scale (u2.get k) X))) :
    Usage.Le (insertUsage (Usage.add u1' u2') k)
      (Usage.add (Usage.add u1 u2) (Usage.scale ((Usage.add u1 u2).get k) X)) := by
  rw [insertUsage_add hlenu' k]
  have hcombine := Usage.add_mono h1 h2
  have hnX : X.length = u1.length := hlenu1X.symm
  have hnS1 : (Usage.scale (u1.get k) X).length = u1.length := by
    rw [Usage.length_scale, hnX]
  have hnS2 : (Usage.scale (u2.get k) X).length = u1.length := by
    rw [Usage.length_scale, hnX, hlenu]
  have hnu2S2 : (Usage.add u2 (Usage.scale (u2.get k) X)).length = u1.length := by
    rw [Usage.length_add, ← hlenu, hnS2, Nat.min_self]
  have hnu2 : u2.length = u1.length := hlenu.symm
  have hnS1S2 : (Usage.add (Usage.scale (u1.get k) X) (Usage.scale (u2.get k) X)).length
      = u1.length := by
    rw [Usage.length_add, hnS1, hnS2, Nat.min_self]
  have e1 : u1.length = (Usage.scale (u1.get k) X).length := hnS1.symm
  have e2 : (Usage.scale (u1.get k) X).length
      = (Usage.add u2 (Usage.scale (u2.get k) X)).length := hnS1.trans hnu2S2.symm
  have e3 : (Usage.scale (u1.get k) X).length = u2.length := hnS1.trans hnu2.symm
  have e4 : u2.length = (Usage.scale (u2.get k) X).length := hnu2.trans hnS2.symm
  have e6 : (Usage.scale (u1.get k) X).length = (Usage.scale (u2.get k) X).length :=
    hnS1.trans hnS2.symm
  have e8 : u2.length = (Usage.add (Usage.scale (u1.get k) X) (Usage.scale (u2.get k) X)).length :=
    hnu2.trans hnS1S2.symm
  have hrearranged :
      Usage.add (Usage.add u1 (Usage.scale (u1.get k) X)) (Usage.add u2 (Usage.scale (u2.get k) X))
      = Usage.add (Usage.add u1 u2) (Usage.scale ((Usage.add u1 u2).get k) X) := by
    rw [Usage.add_assoc u1 (Usage.scale (u1.get k) X) (Usage.add u2 (Usage.scale (u2.get k) X))
        e1 e2,
      ← Usage.add_assoc (Usage.scale (u1.get k) X) u2 (Usage.scale (u2.get k) X) e3 e4,
      Usage.add_comm (Usage.scale (u1.get k) X) u2 e3,
      Usage.add_assoc u2 (Usage.scale (u1.get k) X) (Usage.scale (u2.get k) X) e3.symm e6,
      ← Usage.add_assoc u1 u2 (Usage.add (Usage.scale (u1.get k) X) (Usage.scale (u2.get k) X))
        hlenu e8,
      Usage.scale_add_grade, ← Usage.get_add hlenu]
  rwa [hrearranged] at hcombine

/-- **Scaled grade demotion**: strengthens `demote`'s bound from a plain `Le φ' φ` to `Le φ'
    (scale σ' φ)`. This is what the substitution lemma actually needs — a *single* occurrence's
    demoted usage must fit inside a `σ'`-scaled copy of `φa`, so that summing several occurrences
    (`T-app`/`T-ite`'s additive accounting) via `scale_add_grade` reconstructs a bound scaled by
    their *combined* demand, matching the `k`-th slot's aggregate usage. Proved as a thin case
    split on the (finite) grade `σ'` over the already-established unscaled `demote`, rather than
    redoing its structural induction: at `σ' = 1`, `scale` is the identity (`demote` verbatim); at
    `σ' = ω`, scaling never shrinks (`le_scale_omega`); at `σ' = 0`, `ambient_zero_usage` forces
    the demoted usage to be all-zero outright. -/
theorem demote_scaled {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) {σ' : Grade} (hσ' : σ' ≤ σ) :
    ∃ φ', HasType Γ d e A σ' φ' ∧ Usage.Le φ' (Usage.scale σ' φ) := by
  obtain ⟨φ', hφ', hLe⟩ := demote h hσ'
  cases σ' with
  | zero =>
    have hz : φ' = Usage.zero Γ.length := ambient_zero_usage hφ' rfl
    subst hz
    refine ⟨Usage.zero Γ.length, hφ', ?_⟩
    rw [Usage.scale_zero, usage_length h]
    exact Usage.le_refl _
  | one =>
    refine ⟨φ', hφ', ?_⟩
    rwa [Usage.scale_one]
  | omega =>
    exact ⟨φ', hφ', Usage.le_trans hLe (Usage.le_scale_omega φ)⟩

/-- **Dimension weakening**: opening additional dimension binders never invalidates a derivation —
    `d` is pure well-scoping bookkeeping that no rule ever compares against a specific value (only
    `iabs` even mentions it, and only to increment it relative to its own conclusion), so a
    derivation valid with `d` dimensions in scope is just as valid with more. `Substitution.lean`'s
    `iabs` case needs this to make the substituted term's own derivation available one dimension
    deeper, mirroring the ordinary `weaken 0` re-shift its `lam` case already needs for one more
    *term* binder — the exact dimension-side counterpart. -/
theorem dim_weaken {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) : HasType Γ (d + 1) e A σ φ := by
  induction h with
  | var hlk => exact HasType.var hlk
  | lam _ hle ih => exact HasType.lam ih hle
  | app _ _ ihf iha => exact HasType.app ihf iha
  | tt => exact HasType.tt
  | ff => exact HasType.ff
  | ite _ _ _ ihc iht ihe => exact HasType.ite ihc iht ihe
  | iabs _ ihbody => exact HasType.iabs ihbody
  | transp _ ihbase => exact HasType.transp ihbase
  | hcomp _ _ ihtube ihbase => exact HasType.hcomp ihtube ihbase

/-- **Dimension-count is fully immaterial**: since no rule ever inspects `d`'s concrete value
    (only `iabs` even mentions it, purely to increment it locally for its own premise), a
    derivation valid at any one dimension count is valid at *every* other — strictly stronger than
    `dim_weaken`'s one-directional `d → d + 1` (which only needed the "grows" half). `Progress.lean`
    needs the *other* direction: stepping `.iabs body` to `body` moves from a `d + 1`-deep
    derivation (the `iabs` rule's premise) back down to the ambient `d`, matching the operational
    reading that opening a dimension binder is a complete runtime no-op, not merely a typing one. -/
theorem dim_change {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) : ∀ d' : Nat, HasType Γ d' e A σ φ := by
  induction h with
  | var hlk => intro d'; exact HasType.var hlk
  | lam _ hle ih => intro d'; exact HasType.lam (ih d') hle
  | app _ _ ihf iha => intro d'; exact HasType.app (ihf d') (iha d')
  | tt => intro d'; exact HasType.tt
  | ff => intro d'; exact HasType.ff
  | ite _ _ _ ihc iht ihe => intro d'; exact HasType.ite (ihc d') (iht d') (ihe d')
  | iabs _ ihbody => intro d'; exact HasType.iabs (ihbody (d' + 1))
  | transp _ ihbase => intro d'; exact HasType.transp (ihbase d')
  | hcomp _ _ ihtube ihbase => intro d'; exact HasType.hcomp (ihtube d') (ihbase d')

/-- **General weakening**: inserting a fresh, unused binder anywhere in the context (not just at
    the front) preserves typability, shifting the term (`Tm.shiftAbove`) and usage
    (`insertUsage`) accordingly. This is the ingredient `subst`'s own recursive `lam` case
    (`subst (j+1) (shiftAbove 0 s) body`) needs: substituting under one more binder requires the
    substituted term to be re-weakened one level deeper, which is exactly `weaken _ 0 _`. -/
theorem weaken {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) : ∀ (c : Nat) (X : Ty),
    HasType (insertTy Γ c X) d (Tm.shiftAbove c e) A σ (insertUsage φ c) := by
  induction h with
  | @var Γ d i A σ hlk =>
    intro c X
    have hlen : i < Γ.length := lookup_lt hlk
    rcases Nat.lt_or_ge i c with hic | hic
    · simp only [Tm.shiftAbove, if_pos hic]
      rw [insertUsage_unit_lt hic hlen]
      have hlk' : (insertTy Γ c X)[i]? = some A := (insertTy_get_lt hic hlen).trans hlk
      have hres := HasType.var (Γ := insertTy Γ c X) (d := d) (σ := σ) hlk'
      rwa [insertTy_length] at hres
    · simp only [Tm.shiftAbove, if_neg (Nat.not_lt.mpr hic)]
      rw [insertUsage_unit_ge hic hlen]
      have hlk' : (insertTy Γ c X)[i + 1]? = some A := (insertTy_get_ge hic).trans hlk
      have hres := HasType.var (Γ := insertTy Γ c X) (d := d) (i := i + 1) (σ := σ) hlk'
      rwa [insertTy_length] at hres
  | @lam Γ d body ρ σ δ A B rest _ hle ihbody =>
    intro c X
    have hbody' := ihbody (c + 1) X
    exact HasType.lam hbody' hle
  | @app Γ d f a ρ σ A B φf φa hf ha ihf iha =>
    intro c X
    have hf' := ihf c X
    have ha' := iha c X
    have hlen : φf.length = φa.length := by rw [usage_length hf, usage_length ha]
    show HasType (insertTy Γ c X) d (Tm.app (Tm.shiftAbove c f) (Tm.shiftAbove c a)) B σ
      (insertUsage (Usage.add φf φa) c)
    rw [insertUsage_add hlen c]
    exact HasType.app hf' ha'
  | @tt Γ d σ =>
    intro c X
    show HasType (insertTy Γ c X) d Tm.tt Ty.bool σ (insertUsage (Usage.zero Γ.length) c)
    rw [insertUsage_zero, ← insertTy_length (Γ := Γ) (c := c) (X := X)]
    exact HasType.tt
  | @ff Γ d σ =>
    intro c X
    show HasType (insertTy Γ c X) d Tm.ff Ty.bool σ (insertUsage (Usage.zero Γ.length) c)
    rw [insertUsage_zero, ← insertTy_length (Γ := Γ) (c := c) (X := X)]
    exact HasType.ff
  | @ite Γ d cnd t e σ A φc φt φe hc ht he ihc iht ihe =>
    intro c X
    have hlc := usage_length hc
    have hlt := usage_length ht
    have hle := usage_length he
    have hlen1 : φt.length = φe.length := by rw [hlt, hle]
    have hlen2 : φc.length = (Usage.add φt φe).length := by
      rw [Usage.length_add, hlt, hle, hlc, Nat.min_self]
    show HasType (insertTy Γ c X) d
      (Tm.ite (Tm.shiftAbove c cnd) (Tm.shiftAbove c t) (Tm.shiftAbove c e)) A σ
      (insertUsage (Usage.add φc (Usage.add φt φe)) c)
    rw [insertUsage_add hlen2 c, insertUsage_add hlen1 c]
    exact HasType.ite (ihc c X) (iht c X) (ihe c X)
  | @iabs Γ d body A σ φ hbody ihbody =>
    intro c X
    exact HasType.iabs (ihbody c X)
  | @transp Γ d A base σ φ hbase ihbase =>
    intro c X
    exact HasType.transp (ihbase c X)
  | @hcomp Γ d A phi tube base σ φtube φbase htube hbase ihtube ihbase =>
    intro c X
    have hlen : φtube.length = φbase.length := by rw [usage_length htube, usage_length hbase]
    show HasType (insertTy Γ c X) d
      (Tm.hcomp A phi (Tm.shiftAbove c tube) (Tm.shiftAbove c base)) A σ
      (insertUsage (Usage.add φtube φbase) c)
    rw [insertUsage_add hlen c]
    exact HasType.hcomp (ihtube c X) (ihbase c X)

end BlightMeta
