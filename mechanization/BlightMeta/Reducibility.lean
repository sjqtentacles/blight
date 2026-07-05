/-
  Wave 8 / M8: strong normalization + canonicity for the M5/M6 fragment (`docs/design-wave4-gobars.md`
  §1's go-bar). A Tait-style reducibility-candidates proof, indexed by `Ty`, showing every well-typed
  term is reducible — hence (the standard corollary) strongly normalizing — plus a `Step` determinism
  lemma and canonicity (a closed `Bool` reduces to `tt`/`ff`) as a short corollary of SN + determinism
  + `progress`.

  ── Why a fresh, grade-free `Typed` judgement ────────────────────────────────────────────────────
  The go-bar is explicit that "grades are orthogonal to this proof, not an extra dimension of it":
  `Step`/`Value` (`Progress.lean`) never mention `σ`/`φ`, so the logical relation below is a property
  of `Tm`/`Ty` alone. But the reducibility candidate for `Pi` still needs *some* notion of well-typing
  bundled in (see the next section for why), so this file introduces `Typed : List Ty → Tm → Ty →
  Prop` — `HasType` with every grade/usage/dimension index erased — with its own (much shorter, no
  usage arithmetic) weakening + substitution + progress + preservation lemmas, all re-derived from
  scratch alongside an easy one-line erasure `of_has_type : HasType Γ d e A σ φ → Typed Γ e A` used
  only at the two theorems' entry points. This keeps the *reducibility* argument itself free of any
  grade bookkeeping while still connecting back to `HasType` for the final statements.

  ── Why `Reducible` bundles `Typed [] t A`, not just `SN t` ──────────────────────────────────────
  The textbook reason: proving `lam`'s case (`Pi`-introduction is reducible when its body's every
  substitution instance is) needs, for an *arbitrary* reducible argument `a`, to case on whether `a`
  is already a value or can still step — i.e. `Typed.progress` — to run the standard induction on
  `a`'s strong normalization. Without tying `Reducible` to `Typed`, an ill-typed "stuck junk" term
  (e.g. `.app .tt .tt`, neither a value nor able to step) would vacuously count as reducible at
  `Bool` (it can't step, so it is trivially `SN`) while breaking that case split. Bundling `Typed`
  rules this out for free via `progress`.

  ── Layout ────────────────────────────────────────────────────────────────────────────────────────
  §0 `NoFreeAbove`/`ClosedTm` + shift/subst invariance, and the one general two-substitution
     commutation lemma (`subst_comm`) everything else is built from.
  §1 `Typed` and its mini metatheory (weakening, substitution, progress, preservation).
  §2 `Step` determinism.
  §3 `SN` and its basic closure facts.
  §4 `closeAt`/`close`: closing an open term with a list of (closed) values, one variable at a time,
     front-to-back — the substitution-list algebra the fundamental lemma runs on.
  §5 `Reducible`, its closure lemmas (`step` = CR2 forward, `backward` = the beta/expansion direction),
     and the five "reducibility survives every M5 `Step` rule" lemmas the go-bar calls out
     (`Reducible_lam` for β, `Reducible_ite` for ι, `Reducible_transp`/`Reducible_hcomp`/
     `Reducible_iabs` for the Kan formers).
  §6 `RedSubst` and the fundamental lemma.
  §7 `strong_normalization`, `step_deterministic`, `canonicity`.
-/

import BlightMeta.Progress

namespace BlightMeta

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §0. Bound variables, closedness, and the substitution-commutation lemma.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- `e`'s free variables are all `< n` (crossing a `lam` bumps `n`, matching `shiftAbove`/`subst`'s
    own recursion) — the standard "de Bruijn bound" predicate. -/
def NoFreeAbove : Tm → Nat → Prop
  | .var i, n => i < n
  | .lam body, n => NoFreeAbove body (n + 1)
  | .app f a, n => NoFreeAbove f n ∧ NoFreeAbove a n
  | .tt, _ => True
  | .ff, _ => True
  | .ite c t e, n => NoFreeAbove c n ∧ NoFreeAbove t n ∧ NoFreeAbove e n
  | .iabs body, n => NoFreeAbove body n
  | .transp _ base, n => NoFreeAbove base n
  | .hcomp _ _ tube base, n => NoFreeAbove tube n ∧ NoFreeAbove base n

/-- No free variables at all. -/
def ClosedTm (t : Tm) : Prop := NoFreeAbove t 0

/-- Shifting above every free variable is a no-op: nothing at or past `c` was ever free. -/
theorem NoFreeAbove_shift : ∀ {t : Tm} {n c : Nat}, NoFreeAbove t n → n ≤ c →
    Tm.shiftAbove c t = t := by
  intro t
  induction t with
  | var i =>
    intro n c h hnc
    simp only [NoFreeAbove] at h
    simp only [Tm.shiftAbove]; rw [if_pos (by omega : i < c)]
  | lam body ih => intro n c h hnc; simp only [Tm.shiftAbove]; congr 1; exact ih h (by omega)
  | app f a ihf iha =>
    intro n c h hnc
    obtain ⟨hf, ha⟩ := h
    simp only [Tm.shiftAbove]; rw [ihf hf hnc, iha ha hnc]
  | tt => intros; rfl
  | ff => intros; rfl
  | ite c t e ihc iht ihe =>
    intro n cc h hnc
    obtain ⟨hc, ht, he⟩ := h
    simp only [Tm.shiftAbove]; rw [ihc hc hnc, iht ht hnc, ihe he hnc]
  | iabs body ih => intro n c h hnc; simp only [Tm.shiftAbove]; congr 1; exact ih h hnc
  | transp A base ih => intro n c h hnc; simp only [Tm.shiftAbove]; congr 1; exact ih h hnc
  | hcomp A phi tube base ihtube ihbase =>
    intro n c h hnc
    obtain ⟨ht, hb⟩ := h
    simp only [Tm.shiftAbove]; rw [ihtube ht hnc, ihbase hb hnc]

/-- Substituting a variable strictly above every free variable of `e` is a no-op: `e` never
    mentions that variable, at any nesting depth. -/
theorem NoFreeAbove_subst : ∀ {e : Tm} {n j : Nat} {s : Tm}, NoFreeAbove e n → n ≤ j →
    Tm.subst j s e = e := by
  intro e
  induction e with
  | var i =>
    intro n j s h hnj
    simp only [NoFreeAbove] at h
    simp only [Tm.subst]
    rw [if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ i > j)]
  | lam body ih => intro n j s h hnj; simp only [Tm.subst]; congr 1; exact ih h (by omega)
  | app f a ihf iha =>
    intro n j s h hnj
    obtain ⟨hf, ha⟩ := h
    simp only [Tm.subst]; rw [ihf hf hnj, iha ha hnj]
  | tt => intros; rfl
  | ff => intros; rfl
  | ite c t e ihc iht ihe =>
    intro n j s h hnj
    obtain ⟨hc, ht, he⟩ := h
    simp only [Tm.subst]; rw [ihc hc hnj, iht ht hnj, ihe he hnj]
  | iabs body ih => intro n j s h hnj; simp only [Tm.subst]; congr 1; exact ih h hnj
  | transp A base ih => intro n j s h hnj; simp only [Tm.subst]; congr 1; exact ih h hnj
  | hcomp A phi tube base ihtube ihbase =>
    intro n j s h hnj
    obtain ⟨ht, hb⟩ := h
    simp only [Tm.subst]; rw [ihtube ht hnj, ihbase hb hnj]

theorem ClosedTm.shift {t : Tm} (h : ClosedTm t) (c : Nat) : Tm.shiftAbove c t = t :=
  NoFreeAbove_shift h (Nat.zero_le c)

theorem ClosedTm.subst {t : Tm} (h : ClosedTm t) (j : Nat) (s : Tm) : Tm.subst j s t = t :=
  NoFreeAbove_subst h (Nat.zero_le j)

/-- **The substitution-commutation lemma.** Substituting two *closed* terms at two different
    (adjacent-after-the-first-removes-a-slot) positions commutes, in the precise sense needed to
    re-associate a chain of single-variable substitutions: substituting `s1` at `i` after `s2` at
    `j + 1` agrees with substituting `s2` at `j` after `s1` at `i` (`i ≤ j`), since closedness means
    neither `s1` nor `s2` needs any further shifting once it lands. This is the one genuinely fiddly
    fact `docs/design-wave4-gobars.md` warns "mechanizing SN is notoriously fiddly" over; every other
    closing-substitution lemma below (`closeAt_lam`, `subst0_closeAt1`) is a direct corollary. -/
theorem subst_comm : ∀ {e : Tm} {i j : Nat}, i ≤ j → ∀ {s1 s2 : Tm}, ClosedTm s1 → ClosedTm s2 →
    Tm.subst i s1 (Tm.subst (j + 1) s2 e) = Tm.subst j s2 (Tm.subst i s1 e) := by
  intro e
  induction e with
  | var k =>
    intro i j hij s1 s2 hs1 hs2
    -- Each branch below feeds every `if_neg`/`if_pos` fact its case needs to a single fixpoint
    -- `simp` (not `simp only`, so the ambient arithmetic lemmas — `Nat.add_sub_cancel` etc. — are
    -- on hand to normalize index arithmetic like `j + 1 - 1` down to `j`) call, which re-fires on
    -- every freshly-exposed `Tm.subst _ _ (Tm.var _)` redex a previous collapse reveals, finishing
    -- with `hs1.subst`/`hs2.subst` to discharge whichever side lands on the *other* closed term.
    rcases Nat.lt_trichotomy k i with hki | hki | hki
    · -- k < i ≤ j < j + 1: untouched by either substitution.
      simp [Tm.subst, if_neg (show ¬ k = j + 1 by omega), if_neg (show ¬ k > j + 1 by omega),
        if_neg (show ¬ k = i by omega), if_neg (show ¬ k > i by omega),
        if_neg (show ¬ k = j by omega), if_neg (show ¬ k > j by omega)]
    · -- k = i ≤ j: the LHS's inner step is a no-op (i < j+1, so `subst (j+1) s2` doesn't touch
      -- `var i`), landing both sides on `Tm.subst i s1 (Tm.var i) = s1` — the LHS immediately, the
      -- RHS after one more (no-op, since s1 is closed) pass through `subst j s2`. `hki` is fed to
      -- `simp` itself (rather than `subst`, whose choice of which of `k`/`i` survives is opaque)
      -- so every fact below can be phrased in the one name, `i`, guaranteed to be what remains.
      simp [Tm.subst, hki, if_neg (show ¬ i = j + 1 by omega), if_neg (show ¬ i > j + 1 by omega),
        hs1.subst j s2]
    rcases Nat.lt_trichotomy k (j + 1) with hkj | hkj | hkj
    · -- i < k < j + 1, i.e. i < k ≤ j.
      simp [Tm.subst, if_neg (show ¬ k = j + 1 by omega), if_neg (show ¬ k > j + 1 by omega),
        if_neg (show ¬ k = i by omega), if_pos (show k > i by omega),
        if_neg (show ¬ k - 1 = j by omega), if_neg (show ¬ k - 1 > j by omega)]
    · -- k = j + 1: the LHS lands directly on `s2`; the RHS's `subst i s1` first knocks `var (j+1)`
      -- down to `var j` (since `j + 1 > i`), which `subst j s2` then hits, landing on `s2` too.
      simp [Tm.subst, hkj, if_neg (show ¬ j + 1 = i by omega), if_pos (show j + 1 > i by omega),
        hs2.subst i s1]
    · -- k > j + 1 ≥ i + 1, i.e. k > j + 1 > i.
      simp [Tm.subst, if_neg (show ¬ k = j + 1 by omega), if_pos (show k > j + 1 by omega),
        if_neg (show ¬ k = i by omega), if_pos (show k > i by omega),
        if_neg (show ¬ k - 1 = j by omega), if_pos (show k - 1 > j by omega),
        if_neg (show ¬ k - 1 = i by omega), if_pos (show k - 1 > i by omega)]
  | lam body ih =>
    intro i j hij s1 s2 hs1 hs2
    simp only [Tm.subst, hs1.shift, hs2.shift]
    congr 1
    exact ih (by omega) hs1 hs2
  | app f a ihf iha =>
    intro i j hij s1 s2 hs1 hs2
    simp only [Tm.subst]; rw [ihf hij hs1 hs2, iha hij hs1 hs2]
  | tt => intros; rfl
  | ff => intros; rfl
  | ite c t e ihc iht ihe =>
    intro i j hij s1 s2 hs1 hs2
    simp only [Tm.subst]; rw [ihc hij hs1 hs2, iht hij hs1 hs2, ihe hij hs1 hs2]
  | iabs body ih =>
    intro i j hij s1 s2 hs1 hs2
    simp only [Tm.subst]; congr 1; exact ih hij hs1 hs2
  | transp A base ih =>
    intro i j hij s1 s2 hs1 hs2
    simp only [Tm.subst]; congr 1; exact ih hij hs1 hs2
  | hcomp A phi tube base ihtube ihbase =>
    intro i j hij s1 s2 hs1 hs2
    simp only [Tm.subst]; rw [ihtube hij hs1 hs2, ihbase hij hs1 hs2]

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §1. `Typed`: `HasType` with every grade/usage/dimension index erased.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- `HasType` stripped down to plain simple types: no ambient demand, no usage vector, no dimension
    count — just "`e` has type `A` in context `Γ`" for this fragment's `Bool`/`Π`/Kan-former shapes.
    `lam`'s binder grade `ρ` is carried only because `Ty.arr` itself is indexed by one (it plays no
    typing role here, unlike `HasType.lam`'s `hle : δ ≤ ρ` side-condition, which this judgement has
    no usage vector to state). See the module doc for why this — not a wrapper existentially
    quantifying `HasType`'s own `σ`/`φ` — is the right grade-free relation: `HasType.lam`'s `δ ≤ ρ`
    bound can *shrink* under grade change but never grow back, so no single fixed grade (e.g. `ω`)
    embeds every `HasType`-derivable term uniformly; erasing the bookkeeping *syntactically*
    (this inductive) rather than *semantically* (an existential over `HasType`) sidesteps that
    entirely, at the cost of `Typed` being a strictly bigger relation than `HasType`'s image — which
    is exactly what we want, since a strong-normalization proof for the bigger, easier-to-reduce-on
    class immediately specializes to the smaller graded one. -/
inductive Typed : List Ty → Tm → Ty → Prop where
  | var {Γ : List Ty} {i : Nat} {A : Ty} (h : Γ[i]? = some A) : Typed Γ (.var i) A
  | lam {Γ : List Ty} {body : Tm} {A B : Ty} {ρ : Grade} (hbody : Typed (A :: Γ) body B) :
      Typed Γ (.lam body) (.arr ρ A B)
  | app {Γ : List Ty} {f a : Tm} {A B : Ty} {ρ : Grade} (hf : Typed Γ f (.arr ρ A B))
      (ha : Typed Γ a A) : Typed Γ (.app f a) B
  | tt {Γ : List Ty} : Typed Γ .tt .bool
  | ff {Γ : List Ty} : Typed Γ .ff .bool
  | ite {Γ : List Ty} {c t e : Tm} {A : Ty} (hc : Typed Γ c .bool) (ht : Typed Γ t A)
      (he : Typed Γ e A) : Typed Γ (.ite c t e) A
  | iabs {Γ : List Ty} {body : Tm} {A : Ty} (hbody : Typed Γ body A) : Typed Γ (.iabs body) A
  | transp {Γ : List Ty} {A : Ty} {base : Tm} (hbase : Typed Γ base A) :
      Typed Γ (.transp A base) A
  | hcomp {Γ : List Ty} {A : Ty} {phi : Bool} {tube base : Tm} (htube : Typed Γ tube A)
      (hbase : Typed Γ base A) : Typed Γ (.hcomp A phi tube base) A

namespace Typed

/-- **Erasure**: every `HasType`-derivable term is `Typed` (drop `σ`/`φ`/`d`, keep the binder's
    declared grade `ρ` as `Ty.arr`'s own index). The one entry point the rest of this file needs
    from the graded fragment into the grade-free one. -/
theorem of_has_type {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) : Typed Γ e A := by
  induction h with
  | var hlk => exact Typed.var hlk
  | lam _ _ ihbody => exact Typed.lam ihbody
  | app _ _ ihf iha => exact Typed.app ihf iha
  | tt => exact Typed.tt
  | ff => exact Typed.ff
  | ite _ _ _ ihc iht ihe => exact Typed.ite ihc iht ihe
  | iabs _ ihbody => exact Typed.iabs ihbody
  | transp _ ihbase => exact Typed.transp ihbase
  | hcomp _ _ ihtube ihbase => exact Typed.hcomp ihtube ihbase

/-- **Weakening**, `Weakening.lean`'s `weaken` with the usage bookkeeping dropped. -/
theorem weaken {Γ : List Ty} {e : Tm} {A : Ty} (h : Typed Γ e A) :
    ∀ (c : Nat) (X : Ty), Typed (insertTy Γ c X) (Tm.shiftAbove c e) A := by
  induction h with
  | @var Γ i A hlk =>
    intro c X
    rcases Nat.lt_or_ge i c with hic | hic
    · have hlen : i < Γ.length := lookup_lt hlk
      simp only [Tm.shiftAbove, if_pos hic]
      exact Typed.var ((insertTy_get_lt hic hlen).trans hlk)
    · simp only [Tm.shiftAbove, if_neg (Nat.not_lt.mpr hic)]
      exact Typed.var ((insertTy_get_ge hic).trans hlk)
  | lam _ ihbody => intro c X; exact Typed.lam (ihbody (c + 1) X)
  | app _ _ ihf iha => intro c X; exact Typed.app (ihf c X) (iha c X)
  | tt => intro c X; exact Typed.tt
  | ff => intro c X; exact Typed.ff
  | ite _ _ _ ihc iht ihe => intro c X; exact Typed.ite (ihc c X) (iht c X) (ihe c X)
  | iabs _ ihbody => intro c X; exact Typed.iabs (ihbody c X)
  | transp _ ihbase => intro c X; exact Typed.transp (ihbase c X)
  | hcomp _ _ ihtube ihbase => intro c X; exact Typed.hcomp (ihtube c X) (ihbase c X)

/-- The workhorse form of `Typed`'s substitution lemma — `Substitution.lean`'s `subst_lemma_aux`
    with every usage-bound computation dropped, leaving only the context-index bookkeeping
    (`insertTy_get_lt`/`_eq`/`_ge`) `HasType`'s own proof needed anyway. -/
theorem subst_lemma_aux {A' : Ty} {Γ0 : List Ty} {e : Tm} {B : Ty} (h : Typed Γ0 e B) :
    ∀ {k : Nat} {Γ : List Ty}, Γ0 = insertTy Γ k A' → k ≤ Γ.length →
    ∀ {a : Tm}, Typed Γ a A' → Typed Γ (Tm.subst k a e) B := by
  induction h with
  | @var Γ0 i A hlk =>
    intro k Γ heq hk a ha
    subst heq
    rcases Nat.lt_trichotomy i k with hik | hik | hik
    · have hiG : i < Γ.length := by
        have hb := lookup_lt hlk
        rw [insertTy_length] at hb
        omega
      have hlkΓ : Γ[i]? = some A := by rw [← insertTy_get_lt hik hiG]; exact hlk
      have hsub : Tm.subst k a (Tm.var i) = Tm.var i := by
        simp only [Tm.subst]
        rw [if_neg (by omega : ¬ i = k), if_neg (by omega : ¬ i > k)]
      rw [hsub]; exact Typed.var hlkΓ
    · have hAeq : A = A' := by
        have h1 := insertTy_get_eq (Γ := Γ) (c := k) (X := A') hk
        rw [hik] at hlk; rw [hlk] at h1
        exact Option.some.inj h1
      have hsub : Tm.subst k a (Tm.var i) = a := by simp only [Tm.subst]; rw [if_pos hik]
      rw [hsub, hAeq]; exact ha
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hge : k ≤ i' := by omega
      have hlkΓ : Γ[i']? = some A := by rw [← insertTy_get_ge hge]; exact hlk
      have hsub : Tm.subst k a (Tm.var (i' + 1)) = Tm.var i' := by
        have h1 : ¬ (i' + 1 = k) := by omega
        have h2 : i' + 1 > k := by omega
        simp [Tm.subst, h1, h2]
      rw [hsub]; exact Typed.var hlkΓ
  | @lam Γ0 body A B ρ hbody ihbody =>
    intro k Γ heq hk a ha
    subst heq
    have heq2 : A :: insertTy Γ k A' = insertTy (A :: Γ) (k + 1) A' := rfl
    rw [heq2] at hbody ihbody
    have ha' : Typed (A :: Γ) (Tm.shiftAbove 0 a) A' := by
      have hw := ha.weaken 0 A
      rwa [insertTy_zero] at hw
    exact Typed.lam (ihbody rfl (by simp only [List.length_cons]; omega) ha')
  | app _ _ ihf iha0 =>
    intro k Γ heq hk a ha
    subst heq
    exact Typed.app (ihf rfl hk ha) (iha0 rfl hk ha)
  | tt => intro k Γ heq hk a ha; subst heq; exact Typed.tt
  | ff => intro k Γ heq hk a ha; subst heq; exact Typed.ff
  | ite _ _ _ ihc iht ihe =>
    intro k Γ heq hk a ha
    subst heq
    exact Typed.ite (ihc rfl hk ha) (iht rfl hk ha) (ihe rfl hk ha)
  | iabs _ ihbody =>
    intro k Γ heq hk a ha
    subst heq
    exact Typed.iabs (ihbody rfl hk ha)
  | transp _ ihbase =>
    intro k Γ heq hk a ha
    subst heq
    exact Typed.transp (ihbase rfl hk ha)
  | hcomp _ _ ihtube ihbase =>
    intro k Γ heq hk a ha
    subst heq
    exact Typed.hcomp (ihtube rfl hk ha) (ihbase rfl hk ha)

/-- The public substitution lemma: plugging a well-typed `a` into a well-typed `e` at exactly the
    slot `a`'s type matches preserves `e`'s type. -/
theorem subst {Γ : List Ty} {a : Tm} {A' : Ty} (ha : Typed Γ a A') {k : Nat} {e : Tm} {B : Ty}
    (h : Typed (insertTy Γ k A') e B) (hk : k ≤ Γ.length) : Typed Γ (Tm.subst k a e) B :=
  subst_lemma_aux h rfl hk ha

/-- Specialization of `subst` to slot `0` — the one `Step.beta` actually performs. -/
theorem subst0 {Γ : List Ty} {a body : Tm} {A B : Ty} (ha : Typed Γ a A)
    (hbody : Typed (A :: Γ) body B) : Typed Γ (Tm.subst0 a body) B := by
  have h := subst (k := 0) ha (by rwa [insertTy_zero]) (Nat.zero_le _)
  exact h

/-- **Progress**, ungraded: a closed, `Typed` term is either a value or can step. Verbatim
    `Progress.lean`'s `progress`, minus the grade/usage indices. -/
theorem progress {Γ : List Ty} {e : Tm} {A : Ty} (h : Typed Γ e A) :
    Γ = [] → Value e ∨ ∃ e', Step e e' := by
  induction h with
  | var hlk => intro hΓ; subst hΓ; simp at hlk
  | lam _ _ => intro _; exact Or.inl .lam
  | app hf ha ihf iha =>
    intro hΓ
    rcases ihf hΓ with hf_val | ⟨f', hf'⟩
    · rcases iha hΓ with ha_val | ⟨a', ha'⟩
      · cases hf_val with
        | lam => exact Or.inr ⟨_, .beta ha_val⟩
        | tt => cases hf
        | ff => cases hf
      · exact Or.inr ⟨_, .app2 hf_val ha'⟩
    · exact Or.inr ⟨_, .app1 hf'⟩
  | tt => intro _; exact Or.inl .tt
  | ff => intro _; exact Or.inl .ff
  | ite hc _ _ ihc _ _ =>
    intro hΓ
    rcases ihc hΓ with hc_val | ⟨c', hc'⟩
    · cases hc_val with
      | tt => exact Or.inr ⟨_, .ite_tt⟩
      | ff => exact Or.inr ⟨_, .ite_ff⟩
      | lam => cases hc
    · exact Or.inr ⟨_, .ite_cond hc'⟩
  | iabs _ _ => intro _; exact Or.inr ⟨_, .iabs_elim⟩
  | transp _ ihbase =>
    intro hΓ
    rcases ihbase hΓ with hb_val | ⟨b', hb'⟩
    · exact Or.inr ⟨_, .transp_val hb_val⟩
    · exact Or.inr ⟨_, .transp_base hb'⟩
  | @hcomp Γ0 A phi tube base htube hbase ihtube ihbase =>
    intro _
    cases phi with
    | true => exact Or.inr ⟨_, .hcomp_true⟩
    | false => exact Or.inr ⟨_, .hcomp_false⟩

/-- **Preservation**, ungraded: stepping never changes a `Typed` term's type. Verbatim
    `Progress.lean`'s `preservation`, with the `beta` case now discharged by `Typed.subst0`
    directly — no `demand_le_scale`/`ambient_zero_usage` side-condition to satisfy, since there is
    no usage vector to bound. -/
theorem preservation {Γ : List Ty} {e e' : Tm} {A : Ty} (h : Typed Γ e A) (hstep : Step e e') :
    Typed Γ e' A := by
  induction hstep generalizing A with
  | app1 _ ih =>
    cases h with
    | app hf0 ha0 => exact Typed.app (ih hf0) ha0
  | app2 _ _ ih =>
    cases h with
    | app hf0 ha0 => exact Typed.app hf0 (ih ha0)
  | @beta body a haval =>
    cases h with
    | app hf0 ha0 =>
      cases hf0 with
      | lam hbody => exact Typed.subst0 ha0 hbody
  | ite_cond _ ih =>
    cases h with
    | ite hc0 ht0 he0 => exact Typed.ite (ih hc0) ht0 he0
  | ite_tt => cases h with | ite _ ht0 _ => exact ht0
  | ite_ff => cases h with | ite _ _ he0 => exact he0
  | transp_base _ ih =>
    cases h with
    | transp hbase0 => exact Typed.transp (ih hbase0)
  | transp_val _ => cases h with | transp hbase0 => exact hbase0
  | hcomp_true => cases h with | hcomp htube0 _ => exact htube0
  | hcomp_false => cases h with | hcomp _ hbase0 => exact hbase0
  | iabs_elim => cases h with | iabs hbody0 => exact hbody0

end Typed

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §2. `Step` determinism.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- No term is both a `Value` and takes a `Step` — `Value`/`Step`'s constructors are keyed on
    disjoint head shapes (`lam`/`tt`/`ff` vs. everything `Step` can fire on), so this is immediate
    case analysis, but it's exactly the fact `step_deterministic`'s `app`/`ite`/`transp` congruence
    cases need to rule out "both a congruence step *and* the value-headed rule fired." -/
theorem Value.not_step {e e' : Tm} (hv : Value e) (hs : Step e e') : False := by
  cases hv <;> cases hs

/-- **`Step` is deterministic**: a term steps to at most one successor. Proved by induction on the
    first step, inverting the second; every "both sides fired a rule" mismatch is ruled out by
    `Value.not_step` (a congruence-position redex can't simultaneously be the value the sibling
    rule needed), and every matching pair of rules concludes by the corresponding congruence
    sub-case's induction hypothesis or is immediate. -/
theorem step_deterministic {e e1 e2 : Tm} (h1 : Step e e1) (h2 : Step e e2) : e1 = e2 := by
  induction h1 generalizing e2 with
  | app1 h1' ih =>
    cases h2 with
    | app1 h2' => rw [ih h2']
    | app2 hf h2' => exact absurd h1' (fun h => hf.not_step h)
    | beta ha => cases h1'
  | app2 hf1 h1' ih =>
    cases h2 with
    | app1 h2' => exact absurd h2' (fun h => hf1.not_step h)
    | app2 _ h2' => rw [ih h2']
    | beta ha => exact absurd h1' (fun h => ha.not_step h)
  | beta ha1 =>
    cases h2 with
    | app1 h2' => cases h2'
    | app2 _ h2' => exact absurd h2' (fun h => ha1.not_step h)
    | beta _ => rfl
  | ite_cond h1' ih =>
    cases h2 with
    | ite_cond h2' => rw [ih h2']
    | ite_tt => cases h1'
    | ite_ff => cases h1'
  | ite_tt =>
    cases h2 with
    | ite_cond h2' => cases h2'
    | ite_tt => rfl
  | ite_ff =>
    cases h2 with
    | ite_cond h2' => cases h2'
    | ite_ff => rfl
  | transp_base h1' ih =>
    cases h2 with
    | transp_base h2' => rw [ih h2']
    | transp_val hv => exact absurd h1' (fun h => hv.not_step h)
  | transp_val hv1 =>
    cases h2 with
    | transp_base h2' => exact absurd h2' (fun h => hv1.not_step h)
    | transp_val _ => rfl
  | hcomp_true => cases h2 with | hcomp_true => rfl
  | hcomp_false => cases h2 with | hcomp_false => rfl
  | iabs_elim => cases h2 with | iabs_elim => rfl

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §3. Strong normalization: the accessibility-style definition and its basic closure facts.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- `e` is strongly normalizing: every step out of `e` lands somewhere itself strongly normalizing.
    An inductive (not merely universally-quantified-over-sequences) definition — Lean's `Acc` on the
    converse of `Step` in disguise — so that `SN.rec`/well-founded induction is directly available,
    exactly what the `Reducible_lam` beta case's induction on the argument's normalization needs. -/
inductive SN : Tm → Prop where
  | intro {e : Tm} (h : ∀ {e'}, Step e e' → SN e') : SN e

/-- Unpacking `SN`'s single field by name, for readability at call sites. -/
theorem SN.step {e e' : Tm} (h : SN e) (hstep : Step e e') : SN e' := by
  cases h with
  | intro h => exact h hstep

/-- Every value is (trivially) strongly normalizing: it has no step to even consider. -/
theorem Value.sn {e : Tm} (hv : Value e) : SN e :=
  ⟨fun hstep => absurd hstep (fun h => hv.not_step h)⟩

/-- **Backward closure (CR2 direction, "expansion")**: if `e` steps to a strongly-normalizing `e'`,
    and every *other* possible step from `e` is also to something strongly normalizing (vacuous
    here since `Step` targets are unique — `step_deterministic` — but stated in the general shape
    `Reducible`'s own `app`/`ite`/Kan cases below actually consume), `e` itself is SN. Specialized
    immediately to the deterministic case: since `e`'s only step is to `e'` (`step_deterministic`),
    `SN e'` alone suffices. -/
theorem SN.backward {e e' : Tm} (hstep : Step e e') (h : SN e') : SN e := by
  refine ⟨fun {e''} hstep' => ?_⟩
  rw [step_deterministic hstep' hstep]
  exact h

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §4. `closeAt`: closing an open term against a list of (closed) values, front-to-back.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- Close `e` against `vs = [v0, v1, ...]` by substituting `v0` for variable `k`, then `v1` for
    (the new) variable `k`, and so on — i.e. `vs`'s *first* element always lands in the *same* slot
    `k` the next one will, because each substitution already removed and reindexed everything past
    it. This is what makes `closeAt`'s `lam` case (`closeAt_lam` below) commute with the binder using
    only closedness of `vs`'s elements, no index arithmetic on `vs` itself: crossing one `lam` bumps
    every *remaining* substitution's target slot from `k` to `k + 1` uniformly, since they were all
    going to hit slot `k` next regardless of which one goes first. -/
def closeAt (k : Nat) : List Tm → Tm → Tm
  | [], e => e
  | v :: vs, e => closeAt k vs (Tm.subst k v e)

/-- Every element of `vs` is closed — the hypothesis `closeAt_lam`/`closeAt_subst0` need to justify
    that crossing a binder only bumps *where* each substitution lands, never requiring it to also
    shift the substituted *value* (`ClosedTm.shift` erases that shift outright). -/
def AllClosed (vs : List Tm) : Prop := ∀ v ∈ vs, ClosedTm v

theorem AllClosed.tail {v : Tm} {vs : List Tm} (h : AllClosed (v :: vs)) : AllClosed vs :=
  fun v' hv' => h v' (List.mem_cons_of_mem _ hv')

theorem AllClosed.head {v : Tm} {vs : List Tm} (h : AllClosed (v :: vs)) : ClosedTm v :=
  h v List.mem_cons_self

/-- Closing a term that has no free variables at or above `k` is a no-op — `vs`'s substitutions
    never find anything of theirs to touch. (No closedness of `vs` itself needed: an inert
    substitution is inert regardless of what's being substituted.) -/
theorem closeAt_closed {k : Nat} : ∀ (vs : List Tm) {t : Tm}, NoFreeAbove t k → closeAt k vs t = t
  | [], _, _ => rfl
  | v :: vs, t, ht => by
    show closeAt k vs (Tm.subst k v t) = t
    rw [NoFreeAbove_subst ht (Nat.le_refl k)]
    exact closeAt_closed vs ht

/-- `closeAt` commutes with every non-binding, non-`var` constructor exactly because `Tm.subst`
    itself does (no shift, no reindexing) — proved once per shape by induction on `vs`, reusing
    `Tm.subst`'s own equation for that shape at each step. -/
theorem closeAt_app (k : Nat) (vs : List Tm) (f a : Tm) :
    closeAt k vs (.app f a) = .app (closeAt k vs f) (closeAt k vs a) := by
  induction vs generalizing f a with
  | nil => rfl
  | cons v vs ih =>
    show closeAt k vs (Tm.subst k v (.app f a)) = _
    simp only [Tm.subst]
    exact ih _ _

theorem closeAt_tt (k : Nat) (vs : List Tm) : closeAt k vs .tt = .tt := by
  induction vs with
  | nil => rfl
  | cons v vs ih => show closeAt k vs (Tm.subst k v .tt) = .tt; simp only [Tm.subst]; exact ih

theorem closeAt_ff (k : Nat) (vs : List Tm) : closeAt k vs .ff = .ff := by
  induction vs with
  | nil => rfl
  | cons v vs ih => show closeAt k vs (Tm.subst k v .ff) = .ff; simp only [Tm.subst]; exact ih

theorem closeAt_ite (k : Nat) (vs : List Tm) (c t e : Tm) :
    closeAt k vs (.ite c t e) = .ite (closeAt k vs c) (closeAt k vs t) (closeAt k vs e) := by
  induction vs generalizing c t e with
  | nil => rfl
  | cons v vs ih =>
    show closeAt k vs (Tm.subst k v (.ite c t e)) = _
    simp only [Tm.subst]
    exact ih _ _ _

theorem closeAt_iabs (k : Nat) (vs : List Tm) (body : Tm) :
    closeAt k vs (.iabs body) = .iabs (closeAt k vs body) := by
  induction vs generalizing body with
  | nil => rfl
  | cons v vs ih =>
    show closeAt k vs (Tm.subst k v (.iabs body)) = _
    simp only [Tm.subst]
    exact ih _

theorem closeAt_transp (k : Nat) (vs : List Tm) (A : Ty) (base : Tm) :
    closeAt k vs (.transp A base) = .transp A (closeAt k vs base) := by
  induction vs generalizing base with
  | nil => rfl
  | cons v vs ih =>
    show closeAt k vs (Tm.subst k v (.transp A base)) = _
    simp only [Tm.subst]
    exact ih _

theorem closeAt_hcomp (k : Nat) (vs : List Tm) (A : Ty) (phi : Bool) (tube base : Tm) :
    closeAt k vs (.hcomp A phi tube base)
      = .hcomp A phi (closeAt k vs tube) (closeAt k vs base) := by
  induction vs generalizing tube base with
  | nil => rfl
  | cons v vs ih =>
    show closeAt k vs (Tm.subst k v (.hcomp A phi tube base)) = _
    simp only [Tm.subst]
    exact ih _ _

/-- **The `lam`/binder-crossing case.** Given `vs` all closed, closing `.lam body` at slot `k`
    lands every substitution one slot deeper inside `body` — `k + 1`, not `k` — matching
    `Tm.subst`'s own `lam` case (which bumps its position for exactly this reason), with the
    would-be re-shift of each substituted value erased outright by its closedness. -/
theorem closeAt_lam {k : Nat} : ∀ (vs : List Tm), AllClosed vs → ∀ (body : Tm),
    closeAt k vs (.lam body) = .lam (closeAt (k + 1) vs body)
  | [], _, _ => rfl
  | v :: vs, hcl, body => by
    show closeAt k vs (Tm.subst k v (.lam body)) = .lam (closeAt (k + 1) (v :: vs) body)
    simp only [Tm.subst, hcl.head.shift]
    exact closeAt_lam vs hcl.tail (Tm.subst (k + 1) v body)

/-- **The beta/environment-commutation lemma.** Substituting a closed `w` for the fresh slot `0`
    *after* closing the rest of `body` at slot `1` agrees with closing at slot `0` *after*
    substituting `w` first — i.e. extending the closing environment by one (closed, reducible)
    value up front and re-closing from scratch is the same as closing the tail environment against
    the already-`w`-substituted body. This is exactly `subst_comm` (§0), applied once per
    environment entry via induction on `vs`, that lets `Reducible_lam`'s β case identify the
    beta-reduct of a closed `.lam` with the fundamental lemma's *next* recursive instance (`w ::
    vs`) rather than a bespoke substitution fact. -/
theorem closeAt_subst0 {w : Tm} (hw : ClosedTm w) : ∀ (vs : List Tm), AllClosed vs → ∀ (body : Tm),
    Tm.subst 0 w (closeAt 1 vs body) = closeAt 0 vs (Tm.subst 0 w body)
  | [], _, _ => rfl
  | v :: vs, hcl, body => by
    show Tm.subst 0 w (closeAt 1 vs (Tm.subst 1 v body))
      = closeAt 0 vs (Tm.subst 0 v (Tm.subst 0 w body))
    rw [closeAt_subst0 hw vs hcl.tail (Tm.subst 1 v body),
      subst_comm (Nat.le_refl 0) hw hcl.head]

/-- A term well-typed in the empty context has no free variables — the fact tying `Typed`'s notion
    of closedness back to the syntactic one (`ClosedTm`/`NoFreeAbove`) `closeAt`'s lemmas need.
    Proved in the more general form (bound `Γ.length`, not just the `Γ = []` specialization) since
    the induction's `lam` case needs exactly that one-deeper instance. -/
theorem Typed.no_free_above {Γ : List Ty} {e : Tm} {A : Ty} (h : Typed Γ e A) :
    NoFreeAbove e Γ.length := by
  induction h with
  | var hlk => exact lookup_lt hlk
  | lam _ ihbody => exact ihbody
  | app _ _ ihf iha => exact ⟨ihf, iha⟩
  | tt => trivial
  | ff => trivial
  | ite _ _ _ ihc iht ihe => exact ⟨ihc, iht, ihe⟩
  | iabs _ ihbody => exact ihbody
  | transp _ ihbase => exact ihbase
  | hcomp _ _ ihtube ihbase => exact ⟨ihtube, ihbase⟩

theorem Typed.closed {e : Tm} {A : Ty} (h : Typed [] e A) : ClosedTm e := h.no_free_above

/-- A closed term retypes in *any* context — weakening specialized to the case where the term
    itself has nothing to shift (`ClosedTm.shift`), so only the context padding (`insertTy_zero`)
    is left to iterate, once per fresh entry, front-to-back. -/
theorem Typed.weaken_closed {e : Tm} {A : Ty} (h : Typed [] e A) (hce : ClosedTm e) :
    ∀ Γ : List Ty, Typed Γ e A
  | [] => h
  | X :: Γ => by
    have hw := (Typed.weaken_closed h hce Γ).weaken 0 X
    rwa [insertTy_zero, hce.shift 0] at hw

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §5. `Reducible`: Tait-style reducibility candidates indexed by `Ty`.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- **The reducibility candidate**, by structural recursion on `Ty` (so the `Pi`-case's
    well-foundedness is literally Lean's own structural recursion on `B`, a syntactic subterm of
    `arr ρ A B` — no separate well-foundedness argument to construct). At `Bool`, reducible is just
    "closed, well-typed, and `SN`" (there is no elimination form to close under besides `ite`, and
    that's handled at the *use* site, `Reducible_ite`, not baked into the definition). At `Pi`,
    reducible additionally demands that applying to *any* reducible argument stays reducible at the
    codomain — the standard Tait-Girard closure condition. `SN e` is bundled directly at *both*
    types (not just derived later for `Pi` from an inhabitant of `A`) to avoid needing a separate
    "every type is inhabited" side lemma; `Typed [] e A` is bundled so `Reducible_lam`'s β case can
    invoke `Typed.progress` on the applied argument without threading typing separately alongside
    reducibility everywhere. -/
def Reducible : Ty → Tm → Prop
  | .bool, e => Typed [] e .bool ∧ SN e
  | .arr ρ A B, e => Typed [] e (.arr ρ A B) ∧ SN e ∧ ∀ {w : Tm}, Reducible A w → Reducible B (.app e w)

theorem Reducible.typed {A : Ty} {e : Tm} (h : Reducible A e) : Typed [] e A := by
  cases A with
  | bool => exact h.1
  | arr ρ A B => exact h.1

/-- **CR1**: every reducible term is strongly normalizing. -/
theorem Reducible.sn {A : Ty} {e : Tm} (h : Reducible A e) : SN e := by
  cases A with
  | bool => exact h.2
  | arr ρ A B => exact h.2.1

/-- **CR2, forward direction**: reducibility is preserved by stepping. Paired with `.backward`
    below (the βη-expansion direction proper) these give the two structural closure properties the
    whole fundamental lemma runs on; `step_deterministic` is what lets `Reducible_transp`/
    `Reducible_ite`'s SN-inductions re-derive `Reducible` at each successive reduct via this lemma
    rather than needing a fresh argument every time. -/
theorem Reducible.step {A : Ty} {e e' : Tm} (h : Reducible A e) (hstep : Step e e') :
    Reducible A e' := by
  induction A generalizing e e' with
  | bool => exact ⟨Typed.preservation h.1 hstep, h.2.step hstep⟩
  | arr ρ A B ihA ihB =>
    refine ⟨Typed.preservation h.1 hstep, h.2.1.step hstep, ?_⟩
    intro w hw
    exact ihB (h.2.2 hw) (.app1 hstep)

/-- **CR3 / backward closure ("expansion")**: if `e` steps to a reducible `e'`, and `e` is itself
    well-typed at the same type, then `e` is reducible too. This is the direction that actually
    does work in a call-by-value, non-confluent-looking setting: since `Step` is deterministic
    (`step_deterministic`), `e`'s *only* successor is `e'`, so nothing else needs separately
    checking — unlike the textbook CR3 for a *reduction* relation with potentially many one-step
    successors, no least-upper-bound argument over siblings is needed here. -/
theorem Reducible.backward {A : Ty} {e e' : Tm} (hstep : Step e e') (hr : Reducible A e')
    (hty : Typed [] e A) : Reducible A e := by
  induction A generalizing e e' with
  | bool => exact ⟨hty, hr.2.backward hstep⟩
  | arr ρ A B ihA ihB =>
    refine ⟨hty, hr.2.1.backward hstep, ?_⟩
    intro w hw
    exact ihB (.app1 hstep) (hr.2.2 hw) (Typed.app hty hw.typed)

/-- **`ite`'s reducibility-preservation case**: an SN-induction on the scrutinee `c`, congruence-
    stepping it down to a canonical `tt`/`ff` (`Typed.progress`) and then discharging via whichever
    branch is already known reducible, backward-closing across every intermediate `ite_cond` step.
    The `lam`-headed-`Bool` case is ruled out the same way `Progress.lean`'s own `ite` case rules it
    out: `Typed [] (.lam _) .bool` has no derivation (`Ty.bool ≠ Ty.arr _ _ _`). -/
theorem Reducible_ite {c t e : Tm} {A : Ty} (hc : SN c) :
    Typed [] c .bool → Reducible A t → Reducible A e → Reducible A (.ite c t e) := by
  induction hc with
  | intro _ ih =>
    intro hct ht he
    rcases hct.progress rfl with hv | ⟨c', hc'⟩
    · cases hv with
      | tt => exact Reducible.backward .ite_tt ht (Typed.ite hct ht.typed he.typed)
      | ff => exact Reducible.backward .ite_ff he (Typed.ite hct ht.typed he.typed)
      | lam => cases hct
    · exact Reducible.backward (.ite_cond hc') (ih hc' (Typed.preservation hct hc') ht he)
        (Typed.ite hct ht.typed he.typed)

/-- **`transp`'s reducibility-preservation case**: an SN-induction on the base, mirroring
    `Progress.lean`'s `transp_val`/`transp_base` split exactly — `transp`'s conclusion type is
    *definitionally* its base's own type (`Calculus.lean`'s `HasType.transp`/`Typed.transp`), so the
    value case needs no case analysis at all, just `Reducible.backward` against the base's own
    (already-established) reducibility. -/
theorem Reducible_transp {A : Ty} {base : Tm} (hsn : SN base) :
    Reducible A base → Reducible A (.transp A base) := by
  induction hsn with
  | intro _ ih =>
    intro hr
    rcases hr.typed.progress rfl with hv | ⟨base', hstep'⟩
    · exact Reducible.backward (.transp_val hv) hr (Typed.transp hr.typed)
    · exact Reducible.backward (.transp_base hstep') (ih hstep' (hr.step hstep'))
        (Typed.transp hr.typed)

/-- **`hcomp`'s reducibility-preservation case**: no induction needed at all — `hcomp` reduces to
    exactly one of its two (already-typed, unevaluated) branches *unconditionally*, per `phi`, per
    `Progress.lean`'s `hcomp_true`/`hcomp_false` (mechanizing §1.1(c): the cofibration is not
    consulted by typing and is not forced by evaluation either, beyond this immediate branch
    selection). -/
theorem Reducible_hcomp {A : Ty} {phi : Bool} {tube base : Tm} (htube : Reducible A tube)
    (hbase : Reducible A base) : Reducible A (.hcomp A phi tube base) := by
  cases phi with
  | true => exact Reducible.backward .hcomp_true htube (Typed.hcomp htube.typed hbase.typed)
  | false => exact Reducible.backward .hcomp_false hbase (Typed.hcomp htube.typed hbase.typed)

/-- **`iabs`'s reducibility-preservation case**: `iabs_elim` fires unconditionally too (opening a
    dimension binder is a pure runtime no-op — the module doc's "equally transparent to evaluation"
    gotcha fix), so this is `Reducible.backward` against the body's own reducibility, no induction. -/
theorem Reducible_iabs {A : Ty} {body : Tm} (hbody : Reducible A body) :
    Reducible A (.iabs body) :=
  Reducible.backward .iabs_elim hbody (Typed.iabs hbody.typed)

/-- The β case's inner SN-induction: run the argument `w` down to a value (`Typed.progress`), then
    fire the real `Step.beta`, backward-closing across every intermediate `app2` congruence step —
    exactly mirroring `Reducible_ite`'s shape, with `Value.lam` supplying `app2`'s "function side is
    already a value" side-condition for free. -/
theorem Reducible_app_lam_aux {A B : Ty} {bodyC : Tm} (hty : Typed [A] bodyC B)
    (hyp : ∀ {v : Tm}, Reducible A v → Reducible B (Tm.subst0 v bodyC)) {ρ : Grade} :
    ∀ {w : Tm}, SN w → Reducible A w → Reducible B (.app (.lam bodyC) w) := by
  intro w hsnw
  induction hsnw with
  | intro _ ih =>
    intro hw
    rcases hw.typed.progress rfl with hv | ⟨w', hw'⟩
    · exact Reducible.backward (.beta hv) (hyp hw) (Typed.app (Typed.lam (ρ := ρ) hty) hw.typed)
    · exact Reducible.backward (.app2 .lam hw') (ih hw' (hw.step hw'))
        (Typed.app (Typed.lam (ρ := ρ) hty) hw.typed)

/-- **`lam`'s reducibility-preservation case — the actual β case.** Given a closed body `bodyC`
    with exactly one free variable (slot `0`, the parameter) and the hypothesis that plugging in
    *any* reducible closed argument keeps the substituted body reducible, `.lam bodyC` is reducible
    at the arrow type: `SN` is immediate (`.lam` is already a value), and the application-closure
    condition is exactly `Reducible_app_lam_aux`. -/
theorem Reducible_lam {A B : Ty} {ρ : Grade} {bodyC : Tm} (hty : Typed [A] bodyC B)
    (hyp : ∀ {v : Tm}, Reducible A v → Reducible B (Tm.subst0 v bodyC)) :
    Reducible (.arr ρ A B) (.lam bodyC) :=
  ⟨Typed.lam hty, Value.sn .lam,
    fun hw => Reducible_app_lam_aux hty hyp (ρ := ρ) hw.sn hw⟩

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §6. `RedSubst`: a reducible closing environment, and the fundamental lemma.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- A closing environment `vs` every one of whose entries is reducible at the matching `Γ` slot,
    paired up exactly the way `closeAt`'s "always slot `0`, front-to-back" convention needs: `vs`'s
    head is reducible at `Γ`'s head, matching `closeAt`'s first substitution landing in slot `0`
    (`Γ`'s own head, per `Calculus.lean`'s `var`/`insertTy` convention that a fresh binder is always
    the *front* of the context). -/
inductive RedSubst : List Ty → List Tm → Prop where
  | nil : RedSubst [] []
  | cons {A : Ty} {Γ : List Ty} {v : Tm} {vs : List Tm} (hv : Reducible A v)
      (hrest : RedSubst Γ vs) : RedSubst (A :: Γ) (v :: vs)

theorem RedSubst.all_closed {Γ : List Ty} {vs : List Tm} (h : RedSubst Γ vs) : AllClosed vs := by
  induction h with
  | nil => intro v hv; simp at hv
  | cons hv _ ih =>
    intro v' hv'
    rcases List.mem_cons.mp hv' with heq | hmem
    · subst heq; exact hv.typed.closed
    · exact ih v' hmem

/-- Looking up a reducible slot in `Γ` finds a matching reducible value at the same index in `vs`
    — the fact `fundamental`'s `var` case needs to identify `closeAt 0 vs (.var i)` (via
    `closeAt0_var` below) with an already-known-reducible term. -/
theorem RedSubst.get {Γ : List Ty} {vs : List Tm} (h : RedSubst Γ vs) :
    ∀ {i : Nat} {A : Ty}, Γ[i]? = some A → ∃ v, vs[i]? = some v ∧ Reducible A v := by
  induction h with
  | nil => intro i A hlk; simp at hlk
  | @cons A' Γ' v' vs' hv hrest ih =>
    intro i A hlk
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hlk
      exact ⟨v', by simp, hlk ▸ hv⟩
    | succ i' =>
      have hlk' : Γ'[i']? = some A := by simpa using hlk
      obtain ⟨v, hv', hred⟩ := ih hlk'
      exact ⟨v, by simpa using hv', hred⟩

/-- Closing a body typed one binder deeper than `Γ` against a `Γ`-matching environment leaves
    exactly the fresh binder's slot open (`[A]`, not `[]`) — the fact `fundamental`'s `lam` case
    needs to type `bodyC` before invoking `Reducible_lam`. Mirrors `Typed.subst_lemma_aux`'s own
    `lam` case one level up: each environment entry substitutes at slot `1`, not `0`, since slot `0`
    is reserved for the not-yet-supplied parameter. -/
theorem closeAt1_typed {Γ : List Ty} {vs : List Tm} (hvs : RedSubst Γ vs) :
    ∀ {A B : Ty} {body : Tm}, Typed (A :: Γ) body B → Typed [A] (closeAt 1 vs body) B := by
  induction hvs with
  | nil => intro A B body hbody; exact hbody
  | @cons A' Γ' v vs' hv hrest ih =>
    intro A B body hbody
    have heq1 : insertTy (A :: Γ') 1 A' = A :: A' :: Γ' := by
      show A :: insertTy Γ' 0 A' = A :: A' :: Γ'
      rw [insertTy_zero]
    have hbody' : Typed (insertTy (A :: Γ') 1 A') body B := by rw [heq1]; exact hbody
    have hvΓ : Typed (A :: Γ') v A' := hv.typed.weaken_closed hv.typed.closed (A :: Γ')
    have hsub : Typed (A :: Γ') (Tm.subst 1 v body) B :=
      Typed.subst hvΓ hbody' (by simp only [List.length_cons]; omega)
    show Typed [A] (closeAt 1 vs' (Tm.subst 1 v body)) B
    exact ih hsub

/-- Closing `.var i` against `vs` reads off exactly the `i`-th entry, given every earlier entry
    (the ones `closeAt`'s substitution processes before reaching slot `i`) is closed — matching
    `closeAt`'s "always slot `0`" convention: substituting `vs`'s head either *is* the lookup
    (`i = 0`) or shifts every later index down by one, recursing into the tail with `i - 1`. -/
theorem closeAt0_var {vs : List Tm} (hcl : AllClosed vs) :
    ∀ {i : Nat} {v : Tm}, vs[i]? = some v → closeAt 0 vs (.var i) = v := by
  induction vs with
  | nil => intro i v h; simp at h
  | cons v0 vs' ih =>
    intro i v h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      show closeAt 0 vs' (Tm.subst 0 v0 (.var 0)) = v0
      simp only [Tm.subst]
      exact closeAt_closed vs' hcl.head
    | succ i' =>
      have h' : vs'[i']? = some v := by simpa using h
      show closeAt 0 vs' (Tm.subst 0 v0 (.var (i' + 1))) = v
      have hsub : Tm.subst 0 v0 (Tm.var (i' + 1)) = Tm.var i' := by simp [Tm.subst]
      rw [hsub]
      exact ih hcl.tail h'

/-- **The fundamental lemma of logical relations**, for this fragment: every `Typed`-well-typed
    term, closed against a matching reducible environment, is reducible at its own type. Proved by
    induction on the typing derivation, generalizing over the closing environment (`vs`/`RedSubst`)
    so the `lam` case's induction hypothesis is available at the *extended* environment
    (`w :: vs`, `RedSubst.cons`) it actually needs — the one place this proof genuinely recurses
    into an open subterm rather than a closed one. Every other case is `closeAt`'s matching
    homomorphism lemma (§4) composed with the corresponding `Reducible_*` closure lemma (§5). -/
theorem fundamental {Γ : List Ty} {e : Tm} {B : Ty} (h : Typed Γ e B) :
    ∀ {vs : List Tm}, RedSubst Γ vs → Reducible B (closeAt 0 vs e) := by
  induction h with
  | @var Γ i A hlk =>
    intro vs hvs
    obtain ⟨v, hget, hred⟩ := hvs.get hlk
    rwa [closeAt0_var hvs.all_closed hget]
  | @lam Γ body A B ρ hbody ihbody =>
    intro vs hvs
    rw [closeAt_lam vs hvs.all_closed]
    refine Reducible_lam (closeAt1_typed hvs hbody) ?_
    intro v hv
    have heq : Tm.subst0 v (closeAt 1 vs body) = closeAt 0 (v :: vs) body := by
      show Tm.subst 0 v (closeAt 1 vs body) = closeAt 0 (v :: vs) body
      rw [closeAt_subst0 hv.typed.closed vs hvs.all_closed]
      rfl
    rw [heq]
    exact ihbody (RedSubst.cons hv hvs)
  | app hf ha ihf iha =>
    intro vs hvs
    rw [closeAt_app 0 vs _ _]
    exact (ihf hvs).2.2 (iha hvs)
  | tt => intro vs _; rw [closeAt_tt]; exact ⟨Typed.tt, Value.sn .tt⟩
  | ff => intro vs _; rw [closeAt_ff]; exact ⟨Typed.ff, Value.sn .ff⟩
  | ite hc ht he ihc iht ihe =>
    intro vs hvs
    rw [closeAt_ite 0 vs _ _ _]
    exact Reducible_ite (ihc hvs).sn (ihc hvs).typed (iht hvs) (ihe hvs)
  | iabs hbody ihbody =>
    intro vs hvs
    rw [closeAt_iabs 0 vs _]
    exact Reducible_iabs (ihbody hvs)
  | transp hbase ihbase =>
    intro vs hvs
    rw [closeAt_transp 0 vs _ _]
    exact Reducible_transp (ihbase hvs).sn (ihbase hvs)
  | hcomp htube hbase ihtube ihbase =>
    intro vs hvs
    rw [closeAt_hcomp 0 vs _ _ _ _]
    exact Reducible_hcomp (ihtube hvs) (ihbase hvs)

-- ═══════════════════════════════════════════════════════════════════════════════════════════════
-- §7. The three go-bar theorems: `strong_normalization`, `step_deterministic` (§2), `canonicity`.
-- ═══════════════════════════════════════════════════════════════════════════════════════════════

/-- **Strong normalization**: every closed, well-typed term of the graded fragment (`HasType`, any
    ambient grade/dimension count) is strongly normalizing. The fundamental lemma applied to the
    *empty* closing environment (`RedSubst.nil`) — `closeAt 0 [] e` is `e` outright, so no further
    rewriting is even needed — composed with `Typed.of_has_type`'s erasure and `Reducible.sn`
    (CR1). -/
theorem strong_normalization {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType [] d e A σ φ) : SN e :=
  (fundamental (Typed.of_has_type h) RedSubst.nil).sn

/-- Reflexive-transitive closure of `Step`, for stating canonicity as "reduces to a canonical
    value" rather than the (equivalent, but less standard-looking) "is a value or steps to one,
    repeat." -/
inductive Steps : Tm → Tm → Prop where
  | refl {e : Tm} : Steps e e
  | cons {e e' e'' : Tm} (h1 : Step e e') (h2 : Steps e' e'') : Steps e e''

/-- **Canonicity**: every closed, well-typed `Bool` reduces, in zero or more steps, to `tt` or
    `ff`. The standard corollary of strong normalization + `Typed.progress` + `Typed.preservation`:
    induct along the (finite, by `strong_normalization`) reduction sequence, using `progress` at
    each stage to either land on a canonical value or take one more step and recurse. The `lam`
    case of `progress`'s `Value` split is ruled out exactly as in `Reducible_ite`: `Ty.bool` and
    `Ty.arr _ _ _` are distinct constructors, so `Typed [] (.lam _) .bool` has no derivation. -/
theorem canonicity {d : Nat} {e : Tm} {σ : Grade} {φ : Usage} (h : HasType [] d e .bool σ φ) :
    ∃ e', Steps e e' ∧ (e' = .tt ∨ e' = .ff) := by
  have hsn : SN e := strong_normalization h
  have hty : Typed [] e .bool := Typed.of_has_type h
  clear h
  induction hsn with
  | intro _ ih =>
    rcases hty.progress rfl with hv | ⟨e', hstep⟩
    · cases hv with
      | tt => exact ⟨.tt, .refl, Or.inl rfl⟩
      | ff => exact ⟨.ff, .refl, Or.inr rfl⟩
      | lam => cases hty
    · obtain ⟨e'', hsteps, hcanon⟩ := ih hstep (Typed.preservation hty hstep)
      exact ⟨e'', .cons hstep hsteps, hcanon⟩

/-- **The usage bound, iterated** (M-A.1's headline made multi-step): along ANY finite reduction
    sequence the usage vector is monotonically non-increasing — `preservation`'s single-step
    `Usage.Le` bound composed along `Steps` by `le_trans`. A program can never step its way into
    using a linear resource more than its original typing licensed, no matter how many steps it
    takes. -/
theorem preservation_steps {Γ : List Ty} {d : Nat} {e e' : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) (hsteps : Steps e e') :
    ∃ φ', HasType Γ d e' A σ φ' ∧ Usage.Le φ' φ := by
  induction hsteps generalizing φ with
  | refl => exact ⟨φ, h, Usage.le_refl φ⟩
  | cons h1 _ ih =>
    obtain ⟨φ1, hφ1, hb1⟩ := preservation h h1
    obtain ⟨φ2, hφ2, hb2⟩ := ih hφ1
    exact ⟨φ2, hφ2, Usage.le_trans hb2 hb1⟩

-- Sorry-freedom receipt for the iterated bound.
#print axioms preservation_steps

end BlightMeta
