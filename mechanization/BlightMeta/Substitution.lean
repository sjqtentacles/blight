/-
  The substitution lemma, generalized to substitute at an arbitrary depth `k` (so its own `lam`
  case — substituting one level further under a binder — is just the `k+1` instance, using
  `weaken 0` from `Weakening.lean` to re-shift the substituted term). This is the mechanized form
  of §1.2's "usage is preserved under reduction" sketch, made precise via `Usage.Le`: substituting
  a term `a` (checked at grade `π`) for a variable removed from slot `k` bounds the result's usage
  by the original usage with slot `k` dropped, *plus* a correction term `scale (φ.get k) φa` — the
  substituted term's own usage, scaled by exactly how much the removed variable was demanded. The
  correction term is unavoidable in general (substitution can only *increase* the demand on `a`'s
  free variables, not decrease it) but the `scale` factor is tight: `demote_scaled`
  (`Weakening.lean`) is exactly the fact that lets several occurrences' worth of demand recombine
  via `Usage.scale_add_grade` into a single scale by their *summed* grade, matching `φ.get k`.
-/

import BlightMeta.Weakening

namespace BlightMeta

/-- The workhorse form of the substitution lemma: `Γ0`, the context `e` is checked in, is kept as
    a bare variable (rather than immediately written as `insertTy Γ k A'`) so that plain
    `induction h` — with no `generalizing` gymnastics over a compound index expression — produces
    the right induction hypotheses; the `Γ0 = insertTy Γ k A'` identification is instead threaded
    through as an ordinary hypothesis and `subst`ed in per-case. Crucially, `a`/`π`/`φa`/`ha` are
    *inside* the per-`(k, Γ)` statement (quantified after `h`, not fixed alongside `A'`), so the
    `lam` case's induction hypothesis can be instantiated with a *freshly re-weakened* substituted
    term (`weaken ha 0 A`) when recursing one binder deeper — the same trick `weaken` itself
    doesn't need (it has no substituted term to keep in sync) but substitution does. -/
theorem subst_lemma_aux {A' : Ty} {Γ0 : List Ty} {d : Nat} {e : Tm} {B : Ty} {σ : Grade}
    {φ : Usage} (h : HasType Γ0 d e B σ φ) :
    ∀ {k : Nat} {Γ : List Ty}, Γ0 = insertTy Γ k A' → k ≤ Γ.length →
    ∀ {a : Tm} {π : Grade} {φa : Usage}, HasType Γ d a A' π φa → φ.get k ≤ π →
    ∃ φ', HasType Γ d (Tm.subst k a e) B σ φ' ∧
      Usage.Le (insertUsage φ' k) (Usage.add φ (Usage.scale (φ.get k) (insertUsage φa k))) := by
  induction h with
  | @var Γ0 d i A σ hlk =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    rw [insertTy_length] at hget ⊢
    rcases Nat.lt_trichotomy i k with hik | hik | hik
    · -- i < k: untouched by the substitution, and the slot lines up with `Γ` unchanged.
      have hiG : i < Γ.length := by omega
      have hlkΓ : Γ[i]? = some A := by rw [← insertTy_get_lt hik hiG]; exact hlk
      have hsub : Tm.subst k a (Tm.var i) = Tm.var i := by
        simp only [Tm.subst]
        rw [if_neg (by omega : ¬ i = k), if_neg (by omega : ¬ i > k)]
      refine ⟨Usage.unit i Γ.length σ, by rw [hsub]; exact HasType.var hlkΓ, ?_⟩
      rw [insertUsage_unit_lt hik hiG]
      have hulen : (Usage.unit i (Γ.length + 1) σ).length = Γ.length + 1 :=
        Usage.length_unit i (Γ.length + 1) σ (by omega)
      have hvlen :
          (Usage.scale ((Usage.unit i (Γ.length + 1) σ).get k) (insertUsage φa k)).length
            = Γ.length + 1 := by
        rw [Usage.length_scale, insertUsage_length, usage_length ha]
      exact Usage.le_add_left (hulen.trans hvlen.symm)
    · -- i = k: this occurrence *is* the substituted variable.
      have hAeq : A = A' := by
        have h1 := insertTy_get_eq (Γ := Γ) (c := k) (X := A') hk
        rw [hik] at hlk
        rw [hlk] at h1
        exact Option.some.inj h1
      have hgetk : (Usage.unit i (Γ.length + 1) σ).get i = σ :=
        Usage.get_unit_same i (Γ.length + 1) σ (by omega)
      rw [hik] at hgetk hget
      rw [hgetk] at hget
      have ha2 : HasType Γ d a A π φa := by rw [hAeq]; exact ha
      obtain ⟨φ', hφ', hLe⟩ := demote_scaled ha2 hget
      have hsub : Tm.subst k a (Tm.var i) = a := by
        simp only [Tm.subst]; rw [if_pos hik]
      refine ⟨φ', by rw [hsub]; exact hφ', ?_⟩
      rw [hik, hgetk]
      have hφ'len : φ'.length = Γ.length := usage_length hφ'
      refine Usage.le_of_forall_get ?_ ?_
      · rw [insertUsage_length, hφ'len, Usage.length_add,
          Usage.length_unit k (Γ.length + 1) σ (by omega), Usage.length_scale, insertUsage_length,
          usage_length ha, Nat.min_self]
      · intro j
        rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
        · rw [insertUsage_get_lt hjk,
            Usage.get_add (by rw [Usage.length_unit k (Γ.length + 1) σ (by omega),
              Usage.length_scale, insertUsage_length, usage_length ha]),
            Usage.get_unit_other k j (Γ.length + 1) σ (by omega), Grade.zero_add, Usage.get_scale,
            insertUsage_get_lt hjk]
          have := Usage.le_get hLe j
          rwa [Usage.get_scale] at this
        · subst hjk
          rw [insertUsage_get_self]
          exact Grade.zero_le _
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          have hgej : k ≤ j' := by omega
          rw [insertUsage_get_ge hgej,
            Usage.get_add (by rw [Usage.length_unit k (Γ.length + 1) σ (by omega),
              Usage.length_scale, insertUsage_length, usage_length ha]),
            Usage.get_unit_other k (j' + 1) (Γ.length + 1) σ (by omega), Grade.zero_add,
            Usage.get_scale, insertUsage_get_ge hgej]
          have := Usage.le_get hLe j'
          rwa [Usage.get_scale] at this
    · -- k < i: the substituted binder is gone, so indices above it shift down by one.
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hge : k ≤ i' := by omega
      have hlt : i' < Γ.length := by
        have := lookup_lt hlk
        rw [insertTy_length] at this
        omega
      have hlkΓ : Γ[i']? = some A := by rw [← insertTy_get_ge hge]; exact hlk
      have hsub : Tm.subst k a (Tm.var (i' + 1)) = Tm.var i' := by
        have h1 : ¬ (i' + 1 = k) := by omega
        have h2 : i' + 1 > k := by omega
        simp [Tm.subst, h1, h2]
      refine ⟨Usage.unit i' Γ.length σ, by rw [hsub]; exact HasType.var hlkΓ, ?_⟩
      rw [insertUsage_unit_ge hge hlt]
      have hulen : (Usage.unit (i' + 1) (Γ.length + 1) σ).length = Γ.length + 1 :=
        Usage.length_unit (i' + 1) (Γ.length + 1) σ (by omega)
      have hvlen :
          (Usage.scale ((Usage.unit (i' + 1) (Γ.length + 1) σ).get k) (insertUsage φa k)).length
            = Γ.length + 1 := by
        rw [Usage.length_scale, insertUsage_length, usage_length ha]
      exact Usage.le_add_left (hulen.trans hvlen.symm)
  | @lam Γ0 d body ρ σ δ A B rest hbody hle ihbody =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    have heq2 : A :: insertTy Γ k A' = insertTy (A :: Γ) (k + 1) A' := rfl
    rw [heq2] at hbody
    have ha' : HasType (A :: Γ) d (Tm.shiftAbove 0 a) A' π (insertUsage φa 0) := by
      have hw := weaken ha 0 A
      rwa [insertTy_zero] at hw
    have hget' : Usage.get (δ :: rest) (k + 1) ≤ π := hget
    obtain ⟨φ'', hφ'', hLe⟩ :=
      @ihbody (k + 1) (A :: Γ) rfl (by simp only [List.length_cons]; omega)
        (Tm.shiftAbove 0 a) π (insertUsage φa 0) ha' hget'
    have hgeteq : Usage.get (δ :: rest) (k + 1) = rest.get k := rfl
    rw [hgeteq] at hLe
    have hlen : φ''.length = (A :: Γ).length := usage_length hφ''
    obtain ⟨δ', rest', hφ''eq⟩ : ∃ δ' rest', φ'' = δ' :: rest' := by
      cases φ'' with
      | nil => simp at hlen
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφ''eq
    have hLe' :
        Usage.Le (δ' :: insertUsage rest' k)
          (δ :: Usage.add rest (Usage.scale (rest.get k) (insertUsage φa k))) := by
      have hins1 : insertUsage (δ' :: rest') (k + 1) = δ' :: insertUsage rest' k := rfl
      have hins2 : insertUsage φa 0 = Grade.zero :: φa := insertUsage_cons_zero φa
      have hins3 : insertUsage (Grade.zero :: φa) (k + 1) = Grade.zero :: insertUsage φa k := rfl
      rw [hins1] at hLe
      rw [hins2, hins3] at hLe
      have hrhs :
          Usage.add (δ :: rest) (Usage.scale (rest.get k) (Grade.zero :: insertUsage φa k))
            = δ :: Usage.add rest (Usage.scale (rest.get k) (insertUsage φa k)) := by
        have hmulzero : (rest.get k).mul Grade.zero = Grade.zero := by
          cases (rest.get k) <;> rfl
        simp only [Usage.scale, Usage.add, hmulzero, Grade.add_zero]
      rw [hrhs] at hLe
      exact hLe
    obtain ⟨hδδ, hLetail⟩ := hLe'
    refine ⟨rest', by exact HasType.lam hφ'' (Grade.le_trans hδδ hle), hLetail⟩
  | @app Γ0 d f arg ρ σ A B φf φarg hf harg ihf iharg =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    have hgetsum : (φf.get k).add (φarg.get k) ≤ π := by
      have := hget
      rwa [Usage.get_add (by rw [usage_length hf, usage_length harg])] at this
    have hgetf : φf.get k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgetsum
    have hgetarg : φarg.get k ≤ π := Grade.le_trans (Grade.self_le_add_right _ _) hgetsum
    obtain ⟨φf', hφf', hLef⟩ := ihf rfl hk ha hgetf
    obtain ⟨φarg', hφarg', hLearg⟩ := iharg rfl hk ha hgetarg
    refine ⟨Usage.add φf' φarg', HasType.app hφf' hφarg', ?_⟩
    exact insertUsage_scale_add_bound
      (by rw [usage_length hf, usage_length harg])
      (by rw [usage_length hf, insertTy_length, insertUsage_length, usage_length ha])
      (by rw [usage_length hφf', usage_length hφarg']) hLef hLearg
  | @tt Γ0 d σ =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    refine ⟨Usage.zero Γ.length, HasType.tt, ?_⟩
    rw [insertUsage_zero, insertTy_length]
    rw [Usage.get_zero, Usage.scale_zero, insertUsage_length, usage_length ha, Usage.add_zero_zero]
    exact Usage.le_refl _
  | @ff Γ0 d σ =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    refine ⟨Usage.zero Γ.length, HasType.ff, ?_⟩
    rw [insertUsage_zero, insertTy_length]
    rw [Usage.get_zero, Usage.scale_zero, insertUsage_length, usage_length ha, Usage.add_zero_zero]
    exact Usage.le_refl _
  | @ite Γ0 d cnd t el σ A φc φt φel hc ht hel ihc iht ihel =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    have hlenc : φc.length = Γ.length + 1 := by rw [usage_length hc, insertTy_length]
    have hlent : φt.length = Γ.length + 1 := by rw [usage_length ht, insertTy_length]
    have hlenel : φel.length = Γ.length + 1 := by rw [usage_length hel, insertTy_length]
    have hlenX : (insertUsage φa k).length = Γ.length + 1 := by
      rw [insertUsage_length, usage_length ha]
    have hlen_c_tel : φc.length = (Usage.add φt φel).length := by
      rw [Usage.length_add, hlent, hlenel, Nat.min_self, hlenc]
    have hlen_t_el : φt.length = φel.length := hlent.trans hlenel.symm
    have hgetsum : (φc.get k).add ((φt.get k).add (φel.get k)) ≤ π := by
      have h1 := hget
      rw [Usage.get_add hlen_c_tel, Usage.get_add hlen_t_el] at h1
      exact h1
    have hgetc : φc.get k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgetsum
    have hgettel : (φt.get k).add (φel.get k) ≤ π :=
      Grade.le_trans (Grade.self_le_add_right _ _) hgetsum
    have hgett : φt.get k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgettel
    have hgetel : φel.get k ≤ π := Grade.le_trans (Grade.self_le_add_right _ _) hgettel
    obtain ⟨φc', hφc', hLec⟩ := ihc rfl hk ha hgetc
    obtain ⟨φt', hφt', hLet⟩ := iht rfl hk ha hgett
    obtain ⟨φel', hφel', hLeel⟩ := ihel rfl hk ha hgetel
    have hLetel : Usage.Le (insertUsage (Usage.add φt' φel') k)
        (Usage.add (Usage.add φt φel) (Usage.scale ((Usage.add φt φel).get k) (insertUsage φa k))) :=
      insertUsage_scale_add_bound (hlent.trans hlenel.symm) (hlent.trans hlenX.symm)
        (by rw [usage_length hφt', usage_length hφel']) hLet hLeel
    refine ⟨Usage.add φc' (Usage.add φt' φel'), HasType.ite hφc' hφt' hφel', ?_⟩
    have hlenc' : φc'.length = Γ.length := usage_length hφc'
    have hlent' : φt'.length = Γ.length := usage_length hφt'
    have hlenel' : φel'.length = Γ.length := usage_length hφel'
    exact insertUsage_scale_add_bound hlen_c_tel (hlenc.trans hlenX.symm)
      (by rw [hlenc', Usage.length_add, hlent', hlenel', Nat.min_self]) hLec hLetel
  | @iabs Γ0 d body A σ φ hbody ihbody =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    -- `ihbody` demands its substituted term at one dimension deeper than `hbody`'s own conclusion
    -- (`d + 1`, matching `iabs`'s premise) — `dim_weaken` (Weakening.lean) is exactly the fact
    -- that a derivation valid at `d` stays valid at `d + 1`, the dimension-side counterpart of the
    -- `lam` case's `weaken ha 0 A` re-shift for one more *term* binder.
    obtain ⟨φ', hφ', hLe⟩ := ihbody rfl hk (dim_weaken ha) hget
    exact ⟨φ', HasType.iabs hφ', hLe⟩
  | @transp Γ0 d A base σ φ hbase ihbase =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    obtain ⟨φ', hφ', hLe⟩ := ihbase rfl hk ha hget
    exact ⟨φ', HasType.transp hφ', hLe⟩
  | @hcomp Γ0 d A phi tube base σ φtube φbase htube hbase ihtube ihbase =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    -- Exactly `app`'s shape (two summed sub-usages, both checked in the same context): `hcomp`'s
    -- tube and base play the role of `f`/`arg`, just without `app`'s extra `σ.mul ρ` scaling on
    -- the second branch.
    have hgetsum : (φtube.get k).add (φbase.get k) ≤ π := by
      have := hget
      rwa [Usage.get_add (by rw [usage_length htube, usage_length hbase])] at this
    have hgettube : φtube.get k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgetsum
    have hgetbase : φbase.get k ≤ π := Grade.le_trans (Grade.self_le_add_right _ _) hgetsum
    obtain ⟨φtube', hφtube', hLetube⟩ := ihtube rfl hk ha hgettube
    obtain ⟨φbase', hφbase', hLebase⟩ := ihbase rfl hk ha hgetbase
    refine ⟨Usage.add φtube' φbase', HasType.hcomp hφtube' hφbase', ?_⟩
    exact insertUsage_scale_add_bound
      (by rw [usage_length htube, usage_length hbase])
      (by rw [usage_length htube, insertTy_length, insertUsage_length, usage_length ha])
      (by rw [usage_length hφtube', usage_length hφbase']) hLetube hLebase

/-- The public form of the substitution lemma: substituting `a` (checked against the removed
    binder's type `A'` at grade `π`) into `e` (checked with that binder inserted at depth `k`)
    preserves typability, with usage bounded by the original usage (slot `k` dropped) plus a
    correction scaled by exactly how much slot `k` was demanded. -/
theorem subst_lemma {Γ : List Ty} {d : Nat} {a : Tm} {A' : Ty} {π : Grade} {φa : Usage}
    (ha : HasType Γ d a A' π φa) {k : Nat} {e : Tm} {B : Ty} {σ : Grade} {φ : Usage}
    (h : HasType (insertTy Γ k A') d e B σ φ) (hk : k ≤ Γ.length) (hget : φ.get k ≤ π) :
    ∃ φ', HasType Γ d (Tm.subst k a e) B σ φ' ∧
      Usage.Le (insertUsage φ' k) (Usage.add φ (Usage.scale (φ.get k) (insertUsage φa k))) :=
  subst_lemma_aux h rfl hk ha hget

end BlightMeta
