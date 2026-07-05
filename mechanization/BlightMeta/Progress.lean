/-
  Wave 3 / M6: progress + preservation, combined into full type safety for this fragment (`Bool`,
  `Π`, and the constant-family Kan formers `iabs`/`transp`/`hcomp` from M5). This is the corollary
  `docs/blight-spec.md`/the roadmap flagged as unlocked by `Substitution.lean`'s `subst_lemma`
  once the Kan operational rules are in place: `progress` says a well-typed *closed* term is
  either a canonical value or can take a step; `preservation` says stepping never changes a
  term's type. Together (`type_safety` below) they give the standard "well-typed closed programs
  never get stuck" guarantee for the whole fragment, mirroring `check.rs`'s untrusted evaluator
  being kept in lockstep with the kernel's typing rules — except here it is a proof, not a test.

  ── A genuine gotcha the constant-family Kan rules introduce ───────────────────────────────────
  `HasType.iabs`'s conclusion reuses the body's own type `A` verbatim (§1.1(d)'s "no slot," pushed
  all the way through to "no new type former either" — this fragment's `Ty` has no `Line`/`PathP`
  constructor, only `Bool`/`arr`). That means `.iabs body` can inhabit an *arrow* type `.arr ρ A B`
  without itself being a `lam` — so if `.iabs _` were classified as a value (the "no eliminator,
  so it must be inert, same as `lam`" argument that works for a genuine interval abstraction),
  canonical forms would break: `.app (.iabs body) a` would be a well-typed value-headed redex with
  no applicable `Step` rule, a real progress hole. The fix taken here is *not* to add an ad hoc
  "apply through iabs" rule, but the more principled one implied by `HasType.iabs` already being
  definitionally transparent to typing: make it *equally* transparent to evaluation. `.iabs body`
  is simply never a value; it unconditionally steps to `body` (`Step.iabs_elim` below), matching
  the already-proved `dim_change` (`Weakening.lean`) fact that the specific dimension count `body`
  is checked at does not matter. With `iabs` no longer a `Value` former, canonical forms is
  restored for free: the only remaining values of arrow type are `lam`s (by `Tm`'s constructors
  being pairwise disjoint plus `HasType`'s cases being keyed on term shape), and likewise `tt`/`ff`
  are the only remaining values of `Bool`. -/

import BlightMeta.Substitution

namespace BlightMeta

/-- Canonical forms (closed values) of this fragment. `iabs` is deliberately **not** a value former
    — see the module doc's gotcha note: unlike `lam` (which genuinely has no way to run further
    without an argument that doesn't exist yet), `.iabs body` has nothing blocking it from just
    becoming `body` right away, since this fragment's `Tm` has no dimension-variable former for
    `body` to depend on in the first place. -/
inductive Value : Tm → Prop where
  | lam {body : Tm} : Value (.lam body)
  | tt : Value .tt
  | ff : Value .ff

/-- Call-by-value small-step reduction. `app`/`ite` are the ordinary STLC rules (congruence on the
    function/scrutinee position, then β/ι once it is a value). `transp`/`hcomp`/`iabs` are
    `kan.rs`'s constant-family computation rules verbatim, restricted to this fragment's `phi`
    (a `Bool` standing in for "everywhere false"/"everywhere true", per `Calculus.lean`'s module
    doc):

    * `transp_constant_family_is_identity` (`kan.rs` ~37, tested `kan.rs` ~505): transporting a
      value along a constant line is definitionally that same value — `transp_val` below. (`base`
      is reduced to a value first via `transp_base`, mirroring `transp`/`hcomp` being *value-level*
      operations in `kan.rs` — they consume already-evaluated `Value`s.)
    * `hcomp_total_cofib_picks_tube` / `hcomp_empty_cofib_picks_base` (`kan.rs` ~516, ~523): the
      composite reduces immediately to whichever branch `phi` selects. Both fire unconditionally,
      with no congruence needed on *either* branch first — the kernel picks one `Value` and never
      forces the other, so neither does this rule.
    * `iabs_elim`: opening a dimension binder is a complete no-op, operationally as well as for
      typing (see the module doc) — `.iabs body` always steps straight to `body`. -/
inductive Step : Tm → Tm → Prop where
  | app1 {f f' a : Tm} (h : Step f f') : Step (.app f a) (.app f' a)
  | app2 {f a a' : Tm} (hf : Value f) (h : Step a a') : Step (.app f a) (.app f a')
  | beta {body a : Tm} (ha : Value a) : Step (.app (.lam body) a) (Tm.subst0 a body)
  | ite_cond {c c' t e : Tm} (h : Step c c') : Step (.ite c t e) (.ite c' t e)
  | ite_tt {t e : Tm} : Step (.ite .tt t e) t
  | ite_ff {t e : Tm} : Step (.ite .ff t e) e
  | transp_base {A : Ty} {base base' : Tm} (h : Step base base') :
      Step (.transp A base) (.transp A base')
  | transp_val {A : Ty} {base : Tm} (h : Value base) : Step (.transp A base) base
  | hcomp_true {A : Ty} {tube base : Tm} : Step (.hcomp A true tube base) tube
  | hcomp_false {A : Ty} {tube base : Tm} : Step (.hcomp A false tube base) base
  | iabs_elim {body : Tm} : Step (.iabs body) body

/-- **Progress**: a closed (`Γ = []`), well-typed term is either a value or can step. Proved by
    induction on the typing derivation; the only two cases that need `HasType` inversion (rather
    than falling straight out of the induction hypotheses) are `app`/`ite`, where a `Value`
    premise of the wrong shape (`tt`/`ff` at an arrow type, or `lam` at `Bool`) is ruled out
    exactly because `HasType`'s conclusion type is forced by the term's own head constructor. -/
theorem progress {Γ : List Ty} {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) : Γ = [] → Value e ∨ ∃ e', Step e e' := by
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
  | @hcomp Γ0 d A phi tube base σ φtube φbase htube hbase ihtube ihbase =>
    intro _
    cases phi with
    | true => exact Or.inr ⟨_, .hcomp_true⟩
    | false => exact Or.inr ⟨_, .hcomp_false⟩

/-- **Graded preservation** (M-A.1): stepping never changes a term's type (nor the ambient grade
    or dimension count it was checked at), and the resulting usage vector is PINNED — it only ever
    *shrinks* (`Usage.Le φ' φ`), never grows. Reduction consumes resources; it cannot mint them.

    The bound's provenance, case by case: congruence cases lift the IH bound through `add_mono`;
    eliminator cases (`ite_tt`/`ff`, `hcomp_*`) drop a summand (`le_add_self_*`, with lengths from
    `usage_length`); `beta` is the real content — `subst_lemma`'s own `Usage.Le` bound charges the
    argument at the binder demand `δ`, and `δ ≤ σ·ρ` (`demand_le_scale`) caps `scale δ φa` by
    `φa` itself through **ambient absorption** (`usage_absorbs_ambient`: a judgement's usage is
    saturated at its own ambient, `σ·σ = σ`). -/
theorem preservation {Γ : List Ty} {d : Nat} {e e' : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType Γ d e A σ φ) (hstep : Step e e') :
    ∃ φ', HasType Γ d e' A σ φ' ∧ Usage.Le φ' φ := by
  induction hstep generalizing A σ φ with
  | app1 _ ih =>
    cases h with
    | app hf0 ha0 =>
      obtain ⟨φf', hφf', hb⟩ := ih hf0
      exact ⟨_, HasType.app hφf' ha0, Usage.add_mono hb (Usage.le_refl _)⟩
  | app2 _ _ ih =>
    cases h with
    | app hf0 ha0 =>
      obtain ⟨φa', hφa', hb⟩ := ih ha0
      exact ⟨_, HasType.app hf0 hφa', Usage.add_mono (Usage.le_refl _) hb⟩
  | @beta body a haval =>
    cases h with
    | app hf0 ha0 =>
      rename_i ρ Adom φf φa
      cases hf0 with
      | lam hbody hle =>
        rename_i δ
        have hzero : σ = Grade.zero → δ = Grade.zero := by
          intro hσ
          have hz := ambient_zero_usage hbody hσ
          injection hz with hδ _
        have hget : (δ :: φf).get 0 ≤ σ.mul ρ := demand_le_scale hle hzero
        have hbody' : HasType (insertTy Γ 0 Adom) d body A σ (δ :: φf) := by
          rw [insertTy_zero]; exact hbody
        obtain ⟨φ', hφ', hbound⟩ := subst_lemma ha0 hbody' (Nat.zero_le _) hget
        refine ⟨φ', hφ', ?_⟩
        -- Massage the substitution bound into the app node's usage `add φf φa`.
        rw [insertUsage_cons_zero, insertUsage_cons_zero] at hbound
        have hmulz : δ.mul Grade.zero = Grade.zero := by cases δ <;> rfl
        simp only [Usage.get, Usage.scale, Usage.add, hmulz, Grade.add_zero] at hbound
        obtain ⟨-, htail⟩ := hbound
        have hδ : δ ≤ σ.mul ρ := by simpa [Usage.get] using hget
        have hcap : Usage.Le (Usage.scale δ φa) φa := by
          have hmono := Usage.scale_le_scale hδ φa
          rwa [usage_absorbs_ambient ha0] at hmono
        exact Usage.le_trans htail (Usage.add_mono (Usage.le_refl _) hcap)
  | ite_cond _ ih =>
    cases h with
    | ite hc0 ht0 he0 =>
      obtain ⟨φc', hφc', hb⟩ := ih hc0
      exact ⟨_, HasType.ite hφc' ht0 he0, Usage.add_mono hb (Usage.le_refl _)⟩
  | ite_tt =>
    cases h with
    | @ite Γ0 d0 c0 t0 e0 σ0 A0 φc φt φe hc0 ht0 he0 =>
      refine ⟨_, ht0, ?_⟩
      have lc := usage_length hc0
      have lt := usage_length ht0
      have le := usage_length he0
      have h1 : Usage.Le φt (Usage.add φt φe) :=
        Usage.le_add_self_left (by rw [lt, le])
      have h2 : Usage.Le (Usage.add φt φe) (Usage.add φc (Usage.add φt φe)) :=
        Usage.le_add_self_right (by rw [Usage.length_add, lt, le, lc, Nat.min_self])
      exact Usage.le_trans h1 h2
  | ite_ff =>
    cases h with
    | @ite Γ0 d0 c0 t0 e0 σ0 A0 φc φt φe hc0 ht0 he0 =>
      refine ⟨_, he0, ?_⟩
      have lc := usage_length hc0
      have lt := usage_length ht0
      have le := usage_length he0
      have h1 : Usage.Le φe (Usage.add φt φe) :=
        Usage.le_add_self_right (by rw [lt, le])
      have h2 : Usage.Le (Usage.add φt φe) (Usage.add φc (Usage.add φt φe)) :=
        Usage.le_add_self_right (by rw [Usage.length_add, lt, le, lc, Nat.min_self])
      exact Usage.le_trans h1 h2
  | transp_base _ ih =>
    cases h with
    | transp hbase0 =>
      obtain ⟨φ', hφ', hb⟩ := ih hbase0
      exact ⟨_, HasType.transp hφ', hb⟩
  | transp_val _ =>
    cases h with
    | transp hbase0 => exact ⟨_, hbase0, Usage.le_refl _⟩
  | hcomp_true =>
    cases h with
    | hcomp htube0 hbase0 =>
      exact ⟨_, htube0,
        Usage.le_add_self_left (by rw [usage_length htube0, usage_length hbase0])⟩
  | hcomp_false =>
    cases h with
    | hcomp htube0 hbase0 =>
      exact ⟨_, hbase0,
        Usage.le_add_self_right (by rw [usage_length htube0, usage_length hbase0])⟩
  | iabs_elim =>
    cases h with
    | iabs hbody0 => exact ⟨_, dim_change hbody0 d, Usage.le_refl _⟩

/-- **Full type safety**: combining `progress` and `preservation`, a well-typed closed term never
    "gets stuck" partway through evaluation — at every point it is either already a value, or it
    can step to a term that is *still* well-typed at the very same type (so the argument iterates:
    the successor term is again covered by `progress`, and so on). This is the exact "combine with
    preservation for full type safety" M6 asked for, stated as the standard single corollary. -/
theorem type_safety {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType [] d e A σ φ) :
    Value e ∨ ∃ e' φ', Step e e' ∧ HasType [] d e' A σ φ' := by
  rcases progress h rfl with hval | ⟨e', hstep⟩
  · exact Or.inl hval
  · obtain ⟨φ', hφ', -⟩ := preservation h hstep
    exact Or.inr ⟨e', φ', hstep, hφ'⟩

/-- **Graded type safety** (M-A.2, the headline): the standard corollary, WITH the resource bound
    — a step's successor is well-typed at the same type *and* its usage is bounded by the
    original's (`Usage.Le φ' φ`). Iterating: along ANY reduction sequence the usage vector is
    monotonically non-increasing, so a closed program can never step its way into using a linear
    resource more than its typing licensed. -/
theorem type_safety_graded {d : Nat} {e : Tm} {A : Ty} {σ : Grade} {φ : Usage}
    (h : HasType [] d e A σ φ) :
    Value e ∨ ∃ e' φ', Step e e' ∧ HasType [] d e' A σ φ' ∧ Usage.Le φ' φ := by
  rcases progress h rfl with hval | ⟨e', hstep⟩
  · exact Or.inl hval
  · obtain ⟨φ', hφ', hb⟩ := preservation h hstep
    exact Or.inr ⟨e', φ', hstep, hφ', hb⟩

-- House-style sorry-freedom receipts (M-A.1/M-A.2): the acceptable axiom set is
-- `{propext, Classical.choice, Quot.sound}` — never `sorryAx`.
#print axioms usage_absorbs_ambient
#print axioms preservation
#print axioms type_safety
#print axioms type_safety_graded

end BlightMeta
