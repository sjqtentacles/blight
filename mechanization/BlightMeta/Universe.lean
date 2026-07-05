/-
  Symbolic universe levels (T2, universe polymorphism), mirroring
  `crates/blight-kernel/src/check.rs` (`level_leq` / `level_wf` / `level_max`) and their
  independently-written re-checker twins (`crates/blight-recheck/src/term.rs`, `rlevel_*`).

  What the Rust sides can only claim in doc-comments, this file proves:

  * `leq_sound` — the structural order answers `true` ONLY when `a ≤ b` holds under **every**
    assignment of the level variables (the kernel's stated soundness contract; a spurious
    `false` only rejects, never accepts).
  * `leq_refl` — reflexivity (the "drop-in ⊇ conv" claim: conversion implies cumulativity).
  * `cumul_trans_sound` — **cumulativity-transitivity**: a chain `Univ a ≤ Univ b ≤ Univ c`
    of accepted coercions is semantically sound end-to-end (`den ρ a ≤ den ρ c` for every ρ).
  * `wf_weaken` / `wf_mono` — **level-context weakening**: a level well-formed under `n`
    prenex variables stays well-formed under `n + 1` (and any `m ≥ n`) — the lemma that makes
    extending the prenex telescope conservative.
  * `max_sound` — the dominance-normalizing `level_max` denotes exactly `Nat.max` (dropping a
    dominated summand loses nothing, under every assignment).
  * `closed_den_const` / `closed_leq_complete` — a closed level's denotation is
    assignment-independent, and on **closed** levels the symbolic order agrees exactly with `≤`
    on the denotations (the "byte-identical on the concrete fragment" claim).

  The `Level` syntax and each definition mirror the Rust constructor-for-constructor so the
  transcription is auditable; the proofs are this file's own.
-/

namespace BlightMeta

/-- Symbolic universe level: `crates/blight-kernel/src/term.rs::Level` verbatim. `var u` is a de
    Bruijn index into the prenex level context. -/
inductive Level where
  | zero
  | suc (l : Level)
  | max (a b : Level)
  | var (u : Nat)
  deriving DecidableEq, Repr

namespace Level

/-- Denotation under an assignment `ρ` of the level variables. -/
def den (ρ : Nat → Nat) : Level → Nat
  | zero => 0
  | suc l => den ρ l + 1
  | max a b => Nat.max (den ρ a) (den ρ b)
  | var u => ρ u

/-- The kernel's sound structural order (`check.rs::level_leq`), constructor-for-constructor:
    `0 ≤ b`; `max ≤ b` iff both summands; `suc ≤ suc` descends; a `suc`/`var` left side meets a
    `max` right side if either arm dominates; `var u ≤ suc b` descends; `var u ≤ var v` iff
    `u = v`; everything else is `false`. -/
def leq : Level → Level → Bool
  | zero, _ => true
  | max a1 a2, b => leq a1 b && leq a2 b
  | suc a1, suc b1 => leq a1 b1
  | suc a1, max b1 b2 => leq (suc a1) b1 || leq (suc a1) b2
  | suc _, zero => false
  | suc _, var _ => false
  | var u, var v => u == v
  | var u, suc b1 => leq (var u) b1
  | var u, max b1 b2 => leq (var u) b1 || leq (var u) b2
  | var _, zero => false

/-- Well-formedness under `n` prenex level variables (`check.rs::level_wf`): every `var u`
    satisfies `u < n`. -/
def wf : Level → Nat → Bool
  | zero, _ => true
  | suc a, n => wf a n
  | max a b, n => wf a n && wf b n
  | var u, n => u < n

/-- The dominance-normalizing least upper bound (`check.rs::level_max`, minus the concrete
    fast-path, which agrees with the dominance path on canonical chains): a dominated summand is
    dropped; only incomparable pairs build a `max` node. -/
def smax (a b : Level) : Level :=
  if leq a b then b else if leq b a then a else max a b

/-! ## Soundness of the structural order -/

/-- `leq_sound`: the order is sound — `leq a b = true` forces `den ρ a ≤ den ρ b` for EVERY
    assignment `ρ`. (The converse fails by design: the order is deliberately incomplete, e.g.
    `suc (max u v) ≤ max (suc u) (suc v)` is semantically true but structurally `false` — a
    spurious `false` only rejects.) -/
theorem leq_sound : ∀ (a b : Level), leq a b = true → ∀ ρ, den ρ a ≤ den ρ b := by
  intro a
  induction a with
  | zero =>
    intro b _ ρ
    exact Nat.zero_le _
  | max a1 a2 ih1 ih2 =>
    intro b h ρ
    simp only [leq, Bool.and_eq_true] at h
    exact Nat.max_le.mpr ⟨ih1 b h.1 ρ, ih2 b h.2 ρ⟩
  | suc a1 ih =>
    intro b
    induction b with
    | zero => intro h; simp [leq] at h
    | suc b1 _ =>
      intro h ρ
      simp only [leq] at h
      exact Nat.succ_le_succ (ih b1 h ρ)
    | max b1 b2 ihb1 ihb2 =>
      intro h ρ
      simp only [leq, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Nat.le_trans (ihb1 h ρ) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihb2 h ρ) (Nat.le_max_right _ _)
    | var _ => intro h; simp [leq] at h
  | var u =>
    intro b
    induction b with
    | zero => intro h; simp [leq] at h
    | suc b1 ihb =>
      intro h ρ
      simp only [leq] at h
      exact Nat.le_trans (ihb h ρ) (Nat.le_succ _)
    | max b1 b2 ihb1 ihb2 =>
      intro h ρ
      simp only [leq, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Nat.le_trans (ihb1 h ρ) (Nat.le_max_left _ _)
      · exact Nat.le_trans (ihb2 h ρ) (Nat.le_max_right _ _)
    | var v =>
      intro h ρ
      simp only [leq, beq_iff_eq] at h
      subst h
      exact Nat.le_refl _

/-! ## Reflexivity (the "⊇ conv" claim) -/

/-- Helper: a level under either arm of a right-side `max` is under the `max` — for every head
    shape of `a` (the rule the `suc`/`var` arms carry natively; `zero`/`max` decompose). -/
theorem leq_max_left : ∀ (a b1 b2 : Level), leq a b1 = true → leq a (max b1 b2) = true := by
  intro a
  induction a with
  | zero => intro b1 b2 _; simp [leq]
  | max a1 a2 ih1 ih2 =>
    intro b1 b2 h
    simp only [leq, Bool.and_eq_true] at h ⊢
    exact ⟨ih1 b1 b2 h.1, ih2 b1 b2 h.2⟩
  | suc a1 _ =>
    intro b1 b2 h
    simp only [leq, Bool.or_eq_true]
    exact Or.inl h
  | var u =>
    intro b1 b2 h
    simp only [leq, Bool.or_eq_true]
    exact Or.inl h

/-- Symmetric helper for the right arm. -/
theorem leq_max_right : ∀ (a b1 b2 : Level), leq a b2 = true → leq a (max b1 b2) = true := by
  intro a
  induction a with
  | zero => intro b1 b2 _; simp [leq]
  | max a1 a2 ih1 ih2 =>
    intro b1 b2 h
    simp only [leq, Bool.and_eq_true] at h ⊢
    exact ⟨ih1 b1 b2 h.1, ih2 b1 b2 h.2⟩
  | suc a1 _ =>
    intro b1 b2 h
    simp only [leq, Bool.or_eq_true]
    exact Or.inr h
  | var u =>
    intro b1 b2 h
    simp only [leq, Bool.or_eq_true]
    exact Or.inr h

/-- `leq_refl`: the order is reflexive — so definitional equality of universes implies
    cumulativity (`subtype ⊇ conv`), the kernel's drop-in claim. -/
theorem leq_refl : ∀ (a : Level), leq a a = true := by
  intro a
  induction a with
  | zero => simp [leq]
  | suc a1 ih => simpa [leq] using ih
  | max a1 a2 ih1 ih2 =>
    simp only [leq, Bool.and_eq_true]
    exact ⟨leq_max_left a1 a1 a2 ih1, leq_max_right a2 a1 a2 ih2⟩
  | var u => simp [leq]

/-! ## Cumulativity-transitivity -/

/-- `cumul_trans_sound`: a CHAIN of accepted cumulativity coercions is semantically sound —
    `Univ a ≤ Univ b` and `Univ b ≤ Univ c` compose to `den ρ a ≤ den ρ c` under every
    assignment. This is the lemma the pairwise `subtype` checks rest on when coercions stack
    (each hop is `leq_sound`; `Nat.le_trans` closes the chain). -/
theorem cumul_trans_sound (a b c : Level)
    (hab : leq a b = true) (hbc : leq b c = true) :
    ∀ ρ, den ρ a ≤ den ρ c := by
  intro ρ
  exact Nat.le_trans (leq_sound a b hab ρ) (leq_sound b c hbc ρ)

/-! ## Level-context weakening -/

/-- `wf_weaken`: one more prenex level variable never breaks well-formedness. -/
theorem wf_weaken : ∀ (l : Level) (n : Nat), wf l n = true → wf l (n + 1) = true := by
  intro l
  induction l with
  | zero => intro n _; rfl
  | suc a ih => intro n h; exact ih n h
  | max a b iha ihb =>
    intro n h
    simp only [wf, Bool.and_eq_true] at h ⊢
    exact ⟨iha n h.1, ihb n h.2⟩
  | var u =>
    intro n h
    simp only [wf, decide_eq_true_eq] at h ⊢
    omega

/-- `wf_mono`: weakening iterated — well-formedness is monotone in the level-context size. -/
theorem wf_mono : ∀ (l : Level) (n m : Nat), n ≤ m → wf l n = true → wf l m = true := by
  intro l n m hnm h
  induction m with
  | zero =>
    have : n = 0 := Nat.le_zero.mp hnm
    subst this
    exact h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hle : n ≤ m := Nat.lt_succ_iff.mp hlt
      exact wf_weaken l m (ih hle)
    · have : n = m + 1 := Nat.le_antisymm hnm hge
      subst this
      exact h

/-! ## The dominance-normalizing max -/

/-- `max_sound`: `smax` denotes exactly `Nat.max` under every assignment — dropping a dominated
    summand (via the sound order) loses nothing. So the kernel/re-checker's canonical-form
    normalization in `Pi`/`Sigma` formation is semantics-preserving. -/
theorem max_sound (a b : Level) : ∀ ρ, den ρ (smax a b) = Nat.max (den ρ a) (den ρ b) := by
  intro ρ
  unfold smax
  by_cases hab : leq a b = true
  · rw [if_pos hab]
    exact (Nat.max_eq_right (leq_sound a b hab ρ)).symm
  · rw [if_neg hab]
    by_cases hba : leq b a = true
    · rw [if_pos hba]
      exact (Nat.max_eq_left (leq_sound b a hba ρ)).symm
    · rw [if_neg hba]
      simp [den]

/-! ## Exactness on the closed fragment -/

/-- Evaluate a closed level (`wf l 0`): no variable can occur, so the denotation is
    assignment-independent. -/
theorem closed_den_const (l : Level) (h : wf l 0 = true) :
    ∀ ρ ρ', den ρ l = den ρ' l := by
  induction l with
  | zero => intro _ _; rfl
  | suc a ih =>
    intro ρ ρ'
    simp only [den]
    exact congrArg (· + 1) (ih h ρ ρ')
  | max a b iha ihb =>
    simp only [wf, Bool.and_eq_true] at h
    intro ρ ρ'
    simp only [den]
    rw [iha h.1 ρ ρ', ihb h.2 ρ ρ']
  | var u =>
    simp [wf] at h

/-- Bridge for the `max`-right case below: `x ≤ max m n` (over `Nat`) implies `x ≤ m` or
    `x ≤ n`. -/
theorem max_le_or (m n x : Nat) (h : x ≤ Nat.max m n) : x ≤ m ∨ x ≤ n := by
  rcases Nat.le_total m n with hmn | hnm
  · right
    calc x ≤ Nat.max m n := h
      _ = n := Nat.max_eq_right hmn
  · left
    calc x ≤ Nat.max m n := h
      _ = m := Nat.max_eq_left hnm

/-- On closed levels the order is COMPLETE as well as sound: `den ρ a ≤ den ρ b` (for any — hence
    every — ρ) implies `leq a b = true`. Together with `leq_sound` this is the "agrees exactly
    with `≤` on concrete levels" claim (the byte-identical concrete fragment). -/
theorem closed_leq_complete :
    ∀ (a b : Level), wf a 0 = true → wf b 0 = true →
      den (fun _ => 0) a ≤ den (fun _ => 0) b → leq a b = true := by
  intro a
  induction a with
  | zero => intro b _ _ _; simp [leq]
  | max a1 a2 ih1 ih2 =>
    intro b ha hb h
    simp only [wf, Bool.and_eq_true] at ha
    simp only [den, Nat.max_le] at h
    simp only [leq, Bool.and_eq_true]
    exact ⟨ih1 b ha.1 hb h.1, ih2 b ha.2 hb h.2⟩
  | suc a1 ih =>
    intro b
    induction b with
    | zero =>
      intro _ _ h
      simp [den] at h
    | suc b1 ihb =>
      intro ha hb h
      simp only [den, Nat.succ_le_succ_iff] at h
      simp only [leq]
      exact ih b1 ha hb h
    | max b1 b2 ihb1 ihb2 =>
      intro ha hb h
      simp only [wf, Bool.and_eq_true] at hb
      simp only [den] at h
      simp only [leq, Bool.or_eq_true]
      rcases max_le_or (den (fun _ => 0) b1) (den (fun _ => 0) b2)
          (den (fun _ => 0) (suc a1)) h with h1 | h2
      · exact Or.inl (ihb1 ha hb.1 h1)
      · exact Or.inr (ihb2 ha hb.2 h2)
    | var v => intro _ hb _; simp [wf] at hb
  | var u =>
    intro b ha _ _
    simp [wf] at ha

end Level

-- House-style sorry-freedom receipts: each shipped theorem's axioms print at build time; the
-- acceptable set is `{propext, Classical.choice, Quot.sound}` (never `sorryAx`).
#print axioms Level.leq_sound
#print axioms Level.leq_refl
#print axioms Level.cumul_trans_sound
#print axioms Level.wf_weaken
#print axioms Level.wf_mono
#print axioms Level.max_sound
#print axioms Level.closed_den_const
#print axioms Level.closed_leq_complete

end BlightMeta
