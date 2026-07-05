/-
  The `{0, 1, ω}` resource semiring (spec §3.1), mirroring
  `crates/blight-kernel/src/semiring.rs` exactly (same three constructors, same `add`/`mul`
  pattern matches). This file mechanizes the algebraic laws that file only *spot-checks* by
  exhaustive unit tests (`addition_table`, `multiplication_table`, `units`, `positivity_law`,
  `zero_product_law`, `order`): here they are theorems, proved once and for all by `decide`
  over the (finite, `DecidableEq`) type `Grade`.
-/

namespace BlightMeta

/-- `0` = erased (no runtime use), `1` = linear (exactly once), `ω` = unrestricted. -/
inductive Grade where
  | zero
  | one
  | omega
  deriving DecidableEq, Repr

namespace Grade

/-- Resource demands combine (e.g. two uses). Matches `semiring.rs::Semiring::add` verbatim. -/
def add : Grade → Grade → Grade
  | zero, g => g
  | g, zero => g
  | _, _ => omega

/-- Application scales the argument's demand by the function's demand. Matches
    `semiring.rs::Semiring::mul` verbatim. -/
def mul : Grade → Grade → Grade
  | zero, _ => zero
  | _, zero => zero
  | one, g => g
  | g, one => g
  | omega, omega => omega

/-- The rank realizing the order `0 < 1 < ω` (`semiring.rs::Grade::rank`). -/
def rank : Grade → Nat
  | zero => 0
  | one => 1
  | omega => 2

/-- `ρ ≤ π`: the lattice order `0 ≤ 1 ≤ ω`, matching `semiring.rs::Semiring::leq`. -/
instance : LE Grade := ⟨fun g h => g.rank ≤ h.rank⟩

instance (g h : Grade) : Decidable (g ≤ h) :=
  inferInstanceAs (Decidable (g.rank ≤ h.rank))

@[simp] theorem le_def (g h : Grade) : (g ≤ h) = (g.rank ≤ h.rank) := rfl

-- ---- Exhaustive algebraic laws (spec §3.1), each a `decide` over the 3-element type. ----

/-- Mirrors `semiring::tests::addition_table`. -/
theorem addition_table :
    (zero.add zero = zero) ∧ (zero.add one = one) ∧ (zero.add omega = omega) ∧
    (one.add zero = one) ∧ (one.add one = omega) ∧ (one.add omega = omega) ∧
    (omega.add zero = omega) ∧ (omega.add one = omega) ∧ (omega.add omega = omega) := by
  decide

/-- Mirrors `semiring::tests::multiplication_table`. -/
theorem multiplication_table :
    (zero.mul zero = zero) ∧ (zero.mul one = zero) ∧ (zero.mul omega = zero) ∧
    (one.mul zero = zero) ∧ (one.mul one = one) ∧ (one.mul omega = omega) ∧
    (omega.mul zero = zero) ∧ (omega.mul one = omega) ∧ (omega.mul omega = omega) := by
  decide

theorem add_comm (g h : Grade) : g.add h = h.add g := by cases g <;> cases h <;> rfl

theorem add_assoc (g h k : Grade) : (g.add h).add k = g.add (h.add k) := by
  cases g <;> cases h <;> cases k <;> rfl

theorem mul_comm (g h : Grade) : g.mul h = h.mul g := by cases g <;> cases h <;> rfl

/-- Multiplication is idempotent on `{0,1,ω}` — the fact that makes a judgement's usage vector
    *absorb* its own ambient (`Weakening.lean`'s `usage_absorbs_ambient`). -/
theorem mul_idem (g : Grade) : g.mul g = g := by cases g <;> rfl

theorem mul_assoc (g h k : Grade) : (g.mul h).mul k = g.mul (h.mul k) := by
  cases g <;> cases h <;> cases k <;> rfl

theorem mul_add (g h k : Grade) : g.mul (h.add k) = (g.mul h).add (g.mul k) := by
  cases g <;> cases h <;> cases k <;> rfl

/-- Units: `0` is additive, `1` is multiplicative. Mirrors `semiring::tests::units`. -/
theorem zero_add (g : Grade) : zero.add g = g := by cases g <;> rfl

theorem add_zero (g : Grade) : g.add zero = g := by cases g <;> rfl

theorem one_mul (g : Grade) : one.mul g = g := by cases g <;> rfl

theorem mul_one (g : Grade) : g.mul one = g := by cases g <;> rfl

/-- Positivity: `ρ + π = 0 ⟹ ρ = 0 ∧ π = 0`. Mirrors `semiring::tests::positivity_law`,
    upgraded from a spot-check over the 3 × 3 table to a proof for all `g h`. -/
theorem positivity_law {g h : Grade} (hgh : g.add h = zero) : g = zero ∧ h = zero := by
  cases g <;> cases h <;> simp_all [add]

/-- Zero-product: `ρ · π = 0 ⟹ ρ = 0 ∨ π = 0`. Mirrors `semiring::tests::zero_product_law`. -/
theorem zero_product_law {g h : Grade} (hgh : g.mul h = zero) : g = zero ∨ h = zero := by
  cases g <;> cases h <;> simp_all [mul]

/-- The order is reflexive, and antisymmetric/transitive/total since it's `Nat.le` pulled back
    along an injection. Mirrors `semiring::tests::order`. -/
theorem le_refl (g : Grade) : g ≤ g := Nat.le_refl _

theorem le_trans {g h k : Grade} (hgh : g ≤ h) (hhk : h ≤ k) : g ≤ k := Nat.le_trans hgh hhk

theorem le_total (g h : Grade) : g ≤ h ∨ h ≤ g := Nat.le_total _ _

/-- **Monotonicity of `add`** (needed by the grade-demotion lemma in `Calculus.lean`): grading
    is a genuine ordered semiring, not just a bare algebra — scaling/combining demand can only
    move a grade *up* the `0 < 1 < ω` order, never around it. Not exercised by any Rust unit
    test (the kernel never needs it explicitly — it falls straight out of the graded typing
    rules' soundness argument) but implicitly relied on by §1.2's "usage is preserved [monotone]
    under reduction" sketch, which this mechanization makes precise (see
    `Calculus.usage_le_of_demote`). -/
theorem add_mono_left {g g' : Grade} (h : g ≤ g') (k : Grade) : g.add k ≤ g'.add k := by
  cases g <;> cases g' <;> cases k <;> simp_all [add, le_def, rank]

theorem add_mono_right (g : Grade) {k k' : Grade} (h : k ≤ k') : g.add k ≤ g.add k' := by
  cases g <;> cases k <;> cases k' <;> simp_all [add, le_def, rank]

/-- **Monotonicity of `mul`** in each argument — the fact that makes grade *demotion*
    (checking a term at a smaller ambient grade than it was originally checked at) sound: it is
    what §1.2 calls on when it says the layered/erasure reading is "exactly what standard
    metatheory predicts," generalized here from the flat "`0`-fragment is inert" observation to
    a real order-theoretic property of `·`. -/
theorem mul_mono_left {g g' : Grade} (h : g ≤ g') (k : Grade) : g.mul k ≤ g'.mul k := by
  cases g <;> cases g' <;> cases k <;> simp_all [mul, le_def, rank]

theorem mul_mono_right (g : Grade) {k k' : Grade} (h : k ≤ k') : g.mul k ≤ g.mul k' := by
  cases g <;> cases k <;> cases k' <;> simp_all [mul, le_def, rank]

/-- **`add` is inflationary**: combining more demand never *decreases* a grade. This is what lets
    the substitution lemma (`Substitution.lean`) split a bound on a *sum* of two subterms' usage
    (`T-app`/`T-ite`'s additive accounting) into a bound on each summand individually. -/
theorem self_le_add_left (g h : Grade) : g ≤ g.add h := by
  cases g <;> cases h <;> decide

theorem self_le_add_right (g h : Grade) : g ≤ h.add g := by
  cases g <;> cases h <;> decide

/-- **`ω` absorbs from below under `mul`**: scaling by the top grade never *shrinks* a grade.
    Needed by `demote_scaled` (`Weakening.lean`) to bound the `ω`-ambient case by the already-
    proved unscaled `demote`. -/
theorem self_le_mul_omega (g : Grade) : g ≤ omega.mul g := by
  cases g <;> decide

/-- `0` is the bottom of the order. -/
theorem zero_le (g : Grade) : zero ≤ g := by cases g <;> decide

/-- Right-distributivity of `mul` over `add` (the `mul_add` law with the scalar on the *other*
    side) — lets the substitution lemma (`Substitution.lean`) merge two branches' `scale`
    correction terms (`T-app`/`T-ite`'s summed sub-usages, each individually `scale`d by its own
    piece of the substituted slot's demand) back into a single `scale` by the combined demand. -/
theorem add_mul (g h k : Grade) : (g.add h).mul k = (g.mul k).add (h.mul k) := by
  rw [mul_comm (g.add h) k, mul_add, mul_comm k g, mul_comm k h]

end Grade

end BlightMeta
