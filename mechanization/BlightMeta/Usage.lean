/-
  Usage vectors (spec §3.2), mirroring `crates/blight-kernel/src/usage.rs` exactly: a `Usage` is
  a `List Grade` indexed innermost-first (slot `0` = most recently bound variable), with the same
  five operations (`zero`, `unit`, `add`, `scale`, `pop`/`extend`, `get`). `usage.rs`'s tests pin
  each operation's behavior on hand-picked examples; here the corresponding facts are theorems
  for *all* usage vectors, plus one new piece of algebra (`Le`, entrywise `≤`, and its
  monotonicity under `add`/`scale`) that `usage.rs` never needed but the grade-demotion lemma in
  `Calculus.lean` does. Every operation below is defined by plain structural recursion (rather
  than via `List.replicate`/`List.set`/`getD`) so its defining equations are `rfl` and every
  proof is a direct induction — no dependence on library `simp` sets for `List` indexing.
-/

import BlightMeta.Grade

namespace BlightMeta

abbrev Usage := List Grade

namespace Usage

/-- The all-`0` vector of length `n`. Mirrors `usage.rs::Usage::zero`. -/
def zero : Nat → Usage
  | 0 => []
  | n + 1 => Grade.zero :: zero n

/-- The unit vector `e_i` of length `n`: variable `i` demanded at `grade`, all others `0`.
    Mirrors `usage.rs::Usage::unit` (well-defined for `i < n`; for `i ≥ n` it degrades to
    `zero n`, which is never relied upon). -/
def unit : Nat → Nat → Grade → Usage
  | _, 0, _ => []
  | 0, n + 1, g => g :: zero n
  | i + 1, n + 1, g => Grade.zero :: unit i n g

/-- Entrywise sum. Mirrors `usage.rs::Usage::add`. -/
def add : Usage → Usage → Usage
  | [], _ => []
  | _ :: _, [] => []
  | g :: gs, h :: hs => g.add h :: add gs hs

/-- Scale every slot by `s`. Mirrors `usage.rs::Usage::scale`. -/
def scale (s : Grade) : Usage → Usage
  | [] => []
  | g :: gs => s.mul g :: scale s gs

/-- The demand on variable `i`, or `0` if out of range. Mirrors `usage.rs::Usage::get`. -/
def get : Usage → Nat → Grade
  | [], _ => Grade.zero
  | g :: _, 0 => g
  | _ :: gs, i + 1 => get gs i

@[simp] theorem length_zero (n : Nat) : (zero n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zero, ih]

theorem length_unit (i n : Nat) (g : Grade) (h : i < n) : (unit i n g).length = n := by
  induction i generalizing n with
  | zero => cases n with
    | zero => omega
    | succ n => simp [unit, length_zero]
  | succ i ih => cases n with
    | zero => omega
    | succ n => simp only [unit, List.length_cons, ih n (by omega)]

@[simp] theorem length_add (u v : Usage) : (add u v).length = min u.length v.length := by
  induction u generalizing v with
  | nil => simp [add]
  | cons g gs ih =>
    cases v with
    | nil => simp [add]
    | cons h hs => simp [add, ih]

@[simp] theorem length_scale (s : Grade) (u : Usage) : (scale s u).length = u.length := by
  induction u with
  | nil => rfl
  | cons g gs ih => simp [scale, ih]

/-- Mirrors `usage::tests::zero_is_additive_unit` (`u + 0 = u`, `0 + u = u`), for all `u`. -/
theorem add_zero (u : Usage) : add u (zero u.length) = u := by
  induction u with
  | nil => rfl
  | cons g gs ih => simp [zero, add, ih, Grade.add_zero]

theorem zero_add (u : Usage) : add (zero u.length) u = u := by
  induction u with
  | nil => rfl
  | cons g gs ih => simp [zero, add, ih, Grade.zero_add]

/-- Mirrors `usage::tests::add_is_entrywise_semiring`, generalized to all equal-length `u v`. -/
theorem add_comm (u v : Usage) (h : u.length = v.length) : add u v = add v u := by
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons _ _ => simp_all
  | cons g gs ih =>
    cases v with
    | nil => simp_all
    | cons h2 hs =>
      have hlen : gs.length = hs.length := by simpa using h
      simp [add, Grade.add_comm g h2, ih hs hlen]

/-- Mirrors `usage::tests::scale_zero_annihilates`. -/
theorem scale_zero (u : Usage) : scale Grade.zero u = zero u.length := by
  induction u with
  | nil => rfl
  | cons g gs ih =>
    have hg : Grade.zero.mul g = Grade.zero := by cases g <;> rfl
    simp only [scale, zero, List.length_cons, ih, hg]

/-- Mirrors `usage::tests::scale_one_identity`. -/
theorem scale_one (u : Usage) : scale Grade.one u = u := by
  induction u with
  | nil => rfl
  | cons g gs ih => simp [scale, ih, Grade.one_mul]

/-- Mirrors `usage::tests::unit_is_basis_vector`. -/
theorem get_unit_same (i n : Nat) (g : Grade) (h : i < n) : get (unit i n g) i = g := by
  induction i generalizing n with
  | zero => cases n with
    | zero => omega
    | succ n => rfl
  | succ i ih => cases n with
    | zero => omega
    | succ n => simp only [unit, get]; exact ih n (by omega)

/-- Summing two all-zero vectors of the same length gives an all-zero vector. -/
theorem add_zero_zero (n : Nat) : add (zero n) (zero n) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zero, add, Grade.add_zero, ih]

/-- Placing a `0` demand anywhere in an all-zero vector changes nothing — needed by
    `ambient_zero_usage` (`Weakening.lean`): the `Var` rule's unit contribution at ambient `σ = 0`
    is the all-zero vector, same as `zero`. -/
theorem unit_zero (i n : Nat) : unit i n Grade.zero = zero n := by
  induction i generalizing n with
  | zero => cases n with
    | zero => rfl
    | succ n => rfl
  | succ i ih => cases n with
    | zero => rfl
    | succ n => simp only [unit, zero]; congr 1; exact ih n

theorem get_zero (n i : Nat) : get (zero n) i = Grade.zero := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => cases i with
    | zero => rfl
    | succ i => simp [zero, get, ih]

theorem get_unit_other (i j n : Nat) (g : Grade) : i ≠ j → get (unit i n g) j = Grade.zero := by
  induction i generalizing n j with
  | zero =>
    intro h
    cases n with
    | zero => rfl
    | succ n =>
      cases j with
      | zero => exact absurd rfl h
      | succ j => simp only [unit, get]; exact get_zero n j
  | succ i ih =>
    intro h
    cases n with
    | zero => rfl
    | succ n =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [unit, get]
        have hij : i ≠ j := fun heq => h (heq ▸ rfl)
        exact ih j n hij

/-- Entrywise `≤`: `u` demands no more than `v` at any slot. Not present in `usage.rs` (the
    kernel never compares two usage vectors directly) — introduced here because it is exactly
    the invariant the grade-demotion lemma (`Calculus.lean`) needs to state "reduction never
    *increases* usage" precisely. -/
def Le : Usage → Usage → Prop
  | [], [] => True
  | g :: gs, h :: hs => g ≤ h ∧ Le gs hs
  | _, _ => False

theorem le_refl (u : Usage) : Le u u := by
  induction u with
  | nil => trivial
  | cons g gs ih => exact ⟨Grade.le_refl g, ih⟩

theorem le_trans {u v w : Usage} (huv : Le u v) (hvw : Le v w) : Le u w := by
  induction u generalizing v w with
  | nil => cases v <;> cases w <;> simp_all [Le]
  | cons g gs ih =>
    cases v with
    | nil => simp_all [Le]
    | cons h hs =>
      cases w with
      | nil => simp_all [Le]
      | cons k ks =>
        obtain ⟨hgh, hgs⟩ := huv
        obtain ⟨hhk, hhs⟩ := hvw
        exact ⟨Grade.le_trans hgh hhk, ih hgs hhs⟩

/-- `add` is monotone in each argument w.r.t. `Le` — needed to combine the two branches (`f` and
    `a`, or the three branches of `ite`) of the demotion/substitution lemmas in `Calculus.lean`. -/
theorem add_mono {u u' v v' : Usage} (hu : Le u u') (hv : Le v v') :
    Le (add u v) (add u' v') := by
  induction u generalizing u' v v' with
  | nil =>
    cases u' with
    | nil => cases v <;> cases v' <;> simp_all [Le, add]
    | cons => simp_all [Le]
  | cons g gs ih =>
    cases u' with
    | nil => simp_all [Le]
    | cons g' gs' =>
      obtain ⟨hgg', hgsgs'⟩ := hu
      cases v with
      | nil =>
        cases v' with
        | nil => simp_all [add]
        | cons => simp_all [Le]
      | cons h hs =>
        cases v' with
        | nil => simp_all [Le]
        | cons h' hs' =>
          obtain ⟨hhh', hhshs'⟩ := hv
          refine ⟨Grade.le_trans (Grade.add_mono_left hgg' h) (Grade.add_mono_right g' hhh'), ?_⟩
          exact ih hgsgs' hhshs'

/-- `scale` is monotone (in the vector argument; the semiring's fixed scale factor is a
    constant here, matching how a `check_g` call's ambient σ is fixed for a given check). -/
theorem scale_mono {s : Grade} {u u' : Usage} (h : Le u u') : Le (scale s u) (scale s u') := by
  induction u generalizing u' with
  | nil => cases u' <;> simp_all [Le, scale]
  | cons g gs ih =>
    cases u' with
    | nil => simp_all [Le]
    | cons g' gs' =>
      obtain ⟨hgg', hgsgs'⟩ := h
      exact ⟨Grade.mul_mono_right s hgg', ih hgsgs'⟩

/-- `get` commutes with `add`, for equal-length vectors (always the case here — both summands
    come from `HasType` derivations over the same context, `usage_length`) — needed to split a
    bound on `(add u v).get i` into individual bounds on `u.get i` and `v.get i`
    (`Substitution.lean`'s `app`/`ite` cases). -/
theorem get_add {u v : Usage} (hlen : u.length = v.length) (i : Nat) :
    get (add u v) i = (get u i).add (get v i) := by
  induction u generalizing v i with
  | nil => cases v with
    | nil => cases i <;> rfl
    | cons _ _ => simp_all
  | cons g gs ih =>
    cases v with
    | nil => simp_all
    | cons h vs =>
      have hlen' : gs.length = vs.length := by simpa using hlen
      cases i with
      | zero => rfl
      | succ i => simp only [add, get]; exact ih hlen' i

/-- `get` commutes with `scale` — the pointwise fact `demote_scaled`'s callers (the substitution
    lemma) need to unpack a whole-vector `scale`d bound into a bound on one particular slot. -/
theorem get_scale (s : Grade) (u : Usage) (i : Nat) : get (scale s u) i = s.mul (get u i) := by
  induction u generalizing i with
  | nil => cases i <;> cases s <;> rfl
  | cons g gs ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [scale, get]; exact ih i

/-- Scaling by `ω` never shrinks a vector (pointwise `self_le_mul_omega`, lifted to `Le`). -/
theorem le_scale_omega (u : Usage) : Le u (scale Grade.omega u) := by
  induction u with
  | nil => trivial
  | cons g gs ih => exact ⟨Grade.self_le_mul_omega g, ih⟩

/-- `scale` is monotone in the *grade* argument (pointwise `mul_mono_left`, lifted): scaling by a
    smaller demand keeps the vector below. This is the M-A.1 bound's workhorse — a β-redex charges
    the argument's usage at the body's binder demand `δ`, and `δ ≤ σ·ρ` caps it. -/
theorem scale_le_scale {s s' : Grade} (h : s ≤ s') (u : Usage) :
    Le (scale s u) (scale s' u) := by
  induction u with
  | nil => trivial
  | cons g gs ih => exact ⟨Grade.mul_mono_left h g, ih⟩

/-- The left summand sits below the sum (pointwise `self_le_add_left`), for equal lengths. -/
theorem le_add_self_left {u v : Usage} (hlen : u.length = v.length) : Le u (add u v) := by
  induction u generalizing v with
  | nil => cases v with
    | nil => trivial
    | cons _ _ => simp at hlen
  | cons g gs ih =>
    cases v with
    | nil => simp at hlen
    | cons h hs =>
      exact ⟨Grade.self_le_add_left g h, ih (by simpa using hlen)⟩

/-- The right summand sits below the sum (pointwise `self_le_add_right`), for equal lengths. -/
theorem le_add_self_right {u v : Usage} (hlen : u.length = v.length) : Le v (add u v) := by
  induction u generalizing v with
  | nil => cases v with
    | nil => trivial
    | cons _ _ => simp at hlen
  | cons g gs ih =>
    cases v with
    | nil => simp at hlen
    | cons h hs =>
      exact ⟨Grade.self_le_add_right h g, ih (by simpa using hlen)⟩

/-- `scale` distributes over `add` (the semiring's `mul_add`, lifted entrywise). -/
theorem scale_add (s : Grade) (u v : Usage) :
    scale s (add u v) = add (scale s u) (scale s v) := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons g gs ih =>
    cases v with
    | nil => rfl
    | cons h hs => simp only [add, scale, Grade.mul_add, ih]

/-- Composed scalings multiply (the semiring's `mul_assoc`, lifted entrywise). -/
theorem scale_scale (s t : Grade) (u : Usage) : scale s (scale t u) = scale (s.mul t) u := by
  induction u with
  | nil => rfl
  | cons g gs ih => simp only [scale, Grade.mul_assoc, ih]

/-- Scaling the zero vector is the zero vector (`g·0 = 0` entrywise). -/
theorem scale_zero_vec (s : Grade) (n : Nat) : scale s (zero n) = zero n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : s.mul Grade.zero = Grade.zero := by cases s <;> rfl
    simp only [zero, scale, this, ih]

/-- Scaling a unit vector scales its one live entry. -/
theorem scale_unit (s : Grade) (i n : Nat) (g : Grade) :
    scale s (unit i n g) = unit i n (s.mul g) := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    cases i with
    | zero => simp only [unit, scale, scale_zero_vec]
    | succ i =>
      have : s.mul Grade.zero = Grade.zero := by cases s <;> rfl
      simp only [unit, scale, this, ih]

/-- The converse of `le_get`: for equal-length vectors, agreeing pointwise at every slot is enough
    to conclude `Le`. Lets the substitution lemma build a whole-vector bound out of a per-index
    case analysis (the `var`-hits-the-substituted-slot case, where the comparison naturally
    splits on how a given slot's position relates to the substitution site). -/
theorem le_of_forall_get {u v : Usage} (hlen : u.length = v.length)
    (h : ∀ i, get u i ≤ get v i) : Le u v := by
  induction u generalizing v with
  | nil => cases v with
    | nil => trivial
    | cons _ _ => simp_all
  | cons g gs ih =>
    cases v with
    | nil => simp_all
    | cons g' gs' =>
      have hlen' : gs.length = gs'.length := by simpa using hlen
      refine ⟨h 0, ih hlen' fun i => ?_⟩
      have := h (i + 1)
      simpa [get] using this

theorem le_add_left {u v : Usage} (hlen : u.length = v.length) : Le u (add u v) := by
  induction u generalizing v with
  | nil => cases v with
    | nil => trivial
    | cons _ _ => simp_all
  | cons g gs ih =>
    cases v with
    | nil => simp_all
    | cons h hs =>
      have hlen' : gs.length = hs.length := by simpa using hlen
      exact ⟨Grade.self_le_add_left g h, ih hlen'⟩

/-- A unit basis vector's `≤` is exactly the grade comparison at its one nonzero slot. -/
theorem unit_le {i n : Nat} {g h : Grade} (hgh : g ≤ h) : Le (unit i n g) (unit i n h) := by
  induction i generalizing n with
  | zero => cases n with
    | zero => trivial
    | succ n => exact ⟨hgh, le_refl _⟩
  | succ i ih => cases n with
    | zero => trivial
    | succ n => exact ⟨Grade.le_refl _, ih⟩

/-- `Le` implies pointwise `≤` at every slot — the projection the substitution lemma's `lam` case
    needs to extract "the fresh binder's demand didn't grow" from a whole-vector bound. -/
theorem le_get {u v : Usage} (h : Le u v) (i : Nat) : get u i ≤ get v i := by
  induction u generalizing v i with
  | nil => cases v with
    | nil => cases i <;> exact Grade.le_refl _
    | cons _ _ => simp_all [Le]
  | cons g gs ih =>
    cases v with
    | nil => simp_all [Le]
    | cons h hs =>
      obtain ⟨hgh, hgshs⟩ := h
      cases i with
      | zero => exact hgh
      | succ i => exact ih hgshs i

/-- Associativity of `add`, for pairwise-equal-length vectors (always the case here) — needed to
    regroup a four-way sum (`T-app`'s two summands, each already itself a sum after substitution)
    into the shape the target bound expects. -/
theorem add_assoc (u v w : Usage) (huv : u.length = v.length) (hvw : v.length = w.length) :
    add (add u v) w = add u (add v w) := by
  induction u generalizing v w with
  | nil => cases v with
    | nil => cases w with
      | nil => rfl
      | cons _ _ =>
        simp only [List.length_nil, List.length_cons] at hvw; omega
    | cons _ _ =>
      simp only [List.length_nil, List.length_cons] at huv; omega
  | cons g gs ih =>
    cases v with
    | nil =>
      simp only [List.length_cons, List.length_nil] at huv; omega
    | cons h hs =>
      cases w with
      | nil =>
        simp only [List.length_cons, List.length_nil] at hvw; omega
      | cons k ks =>
        have huv' : gs.length = hs.length := by simpa using huv
        have hvw' : hs.length = ks.length := by simpa using hvw
        simp only [add, Grade.add_assoc, ih hs ks huv' hvw']

/-- `scale` distributes over `add` on its *grade* argument (the semiring scalar), the companion to
    `Grade.mul_add` (which distributes over the *vector* argument): summing two occurrences'
    worth of scaling by `g` and by `h` is the same as scaling once by `g + h`. Needed by the
    substitution lemma to merge two branches' correction terms. -/
theorem scale_add_grade (g h : Grade) (x : Usage) :
    add (scale g x) (scale h x) = scale (g.add h) x := by
  induction x with
  | nil => rfl
  | cons y ys ih => simp only [scale, add, ih, Grade.add_mul]

theorem le_zero (u : Usage) : Le (zero u.length) u := by
  induction u with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨?_, ih⟩
    show Grade.zero ≤ g
    cases g <;> decide

end Usage

end BlightMeta
