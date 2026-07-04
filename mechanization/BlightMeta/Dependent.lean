/-
  Wave 8 / M9: broadening the mechanized fragment toward the real (dependently-typed) kernel.

  `Calculus.lean`'s `Ty`/`Tm` split is *structurally* non-dependent: `Ty` never mentions `Tm` at
  all, so a Π-type's codomain can't reference the value its domain binds — a real restriction
  relative to `crates/blight-kernel`'s actual `Value`, which is genuinely dependent. This file
  develops a second, independent core (`Expr`, `HasType` below) with a *bona fide* dependent
  Π-type, re-proving the same shape of metatheory (`weaken`, the substitution lemma, `progress`,
  `preservation`) the roadmap's M9 item asks for, using the exact same graded (`{0,1,ω}`) judgement
  style as `Calculus.lean` (grades are position-indexed bookkeeping over `Usage`, entirely
  orthogonal to whether the calculus is dependent — nothing about `Grade.lean`/`Usage.lean` needs
  to change).

  ── Why a new file instead of extending `Calculus.lean` in place ────────────────────────────────
  A dependent Π's codomain must be able to contain a *term* (the bound variable, at least), which
  `Calculus.lean`'s `Ty`/`Tm` split forbids by construction (see that file's own module doc: "a
  context here is just `List Ty`" — deliberately, because `Ty` never varies with a `Tm`). Making
  the codomain genuinely dependent therefore requires unifying types and terms into one syntax
  (`Expr` below, the standard PTS/LF-style presentation), which is a different grammar from
  `Calculus.lean`'s, not an in-place extension of it. `Calculus.lean` itself, and everything built
  on it (M5's Kan formers, M8's SN/canonicity), is left completely untouched.

  ── Scope, honestly bounded (matches this repo's existing go-bar discipline) ─────────────────────
  This file mechanizes dependent **Π only**. Two further steps the plan's own text lists ("Pi/Sigma
  then PathP") are *not* attempted here, for a precise, load-bearing reason rather than a vague
  "ran out of time":

  * **Dependent `Σ`** needs a `snd`-style eliminator whose declared result type mentions the *first*
    projection of its own scrutinee (`B[fst p / 0]`). Preservation's `snd`/`hcomp`-style β-case then
    needs `B[fst (pair a b) / 0]` and `B[a / 0]` to be interchangeable — but `fst (pair a b)` and
    `a` are only *reduction-related* (`Step (.fst (.pair a b)) a`), not syntactically identical, so
    closing that gap needs a genuine definitional-equality/conversion relation threaded through
    `HasType` (a `conv` rule plus its own congruence-closure metatheory: substitution-stability,
    compatibility with weakening, etc.). Dependent `Π`'s β-case has no analogous gap — `app (lam
    body) a`'s type is *already* `B[a/0]` by `HasType.app`'s own rule, matching what stepping
    produces with zero extra machinery — which is precisely why `Π` alone is tractable at this pass
    and `Σ` is a real, separately-scoped follow-up (needs the conversion relation as its own
    prerequisite, not a small add-on).
  * **`PathP`** needs an actual interval type with computation rules up to a real definitional
    equality (the fully heterogeneous cubical corner M7 already scoped out of `Calculus.lean` for
    exactly this reason) — strictly harder than `Σ`, so it inherits the same blocker plus more.

  Grading the dependent core, by contrast, needed *no* extra machinery relative to `Calculus.lean`
  (see `HasType` below: the `app`/`lam` rules are a verbatim port, `Usage`/`Grade` don't change at
  all) — matching the plan's own division of labor, where the *grade-skeleton* question is
  Wave 8's separate M10 item, not M9's.

  ── What this file proves, and what it honestly leaves open ─────────────────────────────────────
  Fully proved (no `sorry`), for the dependent-`Π` fragment above:
  * The substitution algebra (`shiftBy`/`subst`/`subst0`) and its composition lemmas
    (`shiftBy_shiftBy_le`/`_add`, and the two shift/substitution commutation halves
    `shiftBy_subst_lt`/`_ge` — the standard de Bruijn "shift commutes with substitution" fact,
    TAPL §6.2.5, needed here because a dependent `Π`'s *type* component, not just its term, must
    shift correctly under weakening).
  * The dependent context operations `ctxGet`/`ctxInsert` (rebasing-aware lookup/insertion) and
    their full interaction lemmas.
  * `HasType.weaken`: inserting a fresh, unused binder anywhere in the context preserves
    typability, shifting *both* the term and its type — the genuinely new content relative to
    `Weakening.lean`'s non-dependent `weaken` (there, types never shift at all).
  * `progress`: a closed, well-typed term is a value or can step (needs no substitution lemma, by
    the same canonical-forms argument `Progress.lean` uses).

  **Landed since (P2, 1/2)**: the companion **substitution/substitution commutation** fact the
  substitution lemma's inductive proof needs — `Expr.subst_subst_comm` (with its cancellation helper
  `subst_shiftBy1_cancel`/`subst_shiftAbove_cancel`), below in `namespace Expr`. This was the "next
  rung of the ladder" past `weaken`'s own `shiftBy_subst_lt`/`_ge`: it says `subst i s (subst j a e)`
  and `subst j (subst i s a) (subst (i+1) (shiftAbove j s) e)` agree for `j ≤ i`, which is exactly
  what the substitution lemma's `app` case needs to line up `subst i s (subst0 a B)` (since
  `HasType.app` concludes at `Expr.subst0 a B`) with `subst0`'s shape. Every case discharges from the
  already-proven `shiftBy_subst_ge` + `shiftBy_shiftBy_le`; `#print axioms` shows it rests on
  `[propext, Quot.sound]` only.

  **Still not attempted here (P2, 2/2)**: the general substitution lemma (`Substitution.lean`'s
  `subst_lemma` analogue over `Expr`) and, consequently, `preservation`. With the commutation fact in
  hand the remaining gap is precisely characterized (no longer a vague "next rung"): unlike the
  non-dependent `subst_lemma`, whose conclusion keeps the type `B` fixed, the dependent one must
  substitute the *type* too (`subst k a B`), which forces the `var` rule's three index subcases to
  reason about the context entry's type — `i < k` cancels via `subst_shiftAbove_cancel` (proved),
  `i = k` reads back `ctxGet_insert_eq`'s `shiftBy (k+1) 0 A'` and needs the substituted term at the
  *lifted* type `shiftBy k 0 A'`, and `i > k` needs a fresh "senior-entry" lemma (a `ctxGet` result
  at index `i` structurally has every free variable `≥ i+1`, so substituting at any `k ≤ i` under one
  `shiftAbove 0` is the identity). Those, plus porting `Substitution.lean`'s `Usage.Le`/`insertUsage`/
  `scale` bookkeeping verbatim (usage vectors don't depend on `Expr`), close it — a bounded but
  genuinely separate effort, cleanly separable from `weaken`/`progress`/`subst_subst_comm` above and
  tracked as P2's second half, per the "state the honest boundary, don't fake it" discipline
  `docs/design-wave4-gobars.md` uses (and the roadmap's own precedent of gating SN/canonicity on
  M5+M6 landing first).
-/

import BlightMeta.Weakening

namespace BlightMeta
namespace Dep

/-- Unified syntax for terms *and* types: a dependent `Π`'s codomain must be able to mention the
    value its domain binds, which requires types and terms to share one de Bruijn scope (the
    standard PTS/LF presentation) — see the module doc for why this can't just extend
    `Calculus.lean`'s `Ty`/`Tm` split. No separate "kind"/universe former is needed: exactly like
    `Calculus.lean`'s `Ty` is never itself typechecked, an `Expr` used in classifier position here
    is taken on faith to be a type, with no well-formedness judgement over it — the same lightness
    of touch, just now shared syntax. -/
inductive Expr where
  | var (i : Nat)
  | bool
  | tt
  | ff
  | ite (c t e : Expr)
  | pi (rho : Grade) (dom cod : Expr)
  | lam (body : Expr)
  | app (f a : Expr)
  deriving DecidableEq, Repr

namespace Expr

/-- Shift by `n` every free variable `≥ c`. Generalizing over the shift amount `n` (rather than
    always `1`, as `Calculus.lean`'s `Tm.shiftAbove` does) is what makes the shift-composition
    algebra below (`shiftBy_shiftBy_le`) provable by one clean induction instead of needing a
    separate "iterate `shiftAbove` n times" bridging lemma. -/
def shiftBy (n c : Nat) : Expr → Expr
  | var i => if i < c then var i else var (i + n)
  | bool => bool
  | tt => tt
  | ff => ff
  | ite cnd t e => ite (shiftBy n c cnd) (shiftBy n c t) (shiftBy n c e)
  | pi rho dom cod => pi rho (shiftBy n c dom) (shiftBy n (c + 1) cod)
  | lam body => lam (shiftBy n (c + 1) body)
  | app f a => app (shiftBy n c f) (shiftBy n c a)

/-- The one-variable case, matching `Calculus.lean`'s `Tm.shiftAbove` exactly (a fresh binder
    inserted at depth `c`). -/
def shiftAbove (c : Nat) (e : Expr) : Expr := shiftBy 1 c e

/-- Capture-avoiding substitution, unified over both term and type positions (an `Expr` used as a
    type may itself contain a substitutable variable, e.g. `Π`'s codomain). Identical shape to
    `Calculus.lean`'s `Tm.subst`. -/
def subst (j : Nat) (s : Expr) : Expr → Expr
  | var i => if i = j then s else if i > j then var (i - 1) else var i
  | bool => bool
  | tt => tt
  | ff => ff
  | ite cnd t e => ite (subst j s cnd) (subst j s t) (subst j s e)
  | pi rho dom cod => pi rho (subst j s dom) (subst (j + 1) (shiftAbove 0 s) cod)
  | lam body => lam (subst (j + 1) (shiftAbove 0 s) body)
  | app f a => app (subst j s f) (subst j s a)

def subst0 (s e : Expr) : Expr := subst 0 s e

/-- **Shift commutation**, the load-bearing arithmetic fact behind every context-shifting lemma
    below: inserting `n1` fresh variables at depth `c1`, *then* `n2` more at depth `c2` (measured
    in the already-`n1`-shifted term) is the same as inserting the `n2` block first at its
    pre-`n1`-shift position `c2`, then the `n1` block at `c1` — provided `c1 ≤ c2`, i.e. the first
    insertion happens at or before the second. This is the standard de Bruijn "two insertions
    commute" fact (e.g. underlying `Calculus.lean`'s `Substitution.lean` `lam` case's `weaken 0`
    call, there trivial only because `Ty` never contains a shiftable variable); here it has to be
    proved once, generally, since `Expr`'s dependent `pi`/`lam` cases route it through the exact
    same case analysis that `Reducibility.lean`'s `subst_comm` used for `Tm.subst`. -/
theorem shiftBy_shiftBy_le (e : Expr) :
    ∀ {n1 c1 n2 c2 : Nat}, c1 ≤ c2 →
    shiftBy n1 c1 (shiftBy n2 c2 e) = shiftBy n2 (c2 + n1) (shiftBy n1 c1 e) := by
  induction e with
  | var i =>
    intro n1 c1 n2 c2 h
    by_cases hA : i < c1
    · have hB : i < c2 := by omega
      simp only [shiftBy, if_pos hA, if_pos hB, if_pos (by omega : i < c2 + n1)]
    · by_cases hB : i < c2
      · simp only [shiftBy, if_neg hA, if_pos hB, if_pos (by omega : i + n1 < c2 + n1)]
      · simp only [shiftBy, if_neg hA, if_neg hB, if_neg (by omega : ¬ i + n2 < c1),
          if_neg (by omega : ¬ i + n1 < c2 + n1)]
        congr 1
        omega
  | bool => intro n1 c1 n2 c2 _; rfl
  | tt => intro n1 c1 n2 c2 _; rfl
  | ff => intro n1 c1 n2 c2 _; rfl
  | ite c t e ihc iht ihe =>
    intro n1 c1 n2 c2 h
    simp only [shiftBy, ihc h, iht h, ihe h]
  | pi rho dom cod ihdom ihcod =>
    intro n1 c1 n2 c2 h
    simp only [shiftBy, ihdom h, ihcod (by omega : c1 + 1 ≤ c2 + 1)]
    congr 2
    omega
  | lam body ihbody =>
    intro n1 c1 n2 c2 h
    simp only [shiftBy, ihbody (by omega : c1 + 1 ≤ c2 + 1)]
    congr 2
    omega
  | app f a ihf iha =>
    intro n1 c1 n2 c2 h
    simp only [shiftBy, ihf h, iha h]

/-- Two shifts anchored at the *same* threshold compose by adding their amounts — the special
    case of shift composition `ctxGet`'s own recursive rebasing repeatedly instantiates (every
    step is `shiftAbove 0`, i.e. `c1 = c2 = 0` always), needed to relate `ctxGet`'s amount at one
    position to its neighbor's. -/
theorem shiftBy_shiftBy_add (e : Expr) (n1 n2 c : Nat) :
    shiftBy n1 c (shiftBy n2 c e) = shiftBy (n1 + n2) c e := by
  induction e generalizing c with
  | var i =>
    by_cases hic : i < c
    · simp only [shiftBy, if_pos hic]
    · simp only [shiftBy, if_neg hic, if_neg (by omega : ¬ i + n2 < c)]
      congr 1
      omega
  | bool => rfl
  | tt => rfl
  | ff => rfl
  | ite cnd t e ihcnd iht ihe => simp only [shiftBy, ihcnd, iht, ihe]
  | pi rho dom cod ihdom ihcod => simp only [shiftBy, ihdom, ihcod]
  | lam body ihbody => simp only [shiftBy, ihbody]
  | app f a ihf iha => simp only [shiftBy, ihf, iha]

/-- Small `var`-case unfolding lemmas for `subst`/`shiftBy`, factored out so the shift/substitution
    commutation proofs below can proceed by plain `rw` chains instead of fighting `simp`'s
    normalization of the `Nat`-equality/`Nat`-comparison decision procedures embedded in `subst`'s
    and `shiftBy`'s `ite`s. -/
theorem subst_var_eq (j : Nat) (s : Expr) : subst j s (var j) = s := by
  simp [subst]

theorem subst_var_gt {i j : Nat} (h : i > j) (s : Expr) : subst j s (var i) = var (i - 1) := by
  have h1 : i ≠ j := by omega
  simp [subst, h1, h]

theorem subst_var_lt {i j : Nat} (h : i < j) (s : Expr) : subst j s (var i) = var i := by
  have h1 : i ≠ j := by omega
  have h2 : ¬ i > j := by omega
  simp [subst, h1, h2]

theorem shiftBy_var_lt {i c : Nat} (h : i < c) (n : Nat) : shiftBy n c (var i) = var i := by
  simp [shiftBy, h]

theorem shiftBy_var_ge {i c : Nat} (h : c ≤ i) (n : Nat) : shiftBy n c (var i) = var (i + n) := by
  have h1 : ¬ i < c := by omega
  simp [shiftBy, h1]

/-- `shiftAbove`-headed restatements of `shiftBy_var_lt`/`shiftBy_var_ge`, needed because `rw`
    matches syntactically: a goal displayed via the `shiftAbove` abbreviation won't unify with a
    lemma stated over raw `shiftBy`, even though the two are definitionally equal. -/
theorem shiftAbove_var_lt {i c : Nat} (h : i < c) : shiftAbove c (var i) = var i :=
  shiftBy_var_lt h 1

theorem shiftAbove_var_ge {i c : Nat} (h : c ≤ i) : shiftAbove c (var i) = var (i + 1) :=
  shiftBy_var_ge h 1

/-- **Shift/substitution commutation, `j` strictly below the shift threshold `c`**: substituting
    at a position more local than where the shift starts leaves the substitution index `j`
    unchanged, shifts the substitute `s` at the *same* threshold `c` the whole term shifts at, and
    shifts the term `e` being substituted into one deeper (`c + 1`, since from `e`'s own
    perspective, position `j` is still a real binder at this point). This and `subst_shift_ge`
    below are the two halves of the standard de Bruijn "shift commutes with substitution" fact
    (e.g. TAPL §6.2.5), needed by `weaken`'s `app` case: `HasType.app`'s conclusion type
    `Expr.subst0 a B` must shift compatibly with weakening for the metatheory to go through. -/
theorem shiftBy_subst_lt (e : Expr) : ∀ (n c j : Nat) (s : Expr), j ≤ c →
    shiftBy n c (subst j s e) = subst j (shiftBy n c s) (shiftBy n (c + 1) e) := by
  induction e with
  | var i =>
    intro n c j s h
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · rw [subst_var_lt hij, shiftBy_var_lt (by omega : i < c),
        shiftBy_var_lt (by omega : i < c + 1), subst_var_lt hij]
    · subst hij
      rw [subst_var_eq, shiftBy_var_lt (by omega : i < c + 1), subst_var_eq]
    · rcases Nat.lt_or_ge (i - 1) c with hic | hic
      · rw [subst_var_gt hij, shiftBy_var_lt hic, shiftBy_var_lt (by omega : i < c + 1),
          subst_var_gt hij]
      · rw [subst_var_gt hij, shiftBy_var_ge hic, shiftBy_var_ge (by omega : c + 1 ≤ i),
          subst_var_gt (by omega : i + n > j)]
        congr 1
        omega
  | bool => intro n c j s _; rfl
  | tt => intro n c j s _; rfl
  | ff => intro n c j s _; rfl
  | ite cnd t e ihc iht ihe =>
    intro n c j s h
    simp only [subst, shiftBy, ihc n c j s h, iht n c j s h, ihe n c j s h]
  | pi rho dom cod ihdom ihcod =>
    intro n c j s h
    have hcod := ihcod n (c + 1) (j + 1) (shiftAbove 0 s) (by omega)
    have hswap : shiftBy n (c + 1) (shiftAbove 0 s) = shiftAbove 0 (shiftBy n c s) :=
      (shiftBy_shiftBy_le s (Nat.zero_le c)).symm
    simp only [subst, shiftBy, ihdom n c j s h, hcod, hswap]
  | lam body ihbody =>
    intro n c j s h
    have hbody := ihbody n (c + 1) (j + 1) (shiftAbove 0 s) (by omega)
    have hswap : shiftBy n (c + 1) (shiftAbove 0 s) = shiftAbove 0 (shiftBy n c s) :=
      (shiftBy_shiftBy_le s (Nat.zero_le c)).symm
    simp only [subst, shiftBy, hbody, hswap]
  | app f a ihf iha =>
    intro n c j s h
    simp only [subst, shiftBy, ihf n c j s h, iha n c j s h]

/-- **Shift/substitution commutation, `j` at or above the shift threshold `c`**: the dual of
    `shiftBy_subst_lt` — here the substitution index itself grows by the shift amount `n`, while
    both `s` and `e` shift at the *same* threshold `c` (unlike the `lt` case, `e`'s threshold does
    *not* increment: position `j` is no longer "below" `c`, so shifting `e` at `c` already reaches
    exactly the same variables `subst j s e`'s own recursion would touch). -/
theorem shiftBy_subst_ge (e : Expr) : ∀ (n c j : Nat) (s : Expr), c ≤ j →
    shiftBy n c (subst j s e) = subst (j + n) (shiftBy n c s) (shiftBy n c e) := by
  induction e with
  | var i =>
    intro n c j s h
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · rcases Nat.lt_or_ge i c with hic | hic
      · rw [subst_var_lt hij, shiftBy_var_lt hic, subst_var_lt (by omega : i < j + n)]
      · rw [subst_var_lt hij, shiftBy_var_ge hic, subst_var_lt (by omega : i + n < j + n)]
    · subst hij
      rw [subst_var_eq, shiftBy_var_ge h, subst_var_eq]
    · rw [subst_var_gt hij, shiftBy_var_ge (by omega : c ≤ i - 1),
        show shiftBy n c (var i) = var (i + n) from shiftBy_var_ge (by omega : c ≤ i) n,
        subst_var_gt (by omega : i + n > j + n)]
      congr 1
      omega
  | bool => intro n c j s _; rfl
  | tt => intro n c j s _; rfl
  | ff => intro n c j s _; rfl
  | ite cnd t e ihc iht ihe =>
    intro n c j s h
    simp only [subst, shiftBy, ihc n c j s h, iht n c j s h, ihe n c j s h]
  | pi rho dom cod ihdom ihcod =>
    intro n c j s h
    have hcod := ihcod n (c + 1) (j + 1) (shiftAbove 0 s) (by omega)
    have hswap : shiftBy n (c + 1) (shiftAbove 0 s) = shiftAbove 0 (shiftBy n c s) :=
      (shiftBy_shiftBy_le s (Nat.zero_le c)).symm
    simp only [subst, shiftBy, ihdom n c j s h, hcod, hswap]
    congr 2
    omega
  | lam body ihbody =>
    intro n c j s h
    have hbody := ihbody n (c + 1) (j + 1) (shiftAbove 0 s) (by omega)
    have hswap : shiftBy n (c + 1) (shiftAbove 0 s) = shiftAbove 0 (shiftBy n c s) :=
      (shiftBy_shiftBy_le s (Nat.zero_le c)).symm
    simp only [subst, shiftBy, hbody, hswap]
    congr 2
    omega
  | app f a ihf iha =>
    intro n c j s h
    simp only [subst, shiftBy, ihf n c j s h, iha n c j s h]

/-- `subst0`-specialized shift commutation: the exact fact `weaken`'s `app` case needs, since
    `HasType.app`'s conclusion type is `Expr.subst0 a B`, not a bare type. Always in the
    `shiftBy_subst_lt` regime (`j = 0 ≤ c`, for any `c`) — note the codomain shifts one deeper
    (`c + 1`) than the argument (`c`), since `B` still has its own binder in scope. -/
theorem shiftAbove_subst0 (c : Nat) (a B : Expr) :
    shiftAbove c (subst0 a B) = subst0 (shiftAbove c a) (shiftAbove (c + 1) B) := by
  unfold shiftAbove subst0
  exact shiftBy_subst_lt B 1 c 0 a (Nat.zero_le c)

/-- **Substituting at a freshly-inserted binder's own threshold is the identity.** `shiftBy 1 c`
    moves every variable out of slot `c` (to `< c` or `> c`), so `subst c s` finds no occurrence to
    replace and the surviving `> c` variables shift back down by one — undoing the insertion exactly.
    The `c`-below-the-substituted-slot case of the substitution-commutation lemma needs this to see a
    shifted-then-substituted subterm return unchanged. -/
theorem subst_shiftBy1_cancel : ∀ (e : Expr) (c : Nat) (s : Expr),
    subst c s (shiftBy 1 c e) = e := by
  intro e
  induction e with
  | var i =>
    intro c s
    by_cases h : i < c
    · rw [shiftBy_var_lt h, subst_var_lt h]
    · rw [shiftBy_var_ge (by omega : c ≤ i), subst_var_gt (by omega : i + 1 > c), Nat.add_sub_cancel]
  | bool => intro c s; rfl
  | tt => intro c s; rfl
  | ff => intro c s; rfl
  | ite cnd t e ihc iht ihe => intro c s; simp only [shiftBy, subst, ihc, iht, ihe]
  | pi rho dom cod ihd ihc => intro c s; simp only [shiftBy, subst, ihd, ihc]
  | lam body ih => intro c s; simp only [shiftBy, subst, ih]
  | app f a ihf iha => intro c s; simp only [shiftBy, subst, ihf, iha]

/-- `shiftAbove`-headed restatement of `subst_shiftBy1_cancel` (`shiftAbove c = shiftBy 1 c`),
    needed because `rw` matches syntactically. -/
theorem subst_shiftAbove_cancel (c : Nat) (s e : Expr) : subst c s (shiftAbove c e) = e :=
  subst_shiftBy1_cancel e c s

/-- **Substitution/substitution commutation** — the "next rung of the ladder" the module doc names
    as the missing prerequisite for the dependent substitution lemma. Substituting at an outer index
    `i` after an inner index `j ≤ i` commutes with substituting at `j` after `i`, up to the standard
    de Bruijn reindexing: the inner substitute `a` gains the outer substitution (`subst i s a`), the
    outer substitute `s` shifts past the inner binder (`shiftAbove j s`), and the outer index steps
    up by one (`i + 1`). This is exactly the identity the substitution lemma's `app` case needs to
    line up `subst i s (subst0 a B)` (the substituted codomain, since `HasType.app` concludes at
    `Expr.subst0 a B`) with `subst0`'s own shape. Every case discharges from the already-proven
    `shiftBy_subst_ge` (moving a shift past the inner substitution) and `shiftBy_shiftBy_le` (two
    shifts commuting) — no new arithmetic beyond `subst_shiftBy1_cancel`'s cancellation. -/
theorem subst_subst_comm : ∀ (e : Expr) (i j : Nat) (s a : Expr), j ≤ i →
    subst i s (subst j a e) = subst j (subst i s a) (subst (i + 1) (shiftAbove j s) e) := by
  intro e
  induction e with
  | var p =>
    intro i j s a hji
    rcases Nat.lt_trichotomy p j with hpj | hpj | hpj
    · -- p < j ≤ i < i+1: below both, untouched everywhere.
      rw [subst_var_lt hpj, subst_var_lt (by omega : p < i), subst_var_lt (by omega : p < i + 1),
        subst_var_lt hpj]
    · -- p = j: the inner substitution fires here.
      subst hpj
      rw [subst_var_eq, subst_var_lt (by omega : p < i + 1), subst_var_eq]
    · -- p > j: the inner substitution decrements to `var (p-1)`. `Nat.add_sub_cancel` normalizes the
      -- de Bruijn `_+1-1` back to a bare index after each `subst_var_gt` so the next `rw` matches
      -- syntactically (the two are defeq, but `rw` is syntactic).
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [subst_var_gt (by omega : p' + 1 > j), Nat.add_sub_cancel]
      rcases Nat.lt_trichotomy p' i with hp'i | hp'i | hp'i
      · -- j ≤ p' < i
        rw [subst_var_lt hp'i, subst_var_lt (by omega : p' + 1 < i + 1),
          subst_var_gt (by omega : p' + 1 > j), Nat.add_sub_cancel]
      · -- p' = i: the outer substitution fires here; the outer substitute survives the round-trip.
        subst hp'i
        rw [subst_var_eq, subst_var_eq, subst_shiftAbove_cancel]
      · -- p' > i
        obtain ⟨p'', rfl⟩ : ∃ p'', p' = p'' + 1 := ⟨p' - 1, by omega⟩
        rw [subst_var_gt (by omega : p'' + 1 > i), Nat.add_sub_cancel,
          subst_var_gt (by omega : p'' + 1 + 1 > i + 1), Nat.add_sub_cancel,
          subst_var_gt (by omega : p'' + 1 > j), Nat.add_sub_cancel]
  | bool => intro i j s a _; rfl
  | tt => intro i j s a _; rfl
  | ff => intro i j s a _; rfl
  | ite cnd t e ihc iht ihe =>
    intro i j s a hji
    simp only [subst, ihc i j s a hji, iht i j s a hji, ihe i j s a hji]
  | pi rho dom cod ihdom ihcod =>
    intro i j s a hji
    have hcod := ihcod (i + 1) (j + 1) (shiftAbove 0 s) (shiftAbove 0 a) (by omega)
    have hA : subst (i + 1) (shiftAbove 0 s) (shiftAbove 0 a) = shiftAbove 0 (subst i s a) :=
      (shiftBy_subst_ge a 1 0 i s (Nat.zero_le i)).symm
    have hS : shiftAbove (j + 1) (shiftAbove 0 s) = shiftAbove 0 (shiftAbove j s) :=
      (shiftBy_shiftBy_le s (Nat.zero_le j)).symm
    simp only [subst, ihdom i j s a hji, hcod, hA, hS]
  | lam body ihbody =>
    intro i j s a hji
    have hbody := ihbody (i + 1) (j + 1) (shiftAbove 0 s) (shiftAbove 0 a) (by omega)
    have hA : subst (i + 1) (shiftAbove 0 s) (shiftAbove 0 a) = shiftAbove 0 (subst i s a) :=
      (shiftBy_subst_ge a 1 0 i s (Nat.zero_le i)).symm
    have hS : shiftAbove (j + 1) (shiftAbove 0 s) = shiftAbove 0 (shiftAbove j s) :=
      (shiftBy_shiftBy_le s (Nat.zero_le j)).symm
    simp only [subst, hbody, hA, hS]
  | app f a' ihf iha =>
    intro i j s a hji
    simp only [subst, ihf i j s a hji, iha i j s a hji]

end Expr

/-- A dependent context lookup: unlike `Calculus.lean`'s plain `Γ[i]?` (safe there because `Ty`
    never mentions a `Tm`, so no reindexing is ever needed), a stored entry here is written
    relative to *its own* suffix (`Γ.drop (i+1)`, the scope that existed when it was declared), so
    reading it back out at the full context `Γ` needs re-basing by exactly `i + 1` — one shift per
    binder crossed on the way to it, accumulated by the recursion below. -/
def ctxGet : List Expr → Nat → Option Expr
  | [], _ => none
  | A :: _, 0 => some (Expr.shiftAbove 0 A)
  | _ :: Γ, n + 1 => (ctxGet Γ n).map (Expr.shiftAbove 0)

/-- Insert a fresh type `X` at position `c` (`c = 0`: brand new innermost binder, shadowing
    nothing — the case `HasType.lam`'s premise itself uses, needing no shift at all, since nothing
    yet in `Γ` could possibly reference a binder more local than all of them). A binder originally
    *above* the insertion point (`c`'s recursive `A :: Γ, c+1, X` case, `A` at local position `0`
    relative to what's left to insert past) has the new variable land *inside* its own local scope,
    so its stored `Expr` needs `Expr.shiftAbove` at the corresponding relative depth to keep
    pointing at the same things; a binder at or below the insertion point is untouched (its own
    local scope doesn't change — see the module-level derivation this mirrors). -/
def ctxInsert : List Expr → Nat → Expr → List Expr
  | Γ, 0, X => X :: Γ
  | [], _ + 1, X => [X]
  | A :: Γ, c + 1, X => Expr.shiftAbove c A :: ctxInsert Γ c X

theorem ctxInsert_zero (Γ : List Expr) (X : Expr) : ctxInsert Γ 0 X = X :: Γ := by
  cases Γ <;> rfl

theorem ctxInsert_length {Γ : List Expr} {c : Nat} {X : Expr} :
    (ctxInsert Γ c X).length = Γ.length + 1 := by
  induction Γ generalizing c with
  | nil => cases c <;> rfl
  | cons A Γ ih => cases c with
    | zero => rfl
    | succ c => simp [ctxInsert, ih]

/-- The raw (pre-`ctxGet`-rebasing) shape of `ctxInsert` at a position strictly above an existing
    entry: exactly `insertTy_get_lt`'s statement, but the "untouched" claim only holds for the raw
    `List.get?`-level entry — see `ctxGet_insert_lt` below for what this implies once rebased. -/
theorem ctxInsert_get_lt {Γ : List Expr} {c i : Nat} {X : Expr} (h : i < c) (hin : i < Γ.length) :
    (ctxInsert Γ c X)[i]? = (Γ[i]?).map (Expr.shiftAbove (c - i - 1)) := by
  induction Γ generalizing c i with
  | nil => simp only [List.length_nil] at hin; omega
  | cons A Γ ih => cases c with
    | zero => omega
    | succ c => cases i with
      | zero => rfl
      | succ i =>
        have hin' : i < Γ.length := by simp only [List.length_cons] at hin; omega
        have hic : i < c := by omega
        have hexp : c + 1 - (i + 1) - 1 = c - i - 1 := by omega
        rw [hexp]
        exact ih hic hin'

theorem ctxInsert_get_ge {Γ : List Expr} {c i : Nat} {X : Expr} (h : i ≥ c) :
    (ctxInsert Γ c X)[i + 1]? = Γ[i]? := by
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
      | succ i => exact ih (c := c) (i := i) (by omega)

theorem ctxInsert_get_eq {Γ : List Expr} {c : Nat} {X : Expr} (h : c ≤ Γ.length) :
    (ctxInsert Γ c X)[c]? = some X := by
  induction Γ generalizing c with
  | nil =>
    simp only [List.length_nil] at h
    have hc : c = 0 := Nat.le_zero.mp h
    subst hc; rfl
  | cons A Γ ih => cases c with
    | zero => rfl
    | succ c => exact ih (c := c) (by simpa using h)

/-- **`ctxGet` naturality under insertion, below the insertion point.** A binder more local than
    the freshly-inserted one (`i < c`) keeps its de Bruijn index, but its rebased type shifts by
    exactly the amount `weaken` needs — `Expr.shiftAbove c`, uniformly, regardless of `i` — because
    the raw shift `ctxInsert` applies (`shiftAbove (c - i - 1)`, by `ctxInsert_get_lt`) composes
    with `ctxGet`'s own `i + 1`-fold rebasing via `shiftBy_shiftBy_le` into exactly that. This is
    the one place `shiftBy_shiftBy_le`'s general two-shift commutation actually gets used. -/
theorem ctxGet_insert_lt {Γ : List Expr} {c i : Nat} {X : Expr} (h : i < c) (hin : i < Γ.length) :
    ctxGet (ctxInsert Γ c X) i = (ctxGet Γ i).map (Expr.shiftAbove c) := by
  induction Γ generalizing c i with
  | nil => simp only [List.length_nil] at hin; omega
  | cons A Γ ih => cases c with
    | zero => omega
    | succ c => cases i with
      | zero =>
        show some (Expr.shiftAbove 0 (Expr.shiftAbove c A)) =
          (some (Expr.shiftAbove 0 A)).map (Expr.shiftAbove (c + 1))
        simp only [Option.map_some]
        congr 1
        exact Expr.shiftBy_shiftBy_le A (Nat.zero_le c)
      | succ i =>
        have hin' : i < Γ.length := by simp only [List.length_cons] at hin; omega
        show (ctxGet (ctxInsert Γ c X) i).map (Expr.shiftAbove 0) =
          ((ctxGet Γ i).map (Expr.shiftAbove 0)).map (Expr.shiftAbove (c + 1))
        rw [ih (by omega) hin']
        rw [Option.map_map, Option.map_map]
        congr 1
        funext A'
        show Expr.shiftAbove 0 (Expr.shiftAbove c A') = Expr.shiftAbove (c + 1) (Expr.shiftAbove 0 A')
        exact Expr.shiftBy_shiftBy_le A' (Nat.zero_le c)

/-- **`ctxGet` naturality under insertion, at or above the insertion point.** A binder no more
    local than the freshly-inserted one is untouched in raw content — `ctxGet`'s *own* rebasing
    shift is always anchored at threshold `0` (every step of its recursion is `shiftAbove 0`), so
    reading the same raw entry one slot further out just adds one more `shiftAbove 0`, independent
    of where `X` itself landed (`c` never enters this one — contrast `ctxGet_insert_lt`, where the
    raw content genuinely does change, and threading `c` through is the whole content). -/
theorem ctxGet_insert_ge {Γ : List Expr} {c i : Nat} {X : Expr} (h : i ≥ c) :
    ctxGet (ctxInsert Γ c X) (i + 1) = (ctxGet Γ i).map (Expr.shiftAbove 0) := by
  induction Γ generalizing c i with
  | nil => cases c with
    | zero => cases i <;> rfl
    | succ c => cases i with
      | zero => omega
      | succ i => rfl
  | cons A Γ ih => cases c with
    | zero => rfl
    | succ c => cases i with
      | zero => omega
      | succ i =>
        show (ctxGet (ctxInsert Γ c X) (i + 1)).map (Expr.shiftAbove 0) =
          ((ctxGet Γ i).map (Expr.shiftAbove 0)).map (Expr.shiftAbove 0)
        rw [ih (c := c) (i := i) (by omega)]

/-- The freshly-inserted slot itself reads back as `X` rebased by `c + 1` (`X` is stored raw,
    relative to the suffix `Γ.drop c` it lands on top of — see the theorem's use site for why that
    is exactly the right convention: `X` here plays the role of a context entry's own declared
    type, which by well-scopedness can only mention what's strictly below it, i.e. `Γ.drop c`, the
    *same* discipline every other entry in `Γ` already follows). `c + 1` is `ctxGet`'s uniform,
    purely-positional rebasing amount, not a special case — matching `ctxGet`'s general shape,
    with no dependence on `X`'s own content. -/
theorem ctxGet_insert_eq {Γ : List Expr} {c : Nat} {X : Expr} (h : c ≤ Γ.length) :
    ctxGet (ctxInsert Γ c X) c = some (Expr.shiftBy (c + 1) 0 X) := by
  induction Γ generalizing c with
  | nil =>
    simp only [List.length_nil] at h
    have hc : c = 0 := Nat.le_zero.mp h
    subst hc
    show some (Expr.shiftAbove 0 X) = some (Expr.shiftBy 1 0 X)
    rfl
  | cons A Γ ih => cases c with
    | zero => rfl
    | succ c =>
      show (ctxGet (ctxInsert Γ c X) c).map (Expr.shiftAbove 0) =
        some (Expr.shiftBy (c + 1 + 1) 0 X)
      rw [ih (c := c) (by simpa using h)]
      show some (Expr.shiftAbove 0 (Expr.shiftBy (c + 1) 0 X)) =
        some (Expr.shiftBy (c + 1 + 1) 0 X)
      congr 1
      show Expr.shiftBy 1 0 (Expr.shiftBy (c + 1) 0 X) = Expr.shiftBy (c + 1 + 1) 0 X
      rw [Expr.shiftBy_shiftBy_add X 1 (c + 1) 0]
      congr 1
      omega

/-- A successful `ctxGet` lookup is always in bounds — needed to feed `Usage.length_unit` the
    bound it requires when the `var` typing rule fires. -/
theorem lookup_ctxGet_lt {Γ : List Expr} {i : Nat} {A : Expr} (h : ctxGet Γ i = some A) :
    i < Γ.length := by
  induction Γ generalizing i A with
  | nil => simp [ctxGet] at h
  | cons A' Γ ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [ctxGet, Option.map_eq_some_iff] at h
      obtain ⟨A'', hA'', _⟩ := h
      have := ih hA''
      simp
      omega

/-- **A `ctxGet` result is insensitive to the shift threshold below its own position.** Since
    `ctxGet Γ i`'s value can only ever mention *raw* content coming from strictly-more-senior
    entries (indices `> i`, by the well-scoping discipline `ctxGet`'s own recursive rebasing
    embodies), shifting it at *any* threshold `c ≤ i` gives the same answer as shifting it at
    threshold `0` — the two thresholds can only disagree on free variables in `[0, c)`, and no such
    variable can occur. This is exactly the fact `weaken`'s `var` case needs to reconcile
    `ctxGet_insert_lt`'s uniform `shiftAbove c` (the `i < c` branch) with `ctxGet_insert_ge`'s
    `shiftAbove 0` (the `i ≥ c` branch) into one uniform `shiftAbove c A` conclusion. -/
theorem ctxGet_shift_below_eq {Γ : List Expr} : ∀ {i : Nat} {A : Expr}, ctxGet Γ i = some A →
    ∀ {c : Nat}, c ≤ i → Expr.shiftAbove c A = Expr.shiftAbove 0 A := by
  induction Γ with
  | nil => intro i A h; simp [ctxGet] at h
  | cons B Γ' ih =>
    intro i A h c hc
    cases i with
    | zero =>
      have hc0 : c = 0 := Nat.le_zero.mp hc
      subst hc0
      rfl
    | succ n =>
      simp only [ctxGet, Option.map_eq_some_iff] at h
      obtain ⟨A0, hA0, hAeq⟩ := h
      subst hAeq
      cases c with
      | zero => rfl
      | succ c' =>
        have hc' : c' ≤ n := by omega
        have hIH : Expr.shiftBy 1 c' A0 = Expr.shiftBy 1 0 A0 := ih hA0 hc'
        show Expr.shiftBy 1 (c' + 1) (Expr.shiftBy 1 0 A0) = Expr.shiftBy 1 0 (Expr.shiftBy 1 0 A0)
        calc Expr.shiftBy 1 (c' + 1) (Expr.shiftBy 1 0 A0)
            = Expr.shiftBy 1 0 (Expr.shiftBy 1 c' A0) :=
              (Expr.shiftBy_shiftBy_le A0 (Nat.zero_le c')).symm
          _ = Expr.shiftBy 1 0 (Expr.shiftBy 1 0 A0) := by rw [hIH]

/-- **The graded, dependent judgement** `Γ ⊢ e :^σ A ⊣ φ` — the exact `Calculus.lean` `HasType`
    shape (`var`/`lam`/`app`/`tt`/`ff`/`ite`, no dimension/Kan formers: those are M5/M8's concern,
    orthogonal to M9's dependent-`Π` extension), with two changes, both purely about `Π` becoming
    dependent, *not* about grading:

    * `var` looks up through `ctxGet` (rebasing-aware) instead of a plain `Γ[i]?`.
    * `app`'s conclusion type is `Expr.subst0 a B` (the codomain instantiated at the actual
      argument), not the bare `B` `Calculus.lean`'s non-dependent `Ty.arr` allows — this is the one
      substantive difference a real dependent `Π` requires. -/
inductive HasType : List Expr → Expr → Expr → Grade → Usage → Prop where
  | var {Γ : List Expr} {i : Nat} {A : Expr} {σ : Grade} (h : ctxGet Γ i = some A) :
      HasType Γ (.var i) A σ (Usage.unit i Γ.length σ)
  | lam {Γ : List Expr} {body : Expr} {ρ σ δ : Grade} {A B : Expr} {rest : Usage}
      (hbody : HasType (A :: Γ) body B σ (δ :: rest)) (hle : δ ≤ ρ) :
      HasType Γ (.lam body) (.pi ρ A B) σ rest
  | app {Γ : List Expr} {f a : Expr} {ρ σ : Grade} {A B : Expr} {φf φa : Usage}
      (hf : HasType Γ f (.pi ρ A B) σ φf) (ha : HasType Γ a A (σ.mul ρ) φa) :
      HasType Γ (.app f a) (Expr.subst0 a B) σ (Usage.add φf φa)
  | tt {Γ : List Expr} {σ : Grade} : HasType Γ .tt .bool σ (Usage.zero Γ.length)
  | ff {Γ : List Expr} {σ : Grade} : HasType Γ .ff .bool σ (Usage.zero Γ.length)
  | ite {Γ : List Expr} {c t e : Expr} {σ : Grade} {A : Expr} {φc φt φe : Usage}
      (hc : HasType Γ c .bool σ φc) (ht : HasType Γ t A σ φt) (he : HasType Γ e A σ φe) :
      HasType Γ (.ite c t e) A σ (Usage.add φc (Usage.add φt φe))

namespace HasType

theorem usage_length {Γ : List Expr} {e A : Expr} {σ : Grade} {φ : Usage}
    (h : HasType Γ e A σ φ) : φ.length = Γ.length := by
  induction h with
  | @var Γ i A σ hlk => exact Usage.length_unit i Γ.length _ (lookup_ctxGet_lt hlk)
  | lam _ hle ih =>
    have := ih
    simp only [List.length_cons] at this
    omega
  | app _ _ ihf iha => simp [Usage.length_add, ihf, iha]
  | tt => simp
  | ff => simp
  | ite _ _ _ ihc iht ihe => simp [Usage.length_add, ihc, iht, ihe]

/-- **General weakening**, the dependent-`Π` analogue of `Weakening.lean`'s `weaken`: inserting a
    fresh, unused binder `X` anywhere in the context (`ctxInsert Γ c X`) preserves typability,
    shifting *both* the term and its type (`Expr.shiftAbove c`, uniformly — the substantive
    difference from the non-dependent original, where types never needed to shift at all) and
    padding the usage vector (`insertUsage`, unchanged from `Calculus.lean`'s, since usage vectors
    don't depend on `Expr` at all). This is the ingredient the dependent substitution lemma's `lam`
    case needs, exactly mirroring why `Calculus.lean`'s own `weaken` exists (re-weakening the
    substituted term one level deeper when recursing under a binder). -/
theorem weaken {Γ : List Expr} {e A : Expr} {σ : Grade} {φ : Usage}
    (h : HasType Γ e A σ φ) : ∀ (c : Nat) (X : Expr), c ≤ Γ.length →
    HasType (ctxInsert Γ c X) (Expr.shiftAbove c e) (Expr.shiftAbove c A) σ (insertUsage φ c) := by
  induction h with
  | @var Γ i A σ hlk =>
    intro c X hcle
    have hlen : i < Γ.length := lookup_ctxGet_lt hlk
    rcases Nat.lt_or_ge i c with hic | hic
    · rw [Expr.shiftAbove_var_lt hic]
      rw [insertUsage_unit_lt hic hlen]
      have hlk' : ctxGet (ctxInsert Γ c X) i = some (Expr.shiftAbove c A) := by
        rw [ctxGet_insert_lt hic hlen, hlk]; rfl
      have hres := HasType.var (Γ := ctxInsert Γ c X) (i := i) (σ := σ) hlk'
      rwa [ctxInsert_length] at hres
    · rw [Expr.shiftAbove_var_ge hic]
      rw [insertUsage_unit_ge hic hlen]
      have hAeq : Expr.shiftAbove c A = Expr.shiftAbove 0 A := ctxGet_shift_below_eq hlk hic
      have hlk' : ctxGet (ctxInsert Γ c X) (i + 1) = some (Expr.shiftAbove c A) := by
        rw [ctxGet_insert_ge hic, hlk, hAeq]; rfl
      have hres := HasType.var (Γ := ctxInsert Γ c X) (i := i + 1) (σ := σ) hlk'
      rwa [ctxInsert_length] at hres
  | @lam Γ body ρ σ δ A B rest hbody hle ihbody =>
    intro c X hcle
    have hbody' := ihbody (c + 1) X (by simpa using Nat.succ_le_succ hcle)
    exact HasType.lam hbody' hle
  | @app Γ f a ρ σ A B φf φa hf ha ihf iha =>
    intro c X hcle
    have hf' := ihf c X hcle
    have ha' := iha c X hcle
    have hlen : φf.length = φa.length := by rw [usage_length hf, usage_length ha]
    show HasType (ctxInsert Γ c X) (Expr.shiftAbove c (Expr.app f a))
      (Expr.shiftAbove c (Expr.subst0 a B)) σ (insertUsage (Usage.add φf φa) c)
    rw [Expr.shiftAbove_subst0, insertUsage_add hlen c]
    exact HasType.app hf' ha'
  | @tt Γ σ =>
    intro c X hcle
    show HasType (ctxInsert Γ c X) Expr.tt Expr.bool σ (insertUsage (Usage.zero Γ.length) c)
    rw [insertUsage_zero, ← ctxInsert_length (Γ := Γ) (c := c) (X := X)]
    exact HasType.tt
  | @ff Γ σ =>
    intro c X hcle
    show HasType (ctxInsert Γ c X) Expr.ff Expr.bool σ (insertUsage (Usage.zero Γ.length) c)
    rw [insertUsage_zero, ← ctxInsert_length (Γ := Γ) (c := c) (X := X)]
    exact HasType.ff
  | @ite Γ cnd t e σ A φc φt φe hc ht he ihc iht ihe =>
    intro c X hcle
    have hlc := usage_length hc
    have hlt := usage_length ht
    have hle := usage_length he
    have hlen1 : φt.length = φe.length := by rw [hlt, hle]
    have hlen2 : φc.length = (Usage.add φt φe).length := by
      rw [Usage.length_add, hlt, hle, hlc, Nat.min_self]
    show HasType (ctxInsert Γ c X)
      (Expr.ite (Expr.shiftAbove c cnd) (Expr.shiftAbove c t) (Expr.shiftAbove c e))
      (Expr.shiftAbove c A) σ (insertUsage (Usage.add φc (Usage.add φt φe)) c)
    rw [insertUsage_add hlen2 c, insertUsage_add hlen1 c]
    exact HasType.ite (ihc c X hcle) (iht c X hcle) (ihe c X hcle)

end HasType

/-- Canonical forms of the dependent fragment: exactly `lam`/`tt`/`ff`, mirroring `Progress.lean`'s
    `Value` (this fragment has no Kan formers, so no `iabs`-is-not-a-value gotcha to repeat). -/
inductive Value : Expr → Prop where
  | lam {body : Expr} : Value (.lam body)
  | tt : Value .tt
  | ff : Value .ff

/-- Call-by-value small-step reduction, the dependent-`Π` analogue of `Progress.lean`'s `Step`
    restricted to the `app`/`ite` fragment (no Kan formers here): `beta`'s target uses
    `Expr.subst0`, the same substitution the `app` typing rule's conclusion type already commits
    to, so the type produced by `HasType.app` is *exactly* what `beta`'s target needs — no
    coercion or extra type-level step is needed to state `Step` itself (only `preservation`, which
    this file does not attempt — see the module doc, "What this file does not prove"). -/
inductive Step : Expr → Expr → Prop where
  | app1 {f f' a : Expr} (h : Step f f') : Step (.app f a) (.app f' a)
  | app2 {f a a' : Expr} (hf : Value f) (h : Step a a') : Step (.app f a) (.app f a')
  | beta {body a : Expr} (ha : Value a) : Step (.app (.lam body) a) (Expr.subst0 a body)
  | ite_cond {c c' t e : Expr} (h : Step c c') : Step (.ite c t e) (.ite c' t e)
  | ite_tt {t e : Expr} : Step (.ite .tt t e) t
  | ite_ff {t e : Expr} : Step (.ite .ff t e) e

/-- **Progress** for the dependent fragment: a closed, well-typed term is either a value or can
    take a step. Identical proof shape to `Progress.lean`'s `progress` (canonical-forms case
    analysis on `app`/`ite`'s scrutinee) — dependent typing changes *what* `HasType`'s conclusion
    type looks like (`Expr.subst0 a B` instead of a bare `B`), but never *which* term shape a
    derivation could have produced it from, so the argument transfers verbatim. Notably this proof
    needs no substitution lemma at all (`Calculus.lean`'s own `progress` doesn't either) — only
    `preservation`'s `beta` case does, which is exactly the piece this file leaves open. -/
theorem progress {Γ : List Expr} {e A : Expr} {σ : Grade} {φ : Usage}
    (h : HasType Γ e A σ φ) : Γ = [] → Value e ∨ ∃ e', Step e e' := by
  induction h with
  | var hlk => intro hΓ; subst hΓ; simp [ctxGet] at hlk
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

end Dep
end BlightMeta
