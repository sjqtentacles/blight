/-
  Wave 8 / M10, part 2: a machine-checked mechanization of effect/handler type safety — "the
  graded-row discharge" (spec §4, `crates/blight-kernel/src/check.rs`'s `Op`/`Handle` rules,
  `crates/blight-kernel/src/row.rs`'s graded `Row`) — which was, before this file, tested
  operationally (`check.rs`'s `handle_discharges_label`, `handle_with_clause`-style probes) but not
  part of the Lean development at all.

  ── The claim being mechanized (spec §4.4) ───────────────────────────────────────────────────
  "The grade on an effect label in the row records how many times its continuation may be
  invoked. A `0`-graded effect's handler must call `k` zero times (abort/exception); a `1`-graded
  one must call it at most once (state, reader); an `ω`-graded one may call it freely." The kernel
  enforces this with one runtime check (`check.rs`'s `Handle` rule: `demand_k.leq(cont_grade)`,
  where `demand_k` is the op-clause's own *measured* usage of its bound continuation and
  `cont_grade` is the operation's declared continuation-multiplicity). This file reconstructs that
  rule as a graded typing judgement and proves, as genuine corollaries of the grade order (not
  just restating the rule's own premise), that a `0`-graded handler's clause can *never* use its
  continuation and a `1`-graded handler's clause can only ever use it linearly.

  ── Simplifications (honest scope, matching this fragment's existing conventions) ───────────────
  * **A single, globally fixed operation** `op : opDom → opCod` at a globally fixed continuation
    grade `opGrade`, standing in for the general case of many operations across many declared
    effects (spec §4.2's `OpSig` telescope) — the same "one instance stands in for the whole
    shape" simplification `Calculus.Tm.tt`/`ff` already use for "any grade-0-formed data type."
    Consequently there is exactly one effect label in scope; `Row := Option Grade` (`none` =
    absent, `some ρ` = present at accumulated grade `ρ`) is the single-label specialization of
    `row.rs`'s `BTreeMap<EffName, Grade>`, and `Row.union`'s per-label `Grade.add` is `row.rs`'s
    `Row::union`/`insert` read at one label.
  * **No row-variable effect polymorphism** (spec §4.1's trailing `ε`) — every row here is closed.
  * **Lambda bodies are pure** (`HasType.lam`'s premise fixes its body's row to `none`) — this
    fragment does not thread a row through `Ty.arr`'s codomain (spec's `A → B ! E` would need a
    dependent-effect arrow type), so a function value cannot latently carry an unresolved effect
    the way the real kernel's `Value::Pi` implicitly can. Every performed effect in this fragment
    is therefore "immediate" (not hidden behind an un-applied closure) — a real restriction,
    documented rather than silently assumed.
  * **Operational semantics + preservation (P1, v0.1 roadmap): now built, with a sharp negative
    result.** This file used to prove only the *static* discipline; the second half (after the
    static corollaries) now adds a small-step `Step` with genuine delimited-continuation semantics
    (one-hole eval contexts `ECtx`, a deep-handler `handle_perform` that re-installs the handler as a
    captured continuation `k = lam (handle E[var 0] retC opC)`), a full substitution stack for this
    fragment's own `Tm`, and:
      - `progress` — a closed, well-typed, pure-rowed term is a value or steps (via the
        `E[perform v]`-residual decomposition), and
      - `preservation_core` — the *type-preserving fragment* `StepC` (every step **except**
        `handle_perform`: β, ite, perform-arg, handle-body, **handle-ret**) preserves type + ambient
        grade and only *weakens* the row (`Row.Le`), at runtime ambient `σ ∈ {ω, 0}`, and
      - `resume_once_operational`/`never_resumes_operational`/`cont_slot_demand_after_arg_subst` — the
        *operational* upgrade of `handle_linear_at_most_once`: at the actual `handle_perform` redex,
        the captured continuation is resumed at most once (0 or 1 for a 1-graded op, 0 for a 0-graded).
    **The negative result** (`handle_perform_not_preserving`, machine-checked): the deep-handler
    `handle_perform` step does **not** preserve types against *this static presentation* — because the
    static `handle` rule types the op-clause's continuation binder (index 0) at `opCod` (the *value*
    fed to a resume), not at the continuation's *function* type `opCod → B`. A faithful deep handler
    substitutes a `lam` (arrow-typed) into that slot, so a reduct can be a `lam` where a non-arrow
    type was expected (`handle (perform tt) (var 0) (var 0) : bool` steps to a `lam`, which
    `lam_not_bool` shows has no typing at `bool`). The grade discipline stays sound; the *typing of
    the continuation* is the simplification that blocks subject reduction. Recovering it needs the
    `handle` rule to bind `k` at `opCod → B` (a genuine first-class continuation type) — the clean
    next step. See also `docs/metatheory-mechanized.md`.
-/

import BlightMeta.Calculus
import BlightMeta.Weakening

namespace BlightMeta

namespace Effects

/-- A graded effect row for the single ambient operation this fragment mechanizes (spec §4.1's
    `Row`, specialized to one label): `none` is the pure/discharged row; `some ρ` records that the
    operation has been performed, accumulated to grade `ρ` (spec §4.4's continuation-multiplicity
    currency). -/
abbrev Row := Option Grade

namespace Row

/-- Graded union (`row.rs::Row::union`, one label): combine two rows' contributions by `Grade.add`
    — exactly the same semiring operation `Usage.add` uses for ordinary resource accounting (spec
    §3.6's "one mechanism, two polarities": the row is the *producer*-side/monadic reading of the
    same grade algebra `Usage` uses on the *consumer*/comonadic side). -/
def union : Row → Row → Row
  | none, r => r
  | r, none => r
  | some g1, some g2 => some (g1.add g2)

@[simp] theorem union_none_left (r : Row) : union none r = r := rfl
@[simp] theorem union_none_right (r : Row) : union r none = r := by cases r <;> rfl

end Row

/-- Terms: the STLC core (`var`/`lam`/`app`/`tt`/`ff`/`ite`, matching `Calculus.Tm`'s non-Kan
    fragment exactly) plus `perform` (spec §4.2's `Op`) and `handle` (spec §4.3's `Handle`). A
    `handle body retC opC` packages both handler clauses positionally rather than as a labeled
    list (there is only one operation to handle in this fragment): `retC` binds the body's
    returned value (one binder, spec's `return` clause), `opC` binds the operation's argument and
    then its continuation, innermost first — `opC`'s De Bruijn index `0` is `k`, index `1` is the
    operation's argument `x`, matching `Calculus.Tm.lam`'s convention that the most recently bound
    variable is index `0`. -/
inductive Tm where
  | var (i : Nat)
  | lam (body : Tm)
  | app (f a : Tm)
  | tt
  | ff
  | ite (c t e : Tm)
  | perform (a : Tm)
  | handle (body retC opC : Tm)
  deriving DecidableEq, Repr

/-- The graded, row-tracking typing judgement `Γ ⊢ e :^σ A ! E ⊣ φ` (spec §4.1's
    `Γ ⊢ t ! E : A`, decorated with `Calculus.HasType`'s ambient grade `σ` and usage `φ`), for the
    single fixed operation `op : opDom → opCod` declared at continuation grade `opGrade` — both
    made explicit *parameters* of the family (uniform across every constructor, exactly like a
    polymorphic `List α`'s `α`), so a single `HasType opDom opCod opGrade` instance fixes "the"
    ambient operation for an entire derivation.

    * `perform` ↔ `check.rs`'s `Op` rule: check the argument against `opDom`, contribute the
      operation's own declared grade to the row (this fragment's specialization of `Op`'s
      `Row::single(effect, sigma)` — see the module doc's simplification note: every perform is
      charged at the operation's own fixed multiplicity here, rather than at a call-site-chosen
      ambient grade).
    * `handle` ↔ `check.rs`'s `Handle` rule: `body`'s row `Ebody` may be anything (a pure body is
      legally handled too, discharging nothing); the return clause is checked against the *same*
      result type `B` the op-clause is, both required pure (`none`) post-discharge — matching
      "handling the sole effect in scope leaves nothing residual"; and — **the central safety
      constraint** — the op-clause's own measured usage of its bound continuation (`δk`, the
      usage-vector entry for index `0`, exactly as `HasType.lam`'s `δ` is the body's measured
      usage of *its* bound variable) must not exceed the operation's declared grade. This is the
      *exact* mechanization of `check.rs`'s `demand_k.leq(cont_grade)` check. -/
inductive HasType (opDom opCod : Ty) (opGrade : Grade) :
    List Ty → Tm → Ty → Grade → Row → Usage → Prop where
  | var {Γ i A σ} (h : Γ[i]? = some A) :
      HasType opDom opCod opGrade Γ (.var i) A σ none (Usage.unit i Γ.length σ)
  | lam {Γ body ρ σ δ A B rest}
      (hbody : HasType opDom opCod opGrade (A :: Γ) body B σ none (δ :: rest)) (hle : δ ≤ ρ) :
      HasType opDom opCod opGrade Γ (.lam body) (.arr ρ A B) σ none rest
  | app {Γ f a ρ σ A B φf φa Ef Ea}
      (hf : HasType opDom opCod opGrade Γ f (.arr ρ A B) σ Ef φf)
      (ha : HasType opDom opCod opGrade Γ a A (σ.mul ρ) Ea φa) :
      HasType opDom opCod opGrade Γ (.app f a) B σ (Row.union Ef Ea) (Usage.add φf φa)
  | tt {Γ σ} : HasType opDom opCod opGrade Γ .tt .bool σ none (Usage.zero Γ.length)
  | ff {Γ σ} : HasType opDom opCod opGrade Γ .ff .bool σ none (Usage.zero Γ.length)
  | ite {Γ c t e σ A φc φt φe Ec Et Ee}
      (hc : HasType opDom opCod opGrade Γ c .bool σ Ec φc)
      (ht : HasType opDom opCod opGrade Γ t A σ Et φt)
      (he : HasType opDom opCod opGrade Γ e A σ Ee φe) :
      HasType opDom opCod opGrade Γ (.ite c t e) A σ (Row.union Ec (Row.union Et Ee))
        (Usage.add φc (Usage.add φt φe))
  | perform {Γ a σ φ} (ha : HasType opDom opCod opGrade Γ a opDom σ none φ) :
      HasType opDom opCod opGrade Γ (.perform a) opCod σ (some opGrade) φ
  | handle {Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody}
      (hbody : HasType opDom opCod opGrade Γ body A σ Ebody φbody)
      (hretC : HasType opDom opCod opGrade (A :: Γ) retC B σ none (δret :: φretC))
      (hopC : HasType opDom opCod opGrade ((.arr Grade.omega opCod B) :: opDom :: Γ) opC B σ none
        (δk :: δarg :: φopC))
      (hgrade : δk ≤ opGrade) :
      HasType opDom opCod opGrade Γ (.handle body retC opC) B σ none
        (Usage.add φbody (Usage.add φretC φopC))

/-- **Frozen "value-continuation" judgement (the documented BEFORE).**  An exact copy of the
    original `HasType` whose `handle` rule types the op-clause's continuation binder (index 0) at the
    *value* type `opCod`.  Kept so the machine-checked negative result
    `handle_perform_not_preserving` — which exhibits that this value-typed presentation is not
    subject-reduction-safe — survives verbatim after `HasType.handle` is retyped to bind the
    continuation at its first-class function type `.arr ω opCod B`. -/
inductive HasTypeVC (opDom opCod : Ty) (opGrade : Grade) :
    List Ty → Tm → Ty → Grade → Row → Usage → Prop where
  | var {Γ i A σ} (h : Γ[i]? = some A) :
      HasTypeVC opDom opCod opGrade Γ (.var i) A σ none (Usage.unit i Γ.length σ)
  | lam {Γ body ρ σ δ A B rest}
      (hbody : HasTypeVC opDom opCod opGrade (A :: Γ) body B σ none (δ :: rest)) (hle : δ ≤ ρ) :
      HasTypeVC opDom opCod opGrade Γ (.lam body) (.arr ρ A B) σ none rest
  | app {Γ f a ρ σ A B φf φa Ef Ea}
      (hf : HasTypeVC opDom opCod opGrade Γ f (.arr ρ A B) σ Ef φf)
      (ha : HasTypeVC opDom opCod opGrade Γ a A (σ.mul ρ) Ea φa) :
      HasTypeVC opDom opCod opGrade Γ (.app f a) B σ (Row.union Ef Ea) (Usage.add φf φa)
  | tt {Γ σ} : HasTypeVC opDom opCod opGrade Γ .tt .bool σ none (Usage.zero Γ.length)
  | ff {Γ σ} : HasTypeVC opDom opCod opGrade Γ .ff .bool σ none (Usage.zero Γ.length)
  | ite {Γ c t e σ A φc φt φe Ec Et Ee}
      (hc : HasTypeVC opDom opCod opGrade Γ c .bool σ Ec φc)
      (ht : HasTypeVC opDom opCod opGrade Γ t A σ Et φt)
      (he : HasTypeVC opDom opCod opGrade Γ e A σ Ee φe) :
      HasTypeVC opDom opCod opGrade Γ (.ite c t e) A σ (Row.union Ec (Row.union Et Ee))
        (Usage.add φc (Usage.add φt φe))
  | perform {Γ a σ φ} (ha : HasTypeVC opDom opCod opGrade Γ a opDom σ none φ) :
      HasTypeVC opDom opCod opGrade Γ (.perform a) opCod σ (some opGrade) φ
  | handle {Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody}
      (hbody : HasTypeVC opDom opCod opGrade Γ body A σ Ebody φbody)
      (hretC : HasTypeVC opDom opCod opGrade (A :: Γ) retC B σ none (δret :: φretC))
      (hopC : HasTypeVC opDom opCod opGrade (opCod :: opDom :: Γ) opC B σ none
        (δk :: δarg :: φopC))
      (hgrade : δk ≤ opGrade) :
      HasTypeVC opDom opCod opGrade Γ (.handle body retC opC) B σ none
        (Usage.add φbody (Usage.add φretC φopC))

/-- **Effect-safety corollary 1 (inversion): every well-typed `handle` term's op-clause is
    grade-safe by construction.** Recovers the `hgrade` side-condition `check.rs`'s `Handle` rule
    enforces, from nothing but the fact that the term type-checked at all — i.e. grade-safety is
    not an extra property one must separately verify of a well-typed handler, it *is* what
    well-typedness of `handle` means in this judgement. -/
theorem handle_grade_safe {opDom opCod : Ty} {opGrade : Grade} {Γ body retC opC B σ φ}
    (h : HasType opDom opCod opGrade Γ (.handle body retC opC) B σ none φ) :
    ∃ A φbody φretC φopC δret δk δarg Ebody,
      HasType opDom opCod opGrade Γ body A σ Ebody φbody ∧
      HasType opDom opCod opGrade (A :: Γ) retC B σ none (δret :: φretC) ∧
      HasType opDom opCod opGrade ((.arr Grade.omega opCod B) :: opDom :: Γ) opC B σ none
        (δk :: δarg :: φopC) ∧
      δk ≤ opGrade := by
  cases h with
  | handle hbody hretC hopC hgrade =>
    exact ⟨_, _, _, _, _, _, _, _, hbody, hretC, hopC, hgrade⟩

/-- `g ≤ Grade.zero` forces `g = Grade.zero`: `0` is not just a lower bound (`Grade.zero_le`,
    `Grade.lean`) but the order's unique minimum, the fact needed to turn "bounded by an abort
    handler's declared grade" into "provably unused." -/
theorem le_zero_eq {g : Grade} (h : g ≤ Grade.zero) : g = Grade.zero := by
  cases g <;> simp_all [Grade.le_def, Grade.rank]

/-- `g ≤ Grade.one` rules out `Grade.omega`: the only grades below `1` are `0` and `1` themselves,
    the fact needed to turn "bounded by a linear handler's declared grade" into "used at most
    once, never unboundedly." -/
theorem le_one_cases {g : Grade} (h : g ≤ Grade.one) : g = Grade.zero ∨ g = Grade.one := by
  cases g <;> simp_all [Grade.le_def, Grade.rank]

/-- **Effect-safety corollary 2 (the headline result): a `0`-graded (abort/exception-style)
    operation's handler clause provably never uses its continuation.** Mechanizes spec §4.4's "a
    `0`-graded effect's handler must call `k` zero times" as a genuine consequence of the grade
    order — not an extra check bolted onto `Handle`, but something *forced* by combining
    `handle_grade_safe`'s recovered bound with `le_zero_eq`. This is exactly `check.rs`'s
    `demand_k.leq(cont_grade)` check specialized to `cont_grade = Zero`, now proved to have the
    semantic consequence the spec claims for it, not merely stated as an accept/reject test. -/
theorem handle_abort_never_resumes {opDom opCod : Ty} {Γ body retC opC B σ φ}
    (h : HasType opDom opCod Grade.zero Γ (.handle body retC opC) B σ none φ) :
    ∃ A φbody φretC φopC δret δarg Ebody,
      HasType opDom opCod Grade.zero Γ body A σ Ebody φbody ∧
      HasType opDom opCod Grade.zero (A :: Γ) retC B σ none (δret :: φretC) ∧
      HasType opDom opCod Grade.zero ((.arr Grade.omega opCod B) :: opDom :: Γ) opC B σ none
        (Grade.zero :: δarg :: φopC) := by
  obtain ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, hgrade⟩ :=
    handle_grade_safe h
  have hδk : δk = Grade.zero := le_zero_eq hgrade
  subst hδk
  exact ⟨A, φbody, φretC, φopC, δret, δarg, Ebody, hbody, hretC, hopC⟩

/-- **Effect-safety corollary 3: a `1`-graded (linear) operation's handler clause never
    over-resumes.** Mechanizes spec §4.4's "a `1`-graded one must resume at most once": the
    op-clause's measured continuation-usage is either `0` (never resumed — legal, since "at most
    once" permits zero) or `1` (resumed exactly once); it can never be `ω`, i.e. the discipline
    that would let a linear-effect handler resume its continuation an unbounded number of times is
    provably excluded, not merely untested. -/
theorem handle_linear_at_most_once {opDom opCod : Ty} {Γ body retC opC B σ φ}
    (h : HasType opDom opCod Grade.one Γ (.handle body retC opC) B σ none φ) :
    ∃ A φbody φretC φopC δret δk δarg Ebody,
      HasType opDom opCod Grade.one Γ body A σ Ebody φbody ∧
      HasType opDom opCod Grade.one (A :: Γ) retC B σ none (δret :: φretC) ∧
      HasType opDom opCod Grade.one ((.arr Grade.omega opCod B) :: opDom :: Γ) opC B σ none
        (δk :: δarg :: φopC) ∧
      (δk = Grade.zero ∨ δk = Grade.one) := by
  obtain ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, hgrade⟩ :=
    handle_grade_safe h
  exact ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, le_one_cases hgrade⟩


/- ═══════════════════════════════════════════════════════════════════════════════════════════
   P1 (roadmap-v0.1): OPERATIONAL SEMANTICS + PRESERVATION for the effect/handler fragment.

   The module doc above says operational semantics + preservation were "future work".  This
   section discharges P1 additively (no existing decl touched).  It adds, all verified zero-sorryAx
   (`#print axioms` shows only propext / Classical.choice / Quot.sound):

     * the substitution/structural infrastructure this judgement needs of its own (this fragment's
       `HasType` is a SEPARATE family from `Calculus.HasType`, so `Weakening`/`Substitution`'s
       lemmas do not apply to it): `Tm.shiftAbove`/`subst`, `usage_length`, `weaken`,
       `ambient_zero_usage`, `demote`/`demote_scaled`, and the full graded `subst_lemma`;
     * `Value`, one-hole evaluation contexts `ECtx`, and a deep-handler small-step `Step`
       (β/ite/congruences, `handle_ret`, and the delimited-continuation `handle_perform`);
     * `progress`: a closed, pure-rowed, well-typed term is a value or steps (via a decomposition
       lemma `progress_or_perform` + the row fact that any `E[perform v]` is non-`none`-rowed);
     * `preservation_core`: type + ambient preserved, row weakened to a SUB-row (`Row.Le`), for
       every step EXCEPT the deep-handler `handle_perform`, at the runtime ambient `σ ∈ {ω,0}`;
     * `handle_perform_not_preserving`: a MACHINE-CHECKED COUNTEREXAMPLE showing the deep-handler
       `handle_perform` rule is NOT type-preserving against this static presentation — the crux
       finding.  The static `handle` rule types the op-clause's continuation binder (index 0) at
       `opCod`, not at the continuation's function type `opCod → B`, so substituting a captured
       continuation `λx. handle E[x] …` (an arrow) into that `opCod`-typed slot breaks types.  The
       grade discipline is sound; the naive delimited-continuation reduction is not type-preserving
       against it.  (Cf. P2's dependent-preservation counterexample — verify, do not assume.)
     * `resume_once_operational` / `never_resumes_operational`: the OPERATIONAL upgrade of
       `handle_linear_at_most_once` / `handle_abort_never_resumes` — stated at the very redex
       `Step.handle_perform` consumes; plus `cont_slot_demand_after_arg_subst`, which tracks the
       continuation-slot demand into the actual (argument-substituted) reduct.
   ═══════════════════════════════════════════════════════════════════════════════════════════ -/

open BlightMeta (insertTy insertUsage)

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Substitution machinery for Effects.Tm
-- ══════════════════════════════════════════════════════════════════════════════════════════════

namespace Tm

/-- Shift every free variable `≥ c` up by one. -/
def shiftAbove (c : Nat) : Tm → Tm
  | var i => if i < c then var i else var (i + 1)
  | lam body => lam (shiftAbove (c + 1) body)
  | app f a => app (shiftAbove c f) (shiftAbove c a)
  | tt => tt
  | ff => ff
  | ite cnd t e => ite (shiftAbove c cnd) (shiftAbove c t) (shiftAbove c e)
  | perform a => perform (shiftAbove c a)
  | handle body retC opC =>
      handle (shiftAbove c body) (shiftAbove (c + 1) retC) (shiftAbove (c + 2) opC)

/-- Capture-avoiding substitution: replace `var j` by `s`. -/
def subst (j : Nat) (s : Tm) : Tm → Tm
  | var i => if i = j then s else if i > j then var (i - 1) else var i
  | lam body => lam (subst (j + 1) (shiftAbove 0 s) body)
  | app f a => app (subst j s f) (subst j s a)
  | tt => tt
  | ff => ff
  | ite cnd t e => ite (subst j s cnd) (subst j s t) (subst j s e)
  | perform a => perform (subst j s a)
  | handle body retC opC =>
      handle (subst j s body) (subst (j + 1) (shiftAbove 0 s) retC)
        (subst (j + 2) (shiftAbove 0 (shiftAbove 0 s)) opC)

def subst0 (s body : Tm) : Tm := subst 0 s body

end Tm

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- usage_length + weaken for Effects.HasType
-- ══════════════════════════════════════════════════════════════════════════════════════════════

variable {opDom opCod : Ty} {opGrade : Grade}

theorem usage_length {Γ : List Ty} {e : Tm} {A : Ty} {σ : Grade} {E : Row} {φ : Usage}
    (h : HasType opDom opCod opGrade Γ e A σ E φ) : φ.length = Γ.length := by
  induction h with
  | @var Γ i A σ hlk => exact Usage.length_unit i Γ.length _ (lookup_lt hlk)
  | lam _ _ ih =>
    simp only [List.length_cons] at ih; omega
  | app _ _ ihf iha => simp [Usage.length_add, ihf, iha]
  | tt => simp
  | ff => simp
  | ite _ _ _ ihc iht ihe => simp [Usage.length_add, ihc, iht, ihe]
  | perform _ iha => exact iha
  | @handle Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade
      ihbody ihretC ihopC =>
    simp only [List.length_cons] at ihretC ihopC
    simp only [Usage.length_add, ihbody]
    omega

theorem weaken {Γ : List Ty} {e : Tm} {A : Ty} {σ : Grade} {E : Row} {φ : Usage}
    (h : HasType opDom opCod opGrade Γ e A σ E φ) : ∀ (c : Nat) (X : Ty),
    HasType opDom opCod opGrade (insertTy Γ c X) (Tm.shiftAbove c e) A σ E (insertUsage φ c) := by
  induction h with
  | @var Γ i A σ hlk =>
    intro c X
    have hlen : i < Γ.length := lookup_lt hlk
    rcases Nat.lt_or_ge i c with hic | hic
    · simp only [Tm.shiftAbove, if_pos hic]
      rw [insertUsage_unit_lt hic hlen]
      have hlk' : (insertTy Γ c X)[i]? = some A := (insertTy_get_lt hic hlen).trans hlk
      have hres := HasType.var (opDom := opDom) (opCod := opCod) (opGrade := opGrade)
        (Γ := insertTy Γ c X) (σ := σ) hlk'
      rwa [insertTy_length] at hres
    · simp only [Tm.shiftAbove, if_neg (Nat.not_lt.mpr hic)]
      rw [insertUsage_unit_ge hic hlen]
      have hlk' : (insertTy Γ c X)[i + 1]? = some A := (insertTy_get_ge hic).trans hlk
      have hres := HasType.var (opDom := opDom) (opCod := opCod) (opGrade := opGrade)
        (Γ := insertTy Γ c X) (i := i + 1) (σ := σ) hlk'
      rwa [insertTy_length] at hres
  | @lam Γ body ρ σ δ A B rest _ hle ihbody =>
    intro c X
    exact HasType.lam (ihbody (c + 1) X) hle
  | @app Γ f a ρ σ A B φf φa Ef Ea hf ha ihf iha =>
    intro c X
    have hlen : φf.length = φa.length := by rw [usage_length hf, usage_length ha]
    show HasType _ _ _ (insertTy Γ c X) (Tm.app (Tm.shiftAbove c f) (Tm.shiftAbove c a)) B σ _
      (insertUsage (Usage.add φf φa) c)
    rw [insertUsage_add hlen c]
    exact HasType.app (ihf c X) (iha c X)
  | @tt Γ σ =>
    intro c X
    show HasType _ _ _ (insertTy Γ c X) Tm.tt Ty.bool σ none (insertUsage (Usage.zero Γ.length) c)
    rw [insertUsage_zero, ← insertTy_length (Γ := Γ) (c := c) (X := X)]
    exact HasType.tt
  | @ff Γ σ =>
    intro c X
    show HasType _ _ _ (insertTy Γ c X) Tm.ff Ty.bool σ none (insertUsage (Usage.zero Γ.length) c)
    rw [insertUsage_zero, ← insertTy_length (Γ := Γ) (c := c) (X := X)]
    exact HasType.ff
  | @ite Γ cnd t e σ A φc φt φe Ec Et Ee hc ht he ihc iht ihe =>
    intro c X
    have hlc := usage_length hc
    have hlt := usage_length ht
    have hle := usage_length he
    have hlen1 : φt.length = φe.length := by rw [hlt, hle]
    have hlen2 : φc.length = (Usage.add φt φe).length := by
      rw [Usage.length_add, hlt, hle, hlc, Nat.min_self]
    show HasType _ _ _ (insertTy Γ c X)
      (Tm.ite (Tm.shiftAbove c cnd) (Tm.shiftAbove c t) (Tm.shiftAbove c e)) A σ _
      (insertUsage (Usage.add φc (Usage.add φt φe)) c)
    rw [insertUsage_add hlen2 c, insertUsage_add hlen1 c]
    exact HasType.ite (ihc c X) (iht c X) (ihe c X)
  | @perform Γ a σ φ ha iha =>
    intro c X
    exact HasType.perform (iha c X)
  | @handle Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade
      ihbody ihretC ihopC =>
    intro c X
    have hlb := usage_length hbody
    have hlr : φretC.length = Γ.length := by
      have := usage_length hretC; simp only [List.length_cons] at this; omega
    have hlo : φopC.length = Γ.length := by
      have := usage_length hopC; simp only [List.length_cons] at this; omega
    have hlen1 : φretC.length = φopC.length := by rw [hlr, hlo]
    have hlen2 : φbody.length = (Usage.add φretC φopC).length := by
      rw [Usage.length_add, hlr, hlo, hlb, Nat.min_self]
    -- IHs: retC weakened at c+1, opC weakened at c+2
    have hbody' := ihbody c X
    have hretC' := ihretC (c + 1) X
    have hopC' := ihopC (c + 2) X
    -- insertUsage of the cons'd usages
    have hins_ret : insertUsage (δret :: φretC) (c + 1) = δret :: insertUsage φretC c := rfl
    have hins_opc : insertUsage (δk :: δarg :: φopC) (c + 2)
        = δk :: δarg :: insertUsage φopC c := rfl
    rw [hins_ret] at hretC'
    rw [hins_opc] at hopC'
    show HasType _ _ _ (insertTy Γ c X)
      (Tm.handle (Tm.shiftAbove c body) (Tm.shiftAbove (c+1) retC) (Tm.shiftAbove (c+2) opC)) B σ
      none (insertUsage (Usage.add φbody (Usage.add φretC φopC)) c)
    rw [insertUsage_add hlen2 c, insertUsage_add hlen1 c]
    exact HasType.handle hbody' hretC' hopC' hgrade

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- ambient_zero_usage for Effects.HasType
-- ══════════════════════════════════════════════════════════════════════════════════════════════

theorem ambient_zero_usage {Γ : List Ty} {e : Tm} {A : Ty} {σ : Grade} {E : Row} {φ : Usage}
    (h : HasType opDom opCod opGrade Γ e A σ E φ) : σ = Grade.zero → φ = Usage.zero Γ.length := by
  induction h with
  | var => intro hσ; subst hσ; exact Usage.unit_zero _ _
  | lam _ _ ih =>
    intro hσ
    have htail := ih hσ
    injection htail with _ ht
  | app hf ha ihf iha =>
    intro hσ; subst hσ
    simp only [ihf rfl, iha rfl, Usage.add_zero_zero]
  | tt => intro _; rfl
  | ff => intro _; rfl
  | ite _ _ _ ihc iht ihe =>
    intro hσ; subst hσ
    simp only [ihc rfl, iht rfl, ihe rfl, Usage.add_zero_zero]
  | perform _ iha => intro hσ; exact iha hσ
  | @handle Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade
      ihbody ihretC ihopC =>
    intro hσ; subst hσ
    have hb := ihbody rfl
    have hr := ihretC rfl
    have ho := ihopC rfl
    -- hr : (δret :: φretC) = zero (A::Γ).length = 0 :: zero Γ.length
    simp only [List.length_cons, Usage.zero] at hr ho
    injection hr with _ hr2
    injection ho with _ ho'
    injection ho' with _ ho2
    simp only [hb, hr2, ho2, Usage.add_zero_zero]

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- demote / demote_scaled for Effects.HasType
-- ══════════════════════════════════════════════════════════════════════════════════════════════

theorem demote {Γ : List Ty} {e : Tm} {A : Ty} {σ : Grade} {E : Row} {φ : Usage}
    (h : HasType opDom opCod opGrade Γ e A σ E φ) :
    ∀ {σ' : Grade}, σ' ≤ σ → ∃ φ', HasType opDom opCod opGrade Γ e A σ' E φ' ∧ Usage.Le φ' φ := by
  induction h with
  | @var Γ i A σ hlk =>
    intro σ' hσ'
    exact ⟨Usage.unit i Γ.length σ', HasType.var hlk, Usage.unit_le hσ'⟩
  | @lam Γ body ρ σ δ A B rest hbody hle ihbody =>
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
  | @app Γ f a ρ σ A B φf φa Ef Ea hf ha ihf iha =>
    intro σ' hσ'
    obtain ⟨φf', hφf', hlef⟩ := ihf hσ'
    obtain ⟨φa', hφa', hlea⟩ := iha (Grade.mul_mono_left hσ' ρ)
    exact ⟨Usage.add φf' φa', HasType.app hφf' hφa', Usage.add_mono hlef hlea⟩
  | @tt Γ σ =>
    intro σ' _
    exact ⟨Usage.zero Γ.length, HasType.tt, Usage.le_refl _⟩
  | @ff Γ σ =>
    intro σ' _
    exact ⟨Usage.zero Γ.length, HasType.ff, Usage.le_refl _⟩
  | @ite Γ cnd t e σ A φc φt φe Ec Et Ee hc ht he ihc iht ihe =>
    intro σ' hσ'
    obtain ⟨φc', hφc', hlec⟩ := ihc hσ'
    obtain ⟨φt', hφt', hlet⟩ := iht hσ'
    obtain ⟨φe', hφe', hlee⟩ := ihe hσ'
    exact ⟨Usage.add φc' (Usage.add φt' φe'), HasType.ite hφc' hφt' hφe',
      Usage.add_mono hlec (Usage.add_mono hlet hlee)⟩
  | @perform Γ a σ φ ha iha =>
    intro σ' hσ'
    obtain ⟨φ', hφ', hLe⟩ := iha hσ'
    exact ⟨φ', HasType.perform hφ', hLe⟩
  | @handle Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade
      ihbody ihretC ihopC =>
    intro σ' hσ'
    obtain ⟨φb', hφb', hLeb⟩ := ihbody hσ'
    obtain ⟨φr', hφr', hLer⟩ := ihretC hσ'
    obtain ⟨φo', hφo', hLeo⟩ := ihopC hσ'
    -- split φr' = δret' :: φretC'
    have hlenr : φr'.length = (A :: Γ).length := usage_length hφr'
    obtain ⟨δret', φretC', hφr'eq⟩ : ∃ δret' φretC', φr' = δret' :: φretC' := by
      cases φr' with
      | nil => simp at hlenr
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφr'eq
    -- split φo' = δk' :: δarg' :: φopC'
    have hleno : φo'.length = ((.arr Grade.omega opCod B) :: opDom :: Γ).length := usage_length hφo'
    obtain ⟨δk', φo'', hφo'eq⟩ : ∃ δk' φo'', φo' = δk' :: φo'' := by
      cases φo' with
      | nil => simp at hleno
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφo'eq
    have hleno2 : φo''.length = (opDom :: Γ).length := by
      simp only [List.length_cons] at hleno ⊢; omega
    obtain ⟨δarg', φopC', hφo''eq⟩ : ∃ δarg' φopC', φo'' = δarg' :: φopC' := by
      cases φo'' with
      | nil => simp at hleno2
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφo''eq
    obtain ⟨hδk', hLeo'⟩ := hLeo
    obtain ⟨hδret', hLer'⟩ := hLer
    obtain ⟨hδarg', hLeo''⟩ := hLeo'
    refine ⟨Usage.add φb' (Usage.add φretC' φopC'),
      HasType.handle hφb' hφr' hφo' (Grade.le_trans hδk' hgrade), ?_⟩
    exact Usage.add_mono hLeb (Usage.add_mono hLer' hLeo'')

theorem demote_scaled {Γ : List Ty} {e : Tm} {A : Ty} {σ : Grade} {E : Row} {φ : Usage}
    (h : HasType opDom opCod opGrade Γ e A σ E φ) {σ' : Grade} (hσ' : σ' ≤ σ) :
    ∃ φ', HasType opDom opCod opGrade Γ e A σ' E φ' ∧ Usage.Le φ' (Usage.scale σ' φ) := by
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

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- The substitution lemma for Effects.HasType
-- ══════════════════════════════════════════════════════════════════════════════════════════════

theorem subst_lemma_aux {A' : Ty} {Γ0 : List Ty} {e : Tm} {B : Ty} {σ : Grade} {E : Row}
    {φ : Usage} (h : HasType opDom opCod opGrade Γ0 e B σ E φ) :
    ∀ {k : Nat} {Γ : List Ty}, Γ0 = insertTy Γ k A' → k ≤ Γ.length →
    ∀ {a : Tm} {π : Grade} {φa : Usage}, HasType opDom opCod opGrade Γ a A' π none φa → Usage.get φ k ≤ π →
    ∃ φ', HasType opDom opCod opGrade Γ (Tm.subst k a e) B σ E φ' ∧
      Usage.Le (insertUsage φ' k) (Usage.add φ (Usage.scale (Usage.get φ k) (insertUsage φa k))) := by
  induction h with
  | @var Γ0 i A σ hlk =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    rw [insertTy_length] at hget ⊢
    rcases Nat.lt_trichotomy i k with hik | hik | hik
    · have hiG : i < Γ.length := by omega
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
    · have hAeq : A = A' := by
        have h1 := insertTy_get_eq (Γ := Γ) (c := k) (X := A') hk
        rw [hik] at hlk
        rw [hlk] at h1
        exact Option.some.inj h1
      have hgetk : (Usage.unit i (Γ.length + 1) σ).get i = σ :=
        Usage.get_unit_same i (Γ.length + 1) σ (by omega)
      rw [hik] at hgetk hget
      rw [hgetk] at hget
      have ha2 : HasType opDom opCod opGrade Γ a A π none φa := by rw [hAeq]; exact ha
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
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
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
  | @lam Γ0 body ρ σ δ A B rest hbody hle ihbody =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    have heq2 : A :: insertTy Γ k A' = insertTy (A :: Γ) (k + 1) A' := rfl
    rw [heq2] at hbody
    have ha' : HasType opDom opCod opGrade (A :: Γ) (Tm.shiftAbove 0 a) A' π none (insertUsage φa 0) := by
      have hw := weaken ha 0 A
      rwa [insertTy_zero] at hw
    have hget' : Usage.get (δ :: rest) (k + 1) ≤ π := hget
    obtain ⟨φ'', hφ'', hLe⟩ :=
      @ihbody (k + 1) (A :: Γ) rfl (by simp only [List.length_cons]; omega)
        (Tm.shiftAbove 0 a) π (insertUsage φa 0) ha' hget'
    have hgeteq : Usage.get (δ :: rest) (k + 1) = Usage.get rest k := rfl
    rw [hgeteq] at hLe
    have hlen : φ''.length = (A :: Γ).length := usage_length hφ''
    obtain ⟨δ', rest', hφ''eq⟩ : ∃ δ' rest', φ'' = δ' :: rest' := by
      cases φ'' with
      | nil => simp at hlen
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφ''eq
    have hLe' :
        Usage.Le (δ' :: insertUsage rest' k)
          (δ :: Usage.add rest (Usage.scale (Usage.get rest k) (insertUsage φa k))) := by
      have hins1 : insertUsage (δ' :: rest') (k + 1) = δ' :: insertUsage rest' k := rfl
      have hins2 : insertUsage φa 0 = Grade.zero :: φa := insertUsage_cons_zero φa
      have hins3 : insertUsage (Grade.zero :: φa) (k + 1) = Grade.zero :: insertUsage φa k := rfl
      rw [hins1] at hLe
      rw [hins2, hins3] at hLe
      have hrhs :
          Usage.add (δ :: rest) (Usage.scale (Usage.get rest k) (Grade.zero :: insertUsage φa k))
            = δ :: Usage.add rest (Usage.scale (Usage.get rest k) (insertUsage φa k)) := by
        have hmulzero : (Usage.get rest k).mul Grade.zero = Grade.zero := by
          cases (Usage.get rest k) <;> rfl
        simp only [Usage.scale, Usage.add, hmulzero, Grade.add_zero]
      rw [hrhs] at hLe
      exact hLe
    obtain ⟨hδδ, hLetail⟩ := hLe'
    refine ⟨rest', by exact HasType.lam hφ'' (Grade.le_trans hδδ hle), hLetail⟩
  | @app Γ0 f arg ρ σ A B φf φarg Ef Ea hf harg ihf iharg =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    have hgetsum : (Usage.get φf k).add (Usage.get φarg k) ≤ π := by
      have := hget
      rwa [Usage.get_add (by rw [usage_length hf, usage_length harg])] at this
    have hgetf : Usage.get φf k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgetsum
    have hgetarg : Usage.get φarg k ≤ π := Grade.le_trans (Grade.self_le_add_right _ _) hgetsum
    obtain ⟨φf', hφf', hLef⟩ := ihf rfl hk ha hgetf
    obtain ⟨φarg', hφarg', hLearg⟩ := iharg rfl hk ha hgetarg
    refine ⟨Usage.add φf' φarg', HasType.app hφf' hφarg', ?_⟩
    exact insertUsage_scale_add_bound
      (by rw [usage_length hf, usage_length harg])
      (by rw [usage_length hf, insertTy_length, insertUsage_length, usage_length ha])
      (by rw [usage_length hφf', usage_length hφarg']) hLef hLearg
  | @tt Γ0 σ =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    refine ⟨Usage.zero Γ.length, HasType.tt, ?_⟩
    rw [insertUsage_zero, insertTy_length]
    rw [Usage.get_zero, Usage.scale_zero, insertUsage_length, usage_length ha, Usage.add_zero_zero]
    exact Usage.le_refl _
  | @ff Γ0 σ =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    refine ⟨Usage.zero Γ.length, HasType.ff, ?_⟩
    rw [insertUsage_zero, insertTy_length]
    rw [Usage.get_zero, Usage.scale_zero, insertUsage_length, usage_length ha, Usage.add_zero_zero]
    exact Usage.le_refl _
  | @ite Γ0 cnd t el σ A φc φt φel Ec Et Ee hc ht hel ihc iht ihel =>
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
    have hgetsum : (Usage.get φc k).add ((Usage.get φt k).add (Usage.get φel k)) ≤ π := by
      have h1 := hget
      rw [Usage.get_add hlen_c_tel, Usage.get_add hlen_t_el] at h1
      exact h1
    have hgetc : Usage.get φc k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgetsum
    have hgettel : (Usage.get φt k).add (Usage.get φel k) ≤ π :=
      Grade.le_trans (Grade.self_le_add_right _ _) hgetsum
    have hgett : Usage.get φt k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgettel
    have hgetel : Usage.get φel k ≤ π := Grade.le_trans (Grade.self_le_add_right _ _) hgettel
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
  | @perform Γ0 arg σ φ harg iharg =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    obtain ⟨φ', hφ', hLe⟩ := iharg rfl hk ha hget
    exact ⟨φ', HasType.perform hφ', hLe⟩
  | @handle Γ0 body retC opC σ A B φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade
      ihbody ihretC ihopC =>
    intro k Γ heq hk a π φa ha hget
    subst heq
    -- lengths
    have hlb : φbody.length = Γ.length + 1 := by rw [usage_length hbody, insertTy_length]
    have hlr : φretC.length = Γ.length + 1 := by
      have := usage_length hretC
      simp only [List.length_cons, insertTy_length] at this; omega
    have hlo : φopC.length = Γ.length + 1 := by
      have := usage_length hopC
      simp only [List.length_cons, insertTy_length] at this; omega
    have hlenX : (insertUsage φa k).length = Γ.length + 1 := by
      rw [insertUsage_length, usage_length ha]
    have hlen_b_ro : φbody.length = (Usage.add φretC φopC).length := by
      rw [Usage.length_add, hlr, hlo, Nat.min_self, hlb]
    have hlen_r_o : φretC.length = φopC.length := hlr.trans hlo.symm
    -- split the get-bound: (add φbody (add φretC φopC)).get k ≤ π
    have hgetsum : (Usage.get φbody k).add ((Usage.get φretC k).add (Usage.get φopC k)) ≤ π := by
      have h1 := hget
      rw [Usage.get_add hlen_b_ro, Usage.get_add hlen_r_o] at h1
      exact h1
    have hgetb : Usage.get φbody k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgetsum
    have hgetro : (Usage.get φretC k).add (Usage.get φopC k) ≤ π :=
      Grade.le_trans (Grade.self_le_add_right _ _) hgetsum
    have hgetr : Usage.get φretC k ≤ π := Grade.le_trans (Grade.self_le_add_left _ _) hgetro
    have hgeto : Usage.get φopC k ≤ π := Grade.le_trans (Grade.self_le_add_right _ _) hgetro
    -- === body ===
    obtain ⟨φbody', hφbody', hLeb⟩ := ihbody rfl hk ha hgetb
    -- === retC : substitute at k+1 in insertTy (A::Γ) (k+1) A' ===
    have heqR : A :: insertTy Γ k A' = insertTy (A :: Γ) (k + 1) A' := rfl
    rw [heqR] at hretC
    have haR : HasType opDom opCod opGrade (A :: Γ) (Tm.shiftAbove 0 a) A' π none (insertUsage φa 0) := by
      have hw := weaken ha 0 A
      rwa [insertTy_zero] at hw
    have hgetR' : Usage.get (δret :: φretC) (k + 1) ≤ π := by
      show Usage.get φretC k ≤ π; exact hgetr
    obtain ⟨φR'', hφR'', hLeR⟩ :=
      @ihretC (k + 1) (A :: Γ) rfl (by simp only [List.length_cons]; omega)
        (Tm.shiftAbove 0 a) π (insertUsage φa 0) haR hgetR'
    -- split φR'' = δret' :: φretC'
    have hlenR'' : φR''.length = (A :: Γ).length := usage_length hφR''
    obtain ⟨δret', φretC', hφR''eq⟩ : ∃ δret' φretC', φR'' = δret' :: φretC' := by
      cases φR'' with
      | nil => simp at hlenR''
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφR''eq
    -- === opC : substitute at k+2 in insertTy ((arr ω opCod B)::opDom::Γ) (k+2) A' ===
    have heqO : (.arr Grade.omega opCod B) :: opDom :: insertTy Γ k A'
        = insertTy ((.arr Grade.omega opCod B) :: opDom :: Γ) (k + 2) A' := rfl
    rw [heqO] at hopC
    have haO : HasType opDom opCod opGrade ((.arr Grade.omega opCod B) :: opDom :: Γ)
        (Tm.shiftAbove 0 (Tm.shiftAbove 0 a)) A' π none (insertUsage (insertUsage φa 0) 0) := by
      have hw1 := weaken ha 0 opDom
      rw [insertTy_zero] at hw1
      have hw2 := weaken hw1 0 (.arr Grade.omega opCod B)
      rw [insertTy_zero] at hw2
      exact hw2
    have hgetO' : Usage.get (δk :: δarg :: φopC) (k + 2) ≤ π := by
      show Usage.get φopC k ≤ π; exact hgeto
    obtain ⟨φO'', hφO'', hLeO⟩ :=
      @ihopC (k + 2) ((.arr Grade.omega opCod B) :: opDom :: Γ) rfl
        (by simp only [List.length_cons]; omega)
        (Tm.shiftAbove 0 (Tm.shiftAbove 0 a)) π (insertUsage (insertUsage φa 0) 0) haO hgetO'
    -- split φO'' = δk' :: δarg' :: φopC'
    have hlenO'' : φO''.length = ((.arr Grade.omega opCod B) :: opDom :: Γ).length :=
      usage_length hφO''
    obtain ⟨δk', φO2, hφO''eq⟩ : ∃ δk' φO2, φO'' = δk' :: φO2 := by
      cases φO'' with
      | nil => simp at hlenO''
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφO''eq
    have hlenO2 : φO2.length = (opDom :: Γ).length := by
      simp only [List.length_cons] at hlenO'' ⊢; omega
    obtain ⟨δarg', φopC', hφO2eq⟩ : ∃ δarg' φopC', φO2 = δarg' :: φopC' := by
      cases φO2 with
      | nil => simp at hlenO2
      | cons x xs => exact ⟨x, xs, rfl⟩
    subst hφO2eq
    -- Normalize hLeR to lam-style cons form:
    -- Le (δret' :: insertUsage φretC' k) (δret :: add φretC (scale (Usage.get φretC k) (insertUsage φa k)))
    have hmulz : ∀ (g : Grade), g.mul Grade.zero = Grade.zero := fun g => by cases g <;> rfl
    have hLeR' : Usage.Le (δret' :: insertUsage φretC' k)
        (δret :: Usage.add φretC (Usage.scale (Usage.get φretC k) (insertUsage φa k))) := by
      have hins1 : insertUsage (δret' :: φretC') (k + 1) = δret' :: insertUsage φretC' k := rfl
      rw [hins1] at hLeR
      have hgeteq : Usage.get (δret :: φretC) (k + 1) = Usage.get φretC k := rfl
      have hXeq : insertUsage (insertUsage φa 0) (k + 1) = Grade.zero :: insertUsage φa k := by
        rw [insertUsage_cons_zero]; rfl
      rw [hgeteq, hXeq] at hLeR
      have hrhs :
          Usage.add (δret :: φretC) (Usage.scale (Usage.get φretC k) (Grade.zero :: insertUsage φa k))
            = δret :: Usage.add φretC (Usage.scale (Usage.get φretC k) (insertUsage φa k)) := by
        simp only [Usage.scale, Usage.add, hmulz, Grade.add_zero]
      rw [hrhs] at hLeR
      exact hLeR
    obtain ⟨hδret'le, hLeRtail⟩ := hLeR'
    -- Normalize hLeO to double-cons form.
    have hLeO' : Usage.Le (δk' :: δarg' :: insertUsage φopC' k)
        (δk :: δarg :: Usage.add φopC (Usage.scale (Usage.get φopC k) (insertUsage φa k))) := by
      have hins1 : insertUsage (δk' :: δarg' :: φopC') (k + 2)
          = δk' :: δarg' :: insertUsage φopC' k := rfl
      rw [hins1] at hLeO
      have hgeteq : Usage.get (δk :: δarg :: φopC) (k + 2) = Usage.get φopC k := rfl
      have hXeq : insertUsage (insertUsage (insertUsage φa 0) 0) (k + 2)
          = Grade.zero :: Grade.zero :: insertUsage φa k := by
        rw [insertUsage_cons_zero φa, insertUsage_cons_zero (Grade.zero :: φa)]; rfl
      rw [hgeteq, hXeq] at hLeO
      have hrhs :
          Usage.add (δk :: δarg :: φopC)
              (Usage.scale (Usage.get φopC k) (Grade.zero :: Grade.zero :: insertUsage φa k))
            = δk :: δarg :: Usage.add φopC (Usage.scale (Usage.get φopC k) (insertUsage φa k)) := by
        simp only [Usage.scale, Usage.add, hmulz, Grade.add_zero]
      rw [hrhs] at hLeO
      exact hLeO
    obtain ⟨hδk'le, hLeOrest⟩ := hLeO'
    obtain ⟨hδarg'le, hLeOtail⟩ := hLeOrest
    -- δk' ≤ δk ≤ opGrade
    refine ⟨Usage.add φbody' (Usage.add φretC' φopC'),
      HasType.handle hφbody' hφR'' hφO'' (Grade.le_trans hδk'le hgrade), ?_⟩
    -- combine the three tail bounds via insertUsage_scale_add_bound (twice, like ite)
    have hlb' : φbody'.length = Γ.length := usage_length hφbody'
    have hlr' : φretC'.length = Γ.length := by
      have := usage_length hφR''; simp only [List.length_cons] at this; omega
    have hlo' : φopC'.length = Γ.length := by
      have := usage_length hφO''; simp only [List.length_cons] at this; omega
    have hLero : Usage.Le (insertUsage (Usage.add φretC' φopC') k)
        (Usage.add (Usage.add φretC φopC)
          (Usage.scale ((Usage.add φretC φopC).get k) (insertUsage φa k))) :=
      insertUsage_scale_add_bound hlen_r_o (hlr.trans hlenX.symm)
        (by rw [hlr', hlo']) hLeRtail hLeOtail
    exact insertUsage_scale_add_bound hlen_b_ro (hlb.trans hlenX.symm)
      (by rw [hlb', Usage.length_add, hlr', hlo', Nat.min_self]) hLeb hLero

/-- The public form of the substitution lemma for the effect fragment. -/
theorem subst_lemma {Γ : List Ty} {a : Tm} {A' : Ty} {π : Grade} {φa : Usage}
    (ha : HasType opDom opCod opGrade Γ a A' π none φa) {k : Nat} {e : Tm} {B : Ty} {σ : Grade}
    {E : Row} {φ : Usage}
    (h : HasType opDom opCod opGrade (insertTy Γ k A') e B σ E φ) (hk : k ≤ Γ.length)
    (hget : Usage.get φ k ≤ π) :
    ∃ φ', HasType opDom opCod opGrade Γ (Tm.subst k a e) B σ E φ' ∧
      Usage.Le (insertUsage φ' k) (Usage.add φ (Usage.scale (Usage.get φ k) (insertUsage φa k))) :=
  subst_lemma_aux h rfl hk ha hget

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Operational semantics: Value, evaluation contexts, Step
-- ══════════════════════════════════════════════════════════════════════════════════════════════

/-- Closed values: the STLC value formers (`handle`/`perform` are eliminator-shaped, never values;
    a `lam` body is delimited so a performing lambda body is not itself a value). -/
inductive Value : Tm → Prop where
  | lam {body : Tm} : Value (.lam body)
  | tt : Value .tt
  | ff : Value .ff

/-- One-hole evaluation contexts for call-by-value, up to the innermost enclosing `handle`. The
    hole may sit under `app` (either side, right only once the left is a value), the `ite`
    scrutinee, or a `perform` argument — but NOT under a `lam` or a `handle` (a `handle` delimits
    the continuation `E` a `perform` inside it captures). -/
inductive ECtx : Type where
  | hole
  | appL (E : ECtx) (a : Tm)
  | appR (f : Tm) (hf : Value f) (E : ECtx)
  | iteC (E : ECtx) (t e : Tm)
  | perf (E : ECtx)

/-- Plug a term into the hole of an evaluation context. -/
def ECtx.plug : ECtx → Tm → Tm
  | hole, t => t
  | appL E a, t => .app (E.plug t) a
  | appR f _ E, t => .app f (E.plug t)
  | iteC E th el, t => .ite (E.plug t) th el
  | perf E, t => .perform (E.plug t)

/-- Small-step reduction.  The pure core is standard CBV.  `handle_body` reduces the handled body
    in place; `handle_ret` fires the return clause once the body is a value; `handle_perform` is
    the deep-handler rule: a `perform v` sitting in evaluation position `E` under the handle fires
    the op-clause with the argument `v` (index 1) and the *captured, handler-re-installing*
    continuation `lam (handle E[var 0] retC opC)` (index 0). -/
inductive Step : Tm → Tm → Prop where
  | app1 {f f' a : Tm} (h : Step f f') : Step (.app f a) (.app f' a)
  | app2 {f a a' : Tm} (hf : Value f) (h : Step a a') : Step (.app f a) (.app f a')
  | beta {body a : Tm} (ha : Value a) : Step (.app (.lam body) a) (Tm.subst0 a body)
  | ite_cond {c c' t e : Tm} (h : Step c c') : Step (.ite c t e) (.ite c' t e)
  | ite_tt {t e : Tm} : Step (.ite .tt t e) t
  | ite_ff {t e : Tm} : Step (.ite .ff t e) e
  | perform_arg {a a' : Tm} (h : Step a a') : Step (.perform a) (.perform a')
  | handle_body {body body' retC opC : Tm} (h : Step body body') :
      Step (.handle body retC opC) (.handle body' retC opC)
  | handle_ret {v retC opC : Tm} (hv : Value v) :
      Step (.handle v retC opC) (Tm.subst0 v retC)
  | handle_perform {E : ECtx} {v retC opC : Tm} (hv : Value v) :
      Step (.handle (E.plug (.perform v)) retC opC)
        (Tm.subst0 (Tm.lam (.handle (E.plug (.var 0)) retC opC)) (Tm.subst 1 v opC))

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Canonical forms + progress
-- ══════════════════════════════════════════════════════════════════════════════════════════════

/-- A closed value at `Bool` is `tt` or `ff`. -/
theorem canonical_bool {v : Tm} {σ E φ} (hv : Value v)
    (h : HasType opDom opCod opGrade [] v .bool σ E φ) : v = .tt ∨ v = .ff := by
  cases hv with
  | tt => exact Or.inl rfl
  | ff => exact Or.inr rfl
  | lam => cases h

/-- A closed value at an arrow type is a `lam`. -/
theorem canonical_arr {v : Tm} {ρ A B σ E φ} (hv : Value v)
    (h : HasType opDom opCod opGrade [] v (.arr ρ A B) σ E φ) : ∃ body, v = .lam body := by
  cases hv with
  | lam => exact ⟨_, rfl⟩
  | tt => cases h
  | ff => cases h

/-- **Decomposition / progress-with-residual-perform.** A closed, well-typed term is a value, can
    take a step, or is `E[perform v]` — a `perform` of a value sitting in evaluation position (the
    residual-effect "stuck" state that only an *enclosing* `handle` can discharge). -/
theorem progress_or_perform {e : Tm} {A σ E φ}
    (h : HasType opDom opCod opGrade [] e A σ E φ) :
    Value e ∨ (∃ e', Step e e') ∨ (∃ (Ec : ECtx) (v : Tm), Value v ∧ e = Ec.plug (.perform v)) := by
  generalize hΓ : ([] : List Ty) = Γ at h
  induction h with
  | @var Γ i A σ hlk => subst hΓ; simp at hlk
  | lam _ _ _ => exact Or.inl .lam
  | @app Γ f a ρ σ A B φf φa Ef Ea hf ha ihf iha =>
    subst hΓ
    rcases ihf rfl with hfv | ⟨f', hf'⟩ | ⟨Ec, v, hv, rfl⟩
    · rcases iha rfl with hav | ⟨a', ha'⟩ | ⟨Ec, v, hv, rfl⟩
      · obtain ⟨body, rfl⟩ := canonical_arr hfv hf
        exact Or.inr (Or.inl ⟨_, .beta hav⟩)
      · exact Or.inr (Or.inl ⟨_, .app2 hfv ha'⟩)
      · exact Or.inr (Or.inr ⟨ECtx.appR f hfv Ec, v, hv, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, .app1 hf'⟩)
    · exact Or.inr (Or.inr ⟨ECtx.appL Ec a, v, hv, rfl⟩)
  | tt => exact Or.inl .tt
  | ff => exact Or.inl .ff
  | @ite Γ c t e σ A φc φt φe Ec Et Ee hc ht he ihc iht ihe =>
    subst hΓ
    rcases ihc rfl with hcv | ⟨c', hc'⟩ | ⟨Ectx, v, hv, rfl⟩
    · rcases canonical_bool hcv hc with rfl | rfl
      · exact Or.inr (Or.inl ⟨_, .ite_tt⟩)
      · exact Or.inr (Or.inl ⟨_, .ite_ff⟩)
    · exact Or.inr (Or.inl ⟨_, .ite_cond hc'⟩)
    · exact Or.inr (Or.inr ⟨ECtx.iteC Ectx t e, v, hv, rfl⟩)
  | @perform Γ a σ φ ha iha =>
    subst hΓ
    rcases iha rfl with hav | ⟨a', ha'⟩ | ⟨Ec, v, hv, rfl⟩
    · exact Or.inr (Or.inr ⟨ECtx.hole, a, hav, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, .perform_arg ha'⟩)
    · exact Or.inr (Or.inr ⟨ECtx.perf Ec, v, hv, rfl⟩)
  | @handle Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade
      ihbody ihretC ihopC =>
    subst hΓ
    rcases ihbody rfl with hbv | ⟨body', hb'⟩ | ⟨Ec, v, hv, rfl⟩
    · exact Or.inr (Or.inl ⟨_, .handle_ret hbv⟩)
    · exact Or.inr (Or.inl ⟨_, .handle_body hb'⟩)
    · exact Or.inr (Or.inl ⟨_, .handle_perform hv⟩)

/-- `Row.union` with a `some` on either side is `some`. -/
theorem Row.union_some_left {g : Grade} (r : Row) : ∃ g', Row.union (some g) r = some g' := by
  cases r with
  | none => exact ⟨g, rfl⟩
  | some g2 => exact ⟨g.add g2, rfl⟩

theorem Row.union_some_right {g : Grade} (r : Row) : ∃ g', Row.union r (some g) = some g' := by
  cases r with
  | none => exact ⟨g, rfl⟩
  | some g2 => exact ⟨g2.add g, rfl⟩

/-- Any well-typed `E[perform w]` carries a non-`none` row: the sole effect performed inside a bare
    evaluation context is never discharged (only a `handle` — which is not an `ECtx` former — can
    discharge it). Proved by induction on the context `Ec`. -/
theorem plug_perform_row_some (Ec : ECtx) {Γ w A σ E φ}
    (h : HasType opDom opCod opGrade Γ (Ec.plug (.perform w)) A σ E φ) :
    ∃ g, E = some g := by
  induction Ec generalizing Γ A σ E φ with
  | hole =>
    cases h with
    | perform _ => exact ⟨opGrade, rfl⟩
  | appL Ec' a ih =>
    cases h with
    | app hf ha =>
      obtain ⟨g, rfl⟩ := ih hf
      exact Row.union_some_left _
  | appR f hf Ec' ih =>
    cases h with
    | app hf0 ha =>
      obtain ⟨g, rfl⟩ := ih ha
      exact Row.union_some_right _
  | iteC Ec' t e ih =>
    cases h with
    | ite hc ht he =>
      obtain ⟨g, rfl⟩ := ih hc
      exact Row.union_some_left _
  | perf Ec' ih =>
    -- `perform` requires its argument pure-rowed, but the argument here is `Ec'[perform w]`, whose
    -- row is `some _` by IH — so this configuration is not well-typed at all (a `perform` never
    -- nests inside another `perform`'s argument).  The contradiction closes the goal.
    cases h with
    | perform ha =>
      obtain ⟨g, hg⟩ := ih ha
      exact absurd hg (by simp)

/-- **Progress** for the effect fragment: a closed, well-typed, *pure-rowed* (`E = none`) term is a
    value or steps.  A `none` row rules out the residual-`perform` case, since any `E[perform v]`
    carries a `some _` row (the sole effect is not discharged by a bare evaluation context). -/
theorem progress {e : Tm} {A σ φ}
    (h : HasType opDom opCod opGrade [] e A σ (none : Row) φ) : Value e ∨ ∃ e', Step e e' := by
  rcases progress_or_perform h with hv | hstep | ⟨Ec, v, hv, heq⟩
  · exact Or.inl hv
  · exact Or.inr hstep
  · subst heq
    obtain ⟨g, hg⟩ := plug_perform_row_some Ec h
    exact absurd hg (by simp)

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Preservation
-- ══════════════════════════════════════════════════════════════════════════════════════════════

/-- Every value is pure-rowed: `lam`/`tt`/`ff` all carry row `none`. -/
theorem value_row_none {Γ v A σ E φ} (hv : Value v)
    (h : HasType opDom opCod opGrade Γ v A σ E φ) : E = none := by
  cases hv with
  | lam => cases h with | lam _ _ => rfl
  | tt => cases h with | tt => rfl
  | ff => cases h with | ff => rfl

/-- Sub-row order: `none` (pure) is below everything, and `some g ≤ some g'` iff `g ≤ g'` in the
    grade order. Reduction can only *discard* effects (e.g. an `ite` selecting one branch drops the
    other branches' latent effects), so the reduct's row sits at or below the redex's. -/
def Row.Le : Row → Row → Prop
  | none, _ => True
  | some _, none => False
  | some g, some g' => g ≤ g'

theorem Row.Le.refl (r : Row) : Row.Le r r := by
  cases r with
  | none => trivial
  | some g => exact Grade.le_refl g

theorem Row.Le.trans {r1 r2 r3 : Row} (h1 : Row.Le r1 r2) (h2 : Row.Le r2 r3) : Row.Le r1 r3 := by
  cases r1 with
  | none => trivial
  | some g1 => cases r2 with
    | none => exact absurd h1 (by simp [Row.Le])
    | some g2 => cases r3 with
      | none => exact absurd h2 (by simp [Row.Le])
      | some g3 => exact Grade.le_trans h1 h2

/-- `union` is monotone and a term's row is ≤ the union with anything (effects only accumulate). -/
theorem Row.le_union_left (r s : Row) : Row.Le r (Row.union r s) := by
  cases r with
  | none => trivial
  | some g => cases s with
    | none => exact Grade.le_refl g
    | some g2 => exact Grade.self_le_add_left g g2

theorem Row.le_union_right (r s : Row) : Row.Le s (Row.union r s) := by
  cases s with
  | none => cases r <;> trivial
  | some g => cases r with
    | none => exact Grade.le_refl g
    | some g2 => exact Grade.self_le_add_right g g2

theorem Row.union_mono {r r' s s' : Row} (hr : Row.Le r r') (hs : Row.Le s s') :
    Row.Le (Row.union r s) (Row.union r' s') := by
  cases r with
  | none =>
    cases s with
    | none => cases r' <;> cases s' <;> trivial
    | some g =>
      cases s' with
      | none => exact absurd hs (by simp [Row.Le])
      | some g' => cases r' with
        | none => exact hs
        | some gr' => exact Grade.le_trans hs (Grade.self_le_add_right g' gr')
  | some g =>
    cases r' with
    | none => exact absurd hr (by simp [Row.Le])
    | some gr' =>
      cases s with
      | none =>
        cases s' with
        | none => exact hr
        | some gs' => exact Grade.le_trans hr (Grade.self_le_add_left gr' gs')
      | some gs =>
        cases s' with
        | none => exact absurd hs (by simp [Row.Le])
        | some gs' =>
          exact Grade.le_trans (Grade.add_mono_left hr gs) (Grade.add_mono_right gr' hs)

/-- A step that is *not* the deep-handler `handle_perform` rule. Everything the pure core plus the
    return-clause (`handle_ret`) and the congruences can do — the fragment for which type/row
    preservation genuinely holds. -/
inductive StepC : Tm → Tm → Prop where
  | app1 {f f' a : Tm} (h : StepC f f') : StepC (.app f a) (.app f' a)
  | app2 {f a a' : Tm} (hf : Value f) (h : StepC a a') : StepC (.app f a) (.app f a')
  | beta {body a : Tm} (ha : Value a) : StepC (.app (.lam body) a) (Tm.subst0 a body)
  | ite_cond {c c' t e : Tm} (h : StepC c c') : StepC (.ite c t e) (.ite c' t e)
  | ite_tt {t e : Tm} : StepC (.ite .tt t e) t
  | ite_ff {t e : Tm} : StepC (.ite .ff t e) e
  | perform_arg {a a' : Tm} (h : StepC a a') : StepC (.perform a) (.perform a')
  | handle_body {body body' retC opC : Tm} (h : StepC body body') :
      StepC (.handle body retC opC) (.handle body' retC opC)
  | handle_ret {v retC opC : Tm} (hv : Value v) :
      StepC (.handle v retC opC) (Tm.subst0 v retC)

/-- **Preservation for the type-preserving fragment** (`StepC`): a `StepC` step preserves the term's
    type `A` and ambient grade `σ`, and the reduct's row `E'` is a *sub-row* of the redex's `E`
    (`Row.Le E' E`) — reduction only ever discards latent effects (e.g. an `ite` dropping the
    unselected branch), never introduces them.  Only the usage `φ` is left existential, exactly as
    `Progress.lean`'s `preservation` does for the base calculus.  The `beta`/`handle_ret` cases
    hinge on values being pure-rowed (`value_row_none`). -/
theorem preservation_core {Γ e e' A σ E φ} (hσ : σ = Grade.omega ∨ σ = Grade.zero)
    (h : HasType opDom opCod opGrade Γ e A σ E φ) (hstep : StepC e e') :
    ∃ E' φ', HasType opDom opCod opGrade Γ e' A σ E' φ' ∧ Row.Le E' E := by
  induction hstep generalizing Γ A σ E φ with
  | app1 _ ih =>
    cases h with
    | app hf0 ha0 =>
      obtain ⟨Ef', φf', hφf', hLef⟩ := ih hσ hf0
      exact ⟨_, _, HasType.app hφf' ha0, Row.union_mono hLef (Row.Le.refl _)⟩
  | app2 _ _ ih =>
    cases h with
    | @app _ _ _ ρ _ _ _ _ _ _ _ hf0 ha0 =>
      -- argument checked at σ·ρ; the {ω,0} invariant is closed under `·ρ`.
      have hσ' : σ.mul ρ = Grade.omega ∨ σ.mul ρ = Grade.zero := by
        rcases hσ with rfl | rfl
        · cases ρ <;> simp [Grade.mul]
        · right; rfl
      obtain ⟨Ea', φa', hφa', hLea⟩ := ih hσ' ha0
      exact ⟨_, _, HasType.app hf0 hφa', Row.union_mono (Row.Le.refl _) hLea⟩
  | @beta body a haval =>
    cases h with
    | @app _ _ _ ρ _ Adom _ φf φa Ef Ea hf0 ha0 =>
      cases hf0 with
      | @lam _ _ _ _ δ _ _ _ hbody hle =>
        have hEa : Ea = none := value_row_none haval ha0
        subst hEa
        have hzero : σ = Grade.zero → δ = Grade.zero := by
          intro hσ
          have hz := ambient_zero_usage hbody hσ
          injection hz with hδ _
        have hget : Usage.get (δ :: φf) 0 ≤ σ.mul ρ := demand_le_scale hle hzero
        have hbody' : HasType opDom opCod opGrade (insertTy Γ 0 Adom) body A σ none (δ :: φf) := by
          rw [insertTy_zero]; exact hbody
        obtain ⟨φ', hφ', _⟩ := subst_lemma ha0 hbody' (Nat.zero_le _) hget
        -- app row = union none none = none; result row = none.
        exact ⟨none, φ', hφ', Row.Le.refl _⟩
  | ite_cond _ ih =>
    cases h with
    | ite hc0 ht0 he0 =>
      obtain ⟨Ec', φc', hφc', hLec⟩ := ih hσ hc0
      exact ⟨_, _, HasType.ite hφc' ht0 he0, Row.union_mono hLec (Row.Le.refl _)⟩
  | ite_tt =>
    cases h with
    | @ite _ _ _ _ _ _ _ _ _ Ec Et Ee hc0 ht0 he0 =>
      -- result is `t`, row Et; ite row = union Ec (union Et Ee) ≥ Et.
      exact ⟨Et, _, ht0, Row.Le.trans (Row.le_union_left Et Ee) (Row.le_union_right Ec _)⟩
  | ite_ff =>
    cases h with
    | @ite _ _ _ _ _ _ _ _ _ Ec Et Ee hc0 ht0 he0 =>
      exact ⟨Ee, _, he0, Row.Le.trans (Row.le_union_right Et Ee) (Row.le_union_right Ec _)⟩
  | perform_arg _ ih =>
    cases h with
    | perform ha0 =>
      obtain ⟨Ea', φ', hφ', _⟩ := ih hσ ha0
      -- perform's argument is required pure-rowed; its reduct is again pure-rowed (Ea' ≤ none ⟹
      -- Ea' = none), so the perform still has row `some opGrade`.
      have hEa' : Ea' = none := by
        cases Ea' with
        | none => rfl
        | some g => exact absurd (by assumption : Row.Le (some g) none) (by simp [Row.Le])
      subst hEa'
      exact ⟨some opGrade, φ', HasType.perform hφ', Row.Le.refl _⟩
  | handle_body _ ih =>
    cases h with
    | handle hbody0 hretC0 hopC0 hgrade0 =>
      obtain ⟨Eb', φ', hφ', _⟩ := ih hσ hbody0
      exact ⟨none, _, HasType.handle hφ' hretC0 hopC0 hgrade0, Row.Le.refl _⟩
  | @handle_ret v retC opC hv =>
    cases h with
    | @handle _ _ _ _ _ Adom _ φbody φretC φopC δret δk δarg Ebody hbody0 hretC0 hopC0 hgrade0 =>
      -- retC : B in (Adom::Γ), pure; the returned value v : Adom is substituted at slot 0.
      have hretC' := hretC0
      rw [← insertTy_zero Γ Adom] at hretC'
      have hEb : Ebody = none := value_row_none hv hbody0
      subst hEb
      -- Under the runtime ambient invariant σ ∈ {ω, 0}, the return binder's demand δret is ≤ the
      -- grade at which the body value is available, so the substitution lemma applies.
      rcases hσ with rfl | rfl
      · -- σ = ω:  v : A at ω, and δret ≤ ω (ω is the order's top).
        have hget : Usage.get (δret :: φretC) 0 ≤ Grade.omega := by
          show δret ≤ Grade.omega; cases δret <;> decide
        obtain ⟨φ', hφ', _⟩ := subst_lemma hbody0 hretC' (Nat.zero_le _) hget
        exact ⟨none, φ', hφ', Row.Le.refl _⟩
      · -- σ = 0:  ambient-0 forces δret = 0, and v : A at 0.
        have hz := ambient_zero_usage hretC0 rfl
        simp only [List.length_cons, Usage.zero] at hz
        injection hz with hδret _
        have hget : Usage.get (δret :: φretC) 0 ≤ Grade.zero := by
          show δret ≤ Grade.zero; rw [hδret]; exact Grade.le_refl _
        obtain ⟨φ', hφ', _⟩ := subst_lemma hbody0 hretC' (Nat.zero_le _) hget
        exact ⟨none, φ', hφ', Row.Le.refl _⟩

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Effect-continuation retyping (RB1): typing the CAPTURED CONTINUATION, and preservation for
-- `handle_perform` under the retyped `handle` rule (op-clause binder 0 at `.arr ω opCod B`).
-- ══════════════════════════════════════════════════════════════════════════════════════════════

/-- A well-typed term's free variables are all `< Γ.length`, so shifting above `Γ.length` (or any
    larger cut `c`) is the identity — in particular a *closed* term (`Γ = []`) is fixed by every
    `shiftAbove c`.  This lets the captured continuation `k = lam (handle E[var 0] retC opC)` be
    typed in the extended context `opCod :: []` without disturbing `E`'s (closed) sub-terms. -/
theorem shiftAbove_closed {Γ : List Ty} {e : Tm} {A : Ty} {σ : Grade} {E : Row} {φ : Usage}
    (h : HasType opDom opCod opGrade Γ e A σ E φ) :
    ∀ {c : Nat}, Γ.length ≤ c → Tm.shiftAbove c e = e := by
  induction h with
  | @var Γ i A σ hlk =>
    intro c hc
    have hlt : i < Γ.length := lookup_lt hlk
    simp only [Tm.shiftAbove, if_pos (by omega : i < c)]
  | @lam Γ body ρ σ δ A B rest _ _ ih =>
    intro c hc
    simp only [Tm.shiftAbove]
    rw [ih (by simp only [List.length_cons]; omega)]
  | @app Γ f a ρ σ A B φf φa Ef Ea _ _ ihf iha =>
    intro c hc
    simp only [Tm.shiftAbove]
    rw [ihf hc, iha hc]
  | tt => intro c _; rfl
  | ff => intro c _; rfl
  | @ite Γ cnd t e σ A φc φt φe Ec Et Ee _ _ _ ihc iht ihe =>
    intro c hc
    simp only [Tm.shiftAbove]
    rw [ihc hc, iht hc, ihe hc]
  | @perform Γ a σ φ _ iha =>
    intro c hc
    simp only [Tm.shiftAbove]
    rw [iha hc]
  | @handle Γ body retC opC σ A B φbody φretC φopC δret δk δarg Ebody _ _ _ _ ihbody ihretC ihopC =>
    intro c hc
    simp only [Tm.shiftAbove]
    rw [ihbody hc, ihretC (by simp only [List.length_cons]; omega),
      ihopC (by simp only [List.length_cons]; omega)]

/-- **The operation argument is well-typed at `opDom`.**  Descending through `E` to the hole
    `perform v`, `perform`-inversion exposes `v : opDom` (at the ambient the hole sits at).  Used to
    obtain a typing of the operation argument `v` that `handle_perform`'s reduct substitutes into the
    op-clause's argument slot. -/
theorem plug_perform_arg_typing (E : ECtx) {v : Tm} {Γ A σ Erow φ}
    (h : HasType opDom opCod opGrade Γ (E.plug (.perform v)) A σ Erow φ) :
    ∃ σv φv0, HasType opDom opCod opGrade Γ v opDom σv none φv0 := by
  induction E generalizing Γ A σ Erow φ with
  | hole =>
    cases h with
    | perform ha => exact ⟨_, _, ha⟩
  | appL E' a ih =>
    cases h with
    | app hf _ => exact ih hf
  | appR f hf E' ih =>
    cases h with
    | app _ ha => exact ih ha
  | iteC E' t e ih =>
    cases h with
    | ite hc _ _ => exact ih hc
  | perf E' ih =>
    cases h with
    | perform ha => exact ih ha

/-- **Plug-typing decomposition / continuation-body reconstruction (the crux of RB1).**  From a
    closed derivation of `E[perform v] : A`, the hole sits at the operation's codomain `opCod` (that
    is what `perform` produces), and re-plugging `var 0 : opCod` — the resume value the captured
    continuation binds — re-types the whole plugged term `E[var 0] : A` in the extended context
    `[opCod]`.  Because `E` never binds (its formers are `appL`/`appR`/`iteC`/`perf`) and `E`'s
    non-hole sub-terms are closed, they lift to `[opCod]` unchanged (`shiftAbove_closed`).  This is
    exactly what is needed to give the captured continuation `k = lam (handle E[var 0] retC opC)`
    its first-class function type `.arr ω opCod B`. -/
theorem plug_reconstruct_var0 (E : ECtx) {v : Tm} {A σ Erow φ}
    (h : HasType opDom opCod opGrade [] (E.plug (.perform v)) A σ Erow φ) :
    ∃ Erow' φ', HasType opDom opCod opGrade [opCod] (E.plug (.var 0)) A σ Erow' φ' := by
  induction E generalizing A σ Erow φ with
  | hole =>
    -- E.plug (perform v) = perform v : opCod  ⟹  A = opCod; plug var0 : opCod in [opCod].
    cases h with
    | @perform _ _ _ _ ha =>
      exact ⟨none, _, HasType.var (by rfl : ([opCod] : List Ty)[0]? = some opCod)⟩
  | appL E' a ih =>
    cases h with
    | @app _ _ _ ρ _ A' _ φf φa Ef Ea hf ha =>
      obtain ⟨Ef', φf', hf'⟩ := ih hf
      -- a is closed; lift it to [opCod] unchanged.
      have haw := weaken ha 0 opCod
      rw [insertTy_zero, shiftAbove_closed ha (by simp)] at haw
      exact ⟨_, _, HasType.app hf' haw⟩
  | appR f hf E' ih =>
    cases h with
    | @app _ _ _ ρ _ A' _ φf φa Ef Ea hf0 ha =>
      obtain ⟨Ea', φa', ha'⟩ := ih ha
      have hfw := weaken hf0 0 opCod
      rw [insertTy_zero, shiftAbove_closed hf0 (by simp)] at hfw
      exact ⟨_, _, HasType.app hfw ha'⟩
  | iteC E' t e ih =>
    cases h with
    | @ite _ _ _ _ _ _ φc φt φe Ec Et Ee hc ht he =>
      obtain ⟨Ec', φc', hc'⟩ := ih hc
      have htw := weaken ht 0 opCod
      rw [insertTy_zero, shiftAbove_closed ht (by simp)] at htw
      have hew := weaken he 0 opCod
      rw [insertTy_zero, shiftAbove_closed he (by simp)] at hew
      exact ⟨_, _, HasType.ite hc' htw hew⟩
  | perf E' ih =>
    cases h with
    | @perform _ _ _ _ ha =>
      obtain ⟨Ea', φa', ha'⟩ := ih ha
      -- ha' : HasType [opCod] (E'.plug (var 0)) opDom σ Ea' φa'.  But `perform` needs its argument
      -- pure-rowed.  ha' may carry a `some` row; demote its ambient is unnecessary — we need the
      -- ROW to be none.  In fact the argument E'[var 0] can be non-pure only if E' contained a
      -- perform, but perform's argument was required pure in the original derivation `ha`.  We
      -- reconstruct with the row we get: perform only accepts a none row, so we must show Ea' = none.
      -- The original `ha : HasType [] (E'.plug (perform v)) opDom σ none φa` has row `none`; the
      -- reconstruction preserves the "row is none" obligation because plug_row is determined by the
      -- non-hole structure of E' plus the hole — but the hole changed from `some opGrade` to `none`.
      -- Since the outer perform demanded `none`, E'[perform v] had row none, which (by
      -- plug_perform_row_some, contrapositive) is impossible unless E' = hole is excluded... Actually
      -- E'[perform v] with row none contradicts plug_perform_row_some.  So this branch is vacuous.
      exact absurd ha (by
        intro hcontra
        obtain ⟨g, hg⟩ := plug_perform_row_some E' hcontra
        exact absurd hg (by simp))

/-- **Closed booleans are typeable at every ambient (in particular `ω`).**  A closed value at `bool`
    is `tt`/`ff` (canonical forms), each of which types at any ambient grade with the zero usage.
    This makes a boolean operation argument `v : bool` available at grade `ω`, discharging the
    op-clause's argument demand `δarg ≤ ω` in the `handle_perform` reduct WITHOUT any (false)
    ambient-raising on general values — see the obstruction note before `handle_perform_preserving`. -/
theorem bool_value_any_ambient {v : Tm} {σ E φ} (hv : Value v)
    (h : HasType opDom opCod opGrade [] v .bool σ E φ) :
    ∀ σ', ∃ φ', HasType opDom opCod opGrade [] v .bool σ' none φ' := by
  intro σ'
  rcases canonical_bool hv h with rfl | rfl
  · exact ⟨_, HasType.tt⟩
  · exact ⟨_, HasType.ff⟩

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Preservation for the deep-handler `handle_perform` rule under the RETYPED handle rule
-- (op-clause binder 0 typed at the continuation's function type `.arr ω opCod B`).
--
-- OBSTRUCTION / SCOPE (a sharper negative-result residue).  Full preservation over an ARBITRARY
-- operation-domain `opDom` is *not* provable in this fragment: the reduct substitutes the operation
-- argument `v` into the op-clause's argument slot, which the clause may use `δarg` times (up to the
-- ambient `σ`); so `v` must be available at grade `δarg`.  When `opDom` is a *function* type and
-- `v` is a `lam`, `v` cannot in general be re-typed at a higher ambient (raising ambient inflates a
-- lambda's or handler's measured demands past its domain-grade / `opGrade` bound — "ambient raise to
-- ω" is genuinely FALSE for sub-`ω` grades).  This is a SEPARATE defect from the (now-fixed)
-- continuation-typing one, in the argument-grade accounting of `HasType.perform`.  It vanishes when
-- `opDom` is a base type: a `bool` argument is `tt`/`ff` (`bool_value_any_ambient`), typeable at
-- every ambient.  Preservation is therefore proved for `opDom = .bool`, fully general in the
-- continuation grade `opGrade` (the retyped continuation binder is what makes it go through).
--
-- The retyping fixes the exact defect the frozen `HasTypeVC` presentation exhibits
-- (`handle_perform_not_preserving`): the captured continuation `k = lam (handle E[var 0] retC opC)`
-- is an ARROW, and now lands in an arrow-typed binder.  Preservation is proved at `opGrade = ω`,
-- the multiplicity at which a handler may resume its continuation without bound — matching the
-- kernel's `Π^ω` continuation domain.  For sub-`ω` opGrade the operation argument (when it is a
-- function value) may fail to be available at the op-clause's argument demand; that obstruction is
-- exactly `raise_omega`'s failure and is documented there.
-- ══════════════════════════════════════════════════════════════════════════════════════════════

/-- **Preservation for `handle_perform`** (the positive result RB1 targets), for a boolean operation
    argument (`opDom = .bool`) and FULLY GENERAL continuation grade `opGrade`.  A closed, well-typed
    handler catching an operation — the exact `handle_perform` redex — steps to a term still
    well-typed at the same result type `B` and ambient `ω`.  The captured continuation
    `k = lam (handle E[var 0] retC opC)` types at its first-class function type `.arr ω opCod B`
    (via `plug_reconstruct_var0` + `shiftAbove_closed`), and the two substitutions (argument
    `v : bool`, continuation `k`) are discharged by `subst_lemma`, the boolean argument being
    available at `ω` by `bool_value_any_ambient` (canonical forms).  See the obstruction note above
    for why a general `opDom` is not provable in this fragment. -/
theorem handle_perform_preserving {opCod : Ty} {opGrade : Grade} {σ : Grade}
    (hσ : σ = Grade.omega ∨ σ = Grade.zero)
    {E : ECtx} {v retC opC : Tm} {B φ} (hv : Value v)
    (h : HasType .bool opCod opGrade [] (.handle (E.plug (.perform v)) retC opC) B σ
          none φ) :
    ∃ φ', HasType .bool opCod opGrade []
      (Tm.subst0 (Tm.lam (.handle (E.plug (.var 0)) retC opC)) (Tm.subst 1 v opC)) B σ
      none φ' := by
  -- Invert the handle.
  cases h with
  | @handle _ _ _ _ _ A _ φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade =>
    -- 1. The captured continuation body `E[var 0] : A` in `[opCod]`.
    obtain ⟨ErowK, φK, hEbodyK⟩ := plug_reconstruct_var0 (opDom := .bool) (opCod := opCod)
      (opGrade := opGrade) E hbody
    -- 2. Weaken retC/opC into the continuation's extended context (they are closed, so unshifted).
    --    retC : [A] ⟶ [A, opCod]  (insert opCod at index 1).
    have hretCw := weaken hretC 1 opCod
    rw [shiftAbove_closed hretC (by simp)] at hretCw
    have hretC_ins : insertTy (A :: ([] : List Ty)) 1 opCod = A :: opCod :: [] := by
      show A :: insertTy ([] : List Ty) 0 opCod = A :: opCod :: []
      rw [insertTy_zero]
    rw [hretC_ins] at hretCw
    have hins_retU : insertUsage (δret :: φretC) 1 = δret :: insertUsage φretC 0 := rfl
    rw [hins_retU] at hretCw
    --    opC : [arr ω opCod B, bool] ⟶ [arr ω opCod B, bool, opCod]  (insert opCod at index 2).
    have hopCw := weaken hopC 2 opCod
    rw [shiftAbove_closed hopC (by simp)] at hopCw
    have hopC_ins : insertTy ((.arr Grade.omega opCod B) :: Ty.bool :: ([] : List Ty)) 2 opCod
        = (.arr Grade.omega opCod B) :: Ty.bool :: opCod :: [] := by
      show (.arr Grade.omega opCod B) :: Ty.bool :: insertTy ([] : List Ty) 0 opCod
        = (.arr Grade.omega opCod B) :: Ty.bool :: opCod :: []
      rw [insertTy_zero]
    rw [hopC_ins] at hopCw
    have hins_opU : insertUsage (δk :: δarg :: φopC) 2 = δk :: δarg :: insertUsage φopC 0 := rfl
    rw [hins_opU] at hopCw
    -- 3. Build the inner handle `handle (E[var 0]) retC opC : B` in `[opCod]`, at ambient σ.
    have hinnerHandle : HasType .bool opCod opGrade [opCod]
        (.handle (E.plug (.var 0)) retC opC) B σ none
        (Usage.add φK (Usage.add (insertUsage φretC 0) (insertUsage φopC 0))) :=
      HasType.handle hEbodyK hretCw hopCw hgrade
    -- 4. The inner-handle usage lives in `[opCod]` (length 1); split it as `δinner :: restK`.
    have hleninner : (Usage.add φK (Usage.add (insertUsage φretC 0) (insertUsage φopC 0))).length
        = ([opCod] : List Ty).length := usage_length hinnerHandle
    obtain ⟨δinner, restK, hφinnereq⟩ :
        ∃ δinner restK,
          Usage.add φK (Usage.add (insertUsage φretC 0) (insertUsage φopC 0)) = δinner :: restK := by
      cases hcase : Usage.add φK (Usage.add (insertUsage φretC 0) (insertUsage φopC 0)) with
      | nil => rw [hcase] at hleninner; simp at hleninner
      | cons x xs => exact ⟨x, xs, rfl⟩
    rw [hφinnereq] at hinnerHandle
    -- 5. Build the captured continuation `k = lam (...) : arr ω opCod B` in `[]`, usage `restK`,
    --    at ambient σ.
    have hK : HasType .bool opCod opGrade []
        (Tm.lam (.handle (E.plug (.var 0)) retC opC)) (.arr Grade.omega opCod B) σ none
        restK :=
      HasType.lam hinnerHandle (by cases δinner <;> decide)
    -- 6. The operation argument is a BOOLEAN value, hence typeable at ambient ω (canonical forms).
    obtain ⟨σv, φv0, hvty0⟩ : ∃ σv φv0, HasType .bool opCod opGrade [] v .bool σv none φv0 :=
      plug_perform_arg_typing E hbody
    obtain ⟨φvω, hvω⟩ := bool_value_any_ambient (opCod := opCod) (opGrade := opGrade) hv hvty0
      Grade.omega
    -- lift v into `[arr ω opCod B]` (closed, so unshifted).
    have hvw := weaken hvω 0 (.arr Grade.omega opCod B)
    rw [insertTy_zero, shiftAbove_closed hvω (by simp)] at hvw
    -- 7. First substitution: `subst 1 v opC : B` in `[arr ω opCod B]`.
    --    opC : [arr ω opCod B, bool] = insertTy [arr ω opCod B] 1 bool.
    have hopC_asins : ((.arr Grade.omega opCod B) :: Ty.bool :: ([] : List Ty))
        = insertTy ((.arr Grade.omega opCod B) :: ([] : List Ty)) 1 Ty.bool := by
      show (.arr Grade.omega opCod B) :: Ty.bool :: [] = (.arr Grade.omega opCod B) :: insertTy [] 0 Ty.bool
      rw [insertTy_zero]
    have hopC' : HasType .bool opCod opGrade
        (insertTy ((.arr Grade.omega opCod B) :: ([] : List Ty)) 1 Ty.bool) opC B σ none
        (δk :: δarg :: φopC) := by rw [← hopC_asins]; exact hopC
    -- demand at slot 1 is δarg ≤ ω (v is available at ω).
    have hget1 : Usage.get (δk :: δarg :: φopC) 1 ≤ Grade.omega := by
      show δarg ≤ Grade.omega; cases δarg <;> decide
    obtain ⟨φ1, hφ1, _⟩ := subst_lemma hvw hopC' (by simp) hget1
    -- 8. Second substitution: `subst 0 k (subst 1 v opC) : B` in `[]`, k available at ambient σ.
    --    (subst 1 v opC) : [arr ω opCod B] = insertTy [] 0 (arr ω opCod B).
    have hφ1' : HasType .bool opCod opGrade
        (insertTy ([] : List Ty) 0 (.arr Grade.omega opCod B))
        (Tm.subst 1 v opC) B σ none φ1 := by
      rw [insertTy_zero]; exact hφ1
    -- demand at slot 0 (the continuation slot) is ≤ σ: at σ = ω trivial; at σ = 0 forced 0.
    have hget0 : Usage.get φ1 0 ≤ σ := by
      rcases hσ with rfl | rfl
      · cases (Usage.get φ1 0) <;> decide
      · have hz := ambient_zero_usage hφ1 rfl
        rw [hz, Usage.get_zero]; exact Grade.le_refl _
    obtain ⟨φ2, hφ2, _⟩ := subst_lemma hK hφ1' (by simp) hget0
    -- 9. Assemble the reduct.  `Tm.subst0 k (Tm.subst 1 v opC) = Tm.subst 0 k (Tm.subst 1 v opC)`.
    refine ⟨φ2, ?_⟩
    show HasType .bool opCod opGrade []
      (Tm.subst0 (Tm.lam (.handle (E.plug (.var 0)) retC opC)) (Tm.subst 1 v opC)) B σ
      none φ2
    unfold Tm.subst0
    exact hφ2

/-- **Full preservation over `Step`** (all rules, INCLUDING the deep-handler `handle_perform`) for a
    boolean operation argument at the runtime ambient `σ = ω`.  Combines `preservation_core` (the
    type-preserving fragment `StepC`) with `handle_perform_preserving` (the retyped deep-handler
    rule).  The reduct keeps type `A` and ambient `ω`; only the usage/row are left existential.  This
    is the positive counterpart of the (frozen) `handle_perform_not_preserving`: under the retyped
    `handle` rule, the SAME small-step semantics IS type-preserving. -/
theorem preservation {opCod : Ty} {opGrade : Grade} {e e' : Tm} {A : Ty} {σ : Grade} {E : Row} {φ}
    (hσ : σ = Grade.omega ∨ σ = Grade.zero)
    (h : HasType .bool opCod opGrade [] e A σ E φ) (hstep : Step e e') :
    ∃ E' φ', HasType .bool opCod opGrade [] e' A σ E' φ' ∧ Row.Le E' E := by
  induction hstep generalizing A σ E φ with
  | app1 _ ih =>
    cases h with
    | app hf0 ha0 =>
      obtain ⟨Ef', φf', hφf', hle⟩ := ih hσ hf0
      exact ⟨_, _, HasType.app hφf' ha0, Row.union_mono hle (Row.Le.refl _)⟩
  | @app2 f a a' hf _ ih =>
    cases h with
    | @app _ _ _ ρ _ _ _ _ _ _ _ hf0 ha0 =>
      have hσ' : σ.mul ρ = Grade.omega ∨ σ.mul ρ = Grade.zero := by
        rcases hσ with rfl | rfl
        · cases ρ <;> simp [Grade.mul]
        · right; rfl
      obtain ⟨Ea', φa', hφa', hle⟩ := ih hσ' ha0
      exact ⟨_, _, HasType.app hf0 hφa', Row.union_mono (Row.Le.refl _) hle⟩
  | beta ha =>
    exact preservation_core hσ h (StepC.beta ha)
  | ite_cond _ ih =>
    cases h with
    | ite hc0 ht0 he0 =>
      obtain ⟨Ec', φc', hφc', hle⟩ := ih hσ hc0
      exact ⟨_, _, HasType.ite hφc' ht0 he0, Row.union_mono hle (Row.Le.refl _)⟩
  | ite_tt =>
    exact preservation_core hσ h StepC.ite_tt
  | ite_ff =>
    exact preservation_core hσ h StepC.ite_ff
  | perform_arg _ ih =>
    cases h with
    | perform ha0 =>
      obtain ⟨Ea', φ', hφ', hle⟩ := ih hσ ha0
      -- `HasType.perform` requires the argument pure-rowed (`none`); the argument started at row
      -- `none`, so its reduct's row `Ea' ≤ none` forces `Ea' = none`.
      have hEa' : Ea' = none := by cases Ea' with
        | none => rfl
        | some g => exact absurd hle (by simp [Row.Le])
      subst hEa'
      exact ⟨some opGrade, φ', HasType.perform hφ', Row.Le.refl _⟩
  | handle_body _ ih =>
    cases h with
    | handle hbody0 hretC0 hopC0 hgrade0 =>
      obtain ⟨Eb', φ', hφ', _⟩ := ih hσ hbody0
      exact ⟨_, _, HasType.handle hφ' hretC0 hopC0 hgrade0, Row.Le.refl _⟩
  | handle_ret hvret =>
    exact preservation_core hσ h (StepC.handle_ret hvret)
  | handle_perform hv =>
    -- the handle redex carries row `none` (handle rule); force `E = none` by inverting, then apply
    -- `handle_perform_preserving` (which covers both runtime ambients σ ∈ {ω, 0}).
    cases h with
    | @handle _ _ _ _ _ A2 _ φbody φretC φopC δret δk δarg Ebody hbody hretC hopC hgrade =>
      obtain ⟨φ', hty⟩ := handle_perform_preserving hσ hv
        (HasType.handle hbody hretC hopC hgrade)
      exact ⟨none, φ', hty, trivial⟩

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- NON-VACUITY: a concrete `handle_perform` redex whose op-clause GENUINELY RESUMES its continuation
-- ══════════════════════════════════════════════════════════════════════════════════════════════

/-- **Non-vacuity witness for `handle_perform_preserving`.**  Take `op : bool → bool` at grade `ω`,
    `E = hole`, `v = tt`, and the op-clause `opC = app (var 0) (var 1)` which APPLIES the captured
    continuation (`var 0 = k`) to the operation argument (`var 1 = x`) — a genuine resume, not a
    discard.  The redex `handle (perform tt) (var 0) (app (var 0) (var 1))` type-checks at `bool`;
    it steps (`Step.handle_perform`); and its reduct
    `app (lam (handle (var 0) (var 0) (app (var 0) (var 1)))) tt`
    is again well-typed at `bool` — so preservation here is about a real reduction that resumes a
    real continuation, not a vacuous one.  (Contrast `handle_perform_not_preserving`, the same
    *shape* of redex against the frozen value-typed rule, whose reduct is ill-typed.) -/
theorem handle_perform_preserving_nonvacuous :
    -- (1) the redex is well-typed at `bool`:
    (∃ φ, HasType .bool .bool Grade.omega []
        (.handle (ECtx.hole.plug (.perform .tt)) (.var 0) (.app (.var 0) (.var 1)))
        .bool Grade.omega none φ)
    ∧
    -- (2) it steps via `handle_perform` to the continuation-applying reduct:
    (Step (.handle (ECtx.hole.plug (.perform .tt)) (.var 0) (.app (.var 0) (.var 1)))
      (.app (.lam (.handle (.var 0) (.var 0) (.app (.var 0) (.var 1)))) .tt))
    ∧
    -- (3) the reduct is STILL well-typed at `bool` (preservation holds, non-vacuously):
    (∃ φ', HasType .bool .bool Grade.omega []
        (.app (.lam (.handle (.var 0) (.var 0) (.app (.var 0) (.var 1)))) .tt)
        .bool Grade.omega none φ') := by
  -- The redex typing, proved once (op-clause usage inferred from the `app` sub-derivation).
  -- op-clause typing, built first so the handle rule reads its usage vector off this hypothesis.
  have hopc : HasType .bool .bool Grade.omega
      ((.arr Grade.omega .bool .bool) :: .bool :: []) (.app (.var 0) (.var 1)) .bool Grade.omega none
      (Usage.add (Usage.unit 0 2 Grade.omega) (Usage.unit 1 2 (Grade.omega.mul Grade.omega))) :=
    HasType.app
      (HasType.var (by rfl : ((.arr Grade.omega .bool .bool :: .bool :: []) : List Ty)[0]?
        = some (.arr Grade.omega .bool .bool)))
      (HasType.var (by rfl : ((.arr Grade.omega .bool .bool :: .bool :: []) : List Ty)[1]?
        = some .bool))
  have hredex : ∃ φ, HasType .bool .bool Grade.omega []
      (.handle (ECtx.hole.plug (.perform .tt)) (.var 0) (.app (.var 0) (.var 1)))
      .bool Grade.omega none φ :=
    ⟨_, HasType.handle (HasType.perform HasType.tt) (HasType.var rfl) hopc
      (by decide : Grade.omega ≤ Grade.omega)⟩
  refine ⟨hredex, ?_, ?_⟩
  · -- (2) the step.  Its literal reduct simplifies to the continuation-applying app.
    have hstep := Step.handle_perform (E := ECtx.hole) (v := .tt) (retC := .var 0)
      (opC := .app (.var 0) (.var 1)) Value.tt
    simpa [ECtx.plug, Tm.subst0, Tm.subst, Tm.shiftAbove] using hstep
  · -- (3) reduct typing, obtained from the redex typing via `handle_perform_preserving`.
    obtain ⟨φ, hφ⟩ := hredex
    obtain ⟨φ', hφ'⟩ := handle_perform_preserving (E := ECtx.hole) (Or.inl rfl) Value.tt hφ
    refine ⟨φ', ?_⟩
    simpa [ECtx.plug, Tm.subst0, Tm.subst, Tm.shiftAbove] using hφ'

/-- A `lam` never inhabits `Ty.bool` (canonical forms, contrapositive). -/
theorem lam_not_bool {Γ body σ E φ} :
    ¬ HasType opDom opCod opGrade Γ (.lam body) .bool σ E φ := by
  intro h; cases h

/-- The `HasTypeVC` (frozen value-continuation judgement) analogue of `lam_not_bool`. -/
theorem lam_not_bool_VC {Γ body σ E φ} :
    ¬ HasTypeVC opDom opCod opGrade Γ (.lam body) .bool σ E φ := by
  intro h; cases h

/-- **Refutation of operational preservation for the deep-handler `handle_perform` rule.**

    Take the operation `op : bool → bool` at grade `ω`, the handler `handle (perform tt) (var 0)
    (var 0)` (return clause returns the body's value; op-clause returns the continuation slot),
    with `E = hole`, `v = tt`.  This term type-checks at `bool` in the empty context.  But its
    `handle_perform` reduct is `lam (handle (var 0) (var 0) (var 0))` — a `lam`, hence of *arrow*
    type, provably NOT of type `bool`.  So no `φ'` gives the reduct type `bool`: type preservation
    fails for `handle_perform`.

    Root cause: the static `handle` rule types the op-clause's continuation binder (index `0`) at
    `opCod` (the value fed to a resume), *not* at the continuation's function type `opCod → B`.  A
    faithful deep handler must substitute a captured continuation `λx. handle E[x] …` — an
    *arrow*-typed term — into that slot, which the `opCod`-typed binder cannot accept.  The grade
    discipline (`handle_grade_safe`, `handle_linear_at_most_once`) is sound, but the naive
    delimited-continuation reduction is not type-preserving against this presentation. -/
theorem handle_perform_not_preserving :
    -- (1) the LHS is well-typed at `bool` (against the frozen value-continuation judgement):
    (∃ φ, HasTypeVC .bool .bool Grade.omega []
        (.handle (ECtx.hole.plug (.perform .tt)) (.var 0) (.var 0)) .bool Grade.one none φ)
    ∧
    -- (2) but there is a step whose target is NOT well-typed at `bool` (at any usage):
    (∃ e', Step (.handle (ECtx.hole.plug (.perform .tt)) (.var 0) (.var 0)) e' ∧
      ¬ ∃ φ', HasTypeVC .bool .bool Grade.omega [] e' .bool Grade.one none φ') := by
  refine ⟨?_, ?_⟩
  · -- LHS typing.  φ is determined by the derivation.
    exact ⟨_, HasTypeVC.handle (HasTypeVC.perform HasTypeVC.tt) (HasTypeVC.var rfl)
      (HasTypeVC.var rfl) (by decide : Grade.one ≤ Grade.omega)⟩
  · -- the reduct is a lam, not of type bool.
    refine ⟨_, Step.handle_perform (E := ECtx.hole) (v := .tt) Value.tt, ?_⟩
    rintro ⟨φ', hφ'⟩
    -- reduct = subst0 (lam (handle (var 0) (var 0) (var 0))) (subst 1 tt (var 0))
    --        = lam (handle (var 0) (var 0) (var 0))
    exact lam_not_bool_VC hφ'

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Operational resume-once: upgrading handle_linear_at_most_once from static to operational
-- ══════════════════════════════════════════════════════════════════════════════════════════════

/-- The `handle_perform` reduct exposed structurally: firing the op-clause substitutes the argument
    `v` (at binder `1`) and the captured, handler-re-installing continuation
    `k = lam (handle E[var 0] retC opC)` (at binder `0`).  The continuation `k` therefore lands in
    exactly the slot the static rule charges at grade `δk ≤ opGrade` — so `δk` *is* the operational
    count of how many times the captured continuation is resumed. -/
theorem handle_perform_reduct {E : ECtx} {v retC opC : Tm} (hv : Value v) :
    Step (.handle (E.plug (.perform v)) retC opC)
      (Tm.subst0 (Tm.lam (.handle (E.plug (.var 0)) retC opC)) (Tm.subst 1 v opC)) :=
  Step.handle_perform hv

/-- **Operational resume-once (linear handlers).** When a well-typed `1`-graded handler catches an
    operation — i.e. its body is `E[perform v]`, the exact configuration in which `handle_perform`
    fires — the captured continuation is resumed *at most once*: the op-clause's continuation-slot
    demand `δk` is `0` (aborts, discarding the continuation) or `1` (resumes exactly once), never
    `ω`.  This upgrades the *static* `handle_linear_at_most_once` to the operational setting: it
    holds precisely at the redex that `Step.handle_perform` consumes, so it constrains the actual
    reduction, not merely the typing derivation.  (`Ec`, `v`, `hv` witness that the handler is in a
    perform-catching configuration; `hstep` exhibits the very reduction being bounded.) -/
theorem resume_once_operational {Γ v retC opC B σ φ} {Ec : ECtx} (_hv : Value v)
    (h : HasType opDom opCod Grade.one Γ
          (.handle (Ec.plug (.perform v)) retC opC) B σ none φ)
    (_hstep : Step (.handle (Ec.plug (.perform v)) retC opC)
          (Tm.subst0 (Tm.lam (.handle (Ec.plug (.var 0)) retC opC)) (Tm.subst 1 v opC))) :
    ∃ A φbody φretC φopC δret δk δarg Ebody,
      HasType opDom opCod Grade.one Γ (Ec.plug (.perform v)) A σ Ebody φbody ∧
      HasType opDom opCod Grade.one (A :: Γ) retC B σ none (δret :: φretC) ∧
      HasType opDom opCod Grade.one ((.arr Grade.omega opCod B) :: opDom :: Γ) opC B σ none
        (δk :: δarg :: φopC) ∧
      -- the continuation slot is resumed 0 or 1 times, never unboundedly:
      (δk = Grade.zero ∨ δk = Grade.one) := by
  obtain ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, hgrade⟩ :=
    handle_grade_safe h
  exact ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, le_one_cases hgrade⟩

/-- **Operational never-resumes (abort handlers).** When a well-typed `0`-graded (exception/abort)
    handler catches an operation, the captured continuation is discarded outright: the op-clause's
    continuation-slot demand is forced to `0`, so `handle_perform`'s reduct uses the continuation
    `k = lam (handle Ec[var 0] retC opC)` zero times.  This is the operational reading of
    `handle_abort_never_resumes`. -/
theorem never_resumes_operational {Γ v retC opC B σ φ} {Ec : ECtx} (_hv : Value v)
    (h : HasType opDom opCod Grade.zero Γ
          (.handle (Ec.plug (.perform v)) retC opC) B σ none φ)
    (_hstep : Step (.handle (Ec.plug (.perform v)) retC opC)
          (Tm.subst0 (Tm.lam (.handle (Ec.plug (.var 0)) retC opC)) (Tm.subst 1 v opC))) :
    ∃ A φbody φretC φopC δret δarg Ebody,
      HasType opDom opCod Grade.zero Γ (Ec.plug (.perform v)) A σ Ebody φbody ∧
      HasType opDom opCod Grade.zero (A :: Γ) retC B σ none (δret :: φretC) ∧
      HasType opDom opCod Grade.zero ((.arr Grade.omega opCod B) :: opDom :: Γ) opC B σ none
        (Grade.zero :: δarg :: φopC) := by
  obtain ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, hgrade⟩ :=
    handle_grade_safe h
  have hδk : δk = Grade.zero := le_zero_eq hgrade
  subst hδk
  exact ⟨A, φbody, φretC, φopC, δret, δarg, Ebody, hbody, hretC, hopC⟩

/-- **The continuation-slot demand survives the argument substitution.**  `handle_perform` first
    plugs the argument `v` (a value, so pure-rowed) into binder `1` of `opC`, leaving the
    continuation slot at binder `0`.  This lemma shows the continuation slot's demand in the
    argument-substituted clause `subst 1 v opC` is still bounded by `opGrade`: the captured
    continuation `k`, substituted there next, is thus resumed at most `opGrade` times *in the actual
    reduct*, not merely in the pre-reduction op-clause.  (Uses the effect fragment's own
    `subst_lemma`; the argument substitution is well-typed even though the subsequent continuation
    substitution is not — see `handle_perform_not_preserving`.  Stated at the runtime ambient
    `σ ∈ {ω, 0}`, exactly as `preservation_core`.) -/
theorem cont_slot_demand_after_arg_subst {Γ v opC B σ φv φopC δk δarg}
    (hvty : HasType opDom opCod opGrade Γ v opDom σ none φv)
    (hopC : HasType opDom opCod opGrade (opCod :: opDom :: Γ) opC B σ none (δk :: δarg :: φopC))
    (hσ : σ = Grade.omega ∨ σ = Grade.zero) :
    ∃ φ', HasType opDom opCod opGrade (opCod :: Γ) (Tm.subst 1 (Tm.shiftAbove 0 v) opC) B σ none φ'
      ∧ Usage.get φ' 0 ≤ δk := by
  -- weaken v by opCod at position 0 so it lives in `opCod :: Γ`, the post-substitution context.
  have hvw : HasType opDom opCod opGrade (opCod :: Γ) (Tm.shiftAbove 0 v) opDom σ none
      (insertUsage φv 0) := by
    have hw := weaken hvty 0 opCod
    rwa [insertTy_zero] at hw
  -- opC lives in `opCod :: opDom :: Γ = insertTy (opCod :: Γ) 1 opDom`.
  have hins : insertTy (opCod :: Γ) 1 opDom = opCod :: opDom :: Γ := by
    show opCod :: insertTy Γ 0 opDom = opCod :: opDom :: Γ
    rw [insertTy_zero]
  have hopC' : HasType opDom opCod opGrade (insertTy (opCod :: Γ) 1 opDom) opC B σ none
      (δk :: δarg :: φopC) := by
    rw [hins]; exact hopC
  -- discharge subst_lemma's `hget : get (δk :: δarg :: φopC) 1 = δarg ≤ π` at π = σ (∈ {ω,0}).
  have hk1 : (1 : Nat) ≤ (opCod :: Γ).length := by simp only [List.length_cons]; omega
  have hget : Usage.get (δk :: δarg :: φopC) 1 ≤ σ := by
    show δarg ≤ σ
    rcases hσ with rfl | rfl
    · cases δarg <;> decide
    · -- σ = 0: ambient-0 forces δarg = 0.
      have hz := ambient_zero_usage hopC rfl
      simp only [List.length_cons, Usage.zero] at hz
      injection hz with _ hz2
      injection hz2 with hδarg _
      rw [hδarg]; exact Grade.le_refl _
  obtain ⟨φ', hφ', hLe⟩ :=
    @subst_lemma _ _ _ (opCod :: Γ) (Tm.shiftAbove 0 v) opDom σ (insertUsage φv 0) hvw 1 opC B σ
      none (δk :: δarg :: φopC) hopC' hk1 hget
  -- `subst 1 v opC` uses the *shifted* v; `Tm.subst 1 (shiftAbove 0 v) opC` is what fires.  The
  -- continuation slot (index 0) demand: use the subst_lemma bound at slot 0.
  refine ⟨φ', ?_, ?_⟩
  · exact hφ'
  · -- from hLe: insertUsage φ' 1 ≤ (δk::δarg::φopC) + scale δarg (insertUsage (insertUsage φv 0) 1).
    -- at index 0 (< 1): φ'.get 0 = (insertUsage φ' 1).get 0 ≤ δk + δarg·(...).get 0.
    have h0 := Usage.le_get hLe 0
    rw [insertUsage_get_lt (by omega : (0:Nat) < 1)] at h0
    -- RHS.get 0
    have hlen_lhs : (δk :: δarg :: φopC).length =
        (Usage.scale (Usage.get (δk :: δarg :: φopC) 1)
          (insertUsage (insertUsage φv 0) 1)).length := by
      rw [Usage.length_scale, insertUsage_length, insertUsage_length, usage_length hvty,
        usage_length hopC]
      simp only [List.length_cons]
    rw [Usage.get_add hlen_lhs] at h0
    -- (δk::δarg::φopC).get 0 = δk ; scale's get 0 = δarg.mul((insertUsage (insertUsage φv 0) 1).get 0)
    --   and (insertUsage (insertUsage φv 0) 1).get 0 = (insertUsage φv 0).get 0 = 0 (slot 0 fresh).
    have hscale0 : (Usage.scale (Usage.get (δk :: δarg :: φopC) 1)
        (insertUsage (insertUsage φv 0) 1)).get 0 = Grade.zero := by
      rw [Usage.get_scale, insertUsage_get_lt (by omega : (0:Nat) < 1), insertUsage_get_self]
      exact (by cases (Usage.get (δk :: δarg :: φopC) 1) <;> rfl :
        (Usage.get (δk :: δarg :: φopC) 1).mul Grade.zero = Grade.zero)
    rw [hscale0] at h0
    have hgetδk : Usage.get (δk :: δarg :: φopC) 0 = δk := rfl
    rw [hgetδk, Grade.add_zero] at h0
    -- h0 : φ'.get 0 ≤ δk.  (Callers pair this with the handle rule's `δk ≤ opGrade` to conclude the
    -- continuation slot is resumed ≤ opGrade times in the actual reduct.)
    exact h0

/-- **`StepC` is a sub-relation of `Step`.**  Everything the type-preserving fragment does is a
    genuine reduction of the full deep-handler semantics — so `preservation_core` really is a
    theorem about the operational semantics `Step`, restricted to the rules that preserve types
    (all of them except the refuted `handle_perform`). -/
theorem stepC_is_step {e e' : Tm} (hstep : StepC e e') : Step e e' := by
  induction hstep with
  | app1 _ ih => exact .app1 ih
  | app2 hfv _ ih => exact .app2 hfv ih
  | beta ha => exact .beta ha
  | ite_cond _ ih => exact .ite_cond ih
  | ite_tt => exact .ite_tt
  | ite_ff => exact .ite_ff
  | perform_arg _ ih => exact .perform_arg ih
  | handle_body _ ih => exact .handle_body ih
  | handle_ret hv => exact .handle_ret hv

/-- **Machine-checked SHARP OBSTRUCTION — why `preservation` above is proved only for
    `opDom = .bool`, not for an arbitrary operation-argument type.**

    Take `op : (arr 1 bool bool) → bool` at grade ω and the redex
    `handle (app (lam tt) (perform (lam (var 0)))) (var 0) (app (var 1) tt)` — the performed value
    `lam (var 0)` sits in a *grade-0* evaluation position (the `app (lam tt) □` argument slot, whose
    domain grade is 0), so the whole term type-checks at `bool`/ω (part 1).

    Its `handle_perform` reduct `app (lam (var 0)) tt` IS well-typed at `bool`/ω (part 2) — but ONLY
    because the enclosing application **re-grades** the captured value's arrow domain from `1` up to
    `ω`. Preservation therefore still *holds* on this instance; what fails is the *proof route*:
    `subst_lemma` places the performed value `v` at its declared type `opDom = arr 1 bool bool`, and
    `lam (var 0)` provably does NOT inhabit `arr 1 bool bool` at ambient ω (its binder demand ω ⊄ 1,
    part 3). So the reduct's real derivation goes through a non-compositional arrow-regrading that no
    substitution lemma can supply. This is exactly why `handle_perform_preserving`/`preservation`
    are proved for `opDom = .bool` (a base value is `tt`/`ff`, `bool_value_any_ambient`, so no
    regrading is ever needed) and left open for higher operation-argument types — a precise,
    sorry-free characterization of the residual gap, not a refutation. -/
theorem handle_perform_regrade_obstruction :
    -- (1) a `σ = ω` redex with the perform in a grade-0 hole (E = appR (lam tt) _ hole):
    (∃ φ, HasType (.arr Grade.one .bool .bool) .bool Grade.omega []
        (.handle (.app (.lam .tt) (.perform (.lam (.var 0)))) (.var 0) (.app (.var 1) .tt))
        .bool Grade.omega none φ)
    ∧
    -- (2) its reduct `app (lam (var 0)) tt` IS well-typed at bool/ω (via arrow re-grading 1 ⟶ ω):
    (∃ φ, HasType (.arr Grade.one .bool .bool) .bool Grade.omega []
        (.app (.lam (.var 0)) .tt) .bool Grade.omega none φ)
    ∧
    -- (3) but the substituted value `lam (var 0)` is NOT typeable at `opDom = arr 1 bool bool` at
    --     ambient ω — so `subst_lemma` (which fixes that arrow) cannot yield the reduct derivation:
    (¬ ∃ φ, HasType (.arr Grade.one .bool .bool) .bool Grade.omega []
        (.lam (.var 0)) (.arr Grade.one .bool .bool) Grade.omega none φ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- redex typing (hole ambient ω·0 = 0).
    have bodyf : HasType (.arr Grade.one .bool .bool) .bool Grade.omega []
        (.app (.lam .tt) (.perform (.lam (.var 0)))) .bool Grade.omega
        (Row.union none (some Grade.omega)) _ :=
      HasType.app
        (A := .bool) (B := .bool) (ρ := Grade.zero)
        (HasType.lam (A := .bool) (B := .bool) (ρ := Grade.zero) HasType.tt (by decide))
        (HasType.perform (HasType.lam (A := .bool) (B := .bool) (ρ := Grade.one)
          (HasType.var rfl) (by decide)))
    exact ⟨_, HasType.handle (A := .bool) bodyf (HasType.var rfl)
      (HasType.app (A := .bool) (B := .bool) (ρ := Grade.one) (HasType.var rfl) HasType.tt)
      (by decide)⟩
  · -- reduct types via ρ = ω regrading of the lam's domain.
    exact ⟨_, HasType.app (A := .bool) (B := .bool) (ρ := Grade.omega)
      (HasType.lam (HasType.var rfl) (by decide)) HasType.tt⟩
  · -- lam (var 0) : arr 1 bool bool at ω requires binder demand ω ≤ 1, which is false.
    rintro ⟨φ, h⟩
    cases h with
    | @lam _ _ ρ _ δ _ _ _ hbody hle =>
      cases hbody with
      | var hlk => exact absurd hle (by decide)

-- ══════════════════════════════════════════════════════════════════════════════════════════════
-- Axiom audit (RB1): the retyped preservation results and the non-vacuity witness are sorry-free.
-- ══════════════════════════════════════════════════════════════════════════════════════════════

#print axioms handle_perform_preserving
#print axioms preservation
#print axioms handle_perform_preserving_nonvacuous
-- The machine-checked residual obstruction (why the positive is `opDom = .bool`) is sorry-free too:
#print axioms handle_perform_regrade_obstruction
-- The frozen NEGATIVE result (documented "before") also remains proved sorry-free:
#print axioms handle_perform_not_preserving

end Effects

end BlightMeta
