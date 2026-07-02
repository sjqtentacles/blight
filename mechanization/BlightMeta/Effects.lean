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
  * **No operational semantics / preservation for this fragment.** Unlike `Calculus.lean`
    (`Progress.lean`'s full `progress`/`preservation`/`type_safety`), this file proves only the
    *static* discipline and its grade-safety corollaries. Modeling `Handle`'s actual reduction
    rule faithfully needs genuine delimited-continuation semantics (the handler body's evaluation
    context up to the innermost enclosing `handle`, not just a single `perform` in tail position);
    building that out is future work, tracked here rather than silently skipped — see "What's not
    covered" in `docs/metatheory-mechanized.md`.
-/

import BlightMeta.Calculus

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
      (hopC : HasType opDom opCod opGrade (opCod :: opDom :: Γ) opC B σ none
        (δk :: δarg :: φopC))
      (hgrade : δk ≤ opGrade) :
      HasType opDom opCod opGrade Γ (.handle body retC opC) B σ none
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
      HasType opDom opCod opGrade (opCod :: opDom :: Γ) opC B σ none (δk :: δarg :: φopC) ∧
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
      HasType opDom opCod Grade.zero (opCod :: opDom :: Γ) opC B σ none
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
      HasType opDom opCod Grade.one (opCod :: opDom :: Γ) opC B σ none (δk :: δarg :: φopC) ∧
      (δk = Grade.zero ∨ δk = Grade.one) := by
  obtain ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, hgrade⟩ :=
    handle_grade_safe h
  exact ⟨A, φbody, φretC, φopC, δret, δk, δarg, Ebody, hbody, hretC, hopC, le_one_cases hgrade⟩

end Effects

end BlightMeta
