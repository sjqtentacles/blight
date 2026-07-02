/-
  A scoped fragment of Blight's fused theory (docs/metatheory.md §1.3 obligation 1): a graded
  (QTT) simply-typed calculus with `Bool` and `Π`-types, de Bruijn-indexed, whose typing rules are
  a direct transcription of `crates/blight-kernel/src/check.rs`'s `Var`/`Pi-Intro`/`Pi-Elim`
  graded rules (the non-cubical core of `infer_g`/`check_g`) — see the doc comment on `HasType`
  for the exact correspondence.

  Departure from the kernel worth flagging: the kernel's `Context` stores a declared grade
  alongside each entry's type, but no typing rule ever *reads* that stored grade back out other
  than the one `Lam` rule that just wrote it (`check.rs`'s `Var` rule builds its usage purely
  from the ambient `σ`, never consulting `entry.grade`). So a context here is just `List Ty`; the
  declared grade is only ever a *local* parameter of the `T-Lam` rule, matching the kernel's
  actual data flow.

  ── M5: the constant-family Kan fragment (docs/metatheory.md §1.1) ─────────────────────────────
  `iabs`/`transp`/`hcomp` below extend the fragment with the *reachable, evidence-backed* corner
  of `crates/blight-kernel/src/kan.rs`'s Kan table: every cited probe in §1.1 transports/composes
  along a **constant family** (the type line `i. A` does not actually mention the bound dimension
  `i`) — `transp_family_use_keeps_grade0_var_erased`, `hcomp_base_and_tube_...`, and
  `interval_var_carries_no_grade_in_usage_vector` all use a closed or constant `A`. This fragment's
  `Ty` is *already* non-dependent (`Ty` never mentions `Tm`, unlike the kernel's real dependent
  `Value`), so a "line of types" `i. A` collapses to a single fixed `A` here by construction — not
  a simplification imposed on top, but a structural consequence of scoping this file to
  `Bool`/`Π` in the first place. Consequently:

  * `transp`'s type-line/family argument is literally just the `Ty` `A` it transports *in* — there
    is no separate family term for a grade-`0` variable to hide inside, so §1.1(a)'s question
    ("does grade-0 erasure survive `transp` actually computing?") does not even arise in this
    fragment (there is nothing to erase); what carries over is §1.1(b), that the *base* is a
    genuine runtime position charged at the ordinary rate — see `transp`'s rule below, which is
    definitionally `hbase` unchanged.
  * `hcomp` sums its base's and tube's demand — §1.1(c)'s "ordinary additive accounting, no special
    interval magic" — exactly like `ite` sums its three branches, just for two. `phi` (a `Bool`
    standing in for the kernel's general cofibration formula, degenerately restricted to
    "everywhere false" / "everywhere true" — the two cases the cited `hcomp_*` probes actually
    exercise) is not consulted by the typing rule at all, matching (c): grading never looks at
    *which* face is live, only that both are charged.
  * `iabs` opens one fresh dimension binder for its body without touching `Γ`, `σ`, or `φ` at
    all — the mechanized form of §1.1(d), "a dimension binder contributes no slot to usage." A
    dimension count `d : Nat` threads through every `HasType` judgement purely as a well-scoping
    ledger (nothing in `Tm` ever *references* a specific dimension index — there is no `ivar`
    former — so `d` is otherwise inert); `iabs`'s body typechecking at `d + 1` against the very
    same `Γ`/`φ` as the `iabs` itself *is* the "no slot" claim, not just consistent with it.

  **Honest scope, unchanged from before this extension:** the fully **heterogeneous** case — a
  type line that actually varies across the dimension, whose grade itself may differ at each
  endpoint (docs/metatheory.md §1.3 obligation 2, and M7's "last open cubical-QTT corner") —
  needs a genuinely dependent `Ty` (so a "line of types" can be a real function of a dimension)
  and is explicitly **not** attempted here; extending this calculus that far is exactly the
  go-bar M7 already exists to probe. See `docs/metatheory-mechanized.md` for the full covered/
  not-covered ledger.
-/

import BlightMeta.Grade
import BlightMeta.Usage

namespace BlightMeta

/-- Types: `Bool`, and a Π-type graded by its domain's declared multiplicity (spec §3.2). -/
inductive Ty where
  | bool
  | arr (rho : Grade) (dom cod : Ty)
  deriving DecidableEq, Repr

/-- Terms, de Bruijn-indexed. `iabs`/`transp`/`hcomp` are the constant-family Kan fragment (M5 —
    see the module doc); `iabs`'s bound dimension lives in a wholly separate index space from
    `var`'s term-variable indices (there is no `ivar` former to conflate them with), which is why
    `shiftAbove`/`subst` below pass straight through it unchanged. -/
inductive Tm where
  | var (i : Nat)
  | lam (body : Tm)
  | app (f a : Tm)
  | tt
  | ff
  | ite (c t e : Tm)
  | iabs (body : Tm)
  | transp (A : Ty) (base : Tm)
  | hcomp (A : Ty) (phi : Bool) (tube base : Tm)
  deriving DecidableEq, Repr

namespace Tm

/-- Shift every free variable `≥ c` up by one — a fresh binder has been inserted at depth `c`
    (index `c` itself becomes the new binder; anything already `< c` is a binder *more local*
    than the insertion point and is untouched). -/
def shiftAbove (c : Nat) : Tm → Tm
  | var i => if i < c then var i else var (i + 1)
  | lam body => lam (shiftAbove (c + 1) body)
  | app f a => app (shiftAbove c f) (shiftAbove c a)
  | tt => tt
  | ff => ff
  | ite cnd t e => ite (shiftAbove c cnd) (shiftAbove c t) (shiftAbove c e)
  | iabs body => iabs (shiftAbove c body)
  | transp A base => transp A (shiftAbove c base)
  | hcomp A phi tube base => hcomp A phi (shiftAbove c tube) (shiftAbove c base)

/-- Capture-avoiding substitution: replace `var j` by `s`, shifting `s` itself every time we
    cross a binder (so its free variables keep pointing at the same outer binders), and shifting
    any `var i` with `i > j` down by one (the binder at `j` is gone). Crossing `iabs` needs no such
    shift — it opens a dimension, not a term variable, so `j`/`s` pass through untouched. -/
def subst (j : Nat) (s : Tm) : Tm → Tm
  | var i => if i = j then s else if i > j then var (i - 1) else var i
  | lam body => lam (subst (j + 1) (shiftAbove 0 s) body)
  | app f a => app (subst j s f) (subst j s a)
  | tt => tt
  | ff => ff
  | ite cnd t e => ite (subst j s cnd) (subst j s t) (subst j s e)
  | iabs body => iabs (subst j s body)
  | transp A base => transp A (subst j s base)
  | hcomp A phi tube base => hcomp A phi (subst j s tube) (subst j s base)

/-- The one substitution `check.rs`'s `β`-reduction actually performs: plug `s` in for the
    variable a `lam` just bound (slot `0`). -/
def subst0 (s body : Tm) : Tm := subst 0 s body

end Tm

/-- Insert a fresh type `X` into the context at position `c` (`c = 0` is "innermost": a brand
    new binder shadowing nothing; a larger `c` slides in past `c` existing, more-local binders,
    matching what `Tm.shiftAbove c` does to term-level indices). -/
def insertTy : List Ty → Nat → Ty → List Ty
  | Γ, 0, X => X :: Γ
  | [], _ + 1, X => [X]
  | A :: Γ, c + 1, X => A :: insertTy Γ c X

/-- The `Usage` analogue of `insertTy`: a fresh, unused (`0`-demanded) slot at position `c`. -/
def insertUsage : Usage → Nat → Usage
  | u, 0 => Grade.zero :: u
  | [], _ + 1 => [Grade.zero]
  | g :: u, c + 1 => g :: insertUsage u c

/-- **The graded judgement** `Γ; d ⊢ e :^σ A ⊣ φ` (spec §3.2/§4.1, restricted to this fragment): at
    ambient demand `σ`, with `d` dimension binders in scope, `e` checks against `A`, producing
    usage `φ`. Each constructor below is the direct transcription of the matching `check.rs` rule:

    * `var`  ↔ `Term::Var` (`check.rs` `infer_g`, "Var (graded, spec §3.2)"): unit usage `e_i` at
      the ambient `σ`.
    * `lam`  ↔ `Term::Lam` against `Value::Pi` (`check_g`, "Pi-Intro (graded)"): check the body
      at the *same* ambient `σ` under the extra binder, then demand `δ ≤ ρ` (the binder's own
      declared grade) and drop the binder's slot from the returned usage.
    * `app`  ↔ `Term::App` (`infer_g`, "Pi-Elim / app (graded)"): infer `f`, check the argument
      at `σ · ρ`, and *add* the two usages.
    * `tt`/`ff` : pure introduction, zero usage (no `check.rs` analogue needed — `Bool` stands
      in for any grade-0-formed, ω-eliminated closed data type, e.g. `crates/blight-prelude`'s
      `Bool`).
    * `ite`  ↔ a graded eliminator in the spirit of `check.rs`'s `Data`/`Elim` handling: all
      three subterms are demanded at the *same* ambient `σ`, usages summed.
    * `iabs` ↔ opening an interval/dimension binder (`check.rs`'s `Term::IAbs`/dimension-context
      extension): the body is checked one dimension deeper (`d + 1`), against the *unchanged*
      `Γ`/`σ`/`φ` — mechanizing §1.1(d), "a dimension binder contributes no slot to usage."
    * `transp` ↔ `Term::Transp` on a constant family (`kan.rs::transp`, `check.rs`'s `Transp`
      rule): the family *is* the fixed `A` being transported in (see the module doc), so this
      rule is definitionally "the base's own judgement, unchanged" — mechanizing §1.1(b), that
      the base is a genuine runtime position charged at the ordinary rate.
    * `hcomp` ↔ `Term::HComp` (`kan.rs::hcomp`, `check.rs`'s `HComp` rule): base and tube are both
      demanded at the *same* ambient `σ` and their usages are summed, exactly like `ite` — the
      cofibration `phi` plays no role in typing, mechanizing §1.1(c)'s "ordinary additive
      accounting, no special interval magic." -/
inductive HasType : List Ty → Nat → Tm → Ty → Grade → Usage → Prop where
  | var {Γ : List Ty} {d i : Nat} {A : Ty} {σ : Grade} (h : Γ[i]? = some A) :
      HasType Γ d (.var i) A σ (Usage.unit i Γ.length σ)
  | lam {Γ : List Ty} {d : Nat} {body : Tm} {ρ σ δ : Grade} {A B : Ty} {rest : Usage}
      (hbody : HasType (A :: Γ) d body B σ (δ :: rest)) (hle : δ ≤ ρ) :
      HasType Γ d (.lam body) (.arr ρ A B) σ rest
  | app {Γ : List Ty} {d : Nat} {f a : Tm} {ρ σ : Grade} {A B : Ty} {φf φa : Usage}
      (hf : HasType Γ d f (.arr ρ A B) σ φf) (ha : HasType Γ d a A (σ.mul ρ) φa) :
      HasType Γ d (.app f a) B σ (Usage.add φf φa)
  | tt {Γ : List Ty} {d : Nat} {σ : Grade} : HasType Γ d .tt .bool σ (Usage.zero Γ.length)
  | ff {Γ : List Ty} {d : Nat} {σ : Grade} : HasType Γ d .ff .bool σ (Usage.zero Γ.length)
  | ite {Γ : List Ty} {d : Nat} {c t e : Tm} {σ : Grade} {A : Ty} {φc φt φe : Usage}
      (hc : HasType Γ d c .bool σ φc) (ht : HasType Γ d t A σ φt) (he : HasType Γ d e A σ φe) :
      HasType Γ d (.ite c t e) A σ (Usage.add φc (Usage.add φt φe))
  | iabs {Γ : List Ty} {d : Nat} {body : Tm} {A : Ty} {σ : Grade} {φ : Usage}
      (hbody : HasType Γ (d + 1) body A σ φ) :
      HasType Γ d (.iabs body) A σ φ
  | transp {Γ : List Ty} {d : Nat} {A : Ty} {base : Tm} {σ : Grade} {φ : Usage}
      (hbase : HasType Γ d base A σ φ) :
      HasType Γ d (.transp A base) A σ φ
  | hcomp {Γ : List Ty} {d : Nat} {A : Ty} {phi : Bool} {tube base : Tm} {σ : Grade}
      {φtube φbase : Usage}
      (htube : HasType Γ d tube A σ φtube) (hbase : HasType Γ d base A σ φbase) :
      HasType Γ d (.hcomp A phi tube base) A σ (Usage.add φtube φbase)

namespace HasType

/-- **Mechanized §1.1(d), stated as a corollary rather than left implicit in the rule shape**:
    the dimension count in an `iabs`'s premise really is "one more than the conclusion's," with
    everything else held fixed — i.e. opening a dimension is *exactly* a no-op on `Γ`/`σ`/`φ`, not
    merely "doesn't happen to change" them because no rule needed to. -/
theorem iabs_preserves_context_and_usage {Γ : List Ty} {d : Nat} {body : Tm} {A : Ty} {σ : Grade}
    {φ : Usage} (h : HasType Γ d (.iabs body) A σ φ) :
    HasType Γ (d + 1) body A σ φ := by
  cases h with
  | iabs hbody => exact hbody

/-- **Mechanized §1.1(b)**: `transp` on a constant family charges its base at exactly the ambient
    ratethe base's own judgement already carries — concretely, an ambient-`0` `transp` forces
    all-zero usage on its base (mirroring `transp_base_charges_demand_erased_base_rejected`'s and
    `transp_base_omega_var_accepted`'s pattern: a `0`-graded base only ever checks at ambient `0`).
    This is really just `ambient_zero_usage` composed with `transp`'s rule, but stated
    concretely here (before `Weakening.lean` even proves the general lemma) as a sanity check that
    the rule's shape is not vacuous. -/
theorem transp_reflects_base {Γ : List Ty} {d : Nat} {A : Ty} {base : Tm} {σ : Grade} {φ : Usage}
    (h : HasType Γ d (.transp A base) A σ φ) : HasType Γ d base A σ φ := by
  cases h with
  | transp hbase => exact hbase

end HasType

-- ── Concrete instances mirroring the cited `crates/blight-kernel/src/check.rs` probes ──────────
-- The kernel's own tests are unit tests (one fixed term, one fixed context); these are the exact
-- Lean analogues, checked once and for all by `decide`/explicit derivation over this fragment's
-- `HasType`, rather than a general theorem (there isn't one to state beyond `ambient_zero_usage`/
-- `demote`, which subsume them — see `Weakening.lean`). Kept here, immediately after the judgement
-- they instantiate, as the concrete cross-check that the constant-family Kan rules above actually
-- reproduce the kernel's tested grading behavior and not just "some" plausible one.

/-- Mirrors `transp_base_omega_var_accepted`: an ω-graded base checks a `transp` at ambient `ω`. -/
example : HasType [Ty.bool] 0 (.transp .bool (.var 0)) .bool Grade.omega
    (Usage.unit 0 1 Grade.omega) :=
  .transp (.var rfl)

/-- Mirrors `transp_base_charges_demand_erased_base_rejected`: the very same term at ambient `ω`
    can *only* produce usage `[ω]` (never, say, `[0]`) — `transp` cannot launder the base's demand
    away. Phrased as a uniqueness fact since "rejected" itself (no derivation at a *different*
    claimed usage) is exactly `Usage.unit`'s injectivity on its grade argument, already given by
    `HasType.var`'s conclusion being syntactically forced. -/
example {φ : Usage} (h : HasType [Ty.bool] 0 (.transp .bool (.var 0)) .bool Grade.omega φ) :
    φ = Usage.unit 0 1 Grade.omega := by
  cases h with
  | transp hbase => cases hbase with
    | var h => rfl

/-- Mirrors `hcomp_base_and_tube_sum_demand_linear_rejected`/`_omega_accepted`'s shared setup: with
    the same variable used as *both* `hcomp`'s base and its tube, the combined demand is the
    semiring sum `σ + σ`, which is `ω` for any nonzero `σ` (in particular already at `σ = 1`) —
    the "no special interval magic, just addition" fact. -/
example : HasType [Ty.bool] 0 (.hcomp .bool true (.var 0) (.var 0)) .bool Grade.one
    (Usage.unit 0 1 Grade.omega) :=
  .hcomp (.var rfl) (.var rfl)

/-- The dimension-scoping half of `interval_var_carries_no_grade_in_usage_vector`: opening a
    dimension (`iabs`) around a `Bool` and *then* checking it still yields the very same
    one-context, zero-usage judgement as the bare `tt` would — the dimension is invisible to `Γ`
    and `φ` alike. -/
example : HasType [] 0 (.iabs .tt) .bool Grade.omega (Usage.zero 0) :=
  .iabs .tt

end BlightMeta
