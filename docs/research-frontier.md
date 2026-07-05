# Blight's Research Frontier

*An honest map of what Blight is trying to do, what we have machine-checked as working, what we have
machine-checked as **not** working, and the open question underneath all of it.*

Blight is a dependently-typed proof language whose kernel deliberately attempts to fuse three type
theories that normally live apart:

- **Cubical** (CCHM): paths, De Morgan interval, `transp`/`hcomp`/`comp`, `Glue`, and **univalence
  that computes** rather than an axiom you postulate;
- **Quantitative / graded** (QTT): a `0 / 1 / ω` semiring — erased / linear / unrestricted —
  threaded through every typing rule;
- **Algebraic effects & handlers**: effect rows with first-class, resumable continuations carrying a
  multiplicity grade.

The whole system is guarded by **two independent checkers** (a small trusted kernel plus a
separately-written re-checker that must agree or honestly abstain) and an external **Lean 4
mechanization** of its metatheory.

This document is not a sales pitch. It is the part most projects hide: the frontier where the
ambition meets what is actually provable. Blight's design bet is that **honesty scales** — that a
system which machine-checks its own limits, and abstains loudly where it cannot vouch, is a better
foundation than one large compiler you must simply trust.

---

## The open question

> **Can quantitative grading × cubical path types × algebraic effects be fused into a single,
> decidable metatheory with subject reduction and strong normalization?**

No published metatheory does all three together. Blight is a concrete artifact for probing whether
it is possible — and the current, machine-checked answer is: **the *seamless* fusion does not go
through as stated; a *stratified* version does.** The evidence is not prose. It is Lean.

Everything below is checkable: `cd mechanization && lake build`, then `#print axioms <name>` — a
theorem is only trusted here if that shows **no `sorryAx`** (only `propext` / `Classical.choice` /
`Quot.sound`, Lean's standard classical axioms, are permitted).

---

## What we machine-checked *works* (all `sorryAx`-free)

| Result | Where | What it says |
|---|---|---|
| **Strong normalization** | `Reducibility.lean:940` (`strong_normalization`) | The graded + constant-family-Kan fragment normalizes. |
| **Canonicity** | `Reducibility.lean:957` (`canonicity`) | A closed `Bool` in that fragment reduces to `tt`/`ff`. |
| **Grade-skeleton preservation** | `GradeSkeleton.lean` (`grade_skeleton_preserved_by_transp`) | Transport across a cubical line **cannot launder a variable's resource grade** — the soundness-critical *quantities × cubical* interaction (mirrors the kernel's `kan_line_grade_skeleton_eq`). |
| **Dependent-Π substitution** | `Dependent.lean:1365` (`subst_lemma`) | Substitution preserves typing for a genuinely dependent Π. |
| **Effect progress + grade safety** | `Effects.lean:1068` (`progress`), `:200` (`handle_grade_safe`), `:250` (`handle_linear_at_most_once`) | A well-typed effectful term is a value, performs, or steps; a handler resumes its continuation no more than its declared multiplicity. |
| **Effect subject reduction, base-type operations** | `Effects.lean:1544` (`preservation`), `:1440` (`handle_perform_preserving`) | *(RB1, see below)* Full subject reduction over the entire small-step relation — closed terms, base-type operation argument. |

That grade-skeleton result is the important one for the "is the fusion even safe" question: the
*soundness-critical* corner of quantities × cubical is mechanized and holds.

---

## What we machine-checked does **not** work (also `sorryAx`-free)

This is the frontier. Two concrete, machine-checked **negative** results pin exactly where the naive
fusion breaks — each is a Lean theorem proving that a desirable property is *false* as stated.

### 1. Dependent subject reduction is false without a conversion rule

`Dependent.lean:1509` — `preservation_false` proves `¬ (∀ … HasType → Step → …)`. For a genuinely
dependent Π, call-by-value argument reduction changes the codomain-instantiated type
(`subst0 a B ≠ subst0 a' B`), and a syntax-directed calculus with **no conversion rule** cannot
recover it. The fix is well-understood (add a definitional-equality/conversion relation), but it is a
real chunk of new metatheory, not a one-liner — and until it is added, dependent preservation
provably fails.

### 2. Deep-handler effect subject reduction fails against a *value-typed* continuation — and the fix only goes so far

`Effects.lean:1679` — `handle_perform_not_preserving` proves a concrete well-typed handler whose
`handle_perform` reduct is **not** typeable at the expected type. Root cause: the naive rule typed
the handler's continuation binder at the *value* type `opCod`, whereas the captured continuation
`k = λr. handle E[r] …` is a *function* of type `opCod → B`.

**The fix, mechanized (RB1).** We retyped the continuation binder to its first-class function type
`opCod → ᵂB` — which is exactly what the *shipping kernel already does*
(`crates/blight-kernel/src/check.rs`, `k : Π^ω(_:Bᵢ). C`). The Lean model had been a simplification
that diverged from the real checker. Against the corrected rule the outcome is **nuanced, and every
part is machine-checked**:

- **Positive** (`Effects.lean:1544` / `:1440`): subject reduction is recovered — over the *entire*
  step relation, for closed terms whose operation argument is a **base type**. A non-vacuity witness
  (`Effects.lean:1614`, `handle_perform_preserving_nonvacuous`) exhibits a handler whose clause
  genuinely *applies* the continuation and proves its reduct still types — so the theorem is not
  vacuously true.
- **The wall** (`Effects.lean:1863`, `handle_perform_regrade_obstruction`): for a *higher-typed*
  operation argument, the reduct still types, but only through an arrow **re-grading** (`1 → ω`) that
  the substitution lemma structurally cannot supply. This is a precise, machine-checked
  characterization of the residual gap — an obstruction to the *proof method*, not a fresh
  refutation.

So the effect corner is *better* than the flat negative suggested: first-class continuation typing
(the rule the kernel ships) recovers effect safety for the common, base-type case. But the general
case remains a documented, machine-pinned open edge.

---

## The decision this forced: stratify, don't fuse (P4)

Given two machine-checked negatives, Blight does **not** pretend the seamless three-way fusion holds.
It adopts the **stratified** theory the spec always kept in reserve:

- the **kernel** stays a pure dependent + cubical core (where SN, canonicity, and the grade-skeleton
  interaction are proven);
- **effects** live in the *tower* as CPS-elaborated, kernel-re-checked code, rather than as a fused
  kernel primitive with its own subject-reduction obligation.

This is a *data-driven* retreat, not a time-pressure one: the negatives say precisely why the unified
bet fails, and the stratification sidesteps exactly those failure modes. (Full checkpoint:
[metatheory.md §2.6](metatheory.md).)

---

## So what is "a more perfect Blight"?

The honest reading of the evidence is that **"perfect Blight" is probably not a single fused
calculus.** The mathematical problem — decidable conversion + heterogeneous Kan + dependent effect
handlers, all normalizing together — is not merely unimplemented; parts of it are *open research*,
and two of its naive forms are machine-checked as false. A perfect Blight is more likely one of:

1. **The stratified language, made rigorous** — a kernel that is proven sound, with a *formally
   verified equivalence* between the pure kernel and the tower's CPS effect elaboration. (This is the
   default target, and the honest one.)
2. **A restricted fragment where fusion genuinely works** — e.g. graded cubical paths *without*
   dependent effect handlers — carved out and proven whole.
3. **An explicit research testbed** — Blight framed as the concrete artifact on which the coherence
   conditions for effect-dependent, quantitative, cubical type theory get worked out, one
   machine-checked result at a time.

Blight currently commits to (1) and serves as (3). What it does **not** do is claim (0): a seamless
fusion that works. The two-checker architecture and the mechanization exist precisely so that if we
ever *did* claim it, the claim could be falsified.

---

## The nearest open edges (where help is welcome)

- **A dependent conversion relation** for `Dependent.lean`, to turn `preservation_false` into a
  positive preservation. Well-scoped, real metatheory.
- **A re-grading substitution lemma** for `Effects.lean`, to push `handle_perform_preserving` past
  base-type operation arguments (the wall characterized by `handle_perform_regrade_obstruction`).
- **The kernel↔tower effect equivalence** — proving the CPS elaboration preserves the pure kernel's
  guarantees is what would make the stratified story airtight.

---

## How to check every claim here

```sh
cd mechanization
lake build                                   # must end "Build completed successfully"
# then, for any theorem cited above:
#   #print axioms <name>
# and confirm it shows no `sorryAx`.
```

Every result named in this document is a real Lean theorem at the cited file:line, and the negative
results are as machine-checked as the positive ones. That symmetry — proving what fails with the same
rigor as what works — is the point.
