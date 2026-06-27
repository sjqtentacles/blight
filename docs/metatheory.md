# Blight metatheory notes — the two research corners

These notes back the two "research bet" corners of [the spec](blight-spec.md) §10.3 (quantities ×
cubical) and §10.4 (graded effects + QTT normalization) with **measured kernel behavior** rather
than speculation. §1 leads with evidence from the `grades-cubical-stress` characterization probes in
`crates/blight-kernel/src/check.rs` (the `transp_*`/`hcomp_*`/`interval_var_*` tests). §2 records the
normalization argument for the fragment we actually compile and run, and the committed fallback.

This is honest status, not a soundness proof. Where the kernel's behavior is pinned by a passing
test, we say so and cite the test by name; where an obligation remains open, we mark it open and
state the committed degradation path.

---

## 1. Quantities × cubical (spec §10.3)

The kernel fuses a QTT resource semiring (`Grade ∈ {0, 1, ω}`) with a CCHM-style cubical core
(`transp`/`hcomp`/`comp`, an interval `𝕀`, cofibrations). Spec §10.3 lists three open questions; the
probes resolve all three *for the kernel as implemented*, and the answers are favorable.

### 1.1 What the kernel actually does (evidence)

All claims below are pinned by tests in `crates/blight-kernel/src/check.rs`.

**(a) Grade-0 erasure survives `transp` — when the erased variable stays on the type line.**
A grade-`0` variable used *only* in the family/type-formation position of a `transp` is never
charged: its binder check `0 ≥ 0` passes and the value remains erased across the Kan op.

> `transp_family_use_keeps_grade0_var_erased`: `λ (A :⁰ U₀). λ (x :ω A). transp (i. A) ⊥ x` checks
> at `(A :⁰ U₀) → (x :ω A) → A`. `A` appears only in the constant transport line and is never
> demanded.

This is the positive resolution of the spec's sharpest worry ("does grade-0 erasure survive `transp`
actually computing at runtime?"): **yes** — the type-level path data that drives the Kan computation
lives in the 0-fragment and is not laundered into runtime relevance.

**(b) The soundness teeth: a Kan op does not launder an erased value into a relevant position.**
`transp`'s *base* is a genuine runtime position and charges ordinary demand on its argument.

> `transp_base_charges_demand_erased_base_rejected`: the same term with `x :⁰ A` (erased base) is a
> `GradeViolation` — a `0`-graded base use fails `1 ≤ 0`.
> `transp_base_omega_var_accepted`: with `x :ω A` the identical term checks. So the rejection is the
> grade discipline discriminating, not `transp` being untypable.

**(c) Kan-op face/tube usage is ordinary additive accounting — no special interval magic.**
`hcomp` sums the demand of its base *and* its tube.

> `hcomp_base_and_tube_sum_demand_linear_rejected`: with `x :¹ A` used in both the base and the tube,
> demand is `1 + 1 = ω`, and `ω ≤ 1` fails ⟹ `GradeViolation`.
> `hcomp_base_and_tube_omega_var_accepted`: with `x :ω A`, ω absorbs the double demand and it checks.

This answers "what usage do `hcomp`/`comp` impose on their faces?": the **same semiring addition** as
any other elimination form. There is no bespoke cubical usage rule.

**(d) Interval/dimension variables are ungraded — the kernel tracks only their count.**
A dimension binder contributes *no slot* to the term usage vector and imposes no multiplicity
constraint.

> `interval_var_carries_no_grade_in_usage_vector`: in context `[A :⁰ U₀, x :ω A]` with one dimension
> `i` in scope, inferring `transp (k. A) ⊥ x` at σ = 1 yields a usage vector of length **2** (only
> the two term variables) with `x ↦ 1` (base use) and `A ↦ 0` (type-line only). The dimension adds
> nothing.

This pins the spec's "multiplicity of an interval variable" question: dimensions are effectively
**ω-replicable / ungraded**, which is sound because they are erased at runtime (they carry no
computational content of their own; they merely index the Kan computation).

### 1.2 Proof sketch for the cases that pass

The above is exactly what the standard CCHM metatheory predicts once grades are read as a *separate*
coeffect annotation layered over the cubical term structure:

- **Erasure-survives-`transp`.** Define the runtime erasure `|·|` that drops all `0`-graded
  sub-terms and all dimension data. On the modeled fragment, `|transp (i. A) ⊥ b| = |b|` because the
  family `A` is in the 0-fragment (type-formation, checked at grade 0) and the cofibration/interval
  are dimension data. Hence a `0`-graded variable occurring only inside `A` does not appear in
  `|transp (i. A) ⊥ b|`, so it is genuinely absent at runtime — consistent with its `0` binder. The
  kernel realizes `|·|` precisely as "the usage vector is computed from runtime positions only,"
  which (a)/(d) above demonstrate operationally.
- **Additive face usage.** `hcomp`/`comp` are elimination-shaped: their result demand σ flows to
  each runtime sub-term (base and each tube face) and the per-variable demands are combined by
  semiring `+`. Subject-reduction for the Kan reductions (`transp` on each type former, `hcomp`
  filling) does not change which variables occupy runtime positions, so usage is preserved under
  reduction. (c) is the linear witness of this.

These sketches cover the fragment the kernel checks and runs; they are *not* a normalization proof
for the fused theory in full generality (see §1.3).

### 1.3 Open obligations and the committed fallback

Still open (not contradicted by any probe, but not proven here):

1. A **unified normalization / decidability** proof for the full fused quantities × cubical theory
   (all type formers, full cofibration algebra, higher inductive types).
2. Face-usage for the **general `comp`** with a non-trivial type line `i. A` where `A` itself is
   graded data (the probes use constant or 0-fragment families).
3. Interaction of grades with **path-induction over HITs**.

**Committed degradation path (unchanged from spec §10.3).** If the unified story cannot be proven,
Blight *stratifies*: the cubical equality machinery lives in the unrestricted (`ω`) fragment where
standard CCHM metatheory applies, and quantities are tracked in a non-cubical layer. The evidence
above means we are **not currently forced** onto this fallback — at grade 0/1 the kernel's behavior
across `transp`/`hcomp`/interval binders is exactly the layered reading, with no anomaly observed.

Primary sources (as in the spec): Mitchell Riley, *A Bunched Homotopy Type Theory* (PhD, 2022);
Maximilian Doré, *Linear Types with Dynamic Multiplicities in Dependent Type Theory* (ICFP'25). Both
*layer* quantities over a cubical host rather than fusing them in one trusted core — precisely the
fallback's published precedent.

---

## 2. Graded effects + QTT normalization (spec §10.4)

### 2.1 The problem

The Gaboardi et al. combined effects+coeffects calculus is *simply typed* with one graded monad and
one graded comonad. Blight's surface offers a *dependent* kernel with multiple interacting modalities
and **full handlers** whose continuations may be invoked 0/1/many times (§4.4). A
normalization/decidability proof for that union does not exist, and continuation-capturing handlers
directly threaten the totality that dependent proofs require.

### 2.2 What Blight actually ships, and why it is sound

Blight resolves the totality threat by **locus separation**, exactly the spec §10.4 fallback:

- The **spore (trusted kernel) is pure**: it is dependent-cubical QTT with *no* handler primitive in
  the trusted core. Effects appear at the surface (`effect`/`handle`/`!`) and are *elaborated* into
  ordinary Blight code over the pure kernel (free-monad / CPS), behind the same proof door. The
  independent re-checker checks effect rows at the *type level* and declines only the genuinely
  out-of-fragment forms (cubical/foreign/higher-order motives) — it does not need a handler
  primitive either.
- The **runtime** implements effects as **full CPS deep handlers with multi-shot delimited
  continuations** (`crates/blight-codegen/runtime/effects.c`). This is strictly more expressive than
  the tail-resumptive fragment, and lives entirely in the (untrusted) tower/runtime, so its
  operational behavior does not enlarge the trusted kernel or its metatheory.

Because handlers are tower code over a pure kernel, the kernel's normalization story is "just"
dependent-cubical QTT (§1), and effectful programs cannot inject non-termination into *proof*
checking: a proof is a closed kernel term, and the kernel has no `perform`/`handle` reduction.

### 2.3 Strong-normalization sketch for the tail-resumptive fragment

For the subset where every handler resumes its continuation **at most once in tail position**
(tail-resumptive handlers), the CPS translation lands in the pure kernel as ordinary
continuation-passing terms with no recursive knot introduced by resumption: each `perform` becomes a
call to a statically-known continuation that is itself a kernel term, and a tail-resumptive handler
is a fold over the operation tree that is structurally decreasing on the computation it interprets.
Hence the translated program normalizes iff the underlying pure kernel term does — which it does by
the kernel's metatheory. Multi-shot and non-tail resumption move strictly outside this fragment and
are therefore handled at runtime (where divergence is permitted), never as kernel reductions.

### 2.4 Partiality

Partiality (§4.5) is realized by the **QIIT** delay-monad construction
(Altenkirch–Danielsson–Kraus): expressible because the kernel already pays for HITs (§2.7). This
gives partiality-as-effect a known-good realization even in the conservative (pure-kernel)
configuration, so non-termination is a *value* (`Delay A`) rather than a metatheoretic hole.

### 2.5 Open obligations and the committed fallback

Open: a normalization/decidability proof for handlers *as a kernel primitive* with multiple modalities.
**Committed fallback (already the shipped design):** keep effects in the tower as free-monad/CPS over
the pure kernel; partiality via the QIIT. The shipped system is thus *on* the conservative
configuration by construction — there is no retreat to perform, because the trusted core never took
the risky bet.

---

## Cross-references

- Spec §10.3 / §10.4 ([docs/blight-spec.md](blight-spec.md)) — the original risk prose and fallbacks.
- [docs/roadmap.md](roadmap.md) — milestone status.
- Evidence tests: `crates/blight-kernel/src/check.rs` (`transp_*`, `hcomp_*`,
  `interval_var_carries_no_grade_in_usage_vector`).
- Runtime effects: `crates/blight-codegen/runtime/effects.c` (full CPS deep handlers, multi-shot).
