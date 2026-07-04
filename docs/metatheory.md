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
   graded data (the probes use constant or 0-fragment families). — **Resolved** (Tracks M3 + M7):
   see below.
3. Interaction of grades with **path-induction over HITs**. — **Resolved, negative** (Track E4): see
   below. Negative *for the implemented fragment* (nullary, non-indexed path constructors); a path
   constructor with its own argument telescope is out of Wave 7's scope and could reopen this
   obligation.

**Track M3 evidence for obligation 2 (partial).** `comp_base_and_tube_over_graded_pi_line_sum_demand_linear_rejected` / `..._omega_accepted` (`crates/blight-kernel/src/check.rs`)
extend (c) above from an *opaque* type-line variable to a genuine graded former: `comp`'s type
line is `j. Pi(1, A, A)` — real graded data (a linearly-graded Π), not a bare `Var(k)` — and its
base and tube both use an `f : Pi(1,A,A)` bound outside the comp. The result is exactly the same
additive semiring accounting as every other Kan-op face probe: `f` used once in the base and once
in the tube demands `1 + 1 = ω`, rejected against a linear binder and accepted against an ω one.
So the "structurally rich, graded-data" half of obligation 2 is now evidence-backed — grading the
type line itself with a real type former does not change `comp`'s additive face accounting.
This type line is still *constant* in the comp's own dimension (it doesn't mention the bound `j`);
the fully **heterogeneous** case — a line whose *grade itself* differs at each dimension endpoint,
which needs an inhabited `Glue` to construct — is the subject of Track M7 below.

**Track M7: the heterogeneous case, probed and closed.** Obligation 2's fully heterogeneous corner
was probed concretely rather than left as a documented-but-unattempted gap. Construction: a
non-constant type line `i. Glue (Pi ω A (Σ A A)) (i=0) (Pi 1 A (Σ A A)) e` — the *same* `Pi`-former
shape at both ends, differing only in *declared grade* (`ω` at `i=0`, `1` at `i=1`). The Glue
boundary reductions (`normalize::eval`'s `Term::Glue` arm, §1.4) collapse this to a bare graded `Pi`
at each face — no special-casing of `Value::Glue` as an expected type is even needed to reach the
corner. Transporting `base = λx. (x, x)` (whose body genuinely demands `ω` on its bound variable,
i.e. it type-checks against the `Pi ω ...` source face but **not** against a `Pi 1 ...` face) along
this line was, prior to this fix, **accepted** by both `Transp` and `Comp`: each checks `base`
*once*, against the line's *source* endpoint, and returns the *target* endpoint as the whole
expression's type with no re-verification that the two endpoints agree in grade. Concretely this
let a value whose body was checked to need `ω` be re-labeled, via the line, as `Pi(1, ...)` — a
**reachable soundness gap**, not merely a theoretical one: a downstream consumer trusting `Pi(1,
...)`'s "body uses its argument at most once" promise (e.g. a future in-place-mutation/uniqueness
optimization built on grade `1`, per Wave 4's RC-reuse go-bar) would be deceived.

*The fix (implemented, not just documented).* `kan_line_grade_skeleton_eq`
(`crates/blight-kernel/src/check.rs`, mirrored independently in
`crates/blight-recheck/src/conv.rs`) is wired into both `Transp` and `Comp`: whenever a line's two
endpoints are not already definitionally equal (`conv`) — which is fine in general, that is the
entire point of `transp`/`ua` — any `Pi`-formers occurring at corresponding positions in the two
endpoints must still agree in *grade*. The type itself may differ across the line; its quantitative
skeleton may not. This is the **committed stratification fallback** below, made precise and minimal
rather than a blanket "non-constant Kan ops require ambient `σ = ω`" rule (which was considered and
rejected: it would restrict only the *ambient* grade at the `Transp`/`Comp` site itself, but the
laundered value can be bound and reused at a *different*, lower ambient grade later — it does not
address the actual gap). `Sigma`-formers (ungraded) and any other matching head shape recurse
structurally with no constraint; mismatched head shapes (e.g. `Pi` vs `Data`, as in genuine `ua`
between unrelated types) are untouched.

Evidence: `transp_heterogeneous_pi_grade_glue_line_rejected` pins the fix — the construction above
is now a `TypeError::BadCubical` — with the red state (kernel `Ok`, confirming the gap was reachable
before the fix) captured in the test's doc comment; `transp_homogeneous_pi_grade_glue_line_accepted`
is the accept twin (same `Glue`-line shape, both faces at `ω`) confirming the rejection is the grade
*mismatch* discriminating, not `Transp`-over-any-`Glue`-line being rejected wholesale. Every
pre-existing Kan-op grade probe (M0–M3) uses a *constant* family (`conv(a0,a1)` trivially holds), so
none is affected by the new restriction — confirmed by the full `blight-kernel` (150 tests) and
`blight-recheck` (property/differential included) suites passing unchanged.
The independent re-checker's copy of this restriction is currently **unreachable in practice**
(`recheck_declines_glue` — `from_kernel` declines any judgement mentioning `Glue` before
typechecking, so the re-checker never actually evaluates a `Glue`-headed line); it is kept anyway
as defense-in-depth matching every other kernel invariant this repo double-implements, and would
activate immediately if the `Glue` decline were ever lifted.

**Obligation 1.3.2 is now machine-checked, not just test-pinned (Wave 8 / M10).**
[`mechanization/BlightMeta/GradeSkeleton.lean`](../mechanization/BlightMeta/GradeSkeleton.lean)
transcribes `kan_line_grade_skeleton_eq` verbatim over the mechanization's `Ty` and proves
`grade_skeleton_preserved_by_transp`: whenever the check accepts two `Π`-formers as a Kan line's
endpoints, their declared grades already coincide — the exact fact that rules out the laundering
attack described above, now an independent Lean proof rather than solely a Rust accept/reject
test pair. `grade_skeleton_preserved_by_transp_nested` extends this to a `Π`-under-`Π` line;
`kanLineGradeSkeletonEq_heterogeneous_pi_rejected`/`_homogeneous_pi_accepted` are `decide`-checked
twins of `transp_heterogeneous_pi_grade_glue_line_rejected`/
`transp_homogeneous_pi_grade_glue_line_accepted` above. See
[docs/metatheory-mechanized.md](metatheory-mechanized.md) for the full correspondence entry.

**Committed degradation path (unchanged from spec §10.3).** If the unified story cannot be proven,
Blight *stratifies*: the cubical equality machinery lives in the unrestricted (`ω`) fragment where
standard CCHM metatheory applies, and quantities are tracked in a non-cubical layer. Track M7 above
is exactly one instance of this fallback, made concrete: rather than prove full compatibility of
grades with arbitrary Kan lines, the kernel now *rejects* the one construction shown to be unsound
(grade-heterogeneous `Pi` endpoints) while continuing to accept every grade-homogeneous line (which
covers the entire corpus). At grade 0/1 elsewhere, the kernel's behavior across `transp`/`hcomp`/
interval binders remains exactly the layered reading, with no other anomaly observed.

Primary sources (as in the spec): Mitchell Riley, *A Bunched Homotopy Type Theory* (PhD, 2022);
Maximilian Doré, *Linear Types with Dynamic Multiplicities in Dependent Type Theory* (ICFP'25). Both
*layer* quantities over a cubical host rather than fusing them in one trusted core — precisely the
fallback's published precedent.

**Track E4: grades × path-induction over user HITs, probed and resolved negative.** Wave 7/E4
generalizes the built-in `PathConstructor` machinery (`crates/blight-kernel/src/signature.rs`,
already used for the `ua`/ `Glue` layer's internals) to a genuinely new *term* former,
[`Term::PCon`]/[`Value::PCon`] — a path constructor applied to its arguments at an interval, whose
declared boundary equations (`lhs`/`rhs`) it collapses to definitionally at `I0`/`I1`
(`normalize::eval`'s `Term::PCon` arm) and otherwise denotes a genuine new canonical value. The
eliminator (`Term::Elim`) gains one *path* method per path constructor, alongside its existing one
*point* method per ordinary constructor (`infer_elim`, `path_method_type`): a path method's type is
the `PathP` connecting the eliminator applied to the path constructor's `lhs` to the eliminator
applied to its `rhs`, and `do_elim`'s new `Value::PCon` arm computes by applying that path method to
the constructor's arguments and then to the same dimension — the eliminator's ι-rule extended, by
direct analogy with the point case, to path constructors
(`hit_path_constructor_elim_commutes_along_the_path` pins this end to end: `plam i. S¹-elim motive
m-base m-loop (loop @ i))` checks as a path between the two `base`-boundary values precisely because
this rule fires).

**Scope of the probe.** As with M7, only a nullary path constructor (`args` empty) over a
non-parameterized, non-indexed carrier is implemented — enough for the classic circle-style HIT
(`S¹` with `base`/`loop`); an indexed carrier, a parameterized one, or a path constructor with a
non-empty (in particular a *recursive*) argument telescope fails safe (`unimplemented!`) in both
`check_g`'s and `infer_g`'s `PCon`/path-constructor-method arms, never silently mis-elaborated.

**The question.** Obligation 1.3.2 (Track M7 above) found that a Kan operation checking a value
*once*, against one endpoint of a non-constant line, then handing back a *different*, unverified
endpoint as the result type, can launder a linear resource's usage discipline. `Term::Elim`'s new
path-constructor branch is superficially similar in shape — it too "connects" two computed values
(the eliminator applied to `lhs` and to `rhs`) via a `PathP` — so the natural probe is: does
*eliminating* a HIT admit an analogous re-verification gap, letting a value checked once at one
grade be laundered into a different grade elsewhere?

**The probe, concretely.** `hit_elim_using_binder_in_both_point_and_path_method`
(`crates/blight-kernel/src/check.rs`) builds `λ x. S¹-elim (λ_.Bool) [x, plam _. x] base`: the
*point* method is the outer binder `x` itself, and — because `base` reduces via that point method to
`x` — `path_method_type` *forces* the path method's type to be `PathP (_.Bool) x x`, whose simplest
inhabitant (`plam _. x`) mentions `x` a second time. This is the sharpest test the implemented
(nullary) fragment admits: both eliminator branches genuinely depend on the same outer resource.

- `grades_across_hit_path_induction_unrestricted_accepted`: at grade `ω` this **must**, and does,
  check — an unrestricted resource may be inspected as many times as needed.
- `grades_across_hit_path_induction_linear_double_use_rejected`: at grade `1` (affine — at most
  once) the *identical* term is **rejected** with `TypeError::GradeViolation`. The point method's
  use of `x` (demand `1`) and the path method's forced re-use (demand `1`) sum, by the ordinary
  semiring (`1 + 1 = ω`, `crate::semiring::Grade::add`), to demand `ω`, and `ω ≤ 1` is false.

**Verdict: negative — no laundering found, no fix needed, for this fragment.** Unlike Track M7,
there is no "check once, hand back a different unverified type" step here to exploit: `infer_elim`
checks *every* method — point or path — with `self.check_g(ctx, method, &method_ty, sigma)` in the
*same* context and at the *same* ambient `sigma`, and folds every method's usage into the total with
the same `usage = usage.add(&method_usage)` this repository already uses for plain point-constructor
branches (`method_type`'s callers, predating E4). A path method is, from the grading discipline's
point of view, simply *one more branch* — exactly like a second point-constructor arm — and the
existing multi-branch-summing accounting (conservative: only one branch runs at a time, but the
checker doesn't statically know which, so it soundly charges the sum) already covers it with no
special-casing. The rejection above is not a bug surfaced by the probe; it is that same
conservative-but-sound accounting correctly recognizing that proving the eliminator's *coherence*
along the new path genuinely requires a second look at a resource the point branch already spent.
So obligation 3 is resolved **negative**: no `kan_line_grade_skeleton_eq`-style restriction is
needed to eliminate a nullary, non-indexed, non-parameterized HIT soundly at any grade.

**Boundary of the negative result.** This verdict is scoped to the implemented fragment. A path
constructor with its own (in particular recursive) argument telescope would introduce genuinely new
binders inside a path method — closer in shape to `comp`'s "graded type line" corner (obligation 2)
than to the nullary case probed here — and is exactly the kind of extension that should re-run this
probe before being accepted as sound, rather than assuming the negative result transfers.

**Parity.** The re-checker declines any judgement mentioning `Term::PCon` outright
(`from_kernel_declines_pcon`, `crates/blight-recheck/src/term.rs`) — the same honest-refusal
discipline as `Glue`/`Partial`/`System` in Track M7, chosen because the re-checker has no
independent model of a HIT's boundary equations (those live only in the kernel's `Signature`) to
re-derive them from. Unlike effect rows and continuation grades — which the re-checker *does*
independently re-derive and enforce (`typecheck.rs`: it re-derives the effect row and Rejects a
handler clause that resumes above the operation's `cont_grade`) — a HIT's boundary equations have no
independent re-derivation available to the re-checker, so this decline is the correct parity story:
an honest refusal, never a silent pass.

### 1.4 Univalence (`ua`) via `Glue`, and the deliberately-deferred polymorphic computation rule

`ua : Equiv A B → Path (Type 0) A B` (`std/path.bl`) is *derived*, not a kernel primitive. Following
CCHM, it is the **single-face** `Glue` line

> `ua A B e := λ i. Glue B (i=0) A e`

whose endpoints are forced by the Glue boundary reductions the kernel applies during evaluation
(`crates/blight-kernel/src/normalize.rs`, the `Term::Glue` arm): on a *total* face `Glue B ⊤ A e ≡ A`
and on an *empty* face `Glue B ⊥ A e ≡ B`. Hence `(ua e) @ i0 ≡ A` and `(ua e) @ i1 ≡ B`
definitionally, so the `Path (Type 0) A B` endpoint check succeeds with no extra coercion. The only
new *trusted primitive rule* this adds beyond `Glue` formation is the **`transp`-over-`Glue`**
reduction (`crates/blight-kernel/src/kan.rs::transp_glue`):

> `transp^i (Glue B (i=0) A e) ⊥ a ≡ equiv-fun e a`

guarded to exactly the reachable univalence shape (an `i=0` face with a base `B` constant in `i`);
every other `Glue` Kan case is `unimplemented!` rather than silently mis-reduced. This is the
univalence *computation* rule. Evidence, at three independent layers:

1. the kernel **white-box** test `kan.rs::transp_ua_glue_line_applies_forward_map` (distinct
   endpoints `A=Nat ≠ B=Bool`, forward map `λ_.true`, so the result `true` is observably *not* the
   input — the rule genuinely fires at the value layer);
2. the **black-box, full-pipeline** conformance golden `kan_conformance::ua_computes_is_conformant`,
   which drives an *inlined* `ua (id-equiv T)` (with `T := Π(A:Type 0)(x:A). A`, built from
   primitives only) through elaborate→kernel and checks `transp (i.(ua e)@i) ⊥ a ≡ a` by a plain
   `refl` — the `Path T` boundary check *only* succeeds because `transp_glue` actually reduces (its
   sibling `ua_formation_is_conformant` pins the formation rule the same way);
3. the closed end-to-end proof obligation `examples/ua_compute.bl`.

The white-box and black-box goldens pin both directions: distinct-endpoint firing (value layer) and
the identity instance through the full surface pipeline (an axiom-free surface witness — a closed
`Equiv` between *distinct* types does not exist for a non-identity map, so the identity instance is
the strongest such surface golden).

**Deliberately deferred: a *polymorphic* in-Blight `ua-computes` lemma.** Stating
`transp (ua e) a ≡ equiv-fun e a` as a Blight term `Π A B e a. Path B (transp (i.(ua e)@i) ⊥ a)
(equiv-fun e a)` would force the kernel's Kan operations to *evaluate* `transp` **under open binders**
(with `A B e a` free). The entire Kan layer — in both the trusted kernel and the independent
re-checker — currently assumes Kan ops run on *closed* values (`family_is_constant`/`line_closure`
quote/convert at de Bruijn level `0`). Supporting the open case means threading ambient De Bruijn
levels through the whole Kan API in *both* checkers — a substantial expansion of trusted surface area
and re-checker parity burden, for a lemma whose computational content is already established by the
closed evidence above. Per this repo's TCB discipline (the kernel is the only trusted base; never add
a kernel feature that closed tower-level evidence already covers; keep the `ua` surface minimal), the
polymorphic lemma is **not** added. The reduction *primitive* is implemented and tested; only its
restatement as an open-term theorem is deferred, and revisited only if a concrete proof in the corpus
needs it.

### 1.5 Kan-table reachability and the fail-safe discipline

The Kan table (`crates/blight-kernel/src/kan.rs`, mirrored in `crates/blight-recheck/src/kan.rs`)
implements `transp`/`hcomp` (and `comp = hcomp ∘ transp`) **per type former**. Not every former ×
operation cell is implemented; the policy is *implement exactly the cells the corpus reaches, and
make every other cell fail-safe (a panic), never a silent reduction.* A panic on a hypothetical
well-typed term is a bug to fix by extending the table — it can **never** accept a false judgement,
so it does not threaten soundness. The cells:

| former | `transp` | `hcomp` |
|---|---|---|
| constant line (any former) | identity (fast path) | floor (constant tube) / lid (⊤) / floor (⊥) |
| `Π` | implemented (heterogeneous, with backward arg-fill) | implemented (pointwise in codomain) |
| `Σ` | implemented (component-wise, dependent fill) | implemented (component-wise) |
| `PathP` | implemented (inner `Comp`, endpoints fixed) | implemented (inner `HComp`) |
| `Data` (no params/indices, e.g. `Nat`/`Bool`) | identity | n/a (no varying face reachable) |
| `Univ` | identity | **fail-safe** (unreachable), pinned `hcomp_univ_varying_face_fails_safe` |
| `Glue` | **implemented** for the univalence line in *either* traversal direction (`transp_glue`); **fail-safe** otherwise | **fail-safe** (unreachable) |
| `Partial`/`System` | **fail-safe** (`CannotInfer`; no infer/check rule at all — parseable, never elaborated by the corpus) | n/a |
| indexed `Data` / `Int` / `Eff` (non-constant line) | **fail-safe** (unreachable) | **fail-safe** (unreachable) |

Reachability argument for the fail-safe cells:

- **`Glue` is reached only through `ua`, in both traversal directions.** `ua` is the sole `Glue`
  constructor in the prelude/examples; it builds the single-face line `i. Glue B (i=0) A e`. The
  corpus transports along this line in its **forward** direction (`ua e` itself, `transp_glue`
  applies the equivalence's forward map, `equiv-fun e`) and, since Wave 7/E3, its **reverse**
  direction (`sym (ua e) = plam i. (ua e) @ (~i)`, `std/path.bl`'s `sym`; `transp_glue` applies the
  equivalence's *inverse* map extracted from its contractible-fibres witness, `vsnd`/`vfst`/`vfst`).
  `sym` produces the De Morgan-negated cofibration `Cofib::Eq0(Neg(Dim))`, which is semantically the
  `i=1` face but not syntactically folded to `Cofib::Eq1(Dim)` by `normalize_interval` (only literal
  `I0`/`I1` endpoints fold); `transp_glue`'s face guard recognizes both the negated and un-negated
  syntactic forms of each face. End-to-end corpus witness: `examples/ua_compute.bl` (forward) and
  `examples/ua_compute_reverse.bl` (reverse), each a closed reflexivity proof that only type-checks
  because the kernel performs the corresponding Glue transport. Kernel white-box:
  `transp_ua_glue_line_applies_forward_map`,
  `transp_ua_glue_line_reverse_face_applies_inverse_map` (bare `Eq1(Dim)` shape),
  `transp_ua_glue_line_negated_dim_reverse_face_applies_inverse_map` (the exact `sym`-produced
  `Eq0(Neg(Dim))` shape). Any other cofibration (a connection, a disjunction, or a genuinely
  non-constant base) is fail-safe; pinned by `transp_glue_non_ua_face_fails_safe` and
  `..._non_constant_base_fails_safe`. `hcomp`-over-`Glue` remains unreachable (no corpus term
  composes inside a glued type) and fails safe as part of the closed-type catch-all, pinned by
  `hcomp_univ_varying_face_fails_safe` (representative closed-type witness).
- **`Partial`/`System` are parseable but never elaborated by the corpus.** The surface forms
  `(Partial φ A)`/`(system (φ t) ...)` elaborate to `Term::Partial`/`Term::System`, but no
  `std/*.bl` module or `examples/*.bl` program constructs one (grepped: zero hits), and the kernel
  has no `infer`/`check` rule for either — `infer_g` falls through to `CannotInfer` rather than
  panicking or (worse) silently accepting. Pinned by
  `check::tests::partial_and_system_have_no_inference_rule`. This is the correct Wave 7/E3
  disposition under the implement-exactly-what-the-corpus-reaches discipline: the corpus does not
  reach these constructs at all, so the fail-safe *is* the terminus, not a placeholder.
- **`hcomp`'s Π branch cannot pass a genuinely varying face through to a closed inner type either.**
  Its `PathP` branch *defers* the inner composition as a `Term::HComp` rather than recursing
  eagerly, but quoting that `Term::HComp` back out of a `Value::PLam` (which the enclosing `Π`
  branch must do to build its λ's body) forces evaluation immediately, so a face that bottoms out at
  a closed inductive/`Univ`/`Glue` still hits the same fail-safe panic — it is not actually made lazy
  by the deferral. Pinned by `hcomp_pi_varying_face_over_closed_codomain_fails_safe`
  (`#[should_panic]`); the companion `hcomp_sigma_varying_face_is_componentwise` shows the same
  varying-face shape *does* reduce structurally when the recursion bottoms out at `PathP` (which
  stays deferred) rather than a closed type.
- **The independent re-checker never reaches its Kan-`Glue` path at all**: it *declines* any judgement
  mentioning `Glue`/`GlueTerm`/`Unglue` at `from_kernel` (before normalization), so the trusted kernel
  solely owns the univalence Kan rule (both directions). Pinned by `recheck::recheck_declines_glue`.
- **A non-constant indexed `Data`/`Int`/`Eff` type line** is never built by the corpus: every such
  line is constant in its dimension and is caught by the `family_is_constant` fast path before
  dispatch. (The general heterogeneous transport over a *graded* type line — obligation 2 in §1.3 —
  is Track M7: the one reachable unsound shape, grade-heterogeneous `Pi` endpoints, is now rejected
  by `kan_line_grade_skeleton_eq` rather than merely left unattempted.)

This is the A1 disposition, generalized by Wave 7/E3 to both `ua` traversal directions: the
heterogeneous Kan lines univalence makes reachable (`transp` over the `ua` Glue line, forward and
reverse) are implemented and conformance-tested (formation by `ua_formation_is_conformant`,
computation by `ua_computes_is_conformant`, plus the kernel white-box tests above); every other cell
— including `Partial`/`System` in their entirety, and every `hcomp`-over-a-closed-type shape — is
documented as unreachable-from-the-corpus and fails safe rather than mis-reducing, each negative
boundary pinned by a `#[should_panic]` golden or a decline golden (`recheck_declines_glue`).

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
  out-of-fragment forms (cubical `Glue`/`ua`/partial, `foreign` postulates, universe-level
  variables) — it does not need a handler
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

**The graded-row discharge's static discipline is now independently mechanized (Wave 8 / M10).**
[`mechanization/BlightMeta/Effects.lean`](../mechanization/BlightMeta/Effects.lean) reconstructs
`check.rs`'s `Op`/`Handle` typing rules (a single fixed operation standing in for the general
`OpSig` shape, matching this fragment's existing "one instance for the whole shape" convention) and
proves, as genuine consequences of the `{0,1,ω}` order rather than restatements of the rule's own
premise, exactly what spec §4.4 claims for continuation multiplicity: `handle_abort_never_resumes`
(a `0`-graded handler clause provably never uses its continuation) and
`handle_linear_at_most_once` (a `1`-graded one's continuation usage is provably `0` or `1`, never
`ω`). This is *not* the open normalization/decidability proof above — it is the narrower, already-
enforced *typing* discipline, now backed by an independent proof rather than solely by the
`demand_k.leq(cont_grade)` check and its accept/reject tests. See
[docs/metatheory-mechanized.md](metatheory-mechanized.md) for the full scope and simplifications
(single operation, closed single-label row, no operational semantics for `Handle`/`Op`).

---

## 3. Backend semantics-preservation lemmas (Grand Arc B4)

The native backend (`crates/blight-codegen`) is **untrusted** (spec §7.1): the kernel and the
independent re-checker never see ANF, so a miscompiling optimization can only ever produce a wrong
*number*, never a false *proof*. The standing mechanical guarantee that the fast paths are
behavior-preserving is the **B1 differential corpus** (`crates/blight-repl/src/main.rs`,
`differential_*`): every example is built with each `BL_NO_*` fast path on and off, and the produced
binary's stdout must be bit-identical to the all-on build (the flags are listed in `DIFF_FLAGS`: M20
`BL_NO_NATPRIM`, M27 `BL_NO_UNBOX`, A1 `BL_NO_FLATTEN`, A2 `BL_NO_STRPACK`, A3 `BL_NO_SPINEFUSE`, A4
`BL_NO_INLINE`, A5 `BL_NO_AUTOREGION`, plus `BL_NO_LTO`). `BL_NO_UNBOX`/`BL_NO_FLATTEN` additionally
gate the A1′ post-monomorphization layout pass (`layout.rs`), so the matrix covers it for free.

B4 adds the **in-Blight companion**: the equational laws those rewrites embody, stated over the
prelude datatypes and proved by tactic scripts whose terms are re-checked through the kernel door
(LCF — a buggy tactic can only fail, never mint a false proof). These live in
`crates/blight-prelude/spore_codegen_meta.bl` and are exercised by
`spore.rs::codegen_meta_lemmas_proved`.

| pass | rewrite | certified law | proof |
|---|---|---|---|
| recognizer (`recognize.rs`, numeric.c) | inductive `plus`/`mult` ⇝ O(1) machine-word `bl_nat_add`/`bl_nat_mul` on a count | `plus a Zero ≡ a` (`rec-add-unit-r`); `mult a Zero ≡ Zero` (`rec-mul-zero-r`) | structural induction, `cong Succ` / `exact` on the IH |
| SRA / unbox (`unbox.rs`) | delete a built-and-projected product, feed fields directly | `pair-fst A B (mk-pair a b) ≡ a` (`sra-beta-fst`); `…snd… ≡ b` (`sra-beta-snd`) | `refl` (product β is definitional) |
| ANF (`anf.rs`) | name every subexpression with a `let` | `anf-let e k ≡ k e` (`anf-let-subst`); `anf-rebuild n ≡ n` (`anf-rebuild-id`) | `refl` (let = substitution) + structural induction |
| ANF (`anf.rs`), accumulator/CPS conversion | direct-style recursive evaluator ⇝ accumulator-threaded evaluator | `aeval-k e acc ≡ plus acc (aeval e)` (`aeval-k-correct`, Track M2b) | structural induction + `trans` (two IH rewrites composed with `plus`-associativity) |

**Why these laws, and why exactly these.** Each pass's correctness rests on a small set of equalities;
B4 proves the *non-definitional* ones and exhibits the definitional ones as `refl` certificates.

- *Recognizer.* Representing a `Nat` by a machine-word count and adding/multiplying counts is sound
  iff the inductive `plus`/`mult` obey the count-arithmetic laws. The *left* recurrences
  (`plus Zero b ≡ b`, `plus (Succ a) b ≡ Succ (plus a b)`, `mult Zero b ≡ Zero`) hold definitionally
  because both functions recurse on their first argument; the only genuine obligations are the laws on
  the *second* argument (right-unit / right-zero), which need induction and are proved.
- *SRA.* Deleting a product that is built and immediately projected is precisely product β
  (`fst (a,b) ≡ a`), a definitional equality — which is *why* the deletion is bit-identical. The proof
  is `refl`, exhibiting that equality through the kernel.
- *ANF.* Each ANF step is a let-introduction whose denotation, in the call-by-value model, is the
  substituted form (`let x = e in k x ≡ k e`); `anf-rebuild-id` additionally certifies, by induction,
  that wrapping each recursive sub-result of a constructor application in an ANF `let` leaves the value
  unchanged.
- *ANF, accumulator conversion (Track M2b, formerly the open follow-up below).* `anf.rs`'s real
  arithmetic-evaluator transform rewrites a direct-style recursive `aeval` into an accumulator/CPS
  form `aeval-k` that threads a running `Nat` instead of composing `plus` on the way back up. The
  `Add` case of `aeval-k-correct` (`Path Nat (aeval-k e acc) (plus acc (aeval e))`, `Expr`/`aeval`/
  `aeval-k` all in `spore_codegen_meta.bl`) needs to rewrite with *each* subterm's induction
  hypothesis and then re-associate the two rewrites' targets with `plus`-associativity — genuine
  multi-step `Path` transitivity, discharged by chaining the Track M2a `trans` combinator
  (`crates/blight-elab/src/tactic.rs`) twice, composed with the `codegen-plus-assoc` lemma. Pinned by
  `spore.rs::codegen_meta_lemmas_proved`.

**Scope.** The prelude's tactic vocabulary is `refl` + single-step congruence induction
(`induction`/`cong`/`exact`, the power of `plus_zero_tac.bl`) plus (Track M2a) a `Path` transitivity
tactic `trans` (built from `hcomp`/`comp`, `crates/blight-elab/src/tactic.rs`) and an `ascribe` tactic
that explicitly types a nested tactic's result term where the elaborator would otherwise need to
*infer* through it (a bare `PLam`, like a bare `Lam`, cannot be inferred without a target type — the
same reason an outer `trans`'s `PApp` of an inner `trans`'s bare result needs one). Landing `trans`
also exposed a genuine kernel-evaluator gap it is worth recording: `Term::Ann(t, ty)`'s runtime value
used to just be `eval(t)`, dropping `ty`; if `t` evaluated to something *stuck* (the common case for a
global lemma applied to an abstract hypothesis, e.g. `plus-assoc a b c` for a free `a`), the resulting
`Value::Neutral` had no memory of its own `PathP`/`Pi` type, so applying it at a boundary
(`p @ 0`/`p @ 1`) inside a `trans` chain stayed maximally stuck instead of reducing to the known
endpoint — the same information ordinary hypothesis *variables* already carry via `reflect`
(`Value::ReflectedPath`/`ReflectedFun`, `crates/blight-kernel/src/normalize.rs`). Reflecting the
ascribed type onto a stuck `Ann`ed value closes that gap uniformly (and is a no-op for values that
were never stuck), fixed alongside `trans`. With `trans` in hand, the fully general
*evaluator-preservation* theorem for ANF's accumulator conversion — previously named here as **out of
reach of the current tactic fragment** — is now proved (`aeval-k-correct`, table above); no ANF
obligation remains open. The laws above are the ones the passes *actually* rely on and are each
provable within the (now transitivity-closed) supported fragment, so the B4 obligation — a
machine-checked, kernel-re-checked certificate of semantics preservation for the recognizer, SRA, and
ANF rewrites, including ANF's accumulator conversion — is fully met.

---

## 4. External mechanization (Track M4, the "going for gold" milestone)

§1.2's substitution/preservation sketch and §2's normalization arguments are, throughout this
document, evidence from *measured kernel behavior* — a real but informal standard. Track M4 adds an
independent, machine-checked witness on top: a from-scratch Lean 4 development
([`mechanization/`](../mechanization)) of the QTT resource semiring and a graded simply-typed core,
proving weakening and — the harder of the two classical preservation lemmas — **substitution**, with
zero `sorry`. It now reaches well beyond that STLC core: the **constant-family cubical Kan fragment**
(`transp`/`hcomp`, M5), a **strong-normalization + canonicity** proof for the `Bool`/`Π` +
constant-family-Kan fragment (a Tait reducibility argument, M8), a **bona-fide dependent-`Π`** core
(M9), and the **graded effect-row discharge** for `perform`/`handle` (M10). What it does *not* attempt
is SN/canonicity for the *full fused theory*: the fully heterogeneous cubical corner
(`PathP`/`Glue`/dimension-varying type lines) and dependent `Σ` remain outside the mechanized
fragment. See [docs/metatheory-mechanized.md](metatheory-mechanized.md) for the exact scope, the
per-lemma correspondence to the kernel tests above, and what remains open.

## Cross-references

- Spec §10.3 / §10.4 ([docs/blight-spec.md](blight-spec.md)) — the original risk prose and fallbacks.
- [docs/roadmap.md](roadmap.md) — milestone status.
- Evidence tests: `crates/blight-kernel/src/check.rs` (`transp_*`, `hcomp_*`,
  `interval_var_carries_no_grade_in_usage_vector`).
- Runtime effects: `crates/blight-codegen/runtime/effects.c` (full CPS deep handlers, multi-shot).
- External mechanization: [docs/metatheory-mechanized.md](metatheory-mechanized.md),
  [`mechanization/`](../mechanization).
