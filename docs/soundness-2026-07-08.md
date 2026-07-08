# Soundness follow-up — 2026-07-08

The adversarial review of PR #2 (the F1 branch, [soundness-2026-07-07.md](soundness-2026-07-07.md))
surfaced a **fourth** Kan-layer defect — a latent unsoundness in `transp_glue` — which this note
records and fixes. It was reproduced end-to-end against the real reducer (a white-box RED test), not
merely code-read, and is pinned by a regression.

Governance: same TCB gate protocol as the 07-03/07-07 work — red-first pinning test, kernel↔recheck
parity, byte-identical verdict golden, clippy/fmt clean. The trusted kernel is edited (a `conv` arm +
a `transp_glue` guard); both changes are mirrored/paralleled in the independent re-checker.

## The defect — `transp_glue` laundered an ambient-face Glue line

`transp_glue` matched the Glue line's face with a **wildcard dimension**
(`Cofib::Eq0(Interval::Dim(_))`, and the `Eq1`/negated variants). A `Glue` line whose face sits on an
**ambient** dimension `j` rather than the bound transport dimension `i` — e.g.
`transp (i. Glue B (j=0) A e) ⊥ base` — is **constant in `i`**, so its transport must be the
**identity**. But the wildcard accepted the ambient face `Eq0(Dim(j))` as if it were the univalence
`i=0` direction and applied the forward map `e.fun`, laundering `base` to `e.fun base`.

**Reproduced** (`crates/blight-kernel/src/kan.rs::transp_glue_ambient_face_is_identity`): the line
`i. Glue Bool (j=0) Nat e` with `e.fun = λ_. true`, transported over a constant `i`, returned
`true` (= `e.fun zero`) instead of the identity `zero`.

**Reachability:** latent. The wrong result is `e.fun base` where `base` is a `Glue`-typed value at a
*neutral* ambient dimension `j`; at either endpoint of `j` the Glue collapses to a plain type and the
mis-fire disappears, so distilling a **closed** false proposition needs distinct connected closed
points — i.e. F3's HITs. There is also a kernel/recheck divergence that would expose it to the
differential harness the moment it became reachable: the re-checker's `conv.rs` already had a `Glue`
arm (so recheck judged the line constant and returned the identity), while the kernel's `conv_at` did
not. Fixed before F3 rather than left to become live.

## The fix (two parts, both checkers)

1. **Kernel `conv_at` gains a `Glue` arm** (`crates/blight-kernel/src/normalize.rs`) — structural:
   folded cofib compared syntactically, the three type components up to conversion. This is exact
   parity with the re-checker's existing `conv.rs` `Glue` arm, and it is what lets
   `kan::family_is_constant` correctly classify a *constant* `Glue` line: the two interior probes fold
   to the **same** cofib for an ambient face (`Eq0(Dim(j))` at both), so the line is seen as constant
   and `transp` returns the identity **before** reaching `transp_glue`. A genuine `ua` line differs at
   the probes (its face moves with the transport dim → `Eq0(Dim(dl))` vs `Eq0(Dim(dl+1))`) and stays
   non-constant, dispatching to `transp_glue` as before.

2. **`transp_glue`'s face match is tightened to the transport dimension** (`Dim(0)` in the open-line
   view) in **both** checkers (`crates/blight-kernel/src/kan.rs`, `crates/blight-recheck/src/kan.rs`).
   With part 1 in place a constant ambient-face line never reaches `transp_glue`; if a *non-constant*
   line with an off-transport face still does (a genuinely heterogeneous Glue line — out of the
   implemented fragment), it now hits the fail-safe `unimplemented!` panic rather than mis-applying
   the equivalence. Defense-in-depth.

## Verification

- `kan::transp_glue_ambient_face_is_identity` (RED→GREEN) pins part 1; the existing
  `transp_glue_non_ua_face_fails_safe` / `transp_glue_non_constant_base_fails_safe` and the three
  `transp_ua_glue_line_*` forward/reverse tests confirm part 2 did not disturb genuine `ua` transport.
- Kernel 197 + recheck 106 unit/integration green; examples 68 + stdlib 39 green (the real `ua`
  corpus — `examples/ua_compute.bl`, `std/path.bl` — is unaffected).
- **Differential verdict golden byte-identical** — the kernel `conv` `Glue` arm is corpus-neutral (no
  corpus judgement compares two proper `Glue` values), so it is a pure completeness/soundness
  hardening with no verdict change. clippy + rustfmt clean.
