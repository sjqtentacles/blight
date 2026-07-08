# Soundness follow-up — 2026-07-07

The F1 full-parity work — making the independent re-checker *model* the cubical `Glue`/univalence
layer instead of declining it — surfaced three Kan-layer defects in the trusted checkers: **two
soundness breaks** (a value could be laundered into the wrong type) and **one crash** (a `quote`
underflow, DoS-only). All three are reproduced end-to-end against the real code, not merely
code-read, and each is pinned by a red-first regression. This note also **retires the R-P5
unreachability caveat** from [soundness-audit-2026-07-03.md](soundness-audit-2026-07-03.md): its
argument rested on the re-checker *declining* `Glue`, which F1 no longer does.

Governance: same TCB gate protocol as the 07-03 audit — full suite, byte-identical verdict golden,
mutants over new logic, red-first pinning test. The trusted kernel was edited (S1/S2/X1 all touch
`blight-kernel`); each change is mirrored in the independent re-checker for parity.

## Context — F1: the re-checker now models `Glue`/`ua`

`from_kernel` translates the `Glue` layer (grammar + typing + Kan reductions) rather than declining
it. The re-checker re-derives `Glue`/`GlueTerm`/`Unglue` typing with its own `equiv_type` (the CCHM
contractible-fibres `Equiv`, equivalence slot checked at grade `0`), the boundary reductions, and the
`transp`-over-`ua` computation in both directions (`transp_glue`: forward `fst e`, inverse `invEq e`).
`std/path.bl`'s `ua` now re-checks `Ok` in *both* checkers (was `Declined` in the differential
golden). Pinned by `recheck::recheck_models_ua_glue_line` (Ok) and
`recheck::recheck_rejects_bogus_glue_equiv` (the grade-0 equiv-slot negative). This is what makes the
two soundness gates below *reachable* by the re-checker at all — previously the decline hid them.

## S1 — `family_is_constant` decided constancy from endpoints only (soundness)

`family_is_constant` (kernel `crates/blight-kernel/src/kan.rs`, mirrored in
`crates/blight-recheck/src/kan.rs`) classified a Kan line as *constant* — and so reduced its `transp`
to the **identity** — by comparing only the line's two `i=0`/`i=1` **endpoints**. The `A ≡ B`
univalence line has equal endpoints by construction but a genuinely varying interior, so a
non-trivial `transp (ua e)` was wrongly short-circuited to the identity, laundering `e`'s forward map
away.

*Fixed:* both checkers now probe the line's **interior** under two fresh dimensions
(`apply_dim` at `Dim(dl)` and `Dim(dl+1)`, `conv` at `dl+2`) rather than at the endpoints. A closed
family still classifies identically to before (`lvl = dl = 0`). Trusted-kernel change, reviewed.

## S2 — a `φ=⊤` / `is_total(cofib)` cofibration bypassed the interior probe (soundness)

Even with S1 in place, the `transp` reducer and the `Transp` typing rule short-circuited to the
identity whenever the cofibration was *totally true* (`is_total(cofib)` / a De-Morgan `⊤`), **without
consulting `family_is_constant`**. A totally-true face therefore laundered a *non-constant* transport
straight back to the identity — re-opening S1 through a different door. Four gates were affected: the
`transp` reducer and the `Transp` rule, in *each* checker.

*Fixed:* the `is_total(cofib)` disjunct is dropped from both `transp` reducers (the cofibration
argument is now `_cofib` — `transp`'s result does not depend on it), and both `Transp` typing rules
gate the identity reduction on `family_is_constant` (the interior probe) instead of on the face.
Pinned by `crates/blight-repl/tests/ua_transp_soundness.rs::transp_ua_does_not_launder_to_identity`
(the `cbot`, `ctop`, and De-Morgan-`⊤` false lemmas are all `Rejected`) and
`crates/blight-recheck/src/kan.rs::transp_glue_total_cofib_does_not_launder_to_identity`.

## X1 — `comp`/`transp` over an *open* family: `quote` underflow + mis-typed adequacy (crash)

Two coupled defects on the open-family path (not a soundness hole — the checker *crashes*, it does not
accept a falsehood):

1. **`quote` underflow.** `family_is_constant` hardcoded ambient term-level `0`, so `quote`/`quote_neutral`
   underflowed (`lvl - k - 1` wrapping) on a family that captured free variables — e.g. the `cconcat`
   path-composition `comp` over an open path. *Fixed:* `family_is_constant` derives `lvl =
   family.env.len()` and `dl = family.env.dim_len()` from the family's captured environment (kernel
   `kan.rs:54-55`, recheck `kan.rs:49-50`), so open lines reached during corpus reductions no longer
   underflow. (`line_closure`/`transp_pi` and the `hcomp`/`comp` component reducers still run at a
   fixed base level — the fully-open *polymorphic* case remains deliberately deferred, see
   [metatheory.md](metatheory.md) §1.4.)
2. **Mis-typed `comp` adequacy.** `comp`'s Kan-adequacy obligation compared the tube against
   `transp(A, ⊥, base)` — a *cross-type* comparison (the values live in different fibres) that also
   fed the level-0 `quote` above. *Fixed:* the obligation is now the correct CCHM condition
   `tube@i0 ≡ base` evaluated *in `A(i0)`* (`check.rs`, `check_kan_adequacy`).

Pinned by `crates/blight-repl/tests/kan_open_family.rs` (`comp_path_composition_over_open_family` — a
real `cconcat` type-checks; `false_comp_still_rejected_by_adequacy` — a bogus `comp` is still
`Rejected`) and `recheck::recheck_handles_comp_over_open_family`.

## Retired: R-P5's "unreachable-by-construction" caveat

[soundness-audit-2026-07-03.md](soundness-audit-2026-07-03.md) R-P5 (`transp_sigma` second-component
line) argued its divergent branch was **unreachable-by-construction** because "a genuinely-varying
first-component *type* line requires a `ua`/`Glue`, which the re-checker **declines**." F1 removes
that premise: the re-checker now *models* `Glue` and implements `transp_glue`, so it **does** receive
`ua`/`Glue` lines. The R-P5 fix (conditionalizing the second-component line on
`family_is_constant(fst_line)`) is therefore no longer *defensive parity* but **load-bearing**, and it
is now correct precisely because S1 made `family_is_constant` an interior probe. The branch is
**reachable-but-correctly-handled**, not unreachable — the constant case still reduces (pinned by the
existing constant-Σ contract test), and the varying case is carried by `transp_glue`.
