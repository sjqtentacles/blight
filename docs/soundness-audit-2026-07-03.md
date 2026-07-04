# Soundness audit — 2026-07-03

A multi-lens bughunt (six finder lenses, 2-of-3 adversarial verification) over the whole
workspace. **7 of the 12 confirmed findings are soundness breaks in the TCB** (kernel + the
independent re-checker) — each reproduced end-to-end against the real code, not merely
code-read. They are tracked here in priority order. Known-tracked issues (flat_esc /
spore_codegen_meta false-`Rejected`, anf load-flake, bench nesting limit) are excluded.

Governance: each fix follows the S3/N6 TCB gate protocol — full suite, byte-identical verdict
golden, llvm bit-identity where relevant, mutants over new logic, plus a red-first pinning test.

**Status (2026-07-03): all 7 kernel-side soundness bugs FIXED (K1–K7). The 5 re-checker parity
bugs (R-P1…R-P5) remain — each false-`Ok` is fatal, so they are the next priority.**

## Kernel soundness (trusted — highest priority) — ✅ COMPLETE

- [x] **K1 — infer-mode `Con` on an indexed family discards recursive-argument indices**
  (`check.rs:620,625`). `rec_ty` was built with empty indices and `Arg::Rec(_)` dropped the
  index terms, so a `Fin (succ (succ zero))` could be laundered as `Fin (succ zero)`. Also
  **K2 — infer-mode `Con` evaluated dependent `NonRec` arg types in the un-threaded base env**
  (`check.rs:627`), panicking `eval: unbound de Bruijn` on a legitimate non-indexed dependent
  constructor (`mkbox : (A:Univ0)->(x:A)->BoxT`). Both fixed together by threading `arg_env`
  exactly as the proven checking-mode path (`check.rs:2040-2081`) does. *Fixed 2026-07-03.*

- [x] **K3 — `Glue` formation never checks `equiv` is an equivalence** (`check.rs:843`). The
  rule only inferred `equiv`'s type; `transp_glue` blindly projects `vfst`/`vsnd`, so a mis-typed
  slot laundered a value into the wrong type or panicked `snd: not a pair`. *Fixed 2026-07-03
  (55525ab):* new `equiv_type(a,b)` constructs the fully-unfolded CCHM `Equiv ty base` (matching
  `std/equiv.bl`), and the rule checks `equiv` against it in the 0-fragment. Also front-runs the
  grade-laundering guard (1.3.2 — the forward map can't be typed `Πω→Π1`), which stays as
  defense-in-depth. Validated by `equiv_type_accepts_the_identity_equivalence` (a real `id-equiv`
  checks) + red pin + rewired grade tests; kernel 178/178; workspace 873/873 incl. all
  `ua`/unglue/univalence; verdict golden byte-identical (ua forms Glue over free-var endpoints);
  mutants 0-missed. **The hardest fix in the audit.**

- [x] **K4 — strict-positivity check misses `EffTy`/`Delay`/`PathP`/… wrappers + unwired**
  (`signature.rs:254`). `mentions_data` recursed only through `Data/Pi/Sigma/App/Lam/Fst/Snd/Ann`
  and the elaborator's `declare_data` never called `check_positivity`. *Fixed 2026-07-03 (fad7b4d):*
  `mentions_data` rewritten as an exhaustive match (no wildcard — future `Term` variants must be
  handled) recursing every subterm-bearing former; `check_positivity` wired into `declare_data`
  (mirrors `declare_effect`, rolls back via `Program`'s per-form snapshot). Gates: red pin +
  comprehensive per-former traversal pin (19/19 mutants) + no-over-rejection guard; workspace
  869/869; verdict golden byte-identical. *Note:* surface syntax can't currently express a
  non-positive occurrence (data name not in scope during its own fields — same limitation blocks
  legitimate nested types), so this hardens the kernel gate and future-proofs the path.

- [x] **K5 — `transp` over a non-constant Π line accepted, then panics** (`check.rs:743`,
  `kan.rs:289`). The grade-skeleton gate accepted a heterogeneous Π line; `transp_pi` then
  underflowed `quote_value_at(1,0,…)` on an escaping ambient neutral. *Fixed 2026-07-03
  (2695749):* the Transp rule now evaluates the *open* line (family at a fresh dim — what
  `kan::transp` dispatches on) and rejects a `Pi`-headed non-constant line. `ua`/Glue lines have
  Π endpoints but a Glue-headed open line, so they still transport via `transp_glue`. Red pin;
  kernel 183/183 incl. all ua/kan-conformance; workspace 876/876; verdict golden byte-identical;
  1 accepted-sound mutant survivor (grade-skeleton check, now defense-in-depth per K3, mechanized
  in GradeSkeleton.lean — documented inline).

- [x] **K6 — infer-mode `Handle` return-clause type escaping `x` underflows** (`check.rs:419`).
  `c_ty` quoted at `ctx.len()` (one level too shallow); a return type mentioning the bound `x`
  panicked with subtraction overflow. *Fixed 2026-07-03 (88774ac):* quote at the extended depth
  (never underflows), reject with a clean `EffectError` if `uses_binder(_, 0)`, then the shallow
  quote runs only when `x` is provably unused. `uses_binder` exposed `pub(crate)`. Red pin +
  workspace 871/871 + verdict golden byte-identical + mutants.

- [x] **K7 — `check_kan_adequacy` shift overflow at ≥32 dimensions** (`check.rs:1012`).
  `1u32 << dims.len()` overflowed/masked at 32+ dims, under-checking the adequacy guard. *Fixed
  2026-07-03 (e835b8a):* reject a cofibration mentioning more than `MAX_KAN_ADEQUACY_DIMS` (16)
  distinct dimensions before the shift — sound (never under-checks), far beyond any real
  cofibration. Red pin (33-dim overflow → reject) + boundary pin (exactly 16 accepted); workspace
  875/875; verdict golden byte-identical; mutants 0-missed.

## Re-checker parity (trusted second opinion — false-`Ok` is fatal)

- [ ] **R-P1 — `quote_interval` `saturating_sub` aliases distinct dimension levels**
  (`recheck/normalize.rs:642`). Non-injective quoting collapses distinct stuck path
  applications to `Dim(0)`, so `conv` equates different neutrals (`p @ j` ≡ `p @ k`) — a
  false definitional equality in the accepts-more direction. Kernel twin uses injective
  `dlvl - k - 1`. Fix: match the kernel's injective computation.

- [ ] **R-P2 — `RTerm::Data` inference skips all param/index arity + type checking**
  (`recheck/typecheck.rs:303`). Returns `Univ(decl.level)` ignoring params/indices; the kernel
  twin rejects wrong arity and checks each against its declared type. Lets recheck return `Ok`
  on a malformed-`Data` term the kernel rejects (false-`Ok`). Fix: port the kernel's arity +
  type checks.

- [x] **R-P3 — `eval` of `Ann` drops the annotation without reflecting stuck neutrals**
  (`recheck/normalize.rs:151`). *Fixed 2026-07-03:* the `Ann` arm now reflects a neutral result
  against its type (mirrors `kernel/normalize.rs:281`), so path `@0`/`@1` boundaries and function/
  pair η fire on ascribed neutrals. Red pins (`ann_reflects_path_neutral_*`). **Closed ONE of the
  two pinned false-`Rejected` verdicts: `spore_codegen_meta.bl aeval-k-correct Rejected → Ok`**
  (the "trans-chain rhs boundary" case). Verdict golden re-blessed — exactly that one line changed
  (diff-reviewed: no `Ok→Rejected` regression). Differential + proptest harnesses still green
  (kernel-accept ⇒ recheck agrees/declines).
  **NOTE — flat_esc.bl::main did NOT flip** (still `Rejected`): its "nested Pair-match inference"
  failure has a *different* root cause than Ann-reflection. Needs separate investigation (likely an
  inference/`from_kernel`/match-compilation issue, not eval reflection). Tracked as a follow-up
  below.

- [ ] **R-P4 — `transp_pi` codomain line uses constant `x1` instead of the transport fill**
  (`recheck/kan.rs:105`); **R-P5 — `transp_sigma` uses source `a0` instead of the fill**
  (`recheck/kan.rs:136`). Both use the collapsed constant-line rule where the kernel instantiates
  at the backward transport-fill, diverging for genuinely-varying dependent lines. Fix: port the
  kernel's `transp_fill_line`. *Medium confidence.*

## Non-TCB (untrusted tooling / cleanup)

The remaining confirmed findings and the full cleanup inventory (dead `pub fn`s, committed
`.profraw`/`.vsix` artifacts, doc-drift in `implementation.md`/`roadmap.md`/`metatheory.md`/
`README.md` overstating the re-checker's coverage) are lower priority and fed into the R4 docs
truth pass. Doc-drift highlights: three docs claim the re-checker "does not track effect rows or
continuation grades" — the code (recheck B2) does track and enforce both; README claims the Lean
mechanization is "non-cubical / no SN-canonicity" — it now mechanizes the constant-family Kan
fragment plus SN + canonicity.
