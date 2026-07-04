# Changelog

All notable changes to this project are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). This project is pre-1.0; the version in
`Cargo.toml` is `0.1.0` and the milestones below track the bootstrap roadmap (spec §9).

## [Unreleased]

## [0.1.0] — 2026-07-04

The first tagged release: the v0.1 roadmap arcs (E, S, N, R) landed on top of the M0–M6 kernel,
plus a full soundness-hardening pass over the trusted checkers.

### Added

- **v0.1 roadmap arc E, milestone E8 (editor support):** the LSP server now formats documents
  (via the shared `format_source`, honoring the None/empty/single-edit contract) and offers
  completion — the module's definitions index plus a curated keyword set, and the embedded `std/`
  module paths inside a `(load "…"` prefix, detected lexically. The VS Code extension advertises
  both capabilities (bumped 0.2.0 → 0.3.0). Zero kernel changes.
- **v0.1 roadmap arc R, milestone R2 (browser playground):** a static page where the whole trust
  story runs client-side — paste Blight source, get the kernel's verdict, `main`'s type, and the
  independent re-checker's verified/declined/rejected tally, with caret diagnostics on errors.
  `crates/blight-playground` exports the checker over a thin C ABI (no wasm-bindgen/bundler/npm);
  the page's killable Web Worker instantiates the raw cdylib, so divergent input cannot wedge the
  tab. Node smoke test + page assembly + asset link-check are required CI; Pages deployment is a
  deliberate workflow_dispatch.
- **v0.1 roadmap arc R, milestone R1 (wasm-clean checker):** the whole checking stack —
  blight-kernel, blight-recheck, and blight-elab with `--no-default-features` — now compiles for
  `wasm32-unknown-unknown`, with a required CI row pinning it. The registry's HTTP transport
  (git deps + publish) sits behind a default-on `net` cargo feature; HTTP locations in a no-net
  build error with a clear message. Found and fixed en route: the metavariable base
  `1 << 40` was a compile-time overflow on 32-bit targets — now `1 << (usize::BITS - 1)`,
  width-portable. This is the doorstep for the R2 browser playground.
- **v0.1 roadmap arc E, milestone E9 (first-session bundle):** the four first-ten-minutes fixes.
  `(do step … last)` sequencing sugar with `(<- x e)` binders (right-nested `let` desugaring,
  refl- and oracle-pinned); the REPL evaluates bare expressions and prints re-sugared values
  (`(plus 2 3)` ⇒ `5`, metered so divergence reports instead of hanging); typed holes — `?name`
  reports the expected type (including applied-argument positions of typed globals) and the
  local context, with single-char `?x` char literals boundary-pinned; and a stdlib decimals
  sweep (21 Peano chains across five modules) that left the verdict golden byte-identical —
  E1's identical-terms guarantee confirmed at stdlib scale. Zero kernel changes.
- **v0.1 roadmap arc E, milestone E7 (diagnostics quality):** the four headline error shapes now
  render for humans — unbound names one edit from a known name get a "did you mean" (Levenshtein
  over locals/constructors/datatypes/globals, LSP span narrowing preserved); a lambda binding
  more parameters than its declared `Pi` names both counts with the type re-sugared; constructor
  mismatches print backticked surface names instead of `DataName("…")` Debug wrappers (the one
  kernel change is message-string-only, as the milestone authorizes); a non-structural `deftotal`
  suggests the E6 `(measure …)` clause alongside `define-rec`. Goldens in
  `crates/blight-elab/tests/diagnostics.rs`, documented in docs/testing.md.
- **v0.1 roadmap arc E, milestone E4 (records):** `(defrecord Point ((x Nat) (y Nat)))` generates
  the whole record kit — nominal type, `mk-Point` constructor, projection `deftotal`s, and the
  `(Point-with p (y 5))` functional-update rewrite (any expression position, dedicated
  unknown-field diagnostics, atomic hygiene-checked declaration). Records lower to a
  single-constructor `defdata` — a design re-verified against the codebase before implementation
  (dependent-index refinement, nominal typing, codegen unboxing, and free match/E3-coverage/E5
  integration all require the inductive encoding; the originally-specified Sigma encoding would
  have failed the milestone's own dependent-position test). std/test.bl's `TestCase`/`TestSuite`
  adopted; `examples/records_demo.bl` added and oracle-pinned. Zero kernel changes.

### Fixed

- **Soundness-hardening pass (trusted checkers):** a multi-lens bughunt with adversarial
  verification found and fixed **7 soundness holes in the kernel** and **5 parity gaps in the
  independent re-checker**, each reproduced end-to-end, then closed red-first with the full gate
  protocol (workspace suite, byte-identical verdict golden, cargo-mutants). Kernel: infer-mode
  constructor index/env threading (`Fin 2` could be laundered as `Fin 1`), `Glue` formation now
  checks its `equiv` is a genuine CCHM equivalence, strict-positivity wired into `defdata`, `transp`
  over a non-constant Π line rejected instead of panicking, `Handle`/`Kan`-adequacy overflow guards.
  Re-checker: injective interval quoting, `Data` arity/type checks, `Ann`-neutral reflection (which
  also un-pinned a long-standing false-`Rejected` verdict), and `transp` fill parity. See
  [docs/soundness-audit-2026-07-03.md](docs/soundness-audit-2026-07-03.md) for the per-bug detail.
- **Roadmap arc N, milestone N5 (the eliminator cliff):** both evaluators — the trusted kernel's
  and the independent re-checker's, each via its own implementation — now skip computing an
  induction hypothesis when the receiving match method provably discards its IH binder (a
  shifted occurs-check mirroring each engine's own `shift`; dead binders get a stuck sentinel;
  `BL_NO_DEAD_IH=1` restores eager behavior for A/B). This removes the ~2^codepoint blow-up that
  made every string-comparing judgement effectively non-terminating at check/re-check time:
  `nat-eq k k` IH counts drop from ×2-per-codepoint to +1-per-codepoint (pinned by deterministic
  counter-slope tests in `crates/blight-repl/tests/nbe_scaling.rs`); the four formerly
  un-re-checkable examples now re-check in 0.1–31 s (json_scratch was >68 min); the verdict
  golden's skip-list is empty. Two long-deferred certifications went live: `reader-demo-refl`
  (spore_reader.bl — the kernel computes the self-hosted *reader* end-to-end inside conversion
  and certifies its output by refl; 5.96 s in a debug build, previously killed at 15+ release
  CPU-minutes) and `bridge_printer_output_checks_for_demo_id` (the S2 bridge's whole proposer
  pipeline — belaborate, verdict, printers, string concatenation — computed inside the kernel
  and refl-pinned to its exact output line).

### Changed

- **v0.1 roadmap arc N, milestone N6 (Value-tree sharing):** the kernel and re-checker value
  layers now share sub-values via `Rc` instead of deep-cloning them, cutting the re-evaluation
  churn that dominated the heavier judgements (the `json`/`regex` re-checks drop from ~17 s → ~9 s
  and ~25 s → ~5 s; the whole verdict corpus ~49 s → ~20 s). Landed under a pre-registered
  protocol: verdict golden byte-identical, the `BL_NO_*` fast-path binaries bit-identical,
  criterion within ±5 %, cargo-mutants over the new sharing helpers all-killed. The scale-pair
  ratio kill-criterion fired (15.3× vs the <12× target) and the keep/kill call was escalated to
  and made by the user, not assumed.
- **v0.1 roadmap arc S, milestone S3 (kernel `Term` representation: `Box` → `Rc`):** the kernel
  term grammar's 42 recursive fields now hold `Rc<Term>`, so cloning a term (notably `eval`'s
  closure construction) is a shallow per-node refcount bump instead of a deep subtree copy.
  Landed under the pre-registered protocol: representation-only diff (one audited helper,
  `blight_kernel::unshare`; zero move-sites in the kernel itself), full suite green, per-global
  kernel+re-checker verdicts over the whole corpus byte-identical to a golden captured before the
  change (`crates/blight-repl/tests/verdict_diff.rs`, the new harness), compiled binaries
  bit-identical across the `BL_NO_*` fast-path matrix, criterion within ±5%, cargo-mutants over
  the new logic. Honest outcome: the predicted payoff did **not** materialize — the deferred
  refl-at-scale go-bar (`reader-demo-refl`) is still infeasible post-Rc. The follow-up
  adversarial review identified the true mechanism, shared by kernel and re-checker at measured
  parity: `do_elim` eagerly computes *discarded* induction hypotheses, making a single character
  comparison cost ~2^codepoint eliminator steps (roadmap arc N has the code-cited analysis and
  fix plan; the harness's skip-list units are its pinned reproducers). The red-phase harness
  also surfaced two pre-existing false `Rejected` verdicts in the re-checker (nested
  `Pair`-match inference; trans-chain path boundary), filed as their own fixes.

### Added

- **v0.1 roadmap arc E, milestone E6 (measure-based totality / auto-fuel):** a `deftotal` with a
  `(measure e)`/`(default e)` clause auto-synthesizes the fuel plumbing that quicksort/mergesort/gcd
  used to hand-write — the elaborator (`crates/blight-elab/src/measure.rs`) emits a helper that
  recurses structurally on a `Nat` fuel (seeded at `(Succ e)`) plus a seeding wrapper, so the kernel
  still certifies a plain `Elim`. The honest contract: totality is certified unconditionally, but
  measure *adequacy* is not — a wrong measure yields "total but returns the default", never
  unsoundness. Composes with E5 (`defn` with a measure clause). quicksort/mergesort/gcd rewritten
  (four-plus helper functions each collapse to one measured definition, output unchanged,
  DIFF_CORPUS bit-identical). Zero kernel changes.
- **v0.1 roadmap arc E, milestone E5 (equation-style definitions):** `(defn name T [(patterns)
  body] …)` writes a recursive function as pattern equations instead of a `lam` + `match`. Desugars
  (sexpr→sexpr, `crates/blight-elab/src/defn.rs`) to a `define-rec` with a single-scrutinee `match`
  on the one pattern-matched argument column (which may be any argument, not just the first);
  exhaustiveness, nested patterns, and recursion recognition all come from the existing match path.
  Also fixes a latent E3 false positive that `defn` surfaced: the duplicate-arm check now only flags
  a *saturating* repeat (all-variable subpatterns), so nested refinements like `(just (nothing))`
  and `(just (just x))` pass. `list_sort.bl` rewritten in equation style; new `examples/equations.bl`.
  Zero kernel changes.
- **v0.1 roadmap arc S, milestone S2 (proposer/disposer bridge):** the trusted kernel now
  independently re-checks *terms* the Blight-written elaborator produces, not just booleans. New
  `crates/blight-prelude/spore_print.bl` renders the elaborator's verdict for a toy-STLC term as
  ordinary Blight surface text (`ACCEPT (the ⟦a⟧ ⟦s⟧)` embedding the object arrow as a real `Pi`, or
  `REJECT`); `examples/selfhost_bridge.bl` prints one line per corpus entry, and a Rust test rebuilds
  the payloads through the unmodified reader→elaborator→kernel and demands `Checked` — a forged
  ill-typed payload is rejected (the disposer has teeth). The printers are plain non-dependent
  recursions, re-verified `Ok` by the independent re-checker. Zero kernel changes.
- **v0.1 roadmap arc S, milestone S1 (end-to-end self-host demo):** `examples/selfhost_check.bl` —
  the first program that runs Blight's own `.bl`-written front end (reader → transcoder →
  proof-carrying elaborator → ANF compiler) over source it reads back from disk. `main : (! (Console
  FileIO Bytes) Unit)` writes a toy-STLC source, reads it via FileIO, checks it with `bcheck-string`,
  and prints the verdict — `OK size=6` for the well-typed `(lam (x Base) x)`, `REJECT` for the
  ill-typed `(lam (x Base) (x x))`. Adds `spore_reader.bl` to the embedded prelude bundle so
  `blight build` can load it. Zero kernel changes.
- **v0.1 roadmap arc E, milestone E3 (match coverage diagnostics):** a coverage pre-pass over a
  `match`'s first-column patterns now reports a clear up-front diagnostic — every missing
  constructor listed at once (`non-exhaustive match on Ordering: missing case eq`), plus duplicate
  and unreachable-after-catch-all arm errors — where the old behavior surfaced a generic
  "no clause for constructor X" one at a time, deep in column compilation. Nested coverage falls
  out of running the pass at every match level. Elaborator-only, zero kernel changes.
- **v0.1 roadmap arc E, milestone E2 (stdlib implicitization):** inferable leading type/index
  arguments of `vec-length`, `pair-fst`/`pair-snd`, `from-maybe`, `length`, `append`, and `filter`
  are now `{…}`-implicit and solved by first-order unification — `(vec-length sample)`, not
  `(vec-length Nat three sample)`. Unsolved/mismatched-implicit errors name the offending binder
  and re-sugar both candidate types; the diagnostic span narrows to the named identifier. The
  elaborator's first-order unifier gained effect-row stripping (`(! E T)` unifies against `T`, the
  elaborator mirror of the kernel's subsumption), and the recursive-self-call check now takes
  priority over the implicit-app path (correct under idempotent module re-load). Implicit binders
  keep their original `ω` grade — implicit-ness is independent of erasure. Zero kernel changes.
- **v0.1 roadmap arc E, milestone E1 (numeric literals):** a bare decimal atom (`3`) in term
  position is now `Nat` sugar for `(Succ (Succ (Succ Zero)))` — elaborator-only (`Surface::NatLit`),
  no reader or kernel changes. The pretty-printer re-sugars canonical `Nat` numerals back to
  decimal in REPL/diagnostic output. See [docs/roadmap-v0.1.md](docs/roadmap-v0.1.md).
- Top-level `README.md`, dual `LICENSE-MIT` / `LICENSE-APACHE`, `CONTRIBUTING.md`, this changelog,
  and a curated [`examples/`](examples/) tree (including the first checked-in `spore.toml` package).
- GitHub CI workflow and issue/PR templates.
- Source spans + caret diagnostics: a span-aware reader, `Diagnostic` renderer, and a kernel
  `TypeError`/`ElabError` `Display`, wired into the REPL and `blight build`.
- A `Term` pretty-printer that re-sugars core to surface s-expressions, used for REPL `Checked`
  output and in diagnostics.
- Heterogeneous cubical Kan operations in the kernel (`transp` over non-constant Π/Σ/PathP, `hcomp`
  over varying faces), each gated by a conformance golden; the re-checker now models the Kan table
  in its value layer (Checked, not Declined).
- Lifted the ≤1-parameter / ≤1-index cap on inductive families in both the kernel and the
  re-checker, with multi-param + multi-index agreement tests.
- Signature-derived per-constructor tag scheme in the backend (replacing the name-byte placeholder).
- WebAssembly link step: `--target=wasm32` links a runnable `.wasm` (exporting `bl_main`) against a
  minimal freestanding wasm ABI when a wasm-capable `clang` + `wasm-ld` are available, else emits the
  object only.
- Standard-library containers `std/maybe`, `std/either` (two-parameter), `std/string`, and the
  length-indexed `std/vec`, each load-tested in isolation and (for the multi-param/indexed ones)
  re-checked by the independent checker; a new `examples/containers.bl`.
- REPL commands `:help`, `:type`/`:t`, `:load`/`:l`, `:quit`/`:q`.
- A `docs/tutorial.md` walking from `Nat` to a tactic proof.

## Milestones

### M6 — Self-hosting model + ecosystem

- Standard library reorganized into a composable `std/` tree (`nat`, `bool`, `order`, `list`,
  `tree`, `prelude`), with the historical flat files kept as compatibility shims.
- `spores` package manager: a `spore.toml` manifest parser and an idempotent, cycle-checked
  `(import "pkg/mod")` form.
- WebAssembly object backend: `blight build --target=wasm32` (object-only).
- Re-checker (`blight-recheck`) generalized to single-parameter / single-index inductive
  eliminators, with an M0-M5 agreement corpus asserting zero rejections.
- `spore.bl` self-model grown with substitution (`bsubst`), well-scopedness (`bwellscoped`), and a
  third metatheorem (`bctx-len-append`); the kernel's index cap is documented.

### M5 — Region elision + GC maturation

- Region capabilities derived from grades; region-disciplined workloads bypass the GC.

### M4 — Native backend (LLVM)

- Lowering through erasure, closure conversion, monomorphization, and ANF to native code via LLVM;
  grade-0 content erased from the binary.

### M3 — Tower in Blight + tactics

- `plus-zero` proved by tactics; `Show`/`Ord` traits and a functorized `RedBlackTree` typecheck.

### M2 — Effects and handlers

- The `! E` effect judgement with handlers.

### M1 — Quantitative grading

- Grading exploited at the surface (erased indices, linear use checking).

### M0 — Stage-0 kernel

- The trusted kernel ("the spore"): terms, normalization-by-evaluation, typing rules, and the full
  cubical Kan table, plus the reader/elaborator/REPL. `plus-zero` accepted, the mutated step
  rejected.
