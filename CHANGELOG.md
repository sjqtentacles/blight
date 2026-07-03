# Changelog

All notable changes to this project are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). This project is pre-1.0; the version in
`Cargo.toml` is `0.0.0` and the milestones below track the bootstrap roadmap (spec §9).

## [Unreleased]

### Added

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
