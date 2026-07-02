# Testing strategy (Track D)

Blight's correctness claim rests on a tiny trusted kernel plus an *independent* re-checker that
re-verifies every proof. Track D hardens the test suite around that claim so a regression in the
soundness-critical code is caught automatically. This document is the map of what runs, where, and
why.

## Layers

| Layer | Location | What it guarantees |
| --- | --- | --- |
| Corpus / acceptance | `crates/blight-repl/tests/`, `crates/blight-recheck/tests/recheck.rs` | The kernel + elaborator accept the prelude and the M0–M6 headline programs; the re-checker agrees (`Ok`) or honestly declines (`Declined`) — never `Rejected`. |
| Property (proptest, shrinking) | `crates/*/tests/proptest_*.rs`, `crates/blight-recheck/tests/properties.rs` | Generative invariants over thousands of cases: kernel↔recheck agreement, NbE idempotence/convertibility, reader round-trip, soundness + fragment-completeness. |
| Soundness negative corpus | `crates/blight-recheck/tests/negative.rs` | A curated set of *ill-typed* terms the kernel rejects **and** the re-checker refuses (actively `Rejected`, never `Ok`). |
| Differential (custom PRNG + proptest) | `crates/blight-recheck/tests/differential.rs`, `proptest_differential.rs` | Many well-typed-by-construction core terms; the re-checker never `Rejected`s what the kernel certified (the soundness alarm). |
| Backend bit-identity | `crates/blight-repl/src/main.rs` (`DIFF_FLAGS`) | Every optimization pass is bit-identical under its `BL_NO_*` off-switch. |
| White-box unit | `#[cfg(test)]` in `crates/blight-recheck/src/*.rs`, `crates/blight-kernel/src/*.rs` | Per-arm behaviour of `conv`/`subtype`, the `from_kernel` decline/reject boundary, the purity flag, and the re-checker's independent Kan table (`kan.rs`: constant-line fast paths, heterogeneous Π/Σ/PathP `transp`/`hcomp`, derived `comp`, and `#[should_panic]` goldens for the two fail-safe `unimplemented!` arms). |
| Mutation (cargo-mutants) | `.cargo/mutants.toml`, `.github/workflows/mutants.yml` | The above tests actually *catch bugs* injected into the kernel + re-checker. |

## Property suites

`proptest` (a dev-dependency only; it never enters the trusted base or the shipped binary) drives
shrinking generators:

- **kernel ↔ re-checker agreement** — `proptest_differential.rs`: well-typed closed core terms; the
  re-checker never `Rejected`s a kernel-accepted term. Shrinks a regression to a minimal witness.
- **NbE idempotence / convertibility** — `blight-kernel/tests/proptest_nbe.rs`: `nf (nf t) ≡ nf t`
  and `conv t (nf t)`.
- **reader round-trip** — `blight-elab/tests/proptest_reader.rs`: `read(render(s)) == s` for arbitrary
  s-expression trees and form sequences.
- **soundness + fragment-completeness** — `blight-recheck/tests/properties.rs`: kernel-reject ⇒
  re-checker never `Ok`; and kernel-accept on the fully-supported fragment ⇒ re-checker `Ok` (never a
  spurious decline).

Case counts default high (2000–4000) and the differential corpus honours `BLIGHT_DIFF_ITERS`.

## Mutation testing (the trusted-base gate)

[`cargo-mutants`](https://mutants.rs) injects small bugs ("mutants") into the source and re-runs the
suite; a mutant no test catches is a *surviving* mutant — a hole. The config
(`.cargo/mutants.toml`) scopes mutation to the soundness-critical crates only:

```toml
examine_globs = [
    "crates/blight-kernel/src/**/*.rs",
    "crates/blight-recheck/src/**/*.rs",
]
```

The workflow runs in two modes so a strict whole-base gate never blocks on historical gaps:

- **PR (gating)** — `cargo mutants --in-diff <pr.diff>`: every *new or changed* line of trusted-base
  code must have its mutants killed. This ratchets coverage upward over time.
- **nightly (informational)** — a full trusted-base run, uploaded as an artifact, tracking the
  surviving-mutant backlog. Non-blocking.

### Baseline

Measured on `crates/blight-recheck/src/conv.rs` (definitional equality — the heart of the
re-checker), before vs after adding the per-arm `conv` unit tests:

| | mutants | caught | missed | unviable |
| --- | --- | --- | --- | --- |
| before | 59 | 31 | 27 | 1 |
| after  | 59 | 55 | 3  | 1 |

The 3 residual survivors are de-Bruijn *level-arithmetic* mutants (`lvl + 1` → `lvl * 1`) inside the
binder/η recursions: because `conv` applies the same level to *both* sides, the substitution is
symmetric and the mutant is behaviourally equivalent (it changes no accept/reject outcome). They are
left rather than papered over with a skip attribute.

To reproduce locally:

```sh
cargo install cargo-mutants --locked
cargo mutants                       # whole trusted base (slow)
cargo mutants -f crates/blight-recheck/src/conv.rs   # one file (fast)
```

## Coverage (`cargo-llvm-cov` + floor)

`.github/workflows/coverage.yml` runs the no-LLVM workspace suite under instrumentation and enforces
a **line-coverage floor** of 65% (collect once with `--no-report`, then emit an lcov artifact and a
`report --fail-under-lines 65` gate). The native backend (codegen) needs the LLVM toolchain and is
covered by the separate `llvm` CI job, so it is deliberately outside this floor.

`--fail-under-lines` is a *global* workspace check, so it cannot express "the trusted base must clear
a stricter bar than the workspace average" on its own. The same job also emits a second, scoped
report from the same instrumentation data (`cargo llvm-cov report -p blight-kernel -p blight-recheck
--fail-under-lines 75`) — a **75% line-coverage floor over `blight-kernel` + `blight-recheck`
combined**, comfortably above the 65% workspace floor since this is precisely the code an unsound bug
would live in. The two crates combined measure ~77.24% lines at the time of writing (individual files
range from 26% to 100% — see the table below); 75% is a few points below that measured baseline, the
same margin-below-baseline the workspace floor itself uses, so ordinary churn does not flap CI. Raise
both floors as coverage improves; do not lower them.

Baseline at the time of writing: **66.71% lines** (74.99% functions) workspace-wide. Highlights and
known gaps:

| Area | Line cov | Note |
| --- | --- | --- |
| `blight-recheck/src/conv.rs` | 100% | per-arm `conv`/`subtype` unit tests |
| `blight-kernel/src/{semiring,proof,usage,context}.rs` | ~96–100% | core algebra well covered |
| `blight-kernel/src/{check,normalize}.rs` | ~78–80% | the trusted checker + NbE |
| `blight-recheck/src/kan.rs` | 91.52% | closed from a 0% gap (Track M1): white-box unit tests exercise the constant-line fast paths, the heterogeneous Π/Σ/PathP `transp`/`hcomp` structural dispatch, derived `comp`, and `#[should_panic]` goldens for the two fail-safe `unimplemented!` arms. The remaining ~8% is the `Glue`-decline dead branches the re-checker deliberately never reaches. |
| `blight-kernel/src/erase.rs` | 26.48% | lowest in the trusted base; the `0`-grade erasure pass has many arms only exercised by graded programs current tests don't yet cover. Biggest lever for raising the 75% scoped floor. |
| `blight-kernel/src/kan.rs` | 55.85% | the *trusted*-checker Kan table; lower than its re-checker mirror (`blight-recheck/src/kan.rs`, above) because the kernel additionally inlines fast paths the white-box suite targets on the recheck side only. |
| `blight-recheck/src/normalize.rs` | 58.90% | the re-checker's independent NbE; property tests (`proptest_nbe.rs`) exercise the kernel's normalizer, not yet this mirror directly. |
| `blight-codegen/src/*` | ~0–93% | needs the `llvm` feature; not under either floor |

Reproduce locally:

```sh
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov --locked
cargo llvm-cov --workspace --summary-only            # table
cargo llvm-cov report --fail-under-lines 65          # the workspace CI gate
cargo llvm-cov report -p blight-kernel -p blight-recheck --fail-under-lines 75  # trusted-base gate
```

## Fuzzing (`cargo-fuzz`)

The `fuzz/` crate (nightly-only, libFuzzer; excluded from the workspace) has three targets:

| Target | Drives | Oracle |
| --- | --- | --- |
| `reader` | `read_all` on arbitrary UTF-8 | no panic / no stack overflow |
| `elab` | read → `parse_surface`/`parse_decl` → `elaborate` | no panic |
| `kernel` | the full `Program` pipeline (read → elaborate → kernel check), `(load …)` disabled | the kernel rejects bad programs, never crashes |

Fuzzing runs in two, deliberately different modes:

- **Exploratory (informational, nightly)** — `.github/workflows/fuzz.yml` builds and briefly runs
  each target with fresh random input (`-max_total_time=120`), uploading any crash inputs it finds.
  Non-gating: a time-boxed search can simply fail to hit a crash within its budget on a given run, so
  "no crash found this time" is not a meaningful pass/fail signal.
- **Corpus replay (gating, every PR)** — the `fuzz-corpus-replay` job in `ci.yml` runs each target
  with `-runs=0` (no new inputs generated; every file in the committed `fuzz/corpus/<target>/`
  directory is replayed exactly once against the current build) and fails the build on any crash.
  This *is* deterministic and fast (well under a minute total), so it is safe to gate: "no
  previously-found input regresses." The corpus directories are committed to the repo specifically so
  this gate has something durable to replay — this is the mechanism through which a crash found by
  the informational nightly run becomes a permanent regression test once minimized and fixed (see
  "Findings and fixes" below).

Run locally:

```sh
cargo install cargo-fuzz --locked
cargo +nightly fuzz run reader -- -max_total_time=60     # exploratory: search for new crashes
cargo +nightly fuzz run reader -- -runs=0                # replay: the deterministic gate, as in CI
```

### Findings and fixes

- **Reader stack overflow on deep nesting** — `(((…` overflowed the recursive descent. Fixed with a
  nesting-depth limit (`sexpr::MAX_DEPTH`) that returns a `ReadError` instead of recursing; regression
  test `deeply_nested_input_is_rejected_not_overflowed`.
- **Unary-Peano string/char literals (known limitation)** — a term-position string/char literal
  desugars to `Nat` codepoints encoded as `Succ^cp Zero` (see `elab.rs`), so a large codepoint builds
  a term thousands–millions of nodes deep that exhausts the stack during elaboration/`Drop`. This is a
  front-end *resource* bound on adversarial input, **not** a soundness issue (the kernel never mints a
  bad proof). Properly removing it means changing the string representation (e.g. primitive
  `Int`/`String`), which is out of scope for the testing track; the fuzz smoke is therefore
  informational rather than gating. Because it is a known, accepted resource bound rather than a bug
  to fix, no minimized reproducer for it belongs in the committed replay corpus (the corpus is small
  and every entry currently completes in milliseconds; a corpus file that deliberately stack-overflows
  would turn the deterministic replay gate into a flaky one, defeating its purpose).
- **TDD for future fuzz-found crashes.** When a nightly exploratory run *does* find a genuine bug: fix
  it, then `cargo fuzz cmin`/copy the (ideally minimized) crashing input into
  `fuzz/corpus/<target>/` and commit it *before or alongside* the fix, the same red-then-green
  discipline as any other regression test — the corpus-replay gate then pins the fix permanently.

## What runs in CI

| Workflow | Trigger | Gating? | What it does |
| --- | --- | --- | --- |
| `ci.yml` · `check` | push/PR | yes | `fmt` + `clippy -D warnings` + `cargo test --workspace` (no native backend). |
| `ci.yml` · `llvm` | push/PR | yes | `clippy` + `cargo test` with `--features llvm`; then the **full differential bit-identity matrix** (`differential -- --ignored`), the **bench goldens** gate (`bench/goldens.sh`), and the **multicore runtime under ThreadSanitizer** (`BL_TSAN=1`). |
| `coverage.yml` | push/PR | yes | `cargo-llvm-cov` with a workspace line-coverage floor (`--fail-under-lines 65`) **and** a scoped trusted-base floor (`-p blight-kernel -p blight-recheck --fail-under-lines 75`). |
| `ci.yml` · `fuzz-corpus-replay` | push/PR | yes | Deterministic `-runs=0` replay of the committed `fuzz/corpus/{reader,elab,kernel}` seed corpus; fails on any crash regression. |
| `mutants.yml` · incremental | PR | yes | `cargo-mutants --in-diff` over changed trusted-base lines. |
| `mutants.yml` · nightly | schedule | no | full `cargo-mutants` over the kernel + re-checker (informational). |
| `fuzz.yml` | schedule | no | time-boxed, randomized `cargo-fuzz` smoke of `reader`/`elab`/`kernel` searching for *new* crashes; uploads any it finds (informational — see `fuzz-corpus-replay` above for the gating counterpart). |

The standing `check` + `llvm` jobs are the merge gate; `coverage`, `fuzz-corpus-replay`, and the
incremental `mutants` run — and gate — on every PR; the nightly mutation full-run and the exploratory
fuzz smoke are informational signals that surface new survivors / crashes without blocking merges.

The `llvm` job earns its name three extra ways beyond the headline test suite:

- **Differential matrix.** The bit-identity harness (`DIFF_FLAGS`) is `#[ignore]`d in the normal run
  because it builds many native binaries; CI runs it explicitly so a miscompiling optimization fails
  the build, not just the nightly.
- **Bench goldens.** `bench/goldens.sh` rebuilds each `bench/games/*/*_{int,nat}.bl` and asserts its
  stdout still equals the committed golden — a cheap end-to-end gate against codegen/runtime drift
  (no `hyperfine`, unlike `bench/game.sh`).
- **ThreadSanitizer.** The share-nothing multicore harnesses are rebuilt with `-fsanitize=thread`
  (`BL_TSAN=1`) and re-run, catching data races in the thread-local GC and worker pool.
