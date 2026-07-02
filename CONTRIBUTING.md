# Contributing to Blight

Thanks for your interest in Blight. This document covers the project's one non-negotiable rule
(the trust boundary), the development workflow, and how to run the checks CI runs.

## The one rule: protect the trusted kernel

Blight's entire value proposition is that **only `crates/blight-kernel` is trusted**. "Trusted" is
the precise, load-bearing sense: *implicitly trusted* — relied on without any external check, so a
bug there is silent and could mint a false `Proof`. It is the
"spore": the sole way to construct a `Proof` (a well-typed term). Everything else — the elaborator,
tactics, the package manager, the backend, the REPL — is *untrusted tower code*, meaning *explicitly
checked*: it can only *propose* terms the kernel must independently accept, so its bugs are caught
rather than believed.

Concretely:

- **Keep the kernel small and auditable.** Changes to `blight-kernel` get the most scrutiny. Prefer
  pushing complexity into the untrusted crates (`blight-elab`, `blight-codegen`) where a bug can
  cause a rejection or a crash, but never an unsound acceptance.
- **`unsafe` is forbidden in the kernel** (`#![forbid(unsafe_code)]`) and in the re-checker. Do not
  add it.
- **The `Proof` constructor stays private.** Untrusted code must go through the public checking API,
  never construct proofs directly.
- **The re-checker is independent.** `crates/blight-recheck` is a deliberately separate, minimal
  implementation. Don't share code with the kernel that would couple their bugs; the point is that
  two independently-written checkers agree.
- **`foreign` is the only TCB-growing hatch — avoid it.** A `foreign` postulate is an FFI *axiom*
  the kernel must believe (it cannot re-verify an external symbol), so it genuinely grows the trusted
  base and the re-checker honestly *declines* any program using it. New runtime capabilities should
  avoid it: the share-nothing multicore + distributed runtime (M15-M19) — the worker pool, the
  serializer, and the `blight-net` TCP transport — adds **zero new `foreign` axioms**. The transport
  in particular is untrusted Rust with **no `blight-kernel` dependency**; it only moves serialized
  bytes, so the kernel never sees a thread or a socket and the TCB does not grow.

If you are unsure whether a change belongs in the kernel, it almost certainly does not.

## Development workflow

Blight is built **test-first** (red → green → refactor); see the test ledger in
[docs/implementation.md §6](docs/implementation.md#6-tdd-workflow-and-the-test-ledger). A new feature
or fix should come with a black-box test (in a crate's `tests/`) and/or a white-box unit test (in a
`#[cfg(test)]` module) that fails before your change and passes after.

- **White-box vs black-box.** Kernel unit tests live next to the code and may build proof fixtures.
  Workspace `tests/` are black-box: they touch only public APIs, doubling as a check that the TCB
  boundary is usable from outside.
- **Examples can't rot.** Programs under [examples/](examples/) are loaded and checked by
  `crates/blight-repl/tests/examples.rs`. If you add an example, add it there.

## Running the checks

CI runs these; run them locally before opening a PR.

```bash
# Format and lint.
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings

# Tests, without the native backend.
cargo test --workspace
```

The native/WASM backend is gated behind the `llvm` feature (requires LLVM 18 + clang). To run those
paths too:

```bash
export LLVM_SYS_181_PREFIX="$(brew --prefix llvm@18)"   # macOS/Homebrew
cargo clippy --workspace --all-targets --features blight-codegen/llvm,blight-repl/llvm -- -D warnings
cargo test --workspace --features blight-codegen/llvm,blight-repl/llvm
```

## Pull requests

- Keep PRs focused; describe what changed and why.
- Note explicitly if a change touches `blight-kernel` or `blight-recheck`.
- Ensure `fmt`, `clippy`, and `test` are green (with and without `llvm` if you touched the backend).

## License

By contributing, you agree that your contributions are dual-licensed under
[MIT](LICENSE-MIT) and [Apache-2.0](LICENSE-APACHE), matching the project license.
