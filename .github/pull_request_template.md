## Summary

What does this PR change, and why?

## Trust boundary

- [ ] This PR does **not** modify `crates/blight-kernel` or `crates/blight-recheck`.
- [ ] It modifies the kernel/re-checker (explain below why it must, and how it was reviewed).

Notes:

## Testing

- [ ] Added/updated a test that fails before this change and passes after.
- [ ] `cargo fmt --all -- --check` is clean.
- [ ] `cargo clippy --workspace --all-targets -- -D warnings` is clean.
- [ ] `cargo test --workspace` is green.
- [ ] If the backend was touched: the `--features llvm` clippy + test paths are green.

## Anything else

Reviewer notes, follow-ups, or open questions.
