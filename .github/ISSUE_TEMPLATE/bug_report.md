---
name: Bug report
about: Report incorrect behavior in Blight
title: ""
labels: bug
assignees: ""
---

## Summary

A clear, concise description of the bug.

## Reproduction

Steps or a minimal `.bl` program that triggers the bug:

```scheme
; minimal repro here
```

How it was run (REPL, `blight build`, a specific test):

```bash
# command here
```

## Expected vs actual

- **Expected:**
- **Actual:** (include the exact error text or wrong output)

## Soundness?

Does this allow an ill-typed term to be **accepted** by the kernel (a soundness bug), or is it a
rejection/crash/wrong-output bug? Soundness bugs are highest priority.

## Environment

- OS:
- Rust version (`rustc --version`):
- Built with `--features llvm`? If so, LLVM version:
- Commit / branch:
