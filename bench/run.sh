#!/usr/bin/env bash
# Blight end-to-end performance harness.
#
# Measures two things over the buildable examples, using `hyperfine` (https://github.com/sharkdp/hyperfine):
#   1. compile time   — how long `blight build <example>` takes (parse → elaborate → recheck →
#                        codegen → LLVM → clang link).
#   2. run time       — how long the produced native binary takes to execute.
#
# This complements the in-tree criterion benches:
#   - `cargo bench -p blight-codegen --bench pipeline`               (pure-Rust pipeline stages)
#   - `cargo bench -p blight-codegen --features llvm --bench runtime` (runtime / GC / arena)
#
# Requirements: a release `blight` built with `--features llvm` (LLVM 18 + clang), and `hyperfine`
# on PATH. Run from anywhere; paths are resolved relative to the repo root.
#
# Usage: bench/run.sh [example1.bl example2.bl ...]   (defaults to the buildable examples)

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if ! command -v hyperfine >/dev/null 2>&1; then
  echo "error: hyperfine not found on PATH. Install it (e.g. 'brew install hyperfine') and retry." >&2
  exit 1
fi

# Default workload: the examples that define a buildable `main`.
examples=("$@")
if [ "${#examples[@]}" -eq 0 ]; then
  examples=(
    hello_nat.bl
    containers.bl
    list_sum.bl
    fib.bl
    minmax.bl
    vec_head.bl
    either_compute.bl
    region_scratch.bl
    gcd.bl
    collatz_steps.bl
    list_sort.bl
    tree_sum.bl
    ackermann.bl
    hello_string.bl
    string_reverse.bl
    string_length.bl
    palindrome.bl
    caesar.bl
    ascii_box.bl
  )
fi

export LLVM_SYS_181_PREFIX="${LLVM_SYS_181_PREFIX:-$(brew --prefix llvm@18 2>/dev/null || true)}"

echo "Building a release blight (--features llvm)..."
cargo build --release -p blight-repl --features llvm >/dev/null
blight="$repo_root/target/release/blight"

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

echo
echo "## Compile time (blight build)"
compile_cmds=()
for ex in "${examples[@]}"; do
  src="examples/$ex"
  [ -f "$src" ] || { echo "skip (missing): $src" >&2; continue; }
  out="$scratch/${ex%.bl}"
  compile_cmds+=( --command-name "$ex" "$blight build $src -o $out" )
done
hyperfine --warmup 1 --shell=none "${compile_cmds[@]}"

echo
echo "## Run time (produced binary)"
run_cmds=()
for ex in "${examples[@]}"; do
  src="examples/$ex"
  [ -f "$src" ] || continue
  out="$scratch/${ex%.bl}"
  "$blight" build "$src" -o "$out" >/dev/null
  run_cmds+=( --command-name "$ex" "$out" )
done
hyperfine --warmup 3 --shell=none "${run_cmds[@]}"
