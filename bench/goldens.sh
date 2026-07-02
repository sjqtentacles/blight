#!/usr/bin/env bash
# Bench *correctness* gate (Track D / CI). Unlike bench/game.sh, this does NOT benchmark and needs no
# hyperfine: it just builds each Blight benchmark implementation and asserts its stdout equals the
# committed golden value. A miscompilation or runtime regression that changes a benchmark's result is
# caught here, cheaply, on every CI run.
#
#   <problem>_int.bl  must print  golden.txt
#   <problem>_nat.bl  must print  golden_nat.txt   (the deliberately-slow unary-Nat variant)
#
# Requires a release `blight` built with the `llvm` feature (native backend). Usage:
#   bench/goldens.sh [problem ...]   (defaults to: fib sum factorial treesum)

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

export LLVM_SYS_181_PREFIX="${LLVM_SYS_181_PREFIX:-$(brew --prefix llvm@18 2>/dev/null || true)}"

echo "Building a release blight (--features llvm)..."
cargo build --release -p blight-repl --features llvm >/dev/null
blight="$repo_root/target/release/blight"

problems=("$@")
if [ "${#problems[@]}" -eq 0 ]; then
  problems=(fib sum factorial treesum hofold)
fi

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

fail=0
checked=0

assert_golden() {
  local label="$1" bin="$2" expected="$3" got
  got="$("$bin")"
  if [ "$got" != "$expected" ]; then
    echo "FAIL: $label produced '$got', expected '$expected'" >&2
    fail=1
  else
    echo "  PASS  $label = $got"
    checked=$((checked + 1))
  fi
}

for prob in "${problems[@]}"; do
  dir="bench/games/$prob"
  if [ ! -d "$dir" ]; then
    echo "warn: no such problem dir: $dir — skipping." >&2
    continue
  fi
  echo "=== $prob ==="

  if [ -f "$dir/${prob}_int.bl" ] && [ -f "$dir/golden.txt" ]; then
    bin="$scratch/${prob}_int"
    "$blight" build "$dir/${prob}_int.bl" -o "$bin" >/dev/null 2>&1 \
      || { echo "FAIL: could not build ${prob}_int.bl" >&2; fail=1; continue; }
    assert_golden "Blight-Int $prob" "$bin" "$(cat "$dir/golden.txt")"
  fi

  if [ -f "$dir/${prob}_nat.bl" ] && [ -f "$dir/golden_nat.txt" ]; then
    bin="$scratch/${prob}_nat"
    "$blight" build "$dir/${prob}_nat.bl" -o "$bin" >/dev/null 2>&1 \
      || { echo "FAIL: could not build ${prob}_nat.bl" >&2; fail=1; continue; }
    assert_golden "Blight-Nat $prob" "$bin" "$(cat "$dir/golden_nat.txt")"
  fi
done

echo
if [ "$fail" -ne 0 ]; then
  echo "bench goldens: FAILED"
  exit 1
fi
if [ "$checked" -eq 0 ]; then
  echo "bench goldens: nothing was checked (no impls/goldens found)" >&2
  exit 1
fi
echo "bench goldens: OK ($checked checks passed)"
