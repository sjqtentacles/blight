#!/usr/bin/env bash
# Blight multicore + serializer performance harness (M15-M19).
#
# Proves the two performance claims of the share-nothing concurrency runtime:
#   1. SCALING  — the worker pool (worker.c / BlPool) runs a fixed set of heavy independent tasks
#                 faster as worker count grows (1/2/4/8, capped at the host core count). Prints a
#                 SPEEDUP table (workers, wall_ms, speedup_vs_1).
#   2. THROUGHPUT — the structural (de)serializer (serialize.c) — the boundary primitive every
#                 cross-heap (M17) and cross-machine (M19) message rides on — round-trips a
#                 representative deep message and reports blob size, ns/op, and MB/s.
#
# It compiles the same C runtime sources + bench harnesses the Rust test driver uses
# (crates/blight-codegen/runtime/tests/{worker_bench,serialize_bench}.c), so the numbers match
# `cargo test -p blight-codegen --features llvm worker_pool_scales_with_cores serializer_throughput_reported`
# but are actually printed here (cargo suppresses a passing test's stdout).
#
# NOTE: absolute speedup and MB/s are host- and load-dependent (core count, cache, scheduler). The
# determinism of the worker-pool result is the hard correctness gate (enforced inside the harness and
# the Rust test); the timings are indicative.
#
# Requirements: clang (the same toolchain the runtime links with). No LLVM/cargo needed.
# Usage: bench/multicore.sh            (runs both benches)
#        BL_TSAN=1 bench/multicore.sh  (build under ThreadSanitizer; timings will be slower)

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
runtime="$repo_root/crates/blight-codegen/runtime"

if ! command -v clang >/dev/null 2>&1; then
  echo "error: clang not found on PATH." >&2
  exit 1
fi

ncores="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo '?')"
echo "host online cores: $ncores"

tsan_flags=()
if [ -n "${BL_TSAN:-}" ]; then
  echo "building under ThreadSanitizer (BL_TSAN set) — timings inflated, race-checking on"
  tsan_flags=(-fsanitize=thread)
fi

workdir="$(mktemp -d)"
trap 'rm -rf "$workdir"' EXIT

# $1 = optimization level, $2.. = source list (relative to $runtime); builds $workdir/<bin>.
build() {
  local bin="$1"; shift
  local opt="$1"; shift
  local objs=()
  local src
  for src in "$@"; do
    local obj="$workdir/$(echo "$src" | tr / _).o"
    # -DBL_NO_MAIN suppresses prelude_rt.c's built-in numeric main (the bench harnesses
    # worker_bench.c / serialize_bench.c provide their own); it is inert for the other sources.
    clang -c "$opt" -g -pthread -DBL_NO_MAIN ${tsan_flags[@]+"${tsan_flags[@]}"} -I "$runtime" "$runtime/$src" -o "$obj"
    objs+=("$obj")
  done
  clang -pthread ${tsan_flags[@]+"${tsan_flags[@]}"} -o "$workdir/$bin" "${objs[@]}"
}

echo
echo "== worker-pool scaling (M17) =="
build worker_bench -O1 gc.c stack.c delay.c effects.c arena.c numeric.c serialize.c worker.c prelude_rt.c tests/worker_bench.c
"$workdir/worker_bench"

echo
echo "== serializer throughput (M18) =="
build serialize_bench -O2 gc.c stack.c delay.c effects.c arena.c numeric.c serialize.c prelude_rt.c tests/serialize_bench.c
"$workdir/serialize_bench"
