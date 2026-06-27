#!/usr/bin/env bash
# Blight cross-language "benchmark game".
#
# For each shared problem in bench/games/<problem>/ this driver:
#   1. compiles every available language impl (gracefully skipping a missing toolchain),
#   2. asserts each binary's stdout equals the problem's golden value (correctness gate),
#   3. benchmarks run time with `hyperfine` across all available languages for that problem,
#   4. captures peak RSS via `/usr/bin/time` (Darwin `-l`, in bytes; Linux `-v`, in KiB),
#   5. prints a markdown summary table and writes machine-readable JSON.
#
# The native-Int Blight impl (<problem>_int.bl) competes against C/Rust/OCaml/Haskell/Python on the
# *shared* golden (golden.txt). The unary-`Nat` Blight impl (<problem>_nat.bl) is the deliberately
# slow comparison point and is checked against its OWN smaller-n golden (golden_nat.txt).
#
# Complements bench/run.sh (compile/run time over the buildable examples) and the criterion benches
# (`cargo bench -p blight-codegen`). Robust to missing tools: an absent toolchain just shrinks the
# comparison set, it never aborts the run. Python and the Blight impls are always available.
#
# Usage: bench/game.sh [problem ...]   (defaults to: fib sum factorial)

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if ! command -v hyperfine >/dev/null 2>&1; then
  echo "error: hyperfine not found on PATH. Install it (e.g. 'brew install hyperfine') and retry." >&2
  exit 1
fi

export LLVM_SYS_181_PREFIX="${LLVM_SYS_181_PREFIX:-$(brew --prefix llvm@18 2>/dev/null || true)}"

# ---------------------------------------------------------------------------------------------------
# Toolchain detection. A missing compiler drops that language from every problem's comparison set.
# ---------------------------------------------------------------------------------------------------
have() { command -v "$1" >/dev/null 2>&1; }

have_c=0;       have clang   && have_c=1
have_rust=0;    have rustc   && have_rust=1
have_ocaml=0;   have ocamlopt && have_ocaml=1
have_haskell=0; have ghc     && have_haskell=1
have_python=0;  have python3 && have_python=1

for tool in clang rustc ocamlopt ghc python3; do
  have "$tool" || echo "warn: '$tool' not found — skipping that language." >&2
done

echo "Building a release blight (--features llvm)..."
cargo build --release -p blight-repl --features llvm >/dev/null
blight="$repo_root/target/release/blight"

problems=("$@")
if [ "${#problems[@]}" -eq 0 ]; then
  problems=(fib sum factorial)
fi

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

# Peak RSS in KiB for a command, via the platform's /usr/bin/time. Darwin reports "maximum resident
# set size" in BYTES (-l); Linux reports "Maximum resident set size" in KiB (-v). Returns "-" if the
# value cannot be parsed (so the table never breaks).
os="$(uname)"
peak_rss_kib() {
  local out
  if [ "$os" = "Darwin" ]; then
    out="$({ /usr/bin/time -l "$@" >/dev/null; } 2>&1 || true)"
    local bytes
    bytes="$(printf '%s\n' "$out" | awk '/maximum resident set size/ { print $1; exit }')"
    if [ -n "${bytes:-}" ]; then echo $(( bytes / 1024 )); else echo "-"; fi
  else
    out="$({ /usr/bin/time -v "$@" >/dev/null; } 2>&1 || true)"
    local kib
    kib="$(printf '%s\n' "$out" | awk -F': ' '/Maximum resident set size/ { print $2; exit }')"
    if [ -n "${kib:-}" ]; then echo "$kib"; else echo "-"; fi
  fi
}

# Assert a binary's stdout equals the expected golden value; FAIL + exit on mismatch.
assert_golden() {
  local label="$1" bin="$2" expected="$3"
  local got
  got="$("$bin")"
  if [ "$got" != "$expected" ]; then
    echo "FAIL: $label produced '$got', expected '$expected'" >&2
    exit 1
  fi
  echo "  PASS  $label = $got"
}

# Accumulators for the final markdown table and combined JSON. Parallel arrays keyed by row index.
declare -a tbl_problem tbl_lang tbl_secs tbl_rss
combined_json_problems=""

for prob in "${problems[@]}"; do
  dir="bench/games/$prob"
  if [ ! -d "$dir" ]; then
    echo "warn: no such problem dir: $dir — skipping." >&2
    continue
  fi
  golden="$(cat "$dir/golden.txt")"
  golden_nat=""
  [ -f "$dir/golden_nat.txt" ] && golden_nat="$(cat "$dir/golden_nat.txt")"

  echo
  echo "=== $prob (shared golden = $golden) ==="

  # Per-problem: build name->binary maps for the langs that compiled. Parallel arrays.
  declare -a names=() bins=()

  # --- C ---
  if [ "$have_c" -eq 1 ] && [ -f "$dir/$prob.c" ]; then
    bin="$scratch/${prob}_c"
    clang -O2 "$dir/$prob.c" -o "$bin"
    assert_golden "C" "$bin" "$golden"
    names+=("C"); bins+=("$bin")
  fi

  # --- Rust ---
  if [ "$have_rust" -eq 1 ] && [ -f "$dir/$prob.rs" ]; then
    bin="$scratch/${prob}_rs"
    rustc -O "$dir/$prob.rs" -o "$bin" 2>/dev/null
    assert_golden "Rust" "$bin" "$golden"
    names+=("Rust"); bins+=("$bin")
  fi

  # --- OCaml (plain stdlib; no ocamlfind) ---
  if [ "$have_ocaml" -eq 1 ] && [ -f "$dir/$prob.ml" ]; then
    bin="$scratch/${prob}_ml"
    # ocamlopt drops .cmi/.cmx/.o next to the source; build inside scratch to keep the tree clean.
    cp "$dir/$prob.ml" "$scratch/$prob.ml"
    ( cd "$scratch" && ocamlopt "$prob.ml" -o "${prob}_ml" 2>/dev/null )
    assert_golden "OCaml" "$bin" "$golden"
    names+=("OCaml"); bins+=("$bin")
  fi

  # --- Haskell (clean up .hi/.o) ---
  if [ "$have_haskell" -eq 1 ] && [ -f "$dir/$prob.hs" ]; then
    bin="$scratch/${prob}_hs"
    cp "$dir/$prob.hs" "$scratch/$prob.hs"
    ( cd "$scratch" && ghc -O2 "$prob.hs" -o "${prob}_hs" >/dev/null 2>&1 )
    assert_golden "Haskell" "$bin" "$golden"
    names+=("Haskell"); bins+=("$bin")
  fi

  # --- Blight (native Int) ---
  if [ -f "$dir/${prob}_int.bl" ]; then
    bin="$scratch/${prob}_blint"
    "$blight" build "$dir/${prob}_int.bl" -o "$bin" >/dev/null 2>&1
    assert_golden "Blight-Int" "$bin" "$golden"
    names+=("Blight-Int"); bins+=("$bin")
  fi

  # --- Python (interpreted; command is `python3 file.py`) ---
  py_cmd=""
  if [ "$have_python" -eq 1 ] && [ -f "$dir/$prob.py" ]; then
    got="$(python3 "$dir/$prob.py")"
    if [ "$got" != "$golden" ]; then
      echo "FAIL: Python produced '$got', expected '$golden'" >&2
      exit 1
    fi
    echo "  PASS  Python = $got"
    py_cmd="python3 $dir/$prob.py"
  fi

  # --- Blight (unary Nat) — checked against its OWN smaller-n golden ---
  if [ -f "$dir/${prob}_nat.bl" ] && [ -n "$golden_nat" ]; then
    bin="$scratch/${prob}_blnat"
    "$blight" build "$dir/${prob}_nat.bl" -o "$bin" >/dev/null 2>&1
    assert_golden "Blight-Nat (own golden $golden_nat)" "$bin" "$golden_nat"
    names+=("Blight-Nat"); bins+=("$bin")
  fi

  # --- Benchmark run time: one hyperfine invocation comparing every available lang. ---
  hf_args=()
  for i in "${!names[@]}"; do
    hf_args+=( --command-name "${names[$i]}" "${bins[$i]}" )
  done
  if [ -n "$py_cmd" ]; then
    hf_args+=( --command-name "Python" "$py_cmd" )
  fi

  export_json="bench/game-$prob.json"
  echo
  echo "-- run time: $prob --"
  hyperfine --warmup 3 --export-json "$export_json" "${hf_args[@]}"

  # --- Peak RSS per language + collect rows for the summary table. ---
  echo
  echo "-- peak RSS: $prob --"
  for i in "${!names[@]}"; do
    rss="$(peak_rss_kib "${bins[$i]}")"
    printf '  %-14s %8s KiB\n' "${names[$i]}" "$rss"
    # mean run time (seconds) for this lang from hyperfine's JSON, matched by command name.
    secs="$(python3 - "$export_json" "${names[$i]}" <<'PYEOF'
import json, sys
data = json.load(open(sys.argv[1]))
name = sys.argv[2]
for r in data["results"]:
    if r.get("command") == name:
        print(f"{r['mean']:.6f}")
        break
else:
    print("-")
PYEOF
)"
    tbl_problem+=("$prob"); tbl_lang+=("${names[$i]}"); tbl_secs+=("$secs"); tbl_rss+=("$rss")
  done
  if [ -n "$py_cmd" ]; then
    rss="$(peak_rss_kib python3 "$dir/$prob.py")"
    printf '  %-14s %8s KiB\n' "Python" "$rss"
    secs="$(python3 - "$export_json" "Python" <<'PYEOF'
import json, sys
data = json.load(open(sys.argv[1]))
name = sys.argv[2]
for r in data["results"]:
    if r.get("command") == name:
        print(f"{r['mean']:.6f}")
        break
else:
    print("-")
PYEOF
)"
    tbl_problem+=("$prob"); tbl_lang+=("Python"); tbl_secs+=("$secs"); tbl_rss+=("$rss")
  fi

  unset names bins
done

# ---------------------------------------------------------------------------------------------------
# Markdown summary table.
# ---------------------------------------------------------------------------------------------------
echo
echo "## Benchmark game results"
echo
echo "| Problem | Language | Mean run time (ms) | Peak RSS (KiB) |"
echo "| --- | --- | ---: | ---: |"
for i in "${!tbl_problem[@]}"; do
  secs="${tbl_secs[$i]}"
  if [ "$secs" = "-" ]; then ms="-"; else ms="$(awk "BEGIN { printf \"%.3f\", $secs * 1000 }")"; fi
  printf '| %s | %s | %s | %s |\n' "${tbl_problem[$i]}" "${tbl_lang[$i]}" "$ms" "${tbl_rss[$i]}"
done

# ---------------------------------------------------------------------------------------------------
# Combined machine-readable JSON.
# ---------------------------------------------------------------------------------------------------
{
  printf '{\n  "os": "%s",\n  "rows": [\n' "$os"
  n=${#tbl_problem[@]}
  for i in "${!tbl_problem[@]}"; do
    secs="${tbl_secs[$i]}"; [ "$secs" = "-" ] && secs="null"
    rss="${tbl_rss[$i]}"; [ "$rss" = "-" ] && rss="null"
    sep=","; [ "$i" -eq "$((n - 1))" ] && sep=""
    printf '    { "problem": "%s", "language": "%s", "mean_secs": %s, "peak_rss_kib": %s }%s\n' \
      "${tbl_problem[$i]}" "${tbl_lang[$i]}" "$secs" "$rss" "$sep"
  done
  printf '  ]\n}\n'
} > bench/game-results.json

echo
echo "Wrote bench/game-results.json (and per-problem bench/game-<problem>.json)."
