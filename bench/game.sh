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
  problems=(fib sum factorial treesum listfold binrec hofold)
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

# ---------------------------------------------------------------------------------------------------
# Per-language startup/RSS baselines. Each near-empty program in bench/games/_baseline/ is built once;
# its peak RSS is the language's runtime/startup floor. We subtract it from each problem's peak RSS to
# report a startup-adjusted "RSS delta" — the memory actually attributable to the workload, not the
# process/interpreter floor (which dominates the tiny register-bound problems). Bash 3.2-safe: scalar
# vars + a case lookup, matching this script's no-associative-array style.
# ---------------------------------------------------------------------------------------------------
base_dir="bench/games/_baseline"
base_c="-"; base_rust="-"; base_ocaml="-"; base_haskell="-"; base_blight="-"; base_python="-"
echo
echo "Measuring per-language startup RSS baselines..."
if [ "$have_c" -eq 1 ] && [ -f "$base_dir/baseline.c" ]; then
  clang -O2 "$base_dir/baseline.c" -o "$scratch/base_c" && base_c="$(peak_rss_kib "$scratch/base_c")"
fi
if [ "$have_rust" -eq 1 ] && [ -f "$base_dir/baseline.rs" ]; then
  rustc -O "$base_dir/baseline.rs" -o "$scratch/base_rs" 2>/dev/null && base_rust="$(peak_rss_kib "$scratch/base_rs")"
fi
if [ "$have_ocaml" -eq 1 ] && [ -f "$base_dir/baseline.ml" ]; then
  cp "$base_dir/baseline.ml" "$scratch/baseline.ml"
  ( cd "$scratch" && ocamlopt baseline.ml -o base_ml 2>/dev/null ) && base_ocaml="$(peak_rss_kib "$scratch/base_ml")"
fi
if [ "$have_haskell" -eq 1 ] && [ -f "$base_dir/baseline.hs" ]; then
  cp "$base_dir/baseline.hs" "$scratch/baseline.hs"
  ( cd "$scratch" && ghc -O2 baseline.hs -o base_hs >/dev/null 2>&1 ) && base_haskell="$(peak_rss_kib "$scratch/base_hs")"
fi
if [ -f "$base_dir/baseline_int.bl" ]; then
  "$blight" build "$base_dir/baseline_int.bl" -o "$scratch/base_bl" >/dev/null 2>&1 && base_blight="$(peak_rss_kib "$scratch/base_bl")"
fi
if [ "$have_python" -eq 1 ] && [ -f "$base_dir/baseline.py" ]; then
  base_python="$(peak_rss_kib python3 "$base_dir/baseline.py")"
fi
printf '  baseline RSS (KiB): C=%s Rust=%s OCaml=%s Haskell=%s Blight=%s Python=%s\n' \
  "$base_c" "$base_rust" "$base_ocaml" "$base_haskell" "$base_blight" "$base_python"

# Map a table language name to its baseline RSS (KiB), or "-".
baseline_for() {
  case "$1" in
    C) echo "$base_c" ;;
    Rust) echo "$base_rust" ;;
    OCaml) echo "$base_ocaml" ;;
    Haskell) echo "$base_haskell" ;;
    Blight-Int|Blight-Nat) echo "$base_blight" ;;
    Python) echo "$base_python" ;;
    *) echo "-" ;;
  esac
}

# RSS delta = max(0, peak - baseline), or "-" if either is unknown. Clamped at 0 because measurement
# noise can make a trivial problem's peak dip just below the standalone baseline.
rss_delta() {
  local peak="$1" base="$2"
  if [ "$peak" = "-" ] || [ "$base" = "-" ]; then echo "-"; return; fi
  local d=$(( peak - base ))
  [ "$d" -lt 0 ] && d=0
  echo "$d"
}

# GC stats for a Blight binary: echoes
#   "collections bytes_allocated promoted_bytes peak_old_reserved shrinks compacting"
# parsed from the BL_GC_STATS stderr line (stdout discarded), or all "-" if unavailable. These are
# startup-independent and are the true memory-efficiency signal (other runtimes expose no uniform
# equivalent). `peak_old_reserved` is the P4.1/P4.2 headline: the high-water old-generation footprint,
# ~1x live under the compacting old generation (BL_GC_OLDGEN=compact) versus ~2x for the semi-space.
gc_stats_blight() {
  local bin="$1" line
  line="$(BL_GC_STATS=1 "$bin" 2>&1 >/dev/null | awk '/^BL_GC_STATS/ { print; exit }')"
  if [ -z "$line" ]; then echo "- - - - - -"; return; fi
  local col alloc prom peak shr comp
  col="$(printf '%s\n' "$line" | sed -n 's/.*collections=\([0-9]*\).*/\1/p')"
  alloc="$(printf '%s\n' "$line" | sed -n 's/.*bytes_allocated=\([0-9]*\).*/\1/p')"
  prom="$(printf '%s\n' "$line" | sed -n 's/.*promoted_bytes=\([0-9]*\).*/\1/p')"
  peak="$(printf '%s\n' "$line" | sed -n 's/.*peak_old_reserved=\([0-9]*\).*/\1/p')"
  shr="$(printf '%s\n' "$line" | sed -n 's/.*shrinks=\([0-9]*\).*/\1/p')"
  comp="$(printf '%s\n' "$line" | sed -n 's/.*compacting=\([0-9]*\).*/\1/p')"
  echo "${col:--} ${alloc:--} ${prom:--} ${peak:--} ${shr:--} ${comp:--}"
}

# Accumulators for the final markdown table and combined JSON. Parallel arrays keyed by row index.
declare -a tbl_problem tbl_lang tbl_secs tbl_rss tbl_delta tbl_collect tbl_alloc tbl_promoted
declare -a tbl_peakold tbl_shrinks tbl_compacting
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
    lang="${names[$i]}"; bin="${bins[$i]}"
    rss="$(peak_rss_kib "$bin")"
    delta="$(rss_delta "$rss" "$(baseline_for "$lang")")"
    printf '  %-14s peak %8s KiB   delta %8s KiB\n' "$lang" "$rss" "$delta"
    # mean run time (seconds) for this lang from hyperfine's JSON, matched by command name.
    secs="$(python3 - "$export_json" "$lang" <<'PYEOF'
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
    # GC stats (bytes allocated / collections / promoted / peak old reserved / shrinks / mode) only for
    # the Blight rows.
    case "$lang" in
      Blight-*) read -r gcoll galloc gprom gpeak gshr gcomp <<EOF
$(gc_stats_blight "$bin")
EOF
        ;;
      *) gcoll="-"; galloc="-"; gprom="-"; gpeak="-"; gshr="-"; gcomp="-" ;;
    esac
    tbl_problem+=("$prob"); tbl_lang+=("$lang"); tbl_secs+=("$secs"); tbl_rss+=("$rss")
    tbl_delta+=("$delta"); tbl_collect+=("$gcoll"); tbl_alloc+=("$galloc"); tbl_promoted+=("$gprom")
    tbl_peakold+=("$gpeak"); tbl_shrinks+=("$gshr"); tbl_compacting+=("$gcomp")
  done
  if [ -n "$py_cmd" ]; then
    rss="$(peak_rss_kib python3 "$dir/$prob.py")"
    delta="$(rss_delta "$rss" "$base_python")"
    printf '  %-14s peak %8s KiB   delta %8s KiB\n' "Python" "$rss" "$delta"
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
    tbl_delta+=("$delta"); tbl_collect+=("-"); tbl_alloc+=("-"); tbl_promoted+=("-")
    tbl_peakold+=("-"); tbl_shrinks+=("-"); tbl_compacting+=("-")
  fi

  unset names bins
done

# ---------------------------------------------------------------------------------------------------
# Markdown summary table.
# ---------------------------------------------------------------------------------------------------
echo
echo "## Benchmark game results"
echo
echo "| Problem | Language | Mean run time (ms) | Peak RSS (KiB) | RSS delta (KiB) |"
echo "| --- | --- | ---: | ---: | ---: |"
for i in "${!tbl_problem[@]}"; do
  secs="${tbl_secs[$i]}"
  if [ "$secs" = "-" ]; then ms="-"; else ms="$(awk "BEGIN { printf \"%.3f\", $secs * 1000 }")"; fi
  printf '| %s | %s | %s | %s | %s |\n' "${tbl_problem[$i]}" "${tbl_lang[$i]}" "$ms" \
    "${tbl_rss[$i]}" "${tbl_delta[$i]}"
done

# ---------------------------------------------------------------------------------------------------
# Blight-only memory detail (BL_GC_STATS): the startup-independent allocator/GC signal that the shared
# RSS columns cannot show (other runtimes expose no uniform equivalent). Only emitted if at least one
# Blight row reported stats.
# ---------------------------------------------------------------------------------------------------
have_gc_rows=0
for i in "${!tbl_problem[@]}"; do
  case "${tbl_lang[$i]}" in
    Blight-*) [ "${tbl_alloc[$i]}" != "-" ] && have_gc_rows=1 ;;
  esac
done
if [ "$have_gc_rows" -eq 1 ]; then
  echo
  echo "## Blight memory detail (BL_GC_STATS)"
  echo
  echo "| Problem | Variant | Bytes allocated | GC collections | Promoted bytes | Peak old reserved | Shrinks | Compacting |"
  echo "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |"
  for i in "${!tbl_problem[@]}"; do
    case "${tbl_lang[$i]}" in
      Blight-*)
        printf '| %s | %s | %s | %s | %s | %s | %s | %s |\n' "${tbl_problem[$i]}" "${tbl_lang[$i]}" \
          "${tbl_alloc[$i]}" "${tbl_collect[$i]}" "${tbl_promoted[$i]}" "${tbl_peakold[$i]}" \
          "${tbl_shrinks[$i]}" "${tbl_compacting[$i]}"
        ;;
    esac
  done
fi

# ---------------------------------------------------------------------------------------------------
# Combined machine-readable JSON.
# ---------------------------------------------------------------------------------------------------
{
  printf '{\n  "os": "%s",\n  "rows": [\n' "$os"
  n=${#tbl_problem[@]}
  for i in "${!tbl_problem[@]}"; do
    secs="${tbl_secs[$i]}"; [ "$secs" = "-" ] && secs="null"
    rss="${tbl_rss[$i]}"; [ "$rss" = "-" ] && rss="null"
    delta="${tbl_delta[$i]}"; [ "$delta" = "-" ] && delta="null"
    alloc="${tbl_alloc[$i]}"; [ "$alloc" = "-" ] && alloc="null"
    coll="${tbl_collect[$i]}"; [ "$coll" = "-" ] && coll="null"
    prom="${tbl_promoted[$i]}"; [ "$prom" = "-" ] && prom="null"
    peakold="${tbl_peakold[$i]}"; [ "$peakold" = "-" ] && peakold="null"
    shr="${tbl_shrinks[$i]}"; [ "$shr" = "-" ] && shr="null"
    comp="${tbl_compacting[$i]}"; [ "$comp" = "-" ] && comp="null"
    sep=","; [ "$i" -eq "$((n - 1))" ] && sep=""
    printf '    { "problem": "%s", "language": "%s", "mean_secs": %s, "peak_rss_kib": %s, "rss_delta_kib": %s, "bytes_allocated": %s, "gc_collections": %s, "promoted_bytes": %s, "peak_old_reserved": %s, "shrinks": %s, "compacting": %s }%s\n' \
      "${tbl_problem[$i]}" "${tbl_lang[$i]}" "$secs" "$rss" "$delta" "$alloc" "$coll" "$prom" "$peakold" "$shr" "$comp" "$sep"
  done
  printf '  ]\n}\n'
} > bench/game-results.json

echo
echo "Wrote bench/game-results.json (and per-problem bench/game-<problem>.json)."
