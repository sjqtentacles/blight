#!/usr/bin/env python3
"""Benchmark regression checker for the Blight "benchmark game".

Compares a fresh `bench/game-results.json` (produced by `bench/game.sh`) against the committed
`bench/game-results.baseline.json`, row by row, keyed on `(problem, language)`.

Two classes of metric, treated very differently:

* **Deterministic** — `bytes_allocated`, `gc_collections`, `promoted_bytes`, and `peak_old_reserved`
  (the Blight rows only). These are a pure function of the compiled program and the runtime; for a
  fixed build they do not vary run to run or machine to machine. A real increase here is a genuine
  memory/allocation regression in codegen or the runtime (and `peak_old_reserved` — the high-water
  old-generation footprint — is the P4.1/P4.2 mark-compact headline), so these are checked **strictly**
  (any increase beyond a tiny tolerance is a hard failure that exits non-zero).

* **Machine-dependent** — `mean_secs` (wall clock) and `peak_rss_kib`. These vary with hardware,
  load, and the OS allocator, so a committed absolute baseline is only meaningful on the machine
  that produced it. They are checked **softly**: a regression beyond a generous tolerance is
  reported as a warning but does not fail the build unless `--strict-time` is given.

Usage:
    bench/check_regress.py [--baseline FILE] [--current FILE]
                           [--alloc-tol FRAC] [--time-tol FRAC] [--strict-time]

Exit status is non-zero iff a hard (deterministic-metric) regression is found — or, with
`--strict-time`, a wall-clock regression too. New rows (present now, absent in the baseline) and
dropped rows (the reverse) are reported but never fail on their own.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from typing import Optional

# Metrics that are a deterministic function of the build — checked strictly.
DETERMINISTIC = ("bytes_allocated", "gc_collections", "promoted_bytes", "peak_old_reserved")


def load_rows(path: str) -> dict[tuple[str, str], dict]:
    with open(path) as f:
        data = json.load(f)
    rows = {}
    for r in data.get("rows", []):
        rows[(r["problem"], r["language"])] = r
    return rows


def regressed(base: Optional[float], cur: Optional[float], tol: float) -> bool:
    """A regression is `cur > base * (1 + tol)`. Nulls (absent metric) never regress."""
    if base is None or cur is None:
        return False
    return cur > base * (1.0 + tol)


def main() -> int:
    repo = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--baseline", default=os.path.join(repo, "bench", "game-results.baseline.json"))
    ap.add_argument("--current", default=os.path.join(repo, "bench", "game-results.json"))
    ap.add_argument("--alloc-tol", type=float, default=0.01,
                    help="fractional tolerance for deterministic metrics (default 0.01 = 1%%)")
    ap.add_argument("--time-tol", type=float, default=0.50,
                    help="fractional tolerance for wall clock / RSS (default 0.50 = 50%%)")
    ap.add_argument("--strict-time", action="store_true",
                    help="treat a wall-clock regression as a hard failure too")
    args = ap.parse_args()

    try:
        base = load_rows(args.baseline)
    except FileNotFoundError:
        print(f"error: baseline not found: {args.baseline}", file=sys.stderr)
        return 2
    try:
        cur = load_rows(args.current)
    except FileNotFoundError:
        print(f"error: current results not found: {args.current}\n"
              f"       run `bench/game.sh` first to produce it.", file=sys.stderr)
        return 2

    hard: list[str] = []   # deterministic-metric regressions (always fail)
    soft: list[str] = []   # wall-clock / RSS regressions (warn, or fail with --strict-time)
    notes: list[str] = []  # new / dropped rows

    for key in sorted(base.keys() | cur.keys()):
        prob, lang = key
        b = base.get(key)
        c = cur.get(key)
        if b is None:
            notes.append(f"+ new row: {prob}/{lang} (not in baseline)")
            continue
        if c is None:
            notes.append(f"- dropped row: {prob}/{lang} (in baseline, absent now)")
            continue

        for m in DETERMINISTIC:
            if regressed(b.get(m), c.get(m), args.alloc_tol):
                hard.append(f"{prob}/{lang}: {m} {b[m]} -> {c[m]} "
                            f"(+{(c[m] / b[m] - 1) * 100:.1f}%, tol {args.alloc_tol * 100:.0f}%)")

        if regressed(b.get("mean_secs"), c.get("mean_secs"), args.time_tol):
            soft.append(f"{prob}/{lang}: mean_secs {b['mean_secs']:.6f} -> {c['mean_secs']:.6f} "
                        f"(+{(c['mean_secs'] / b['mean_secs'] - 1) * 100:.1f}%, tol {args.time_tol * 100:.0f}%)")
        if regressed(b.get("peak_rss_kib"), c.get("peak_rss_kib"), args.time_tol):
            soft.append(f"{prob}/{lang}: peak_rss_kib {b['peak_rss_kib']} -> {c['peak_rss_kib']} "
                        f"(+{(c['peak_rss_kib'] / b['peak_rss_kib'] - 1) * 100:.1f}%, tol {args.time_tol * 100:.0f}%)")

    for n in notes:
        print(n)
    if soft:
        print("\nWALL-CLOCK / RSS regressions (advisory):")
        for s in soft:
            print(f"  ! {s}")
    if hard:
        print("\nHARD regressions (deterministic allocation/GC metrics):")
        for h in hard:
            print(f"  X {h}")

    fail = bool(hard) or (args.strict_time and bool(soft))
    if fail:
        print("\nFAIL: benchmark regression detected.")
        return 1
    if soft:
        print("\nOK (with advisory wall-clock/RSS warnings above).")
    else:
        print("\nOK: no regressions against baseline.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
