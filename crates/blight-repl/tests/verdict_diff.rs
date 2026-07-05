//! S3 verdict-differential harness (gate (c) of the Box→Rc protocol,
//! docs/roadmap-v0.1.md §S3): records, for every module in the corpus (std/, the prelude-root
//! spore/tactics/traits modules, and every standalone example), the kernel's per-form verdict
//! counts and the independent re-checker's per-global verdict (`Ok`/`Declined`/`Rejected`), and
//! compares the whole report byte-for-byte against a checked-in golden.
//!
//! The golden is captured on main *before* the `Term: Box → Rc` representation change lands; the
//! change is representation-only, so the report must be byte-identical after. Any drift — a global
//! that stops re-verifying, a Declined that becomes Rejected, a form that stops checking — is
//! exactly the regression the protocol exists to catch.
//!
//! Regenerate with `BL_BLESS=1 cargo test -p blight-repl --test verdict_diff` after an
//! *intentional* corpus change (new module, new example, new global), and review the diff.

use blight_elab::{ElabEnv, Outcome, Program};
use std::path::PathBuf;

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Absolute path to the repo's top-level `examples/` directory.
fn examples_dir() -> PathBuf {
    PathBuf::from(format!("{}/../../examples", env!("CARGO_MANIFEST_DIR")))
}

/// Absolute path to `crates/blight-prelude/`.
fn prelude_dir() -> PathBuf {
    PathBuf::from(format!(
        "{}/../blight-prelude",
        env!("CARGO_MANIFEST_DIR")
    ))
}

/// Sorted `*.bl` file names directly under `dir` (no recursion).
fn bl_files(dir: &std::path::Path) -> Vec<String> {
    let mut out: Vec<String> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {dir:?}: {e}"))
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.ends_with(".bl"))
        .collect();
    out.sort();
    out
}

/// Recursively collect every standalone `examples/**/*.bl` (the `package/` subtree is `(import …)`d
/// through a manifest, not loaded standalone — same exclusion as `examples.rs`).
fn all_example_sources() -> Vec<String> {
    fn walk(dir: &std::path::Path, base: &std::path::Path, out: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("read {dir:?}: {e}")) {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| n == "package") {
                    continue;
                }
                walk(&path, base, out);
            } else if path.extension().is_some_and(|e| e == "bl") {
                let rel = path.strip_prefix(base).expect("under examples/");
                out.push(rel.to_string_lossy().replace('\\', "/"));
            }
        }
    }
    let base = examples_dir();
    let mut out = Vec::new();
    walk(&base, &base, &mut out);
    out.sort();
    out
}

/// Cross-unit re-check cache. Every unit's closure re-elaborates the std/prelude modules it loads,
/// so the same `(name, term, type)` judgement recurs across most of the 118 units — and a few of
/// the spore globals (the refl-at-scale goldens) are individually expensive to re-check, which is
/// the very cliff S3 exists to fix. The verdict for a given judgement is deterministic, so caching
/// it changes nothing in the report; it only removes the ~100× duplication.
///
/// Keyed by the global's name plus a 64-bit hash of the judgement's `Debug` rendering — not by the
/// `Term`s themselves — so the cache stays `Send` regardless of the term representation (post-S3,
/// `Rc<Term>` is `!Send`, and this harness must run unchanged on both sides of that change).
type VerdictCache = std::sync::Mutex<std::collections::HashMap<(String, u64), &'static str>>;

fn judgement_key(name: &str, term: &blight_kernel::Term, ty: &blight_kernel::Term) -> (String, u64) {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    format!("{term:?}\x00{ty:?}").hash(&mut h);
    (name.to_string(), h.finish())
}

/// Cache lookup without computing on miss — the skip-listed units' path.
fn cached_lookup(
    cache: &VerdictCache,
    name: &str,
    term: &blight_kernel::Term,
    ty: &blight_kernel::Term,
) -> Option<&'static str> {
    let key = judgement_key(name, term, ty);
    cache.lock().unwrap().get(&key).copied()
}

fn cached_verdict(
    cache: &VerdictCache,
    sig: &blight_kernel::Signature,
    name: &str,
    term: blight_kernel::Term,
    ty: blight_kernel::Term,
    n_levels: usize,
) -> &'static str {
    let key = judgement_key(name, &term, &ty);
    if let Some(v) = cache.lock().unwrap().get(&key) {
        return v;
    }
    let j = blight_kernel::Judgement::HasType { term, ty };
    // A `define-level` global (n_levels > 0) is re-verified through the leveled door with the
    // prenex count the elaborator recorded — the kernel checked it through `check_top_leveled`
    // under the same count (T2.3). n_levels == 0 is the ordinary door.
    let verdict = match blight_recheck::recheck_judgement_leveled(sig, &j, n_levels) {
        Ok(()) => "Ok",
        Err(blight_recheck::RecheckError::Declined(_)) => "Declined",
        Err(blight_recheck::RecheckError::Rejected(m)) => {
            // A rejection is the one verdict that must never occur (the kernel accepted this
            // judgement); surface the full message on stderr for triage. The golden line stays
            // just `Rejected` so the report format is stable.
            eprintln!("REJECTED {name}: {m}");
            "Rejected"
        }
    };
    cache.lock().unwrap().insert(key, verdict);
    verdict
}

/// Units whose *own* globals cannot be re-checked in feasible time. **Empty since arc N / N5**
/// (the dead-IH fix): the four units this list carried through S3 — pinned then at
/// `json_scratch` >68 min, `palindrome` >120 s — re-check in 0.1–31 s now that `do_elim` skips
/// induction hypotheses the receiving method provably discards (the ~2^codepoint eager-IH cliff,
/// identified by the post-S3 review; docs/roadmap-v0.1.md arc N). The skip machinery stays: any
/// future over-cliff unit found by the `BL_VERDICT_DISCOVER` watchdog can be parked here with a
/// measurement while its mechanism gets the same treatment.
const RECHECK_SKIP: &[&str] = &[];

/// Load one unit of the corpus in a fresh env and render its verdict block. `label` names the unit
/// in the report; `source` is the program text to run (a `(load …)` form for prelude modules, the
/// example's own source for examples).
fn verdict_block(label: &str, source: &str, cache: &VerdictCache) -> String {
    let mut report = String::new();
    let mut env = ElabEnv::new();
    let run = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(source)
    };
    match run {
        Err(e) => {
            // No module in the corpus fails today; the arm exists so a future failure shows up as
            // golden drift (with its variant), not a harness panic.
            let variant = format!("{e:?}");
            let variant = variant.split(['(', '{']).next().unwrap_or("?").trim();
            report.push_str(&format!("FILE {label} LOAD-ERROR {variant}\n"));
            return report;
        }
        Ok(outcomes) => {
            let declared = outcomes.iter().filter(|o| matches!(o, Outcome::Declared)).count();
            let checked = outcomes.iter().filter(|o| matches!(o, Outcome::Checked(_))).count();
            report.push_str(&format!(
                "FILE {label} forms={} declared={declared} checked={checked}\n",
                outcomes.len()
            ));
        }
    }
    let sig = env.signature();
    // `BL_VERDICT_NOSKIP=1` re-checks even the skip-listed units — for re-measuring the cliff
    // (with `BL_VERDICT_ONLY`/`BL_VERDICT_DISCOVER`), never for the golden.
    let skip =
        RECHECK_SKIP.contains(&label) && std::env::var("BL_VERDICT_NOSKIP").is_err();
    for (name, term, ty) in env.typed_globals() {
        // The cache key deliberately omits the signature: a structurally identical (name, term,
        // ty) triple in this corpus always originates from the same module loaded the same way,
        // so the signature entries the judgement references are identical too.
        let verdict = if skip {
            // Deterministic despite the cache: the std/prelude closure this unit shares was
            // re-checked by earlier corpus units (chunks run in corpus order, std/prelude first),
            // so exactly the unit's own unique globals miss and report `Skipped`.
            cached_lookup(cache, &name, &term, &ty).unwrap_or("Skipped")
        } else {
            let n_levels = env.level_arity(&name).unwrap_or(0);
            cached_verdict(cache, sig, &name, term, ty, n_levels)
        };
        report.push_str(&format!("GLOBAL {label} {name} {verdict}\n"));
    }
    report
}

/// One corpus unit: (report label, program source to run).
fn corpus() -> Vec<(String, String)> {
    let mut units: Vec<(String, String)> = Vec::new();
    for m in bl_files(&prelude_dir().join("std")) {
        units.push((format!("std/{m}"), format!("(load \"std/{m}\")")));
    }
    for m in bl_files(&prelude_dir()) {
        units.push((m.clone(), format!("(load \"{m}\")")));
    }
    for rel in all_example_sources() {
        let path = examples_dir().join(&rel);
        let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
        units.push((format!("examples/{rel}"), src));
    }
    units
}

/// Render the full corpus report. Units run a chunk at a time on worker threads with large stacks
/// (same 16 MiB rationale as `examples.rs`: deep elaboration recursion on string-heavy modules);
/// the report is assembled in corpus order, so the output is deterministic.
///
/// Discovery mode (`BL_VERDICT_DISCOVER=<seconds>`): each unit runs under a watchdog with that
/// per-unit budget; units that exceed it are reported to stderr as `TIMEOUT <label>` and marked in
/// the (non-golden) report. This exists to *find* the over-cliff units to add to [`RECHECK_SKIP`]
/// without waiting out an unbounded re-check — never to produce the golden (timeouts are
/// timing-dependent; the golden must be deterministic, so it only ever ships with skip-listing by
/// label). Timed-out worker threads are abandoned, not killed (Rust threads are not cancellable);
/// they burn CPU until process exit, which a one-shot discovery run tolerates.
fn full_report() -> String {
    let mut units = corpus();
    // `BL_VERDICT_ONLY=<substring>[,<substring>…]` narrows the corpus for triage runs. Never used
    // for the golden (BLESS + ONLY together would capture a truncated report).
    if let Ok(only) = std::env::var("BL_VERDICT_ONLY") {
        let pats: Vec<&str> = only.split(',').collect();
        units.retain(|(label, _)| pats.iter().any(|p| label.contains(p)));
        assert!(
            std::env::var("BL_BLESS").is_err(),
            "refusing to bless a golden from a BL_VERDICT_ONLY-filtered corpus"
        );
    }
    let workers = std::thread::available_parallelism().map_or(4, |p| p.get().min(8));
    let discover_budget: Option<u64> = std::env::var("BL_VERDICT_DISCOVER")
        .ok()
        .and_then(|s| s.parse().ok());
    let cache = std::sync::Arc::new(std::sync::Mutex::new(std::collections::HashMap::new()));
    let mut report = String::new();
    for chunk in units.chunks(workers) {
        let blocks: Vec<String> = std::thread::scope(|s| {
            let handles: Vec<_> = chunk
                .iter()
                .map(|(label, source)| {
                    let cache = std::sync::Arc::clone(&cache);
                    let (label, source) = (label.clone(), source.clone());
                    let (tx, rx) = std::sync::mpsc::channel::<String>();
                    let worker_label = label.clone();
                    std::thread::Builder::new()
                        .stack_size(16 * 1024 * 1024)
                        .spawn(move || {
                            let t0 = std::time::Instant::now();
                            let block = verdict_block(&worker_label, &source, &cache);
                            // Progress/profiling on stderr only — never part of the golden.
                            eprintln!("unit {worker_label}: {:.1}s", t0.elapsed().as_secs_f32());
                            let _ = tx.send(block);
                        })
                        .expect("spawn corpus-unit thread");
                    // Collect on a scoped thread so the whole chunk still runs concurrently.
                    std::thread::Builder::new()
                        .spawn_scoped(s, move || match discover_budget {
                            None => rx.recv().unwrap_or_else(|_| {
                                panic!("corpus unit {label} panicked (worker dropped its channel)")
                            }),
                            Some(secs) => match rx.recv_timeout(std::time::Duration::from_secs(secs)) {
                                Ok(b) => b,
                                Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                                    eprintln!("TIMEOUT {label}");
                                    format!("FILE {label} DISCOVER-TIMEOUT\n")
                                }
                                Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                                    panic!("corpus unit {label} panicked (worker dropped its channel)")
                                }
                            },
                        })
                        .expect("spawn collector thread")
                })
                .collect();
            handles
                .into_iter()
                .zip(chunk)
                .map(|(h, (label, _))| {
                    h.join()
                        .unwrap_or_else(|_| panic!("corpus unit {label} collector panicked"))
                })
                .collect()
        });
        for b in blocks {
            report.push_str(&b);
        }
    }
    report
}

fn golden_path() -> PathBuf {
    PathBuf::from(format!(
        "{}/tests/goldens/verdict_diff.txt",
        env!("CARGO_MANIFEST_DIR")
    ))
}

/// The S3 gate: the per-global kernel/re-checker verdict report over the whole corpus is
/// byte-identical to the golden captured on main.
///
/// Ignored by default for the same reason as `differential_fast_paths_are_bit_identical`: it
/// re-checks every global of every corpus closure (many minutes in a debug build). Run it
/// explicitly — in release, where it is minutes, not tens of minutes:
/// `cargo test --release -p blight-repl --test verdict_diff -- --ignored`
#[test]
#[ignore = "slow: rechecks the whole corpus per unit; S3 gate — run explicitly with --ignored"]
fn verdict_differential_matches_golden() {
    let report = full_report();
    let path = golden_path();
    if std::env::var("BL_BLESS").is_ok() {
        std::fs::create_dir_all(path.parent().unwrap()).expect("create goldens dir");
        std::fs::write(&path, &report).unwrap_or_else(|e| panic!("write golden {path:?}: {e}"));
        eprintln!("blessed {} ({} lines)", path.display(), report.lines().count());
        return;
    }
    let golden = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "read golden {path:?}: {e}\n(first capture: BL_BLESS=1 cargo test -p blight-repl \
             --test verdict_diff)"
        )
    });
    if report != golden {
        // Byte-identical is the gate; on drift, show the first few differing lines for triage.
        let diffs: Vec<String> = golden
            .lines()
            .map(Some)
            .chain(std::iter::repeat(None))
            .zip(report.lines().map(Some).chain(std::iter::repeat(None)))
            .take_while(|(g, r)| g.is_some() || r.is_some())
            .enumerate()
            .filter(|(_, (g, r))| g != r)
            .take(10)
            .map(|(i, (g, r))| {
                format!(
                    "line {}: golden `{}` vs report `{}`",
                    i + 1,
                    g.unwrap_or("<eof>"),
                    r.unwrap_or("<eof>")
                )
            })
            .collect();
        panic!(
            "verdict differential drifted from the golden ({} first diffs shown):\n{}",
            diffs.len(),
            diffs.join("\n")
        );
    }
}
