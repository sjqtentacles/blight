//! # blight — the REPL (untrusted)
//!
//! Read a form, elaborate it to a core term, hand it to the spore to check, and report
//! accept/reject (spec §8 stage 1). M3 upgrades the REPL to the Stage-2 driver
//! ([`blight_elab::Program`]): it reads multi-line forms, threads one environment, supports
//! `(load "path")`, and accepts the typed recursive form `(define-rec name T body)`.

use std::io::{self, Write};
use std::path::{Path, PathBuf};

use blight_elab::{read_all, ElabEnv, ElabError, Outcome, Program};

/// Resolve a `(load "path")` form for CLI/REPL use. We try the real filesystem first — relative to
/// `base` (the directory of the file being built, or the cwd for the REPL) and then the cwd — so a
/// user's own files and local overrides always win. Only when no on-disk file matches do we fall
/// back to the prelude tree embedded in this binary, which is what makes the shipped examples
/// (`(load "std/nat.bl")`) work from any directory without a source checkout.
fn cli_load(base: &Path, path: &str) -> Result<String, ElabError> {
    let candidates = [base.join(path), Path::new(path).to_path_buf()];
    for cand in &candidates {
        if let Ok(src) = std::fs::read_to_string(cand) {
            return Ok(src);
        }
    }
    if let Some(src) = blight_prelude_embed::embedded(path) {
        return Ok(src.to_string());
    }
    Err(ElabError::BadForm(format!(
        "cannot load {path:?}: not found on disk (looked in {} and the current directory) \
         and not a bundled prelude module",
        base.display()
    )))
}

/// Search `base` and its ancestors for a `spore.toml`, stopping at the first match walking
/// upward (the usual "nearest project root" convention). Returns the manifest and the directory
/// it was found in (used as the manifest's own `base_dir` for resolving relative dependency
/// paths — dependency paths in `spore.toml` are relative to the manifest file, not the input
/// file, which may be in a subdirectory).
///
/// A `spore.toml` that fails to parse is reported to stderr and treated as "no manifest found"
/// rather than aborting the whole build/REPL session over a malformed manifest a user may not
/// even realize is being picked up from a parent directory.
fn find_spore_manifest(base: &Path) -> Option<(std::path::PathBuf, blight_elab::PackageManifest)> {
    let mut dir = base;
    loop {
        let candidate = dir.join("spore.toml");
        if let Ok(src) = std::fs::read_to_string(&candidate) {
            return match blight_elab::PackageManifest::parse(&src, dir) {
                Ok(manifest) => Some((dir.to_path_buf(), manifest)),
                Err(e) => {
                    eprintln!("blight: warning: {}: {e} (ignoring)", candidate.display());
                    None
                }
            };
        }
        dir = dir.parent()?;
    }
}

/// Write `<manifest_dir>/blight.lock` recording this package's and every dependency's current
/// content hash. Best-effort: a failure to write is reported to stderr but never aborts a build —
/// the lockfile is a drift-detection convenience, not part of the trust boundary.
fn write_lock(manifest_dir: &Path, manifest: &blight_elab::PackageManifest) {
    let entries = manifest.lock_entries();
    let rendered = blight_elab::PackageManifest::render_lock(&entries);
    let lock_path = manifest_dir.join("blight.lock");
    if let Err(e) = std::fs::write(&lock_path, rendered) {
        eprintln!(
            "blight: warning: could not write {}: {e}",
            lock_path.display()
        );
    }
}

/// Enforce `blight.lock` drift rejection (Wave 9 / T3) before a build proceeds: if a manifest and
/// an existing `blight.lock` are both present, and a dependency's on-disk `.bl` tree no longer
/// matches the hash recorded the last time the lock was written, abort with a specific error
/// naming the drifted dependency — a tampered or unexpectedly changed dependency is rejected, not
/// silently re-locked over. A missing lock (first build in this directory) is not drift.
///
/// Deliberately separate from [`program_with_manifest`] (which unconditionally refreshes
/// `blight.lock` as a REPL/doc-gen convenience): this check must run, and be given the chance to
/// reject, *before* anything overwrites the on-disk lock with fresh hashes — otherwise the very
/// act of building would erase the evidence of drift it's supposed to catch.
///
/// Only called from the `llvm`-gated [`run_build`], but kept unconditionally compiled (rather than
/// `#[cfg(feature = "llvm")]` like [`recheck_before_emit`]) so its logic is tested without needing
/// a system LLVM toolchain — hence the `allow` for the build-without-`llvm` configuration.
#[cfg_attr(not(feature = "llvm"), allow(dead_code))]
fn check_manifest_lock_drift(base: &Path) -> Result<(), String> {
    let Some((manifest_dir, manifest)) = find_spore_manifest(base) else {
        return Ok(());
    };
    let lock_path = manifest_dir.join("blight.lock");
    let Ok(lock_src) = std::fs::read_to_string(&lock_path) else {
        return Ok(());
    };
    manifest
        .check_lock_drift(&lock_src)
        .map_err(|e| e.to_string())
}

/// Build a resolver-equipped [`Program`] for `base` (the directory of the entry file, or the cwd
/// for the REPL): if a `spore.toml` is found, `(import …)` resolves against it and `(load …)`
/// tries the manifest first, falling back to `cli_load` for anything the manifest doesn't know
/// (`Program::with_package_and_fallback`) — so `(load "std/nat.bl")` keeps working via the
/// embedded prelude even in a manifest project. Without a manifest this is exactly the old plain
/// `cli_load`-backed resolver. When a manifest was found, also refreshes `blight.lock` next to it.
fn program_with_manifest<'a>(env: &'a mut ElabEnv, base: &'a Path) -> Program<'a> {
    match find_spore_manifest(base) {
        Some((manifest_dir, manifest)) => {
            write_lock(&manifest_dir, &manifest);
            Program::with_package_and_fallback(env, manifest, move |path: &str| {
                cli_load(base, path)
            })
        }
        None => Program::with_resolver(env, move |path: &str| cli_load(base, path)),
    }
}

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() >= 2 && args[1] == "build" {
        match run_build(&args[2..]) {
            Ok(out) => {
                eprintln!("blight: wrote {out}");
                return Ok(());
            }
            Err(msg) => {
                eprintln!("blight build: error: {msg}");
                std::process::exit(1);
            }
        }
    }
    if args.len() >= 2 && args[1] == "add" {
        match run_add(&args[2..]) {
            Ok(msg) => {
                eprintln!("blight: {msg}");
                return Ok(());
            }
            Err(msg) => {
                eprintln!("blight add: error: {msg}");
                std::process::exit(1);
            }
        }
    }
    if args.len() >= 2 && args[1] == "fmt" {
        match run_fmt(&args[2..]) {
            Ok(msg) => {
                eprintln!("blight: {msg}");
                return Ok(());
            }
            Err(msg) => {
                eprintln!("blight fmt: error: {msg}");
                std::process::exit(1);
            }
        }
    }
    if args.len() >= 2 && args[1] == "doc" {
        match run_doc(&args[2..]) {
            Ok(msg) => {
                eprintln!("blight: {msg}");
                return Ok(());
            }
            Err(msg) => {
                eprintln!("blight doc: error: {msg}");
                std::process::exit(1);
            }
        }
    }
    if args.len() >= 2 && args[1] == "publish" {
        match run_publish(&args[2..]) {
            Ok(msg) => {
                eprintln!("blight: {msg}");
                return Ok(());
            }
            Err(msg) => {
                eprintln!("blight publish: error: {msg}");
                std::process::exit(1);
            }
        }
    }
    repl()
}

/// `blight add <name> <path>` — add (or update) a local path dependency, or
/// `blight add <name> --version <ver> --registry <index>` — fetch, hash-verify, and vendor a
/// registry package, then record it as a `version` dependency (Wave 2 / A5). Either form edits the
/// current directory's `spore.toml`, creating a minimal manifest first if one doesn't exist yet;
/// the new package name defaults to the current directory's name (spec §9 M6).
///
/// The actual work is in [`run_add_in`], parameterized over the directory to operate in, so tests
/// can exercise it without mutating the test process's real (shared, concurrently-used) cwd.
fn run_add(args: &[String]) -> Result<String, String> {
    let cwd = std::env::current_dir().map_err(|e| format!("cannot read cwd: {e}"))?;
    run_add_in(&cwd, args)
}

fn run_add_in(cwd: &Path, args: &[String]) -> Result<String, String> {
    if args.iter().any(|a| a == "--git") {
        run_add_git(cwd, args)
    } else if args.iter().any(|a| a == "--version" || a == "--registry") {
        run_add_registry(cwd, args)
    } else {
        run_add_path(cwd, args)
    }
}

fn run_add_path(cwd: &Path, args: &[String]) -> Result<String, String> {
    let (name, path) = match args {
        [name, path] => (name.as_str(), path.as_str()),
        _ => return Err("usage: blight add <name> <path>".into()),
    };
    let (manifest_path, existing, default_pkg_name) = manifest_context(cwd);
    let updated = blight_elab::add_dependency(existing.as_deref(), &default_pkg_name, name, path)
        .map_err(|e| e.to_string())?;
    std::fs::write(&manifest_path, updated)
        .map_err(|e| format!("cannot write {}: {e}", manifest_path.display()))?;
    Ok(format!(
        "added dependency `{name}` (path {path:?}) to {}",
        manifest_path.display()
    ))
}

/// `blight add <name> --version <ver> --registry <index>`: `<index>` is a registry index (a
/// `file://` URI or bare filesystem path — see `blight_elab::registry`'s module doc for why remote
/// HTTP(S) registries are a deliberate follow-up rather than part of this pass). The package is
/// fetched, extracted, and hash-verified into `<manifest-dir>/.blight/registry/<name>-<ver>/`
/// *before* `spore.toml` is ever touched, so a failed/tampered fetch never leaves the manifest
/// pointing at a package that isn't actually there.
fn run_add_registry(cwd: &Path, args: &[String]) -> Result<String, String> {
    let usage = "usage: blight add <name> --version <ver> --registry <index>";
    let name = match args.first() {
        Some(n) if !n.starts_with("--") => n.as_str(),
        _ => return Err(usage.into()),
    };
    let version = find_flag_value(args, "--version").ok_or(usage)?;
    let registry = find_flag_value(args, "--registry").ok_or(usage)?;

    let (manifest_path, existing, default_pkg_name) = manifest_context(cwd);
    let manifest_dir = manifest_path
        .parent()
        .expect("spore.toml path always has a parent")
        .to_path_buf();

    let index = blight_elab::load_index(registry).map_err(|e| e.to_string())?;
    let dest = blight_elab::registry::cache_dir(&manifest_dir, name, version);
    blight_elab::fetch_and_vendor(&index, name, version, &dest).map_err(|e| e.to_string())?;

    let updated =
        blight_elab::add_registry_dependency(existing.as_deref(), &default_pkg_name, name, version)
            .map_err(|e| e.to_string())?;
    std::fs::write(&manifest_path, updated)
        .map_err(|e| format!("cannot write {}: {e}", manifest_path.display()))?;
    Ok(format!(
        "added dependency `{name}` (version {version:?}, from registry {registry:?}) to {}, \
         vendored at {}",
        manifest_path.display(),
        dest.display()
    ))
}

/// `blight add <name> --git <url> [--rev <rev>]` (Wave 9 / T3): `<url>` is cloned via a subprocess
/// `git` into `<manifest-dir>/.blight/git/<name>-<rev or HEAD>/`, checked out at `<rev>` if given,
/// then recorded as a `git` dependency. Like the registry form, the fetch happens *before*
/// `spore.toml` is touched, so a failed clone/checkout never leaves the manifest pointing at
/// source that isn't actually there.
fn run_add_git(cwd: &Path, args: &[String]) -> Result<String, String> {
    let usage = "usage: blight add <name> --git <url> [--rev <rev>]";
    let name = match args.first() {
        Some(n) if !n.starts_with("--") => n.as_str(),
        _ => return Err(usage.into()),
    };
    let url = find_flag_value(args, "--git").ok_or(usage)?;
    let rev = find_flag_value(args, "--rev");

    let (manifest_path, existing, default_pkg_name) = manifest_context(cwd);
    let manifest_dir = manifest_path
        .parent()
        .expect("spore.toml path always has a parent")
        .to_path_buf();

    let dest = blight_elab::git_cache_dir(&manifest_dir, name, rev);
    blight_elab::fetch_git_dependency(url, rev, &dest).map_err(|e| e.to_string())?;

    let updated =
        blight_elab::add_git_dependency(existing.as_deref(), &default_pkg_name, name, url, rev)
            .map_err(|e| e.to_string())?;
    std::fs::write(&manifest_path, updated)
        .map_err(|e| format!("cannot write {}: {e}", manifest_path.display()))?;
    Ok(format!(
        "added git dependency `{name}` ({url:?}{}) to {}, vendored at {}",
        rev.map(|r| format!(" @ {r}")).unwrap_or_default(),
        manifest_path.display(),
        dest.display()
    ))
}

/// The value following `flag` in `args`, e.g. `find_flag_value(["--version", "1.2.3"], "--version")
/// == Some("1.2.3")`.
fn find_flag_value<'a>(args: &'a [String], flag: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str())
}

/// `cwd`'s `spore.toml` path, its existing text (if any), and the default package name (`cwd`'s own
/// directory name) — `run_add`'s two forms both need this before editing the manifest.
fn manifest_context(cwd: &Path) -> (std::path::PathBuf, Option<String>, String) {
    let manifest_path = cwd.join("spore.toml");
    let existing = std::fs::read_to_string(&manifest_path).ok();
    let default_pkg_name = cwd
        .file_name()
        .map(|n| n.to_string_lossy().to_string())
        .unwrap_or_else(|| "project".to_string());
    (manifest_path, existing, default_pkg_name)
}

/// `blight fmt [--check] <path>...` — canonically format `.bl` source files (Wave 9 / T2). Each
/// `<path>` is either a single `.bl` file or a directory, recursively formatted. Rewrites files in
/// place by default; with `--check`, nothing is written and the command instead reports which
/// files are not already in canonical form and fails (non-zero exit), so CI can gate on it — this
/// is exactly `blight_elab::fmt`'s idempotence guarantee turned into a pass/fail check.
fn run_fmt(args: &[String]) -> Result<String, String> {
    let usage = "usage: blight fmt [--check] <path>...";
    let check = args.iter().any(|a| a == "--check");
    let paths: Vec<&str> = args
        .iter()
        .map(String::as_str)
        .filter(|a| *a != "--check")
        .collect();
    if paths.is_empty() {
        return Err(usage.into());
    }

    let mut files = Vec::new();
    for p in &paths {
        collect_bl_files(Path::new(p), &mut files).map_err(|e| format!("{p}: {e}"))?;
    }
    if files.is_empty() {
        return Err(format!("no `.bl` files found under {paths:?}"));
    }
    files.sort();

    let mut unformatted = Vec::new();
    let mut rewritten = 0usize;
    for file in &files {
        let src = std::fs::read_to_string(file)
            .map_err(|e| format!("reading {}: {e}", file.display()))?;
        let formatted =
            blight_elab::format_source(&src).map_err(|e| format!("{}: {e}", file.display()))?;
        if formatted == src {
            continue;
        }
        if check {
            unformatted.push(file.display().to_string());
        } else {
            std::fs::write(file, &formatted)
                .map_err(|e| format!("writing {}: {e}", file.display()))?;
            rewritten += 1;
        }
    }

    if check {
        if unformatted.is_empty() {
            Ok(format!("{} file(s) already formatted", files.len()))
        } else {
            Err(format!(
                "{} of {} file(s) are not formatted:\n  {}",
                unformatted.len(),
                files.len(),
                unformatted.join("\n  ")
            ))
        }
    } else {
        Ok(format!("formatted {rewritten} of {} file(s)", files.len()))
    }
}

/// Recursively collects every `.bl` file under `path` into `out` — or, if `path` is itself a `.bl`
/// file (not a directory), just that one file. Mirrors `blight-elab/tests/fmt_corpus.rs`'s walk.
fn collect_bl_files(path: &Path, out: &mut Vec<std::path::PathBuf>) -> Result<(), String> {
    let meta = std::fs::metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if meta.is_file() {
        if path.extension().is_some_and(|e| e == "bl") {
            out.push(path.to_path_buf());
        }
        return Ok(());
    }
    let entries = std::fs::read_dir(path).map_err(|e| format!("{}: {e}", path.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("{}: {e}", path.display()))?;
        let p = entry.path();
        if p.is_dir() {
            collect_bl_files(&p, out)?;
        } else if p.extension().is_some_and(|e| e == "bl") {
            out.push(p);
        }
    }
    Ok(())
}

/// `blight doc <file.bl> [-o <output.md>]` — generate Markdown documentation for `file.bl`'s
/// top-level declarations (Wave 9 / T2). Loads the file (and anything it `(load ...)`s, resolved
/// exactly as `blight build` resolves it) into a fresh environment so `blight_elab::extract_docs`
/// can ask the checker for each declaration's inferred signature; a form that fails to typecheck
/// only costs *that* form's signature; a doc pass over a not-yet-finished file is still useful for
/// its names and comments, so only a hard parse error (an unreadable file) aborts this command.
fn run_doc(args: &[String]) -> Result<String, String> {
    let usage = "usage: blight doc <file.bl> [-o <output.md>]";
    let mut input: Option<&str> = None;
    let mut output: Option<&str> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" => {
                i += 1;
                output = Some(args.get(i).ok_or("`-o` requires an argument")?.as_str());
            }
            other => {
                if input.is_some() {
                    return Err(format!("unexpected argument `{other}`"));
                }
                input = Some(other);
            }
        }
        i += 1;
    }
    let input = input.ok_or(usage)?;
    let src = std::fs::read_to_string(input).map_err(|e| format!("reading {input}: {e}"))?;

    let mut env = ElabEnv::new();
    let base = Path::new(input)
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| Path::new(".").to_path_buf());
    {
        let mut prog = program_with_manifest(&mut env, &base);
        let _ = prog.run(&src);
    }

    let entries = blight_elab::extract_docs(&env, &src).map_err(|e| format!("{input}: {e:?}"))?;
    let markdown = blight_elab::render_markdown(&entries);

    match output {
        Some(path) => {
            std::fs::write(path, &markdown).map_err(|e| format!("writing {path}: {e}"))?;
            Ok(format!("wrote {} entries to {path}", entries.len()))
        }
        None => {
            print!("{markdown}");
            Ok(format!("{} entries", entries.len()))
        }
    }
}

/// `blight publish [--registry <dir>]` (Wave 9 / T3): package the current directory's manifest
/// project's own `.bl` tree (not its dependencies) and upsert it into a local registry — the
/// write side of `blight add <name> --version <ver> --registry <index>`. `--registry` defaults to
/// `.blight/local-registry` next to the manifest when omitted, a reasonable default for
/// local/offline experimentation; a shared or CI registry should pass an explicit
/// `--registry <dir>`.
///
/// The actual work is in [`run_publish_in`], parameterized over the directory to operate in, so
/// tests can exercise it without depending on the test process's real (shared) cwd.
fn run_publish(args: &[String]) -> Result<String, String> {
    let cwd = std::env::current_dir().map_err(|e| format!("cannot read cwd: {e}"))?;
    run_publish_in(&cwd, args)
}

fn run_publish_in(cwd: &Path, args: &[String]) -> Result<String, String> {
    let (manifest_dir, manifest) = find_spore_manifest(cwd)
        .ok_or("blight publish: no spore.toml found in this directory or its ancestors")?;
    let registry_dir = match find_flag_value(args, "--registry") {
        Some(dir) => PathBuf::from(dir),
        None => manifest_dir.join(".blight").join("local-registry"),
    };
    let tarball = blight_elab::registry::publish(
        &manifest_dir,
        &manifest.name,
        &manifest.version,
        &registry_dir,
    )
    .map_err(|e| e.to_string())?;
    Ok(format!(
        "published `{}` version {} to {} (tarball {})",
        manifest.name,
        manifest.version,
        registry_dir.display(),
        tarball.display()
    ))
}

/// `blight build <file.bl> [-o <bin>]` — elaborate `file.bl`, type-check every form, then compile
/// its `main` global to a native executable (spec §7). Returns the output path on success.
///
/// Compilation requires the `llvm` feature (a system LLVM 18 + clang). Without it the subcommand
/// reports that the binary was built without native-backend support.
#[cfg(feature = "llvm")]
fn run_build(args: &[String]) -> Result<String, String> {
    let opts = parse_build_args(args)?;
    let src =
        std::fs::read_to_string(&opts.input).map_err(|e| format!("reading {}: {e}", opts.input))?;

    let mut env = ElabEnv::new();
    let base = Path::new(&opts.input)
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| Path::new(".").to_path_buf());
    // Wave 9 / T3: reject drift against `blight.lock` before anything (including
    // `program_with_manifest`'s own refresh) has a chance to overwrite the evidence of it.
    check_manifest_lock_drift(&base)?;
    let outcomes = {
        let mut prog = program_with_manifest(&mut env, &base);
        prog.run_with_diagnostics(&src)
            .map_err(|d| d.render(&src))?
    };

    // `--recheck`: before emitting any code, re-verify every kernel-accepted judgement with the
    // *independent* re-checker (`blight-recheck`). This is the spec §9 "host as seed + re-checker"
    // posture — the trusted kernel checked it, and a second, separately-implemented checker must
    // agree (or honestly decline an out-of-fragment construct) before we compile. A `Rejected`
    // here is a soundness alarm and aborts the build.
    if opts.recheck {
        recheck_before_emit(&env, &outcomes)?;
    }

    let term = env
        .global_term("main")
        .ok_or("no `main` global to compile")?
        .clone();
    let ty = env
        .global_type("main")
        .cloned()
        .unwrap_or_else(|| term.clone());
    let sig = env.signature().clone();

    let out_path = std::path::PathBuf::from(&opts.output);
    // For wasm32: try to link a runnable `.wasm` module (needs a wasm-capable clang + wasm-ld).
    // When that toolchain is absent we fall back to emitting the WebAssembly *object* only, with a
    // note — the codegen path retargets either way.
    if matches!(opts.target, blight_codegen::Target::Wasm32) {
        let work = wasm_work_dir(&out_path);
        match blight_codegen::driver::link_wasm(&term, &ty, &sig, &out_path, &work) {
            Ok(()) => return Ok(opts.output),
            Err(link_err) => {
                eprintln!(
                    "blight: wasm link unavailable ({link_err}); emitting WebAssembly object only"
                );
                blight_codegen::driver::emit_program_object_for_target(
                    &term,
                    &ty,
                    &sig,
                    &out_path,
                    opts.target,
                )?;
                return Ok(opts.output);
            }
        }
    }
    // Per-build scratch dir: derive it from the output path (not just the pid) so concurrent builds
    // in the same process (e.g. parallel tests) never share a `program.o` and clobber each other.
    let work = wasm_work_dir(&out_path);
    blight_codegen::driver::build_binary_opt(&term, &ty, &sig, &out_path, &work, opts.opt)?;
    Ok(opts.output)
}

/// Per-build scratch directory keyed by the output path + pid, so concurrent builds in the same
/// process never share intermediates.
#[cfg(feature = "llvm")]
fn wasm_work_dir(out_path: &std::path::Path) -> std::path::PathBuf {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    out_path.hash(&mut h);
    let work_key = h.finish();
    std::env::temp_dir().join(format!(
        "blight_build_{}_{:x}",
        std::process::id(),
        work_key
    ))
}

/// Re-verify every typed global and every emitted proof with the independent re-checker. Agreement
/// (`Ok`) or an honest `Declined` (out-of-fragment) passes; a `Rejected` aborts the build.
#[cfg(feature = "llvm")]
fn recheck_before_emit(env: &ElabEnv, outcomes: &[Outcome]) -> Result<(), String> {
    use blight_kernel::Judgement;
    let sig = env.signature();
    let mut checked = 0usize;
    let mut declined = 0usize;
    for (name, term, ty) in env.typed_globals() {
        let j = Judgement::HasType { term, ty };
        match blight_recheck::recheck_judgement(sig, &j) {
            Ok(()) => checked += 1,
            Err(blight_recheck::RecheckError::Declined(_)) => declined += 1,
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                return Err(format!(
                    "--recheck: independent re-checker REJECTED `{name}` (soundness alarm): {m}"
                ));
            }
        }
    }
    for o in outcomes {
        if let Outcome::Checked(p) = o {
            match blight_recheck::recheck_proof(sig, p) {
                Ok(()) => checked += 1,
                Err(blight_recheck::RecheckError::Declined(_)) => declined += 1,
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    return Err(format!(
                        "--recheck: independent re-checker REJECTED a checked form (soundness alarm): {m}"
                    ));
                }
            }
        }
    }
    eprintln!("blight: --recheck re-verified {checked} judgement(s) independently before emit");
    if declined > 0 {
        eprintln!(
            "blight: --recheck honestly DECLINED {declined} judgement(s) outside its fragment \
             (cubical `Glue`/`ua`/partial, trusted `foreign` postulates, or universe-level \
             variables — not re-verifiable)"
        );
    }
    Ok(())
}

#[cfg(not(feature = "llvm"))]
fn run_build(_args: &[String]) -> Result<String, String> {
    Err(
        "this `blight` was built without the native backend; rebuild with `--features llvm` \
         (requires LLVM 18 + clang) to use `blight build`"
            .to_string(),
    )
}

/// Parsed `blight build` options.
#[cfg(feature = "llvm")]
struct BuildOpts {
    input: String,
    output: String,
    recheck: bool,
    target: blight_codegen::Target,
    opt: blight_codegen::OptLevel,
}

/// Parse `<file.bl> [-o <bin>] [--recheck] [--target=wasm32] [--opt=<level>]`, defaulting the output
/// to the input stem (or `a.out`). With `--target=wasm32`, only a WebAssembly object is emitted (no
/// link), so the output defaults to `<stem>.wasm`. `--opt` selects the IR optimization pipeline
/// (`0`/`none`, `2`/`default` (the default), `3`/`aggressive`).
#[cfg(feature = "llvm")]
fn parse_build_args(args: &[String]) -> Result<BuildOpts, String> {
    let mut input: Option<String> = None;
    let mut output: Option<String> = None;
    let mut recheck = false;
    let mut target = blight_codegen::Target::Native;
    let mut opt = blight_codegen::OptLevel::default();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" => {
                i += 1;
                output = Some(args.get(i).ok_or("`-o` requires an argument")?.clone());
            }
            "--recheck" => {
                recheck = true;
            }
            "--target=wasm32" => {
                target = blight_codegen::Target::Wasm32;
            }
            "--target=native" => {
                target = blight_codegen::Target::Native;
            }
            other if other.starts_with("--target=") => {
                return Err(format!(
                    "unknown target `{}` (expected `native` or `wasm32`)",
                    &other["--target=".len()..]
                ));
            }
            "--opt" => {
                i += 1;
                let level = args.get(i).ok_or("`--opt` requires an argument")?;
                opt = blight_codegen::OptLevel::parse(level)?;
            }
            other if other.starts_with("--opt=") => {
                opt = blight_codegen::OptLevel::parse(&other["--opt=".len()..])?;
            }
            other => {
                if input.is_some() {
                    return Err(format!("unexpected argument `{other}`"));
                }
                input = Some(other.to_string());
            }
        }
        i += 1;
    }
    let input = input.ok_or(
        "usage: blight build <file.bl> [-o <bin>] [--recheck] [--target=wasm32] [--opt=<level>]",
    )?;
    let output = output.unwrap_or_else(|| {
        let stem = std::path::Path::new(&input)
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "a.out".to_string());
        match target {
            blight_codegen::Target::Wasm32 => format!("{stem}.wasm"),
            blight_codegen::Target::Native => stem,
        }
    });
    Ok(BuildOpts {
        input,
        output,
        recheck,
        target,
        opt,
    })
}

fn repl() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut env = ElabEnv::new();

    eprintln!(
        "blight repl (M3). enter `(defdata …)`, `(define …)`, `(define-rec name T body)`, \
         `(load \"path\")`, or `(the T e)`; multi-line forms are read until balanced; Ctrl-D to exit. \
         `:help` lists commands."
    );
    let mut buffer = String::new();
    loop {
        let prompt = if buffer.is_empty() {
            "blight> "
        } else {
            "   ...> "
        };
        write!(stdout, "{prompt}")?;
        stdout.flush()?;

        let mut line = String::new();
        if stdin.read_line(&mut line)? == 0 {
            break; // EOF
        }
        // REPL commands (only when not mid-form): `:help`, `:type <expr>`, `:load <file>`, `:quit`.
        if buffer.is_empty() && line.trim_start().starts_with(':') {
            if repl_command(&mut env, line.trim()) {
                break; // `:quit`
            }
            continue;
        }
        buffer.push_str(&line);
        // Wait for a complete (balanced) set of forms before evaluating.
        if !is_balanced(&buffer) {
            continue;
        }
        let input = std::mem::take(&mut buffer);
        if input.trim().is_empty() {
            continue;
        }
        match eval_program(&mut env, &input) {
            Ok(msgs) => {
                for m in msgs {
                    println!("{m}");
                }
            }
            Err(rendered) => println!("{rendered}"),
        }
    }
    Ok(())
}

/// Handle a REPL `:` command. Returns `true` if the REPL should exit (`:quit`).
fn repl_command(env: &mut ElabEnv, line: &str) -> bool {
    let (cmd, rest) = match line.split_once(char::is_whitespace) {
        Some((c, r)) => (c, r.trim()),
        None => (line, ""),
    };
    match cmd {
        ":quit" | ":q" => return true,
        ":help" | ":h" | ":?" => {
            println!(
                "commands:\n  \
                 :help                show this help\n  \
                 :type <expr>  (:t)   infer and print the type of an expression\n  \
                 :step <expr>         show a reduction trace and normal form for an expression\n  \
                 :load <file>  (:l)   load and check a file of forms (filesystem path)\n  \
                 :quit         (:q)   exit the repl\n\
                 anything else is read as one or more top-level forms (multi-line until balanced)."
            );
        }
        ":type" | ":t" => {
            if rest.is_empty() {
                println!("usage: :type <expr>");
            } else {
                match blight_elab::infer_type_str(env, rest) {
                    Ok(ty) => println!("{ty}"),
                    Err(rendered) => println!("{rendered}"),
                }
            }
        }
        ":step" => {
            if rest.is_empty() {
                println!("usage: :step <expr>");
            } else {
                match blight_elab::step_trace(env, rest, blight_elab::DEFAULT_STEP_BUDGET) {
                    Ok(trace) => print_step_trace(&trace),
                    Err(rendered) => println!("{rendered}"),
                }
            }
        }
        ":load" | ":l" => {
            if rest.is_empty() {
                println!("usage: :load <file>");
            } else {
                match std::fs::read_to_string(rest) {
                    Ok(src) => match eval_program(env, &src) {
                        Ok(msgs) => println!("loaded {rest}: {} form(s) ok", msgs.len()),
                        Err(rendered) => println!("{rendered}"),
                    },
                    Err(e) => println!("cannot read {rest}: {e}"),
                }
            }
        }
        other => println!("unknown command `{other}` (try `:help`)"),
    }
    false
}

/// Renders a `:step` trace (Wave 9 / T4) to stdout: one line per shown reduction, then the final
/// outcome. Never hangs the REPL — `step_trace` is metered (N2), so a divergent-under-naive-
/// reduction expression reports `BudgetExceeded` here rather than blocking.
fn print_step_trace(trace: &blight_elab::StepTrace) {
    if trace.steps.is_empty() {
        println!("(no intermediate steps shown; see the module doc for scope)");
    }
    for step in &trace.steps {
        println!("{} : {} ~> {}", step.label, step.before, step.after);
    }
    match &trace.outcome {
        blight_elab::StepOutcome::NormalForm(nf) => println!("normal form: {nf}"),
        blight_elab::StepOutcome::BudgetExceeded => {
            println!("normalization budget exceeded (the expression may diverge)")
        }
    }
}

// `:type <expr>` is backed by the shared `blight_elab::infer_type_str` (previously three
// independent copies of the same dozen lines across the REPL, `blight-lsp`, and the T2 doc
// generator; see that function's doc-comment).

/// Run one or more forms through the [`Program`] driver, returning a human-facing line per form.
/// Kept separate from `main` so it is testable. On error, returns the rendered diagnostic (with a
/// caret pointing at the offending form) ready to print.
fn eval_program(env: &mut ElabEnv, src: &str) -> Result<Vec<String>, String> {
    let base = std::env::current_dir().unwrap_or_else(|_| Path::new(".").to_path_buf());
    let mut prog = program_with_manifest(env, &base);
    let outcomes = prog.run_with_diagnostics(src).map_err(|d| d.render(src))?;
    Ok(outcomes
        .into_iter()
        .map(|o| match o {
            Outcome::Declared => "ok".to_string(),
            Outcome::Checked(proof) => blight_elab::pretty_concl(&proof),
        })
        .collect())
}

/// Whether `src` parses into a whole number of top-level forms (i.e. parens balance). Used to let
/// the REPL accept multi-line input.
fn is_balanced(src: &str) -> bool {
    read_all(src).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A scratch on-disk directory under `std::env::temp_dir()`, cleaned up on drop.
    struct TempDir {
        path: std::path::PathBuf,
    }
    impl TempDir {
        fn new(tag: &str) -> TempDir {
            let path =
                std::env::temp_dir().join(format!("blight_repl_test_{tag}_{}", std::process::id()));
            let _ = std::fs::remove_dir_all(&path);
            std::fs::create_dir_all(&path).unwrap();
            TempDir { path }
        }
    }
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.path);
        }
    }

    // ---- Wave 1 / A2: spore.toml detection, manifest+fallback resolver, blight.lock -----------

    #[test]
    fn find_spore_manifest_walks_up_ancestors() {
        let root = TempDir::new("walk_up");
        std::fs::write(
            root.path.join("spore.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        let child = root.path.join("src").join("nested");
        std::fs::create_dir_all(&child).unwrap();

        let (found_dir, manifest) =
            find_spore_manifest(&child).expect("finds the ancestor's spore.toml");
        assert_eq!(found_dir, root.path);
        assert_eq!(manifest.name, "demo");
    }

    #[test]
    fn find_spore_manifest_returns_none_without_one() {
        // `temp_dir()` itself (and everything above it, typically) has no `spore.toml`; the walk
        // must terminate at the filesystem root rather than looping or panicking.
        let dir = TempDir::new("no_manifest");
        assert!(find_spore_manifest(&dir.path).is_none());
    }

    /// The regression this whole task exists to prevent: under a manifest project (a `spore.toml`
    /// present, declaring no `std` dependency), `(load "std/nat.bl")` must still resolve via the
    /// embedded prelude fallback, exactly as it does with no manifest at all.
    #[test]
    fn program_with_manifest_falls_back_to_embedded_prelude() {
        let dir = TempDir::new("fallback");
        std::fs::write(
            dir.path.join("spore.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = program_with_manifest(&mut env, &dir.path);
            prog.run("(load \"std/nat.bl\")\n(the Nat Zero)")
                .expect("embedded prelude fallback still resolves under a manifest project")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// A manifest-backed dependency's own module resolves via the manifest, taking precedence over
    /// (and without needing) the fallback.
    #[test]
    fn program_with_manifest_resolves_a_declared_dependency() {
        let dir = TempDir::new("dep_resolve");
        let dep_dir = dir.path.join("vendor").join("mylib");
        std::fs::create_dir_all(&dep_dir).unwrap();
        std::fs::write(
            dep_dir.join("nat.bl"),
            "(defdata Nat () (Zero) (Succ (n Nat)))",
        )
        .unwrap();
        std::fs::write(
            dir.path.join("spore.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n\
             [dependencies]\nmylib = { path = \"vendor/mylib\" }\n",
        )
        .unwrap();
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = program_with_manifest(&mut env, &dir.path);
            prog.run("(load \"mylib/nat\")\n(the Nat Zero)")
                .expect("dependency module resolves via the manifest")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// Processing a buffer under a manifest project writes/refreshes `blight.lock` next to the
    /// manifest.
    #[test]
    fn program_with_manifest_writes_a_lockfile() {
        let dir = TempDir::new("lockfile");
        std::fs::write(
            dir.path.join("spore.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        let mut env = ElabEnv::new();
        {
            let mut prog = program_with_manifest(&mut env, &dir.path);
            prog.run("(defdata Unit () (unit))").expect("runs");
        }
        let lock =
            std::fs::read_to_string(dir.path.join("blight.lock")).expect("blight.lock was written");
        assert!(lock.contains("name = \"demo\""), "{lock}");
    }

    /// `check_manifest_lock_drift` (Wave 9 / T3): a dependency edited after `blight.lock` was
    /// written is reported as drift and the build-path check rejects it.
    #[test]
    fn check_manifest_lock_drift_rejects_a_tampered_dependency() {
        let dir = TempDir::new("lock_drift_reject");
        std::fs::create_dir_all(dir.path.join("vendor/std")).unwrap();
        std::fs::write(
            dir.path.join("vendor/std/nat.bl"),
            "(defdata Nat () (Zero))",
        )
        .unwrap();
        std::fs::write(
            dir.path.join("spore.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n\
             [dependencies]\nstd = { path = \"vendor/std\" }\n",
        )
        .unwrap();
        // First pass: let `program_with_manifest` write the honest lock.
        let mut env = ElabEnv::new();
        {
            let mut prog = program_with_manifest(&mut env, &dir.path);
            prog.run("(defdata Unit () (unit))").expect("runs");
        }
        // Tamper with the dependency after the lock was written.
        std::fs::write(
            dir.path.join("vendor/std/nat.bl"),
            "(defdata Nat () (Zero) (Succ (n Nat))) ; tampered post-lock",
        )
        .unwrap();

        let err = check_manifest_lock_drift(&dir.path).expect_err("drift must be rejected");
        assert!(err.contains("std") && err.contains("drift"), "{err}");
    }

    #[test]
    fn check_manifest_lock_drift_is_ok_with_no_lock_yet() {
        let dir = TempDir::new("lock_drift_no_lock");
        std::fs::write(
            dir.path.join("spore.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        assert!(check_manifest_lock_drift(&dir.path).is_ok());
    }

    /// Without a `spore.toml`, `program_with_manifest` is just the plain `cli_load` resolver (no
    /// lockfile is written, and behavior matches the pre-A2 baseline).
    #[test]
    fn program_with_manifest_is_plain_resolver_without_a_manifest() {
        let dir = TempDir::new("no_manifest_program");
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = program_with_manifest(&mut env, &dir.path);
            prog.run("(load \"std/bool.bl\")")
                .expect("embedded prelude resolves")
        };
        assert!(!outcomes.is_empty());
        assert!(!dir.path.join("blight.lock").exists());
    }

    // ---- Wave 9 / T2: `blight fmt [--check]` + `blight doc` --------------------------------

    #[test]
    fn run_fmt_rewrites_a_messy_file_in_place() {
        let dir = TempDir::new("fmt_rewrite");
        let file = dir.path.join("a.bl");
        std::fs::write(&file, "(  define a   1 )\n").unwrap();
        let msg = run_fmt(&[file.display().to_string()]).expect("formats");
        assert!(msg.contains("formatted 1"), "unexpected message: {msg}");
        assert_eq!(std::fs::read_to_string(&file).unwrap(), "(define a 1)\n");
    }

    #[test]
    fn run_fmt_check_does_not_write_and_fails_on_unformatted_input() {
        let dir = TempDir::new("fmt_check_fail");
        let file = dir.path.join("a.bl");
        let messy = "(  define a   1 )\n";
        std::fs::write(&file, messy).unwrap();
        let err = run_fmt(&["--check".to_string(), file.display().to_string()])
            .expect_err("messy input must fail --check");
        assert!(err.contains("a.bl"), "error should name the file: {err}");
        assert_eq!(
            std::fs::read_to_string(&file).unwrap(),
            messy,
            "--check must never write"
        );
    }

    #[test]
    fn run_fmt_check_passes_on_already_formatted_input() {
        let dir = TempDir::new("fmt_check_ok");
        let file = dir.path.join("a.bl");
        std::fs::write(&file, "(define a 1)\n").unwrap();
        let msg = run_fmt(&["--check".to_string(), file.display().to_string()])
            .expect("already-formatted input passes --check");
        assert!(
            msg.contains("already formatted"),
            "unexpected message: {msg}"
        );
    }

    #[test]
    fn run_fmt_recurses_into_a_directory() {
        let dir = TempDir::new("fmt_dir");
        std::fs::create_dir_all(dir.path.join("nested")).unwrap();
        std::fs::write(dir.path.join("a.bl"), "(define a   1)\n").unwrap();
        std::fs::write(dir.path.join("nested/b.bl"), "(define  b 2)\n").unwrap();
        let msg = run_fmt(&[dir.path.display().to_string()]).expect("formats both files");
        assert!(
            msg.contains("formatted 2 of 2"),
            "unexpected message: {msg}"
        );
        assert_eq!(
            std::fs::read_to_string(dir.path.join("a.bl")).unwrap(),
            "(define a 1)\n"
        );
        assert_eq!(
            std::fs::read_to_string(dir.path.join("nested/b.bl")).unwrap(),
            "(define b 2)\n"
        );
    }

    #[test]
    fn run_doc_extracts_doc_comment_and_signature_to_stdout() {
        let dir = TempDir::new("doc_stdout");
        let file = dir.path.join("a.bl");
        std::fs::write(
            &file,
            "(defdata Nat () (Zero) (Succ (n Nat)))\n\n\
             ; The number one.\n\
             (define one (the Nat (Succ Zero)))\n",
        )
        .unwrap();
        let msg = run_doc(&[file.display().to_string()]).expect("doc generation succeeds");
        assert!(msg.contains("2 entries"), "unexpected message: {msg}");
    }

    #[test]
    fn run_doc_writes_markdown_to_the_dash_o_path() {
        let dir = TempDir::new("doc_output");
        let file = dir.path.join("a.bl");
        let out = dir.path.join("a.md");
        std::fs::write(
            &file,
            "; The number one.\n(define one (the Nat (Succ Zero)))\n",
        )
        .unwrap();
        let msg = run_doc(&[
            file.display().to_string(),
            "-o".to_string(),
            out.display().to_string(),
        ])
        .expect("doc generation succeeds even though Nat/Zero/Succ are unbound here");
        assert!(msg.contains("wrote"), "unexpected message: {msg}");
        let rendered = std::fs::read_to_string(&out).unwrap();
        assert!(rendered.contains("## one"));
        assert!(rendered.contains("The number one."));
    }

    // ---- Wave 2 / A5: `blight add <name> --version <ver> --registry <index>` ------------------

    #[test]
    fn run_add_path_form_is_unchanged() {
        let dir = TempDir::new("add_path");
        let msg = run_add_in(
            &dir.path,
            &["std".to_string(), "../blight-prelude".to_string()],
        )
        .expect("path form still works");
        assert!(msg.contains("path"));
        let manifest = std::fs::read_to_string(dir.path.join("spore.toml")).unwrap();
        assert!(manifest.contains("path = \"../blight-prelude\""));
    }

    /// End to end: a registry index pointing at a real (in-memory-built) `.tar.gz` whose extracted
    /// hash matches the index's declared hash. `blight add`'s registry form fetches it, vendors it
    /// at the conventional cache path, and records a `version` dependency — which then resolves and
    /// type-checks like any other dependency.
    #[test]
    fn run_add_registry_form_fetches_vendors_and_records_a_version_dependency() {
        let dir = TempDir::new("add_registry_ok");
        let registry_dir = dir.path.join("registry_store");
        std::fs::create_dir_all(&registry_dir).unwrap();
        let tarball_path = registry_dir.join("greet-1.0.0.tar.gz");
        let tgz = blight_elab::registry::make_tar_gz(&[(
            "hello.bl",
            "(defdata Unit () (unit))\n(define x Unit unit)",
        )]);
        std::fs::write(&tarball_path, &tgz).unwrap();

        // Compute the expected hash by extracting to a scratch dir and hashing it the same way
        // `fetch_and_vendor` will, so the test doesn't hand-derive the hash function's internals.
        let scratch = dir.path.join("scratch_for_hash");
        blight_elab::registry::extract_tar_gz(&tgz, &scratch).expect("extracts");
        let expected_hash =
            blight_elab::PackageManifest::parse("[package]\nname = \"scratch\"\n", &scratch)
                .unwrap()
                .lock_entries()[0]
                .hash
                .clone();

        let index_path = registry_dir.join("index.toml");
        std::fs::write(
            &index_path,
            format!(
                "[packages.greet.\"1.0.0\"]\ntarball = {:?}\nhash = {expected_hash:?}\n",
                tarball_path.to_string_lossy()
            ),
        )
        .unwrap();

        let msg = run_add_in(
            &dir.path,
            &[
                "greet".to_string(),
                "--version".to_string(),
                "1.0.0".to_string(),
                "--registry".to_string(),
                index_path.to_string_lossy().to_string(),
            ],
        )
        .expect("registry form fetches, verifies, and records the dependency");
        assert!(msg.contains("greet"), "{msg}");
        assert!(msg.contains("1.0.0"), "{msg}");

        let manifest_src = std::fs::read_to_string(dir.path.join("spore.toml")).unwrap();
        assert!(
            manifest_src.contains("version = \"1.0.0\""),
            "{manifest_src}"
        );

        // The vendored copy actually resolves and type-checks through a full `Program`, exactly
        // like a `path` dependency would.
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = program_with_manifest(&mut env, &dir.path);
            prog.run("(load \"greet/hello\")\n(the Unit x)")
                .expect("vendored registry dependency resolves and type-checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    /// A tampered/corrupted tarball's fetch is rejected, and `spore.toml` is left untouched (no
    /// dependency is recorded for a package that failed hash verification).
    #[test]
    fn run_add_registry_form_rejects_a_hash_mismatch_and_does_not_edit_the_manifest() {
        let dir = TempDir::new("add_registry_bad_hash");
        let registry_dir = dir.path.join("registry_store");
        std::fs::create_dir_all(&registry_dir).unwrap();
        let tarball_path = registry_dir.join("bad-1.0.0.tar.gz");
        let tgz = blight_elab::registry::make_tar_gz(&[("mod.bl", "(the Unit Zero)")]);
        std::fs::write(&tarball_path, &tgz).unwrap();

        let index_path = registry_dir.join("index.toml");
        std::fs::write(
            &index_path,
            format!(
                "[packages.bad.\"1.0.0\"]\ntarball = {:?}\nhash = \"0000000000000000\"\n",
                tarball_path.to_string_lossy()
            ),
        )
        .unwrap();

        let r = run_add_in(
            &dir.path,
            &[
                "bad".to_string(),
                "--version".to_string(),
                "1.0.0".to_string(),
                "--registry".to_string(),
                index_path.to_string_lossy().to_string(),
            ],
        );
        assert!(r.is_err(), "a hash mismatch must fail the whole command");
        assert!(
            !dir.path.join("spore.toml").exists(),
            "a failed fetch must not create/edit spore.toml"
        );
    }

    #[test]
    fn run_add_registry_form_requires_version_and_registry_flags() {
        let dir = TempDir::new("add_registry_usage");
        let r = run_add_in(
            &dir.path,
            &[
                "pkg".to_string(),
                "--version".to_string(),
                "1.0.0".to_string(),
            ],
        );
        assert!(matches!(r, Err(ref m) if m.contains("usage")));
    }

    // ---- Wave 9 / T3: `blight add <name> --git <url> [--rev <rev>]` -------------------------

    /// A minimal on-disk `file://`-clonable git repository fixture, network-free (`git clone`
    /// accepts a plain local path directly): `git init`, commit one `.bl` file, return the repo
    /// directory and the commit SHA it landed on.
    struct GitFixture {
        dir: std::path::PathBuf,
        rev: String,
    }
    impl GitFixture {
        fn new(tag: &str) -> GitFixture {
            let dir = std::env::temp_dir().join(format!(
                "blight_repl_git_fixture_{tag}_{}_{}",
                std::process::id(),
                tag.len()
            ));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            let git = |args: &[&str]| {
                let status = std::process::Command::new("git")
                    .args(args)
                    .current_dir(&dir)
                    .env("GIT_AUTHOR_NAME", "blight-test")
                    .env("GIT_AUTHOR_EMAIL", "test@blight.invalid")
                    .env("GIT_COMMITTER_NAME", "blight-test")
                    .env("GIT_COMMITTER_EMAIL", "test@blight.invalid")
                    .status()
                    .expect("git executable available for the test fixture");
                assert!(status.success(), "git {args:?} failed");
            };
            git(&["init", "--quiet", "-b", "main"]);
            std::fs::write(
                dir.join("hello.bl"),
                "(defdata Unit () (unit))\n(define x Unit unit)",
            )
            .unwrap();
            git(&["add", "."]);
            git(&["commit", "--quiet", "-m", "fixture commit"]);
            let rev = String::from_utf8(
                std::process::Command::new("git")
                    .args(["rev-parse", "HEAD"])
                    .current_dir(&dir)
                    .output()
                    .unwrap()
                    .stdout,
            )
            .unwrap()
            .trim()
            .to_string();
            GitFixture { dir, rev }
        }
    }
    impl Drop for GitFixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    /// End to end: `blight add`'s git form clones a real (if local) git repository at a pinned
    /// rev, vendors it at the conventional cache path, and records a `git` dependency — which
    /// then resolves and type-checks like any other dependency.
    #[test]
    fn run_add_git_form_clones_vendors_and_records_a_git_dependency() {
        let repo = GitFixture::new("add_git_ok");
        let dir = TempDir::new("add_git_ok_project");

        let msg = run_add_in(
            &dir.path,
            &[
                "greet".to_string(),
                "--git".to_string(),
                repo.dir.to_string_lossy().to_string(),
                "--rev".to_string(),
                repo.rev.clone(),
            ],
        )
        .expect("git form clones, checks out, and records the dependency");
        assert!(msg.contains("greet"), "{msg}");
        assert!(msg.contains(&repo.rev), "{msg}");

        let manifest_src = std::fs::read_to_string(dir.path.join("spore.toml")).unwrap();
        assert!(manifest_src.contains("git ="), "{manifest_src}");
        assert!(manifest_src.contains(&repo.rev), "{manifest_src}");

        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = program_with_manifest(&mut env, &dir.path);
            prog.run("(load \"greet/hello\")\n(the Unit x)")
                .expect("vendored git dependency resolves and type-checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));
    }

    #[test]
    fn run_add_git_form_rejects_an_unknown_rev_and_does_not_edit_the_manifest() {
        let repo = GitFixture::new("add_git_bad_rev");
        let dir = TempDir::new("add_git_bad_rev_project");

        let r = run_add_in(
            &dir.path,
            &[
                "greet".to_string(),
                "--git".to_string(),
                repo.dir.to_string_lossy().to_string(),
                "--rev".to_string(),
                "0000000000000000000000000000000000dead".to_string(),
            ],
        );
        assert!(
            r.is_err(),
            "an unresolvable rev must fail the whole command"
        );
        assert!(
            !dir.path.join("spore.toml").exists(),
            "a failed clone/checkout must not create/edit spore.toml"
        );
    }

    #[test]
    fn run_add_git_form_requires_the_git_flag_value() {
        let dir = TempDir::new("add_git_usage");
        let r = run_add_in(&dir.path, &["pkg".to_string(), "--git".to_string()]);
        assert!(matches!(r, Err(ref m) if m.contains("usage")));
    }

    // ---- Wave 9 / T3: `blight publish [--registry <dir>]` -----------------------------------

    /// End to end through the CLI layer: `blight publish` packages a manifest project, then
    /// `blight add --version --registry` (a *separate* consumer project) fetches it back,
    /// verifies its hash, and the vendored copy type-checks — the full publish/consume loop with
    /// no direct calls into `blight_elab::registry` from the test itself.
    #[test]
    fn run_publish_then_add_registers_and_type_checks() {
        let publisher_dir = TempDir::new("publish_cli_publisher");
        std::fs::write(
            publisher_dir.path.join("spore.toml"),
            "[package]\nname = \"greet\"\nversion = \"1.0.0\"\n",
        )
        .unwrap();
        std::fs::write(
            publisher_dir.path.join("hello.bl"),
            "(defdata Unit () (unit))\n(define x Unit unit)",
        )
        .unwrap();

        let registry_dir = std::env::temp_dir().join(format!(
            "blight_publish_cli_registry_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&registry_dir);

        let publish_msg = run_publish_in(
            &publisher_dir.path,
            &[
                "--registry".to_string(),
                registry_dir.to_string_lossy().to_string(),
            ],
        )
        .expect("publish succeeds");
        assert!(publish_msg.contains("greet"), "{publish_msg}");
        assert!(publish_msg.contains("1.0.0"), "{publish_msg}");

        let consumer_dir = TempDir::new("publish_cli_consumer");
        let index_path = registry_dir.join("index.toml");
        let add_msg = run_add_in(
            &consumer_dir.path,
            &[
                "greet".to_string(),
                "--version".to_string(),
                "1.0.0".to_string(),
                "--registry".to_string(),
                index_path.to_string_lossy().to_string(),
            ],
        )
        .expect("consumer fetches the freshly published package");
        assert!(add_msg.contains("greet"), "{add_msg}");

        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = program_with_manifest(&mut env, &consumer_dir.path);
            prog.run("(load \"greet/hello\")\n(the Unit x)")
                .expect("published-then-fetched dependency resolves and type-checks")
        };
        assert!(matches!(outcomes.last(), Some(Outcome::Checked(_))));

        let _ = std::fs::remove_dir_all(&registry_dir);
    }

    #[test]
    fn run_publish_requires_a_manifest() {
        let dir = TempDir::new("publish_no_manifest");
        let r = run_publish_in(&dir.path, &[]);
        assert!(matches!(r, Err(ref m) if m.contains("spore.toml")));
    }

    #[test]
    fn run_publish_defaults_the_registry_dir_next_to_the_manifest() {
        let dir = TempDir::new("publish_default_registry");
        std::fs::write(
            dir.path.join("spore.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        std::fs::write(dir.path.join("main.bl"), "(the Unit Zero)").unwrap();
        run_publish_in(&dir.path, &[]).expect("publishes with the default registry dir");
        assert!(dir
            .path
            .join(".blight")
            .join("local-registry")
            .join("index.toml")
            .exists());
    }

    /// A typed recursive definition entered across (logical) lines elaborates at the REPL.
    #[test]
    fn repl_multiline_define_rec() {
        let mut env = ElabEnv::new();
        eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat");
        let src = "(define-rec double\n\
                     (Pi ((n Nat)) Nat)\n\
                     (lam (n) (match n [(Zero) Zero] [(Succ k) (Succ (Succ (double k)))])))";
        let msgs = eval_program(&mut env, src).expect("define-rec elaborates");
        assert_eq!(msgs, vec!["ok".to_string()]);
        assert!(env.global_term("double").is_some());
    }

    /// Regression: a `deftotal` recursive call on a sub-term exposed by a *nested* match (e.g.
    /// `fib (n-2)`) is non-structural and must be **rejected**, not silently bound to the inner
    /// match's induction hypothesis. The latter once miscompiled `fib 5` to `65` (in the kernel
    /// itself). The immediate-predecessor recursion in the same shape must still be accepted, proving
    /// the gate rejects only the nested (field-scrutinee) IH, not the parameter one.
    #[test]
    fn deftotal_rejects_nonstructural_nested_recursion() {
        let mut env = ElabEnv::new();
        eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat");
        // `bad k`: k = n-2 reached by matching the field `m` — outside the structural fragment.
        let bad = "(deftotal bad (Pi ((n Nat)) Nat)\n\
                     (lam (n) (match n\n\
                       [(Zero) Zero]\n\
                       [(Succ m) (match m\n\
                         [(Zero) (Succ Zero)]\n\
                         [(Succ k) (bad k)])])))";
        let err =
            eval_program(&mut env, bad).expect_err("non-structural deftotal must be rejected");
        assert!(
            err.contains("structural sub-term"),
            "rejection names the structural boundary: {err}"
        );
        // Control: recursing on the immediate predecessor `m` (a parameter's field) is structural.
        let good = "(deftotal countdown (Pi ((n Nat)) Nat)\n\
                      (lam (n) (match n [(Zero) Zero] [(Succ m) (Succ (countdown m))])))";
        eval_program(&mut env, good).expect("immediate-predecessor recursion still elaborates");
        assert!(env.global_term("countdown").is_some());
    }

    /// An incomplete form is detected as unbalanced; once closed it parses.
    #[test]
    fn balance_detection() {
        assert!(!is_balanced("(define-rec double"));
        assert!(is_balanced("(the Nat Zero)"));
    }

    /// An elaboration error (unbound name) renders as a caret diagnostic pointing at the offending
    /// top-level form, not a raw `Debug` dump.
    #[test]
    fn elab_error_renders_a_caret() {
        let mut env = ElabEnv::new();
        let err = eval_program(&mut env, "(the Nat nope)").expect_err("nope is unbound");
        assert!(err.starts_with("error: "), "rendered, got: {err}");
        assert!(
            err.contains("unbound") || err.contains("nope"),
            "names the issue: {err}"
        );
        assert!(err.contains('^'), "has a caret underline: {err}");
        assert!(
            err.contains("(the Nat nope)"),
            "quotes the source line: {err}"
        );
    }

    /// A reader error (unterminated list) renders with a caret too.
    #[test]
    fn reader_error_renders_a_caret() {
        let mut env = ElabEnv::new();
        let err = eval_program(&mut env, "(the Nat").expect_err("unterminated");
        assert!(err.starts_with("error: "), "rendered, got: {err}");
        assert!(err.contains('^'), "has a caret underline: {err}");
    }

    /// A checked conclusion pretty-prints via the surface re-sugaring rather than `Debug`.
    #[test]
    fn checked_conclusion_pretty_prints() {
        let mut env = ElabEnv::new();
        eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat");
        let msgs = eval_program(&mut env, "(the Nat (Succ Zero))").expect("checks");
        assert_eq!(msgs.len(), 1);
        assert!(
            msgs[0].contains('⊢'),
            "turnstile in conclusion: {}",
            msgs[0]
        );
        // E1: a canonical Nat numeral re-sugars to decimal in pretty-printed output.
        assert!(msgs[0].contains('1'), "pretty term: {}", msgs[0]);
        assert!(!msgs[0].contains("Con("), "no Debug leakage: {}", msgs[0]);
    }

    /// `:type` infers and pretty-prints the type of an expression against the REPL env.
    #[test]
    fn repl_type_command_infers() {
        let mut env = ElabEnv::new();
        eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat");
        let ty = blight_elab::infer_type_str(&env, "(Succ Zero)").expect("infers");
        assert_eq!(ty, "Nat", "Succ Zero : Nat, got {ty}");
        // An ill-typed / un-inferable expression reports an error string, not a panic.
        let err = blight_elab::infer_type_str(&env, "(Succ Succ)").expect_err("ill-typed");
        assert!(!err.is_empty(), "non-empty error: {err}");
    }

    /// `:step` (Wave 9 / T4) is backed by `blight_elab::step_trace`; the REPL command itself only
    /// needs to route to it, handle the empty-argument usage message, and never exit the REPL.
    #[test]
    fn repl_step_command_traces_and_never_exits() {
        let mut env = ElabEnv::new();
        eval_program(
            &mut env,
            "(defdata Nat () (Zero) (Succ (n Nat)))\n\
             (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n  \
               (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))",
        )
        .expect("nat + plus");
        assert!(
            !repl_command(&mut env, ":step (plus Zero (Succ Zero))"),
            ":step does not exit"
        );
        assert!(!repl_command(&mut env, ":step"), "usage message, no panic");
        // An unbound expression reports its error string rather than panicking the REPL.
        assert!(!repl_command(&mut env, ":step nope"));
    }

    /// `:quit` returns the exit signal; an unknown command does not.
    #[test]
    fn repl_command_quit_and_unknown() {
        let mut env = ElabEnv::new();
        assert!(repl_command(&mut env, ":quit"), ":quit exits");
        assert!(repl_command(&mut env, ":q"), ":q exits");
        assert!(!repl_command(&mut env, ":help"), ":help does not exit");
        assert!(!repl_command(&mut env, ":bogus"), "unknown does not exit");
    }

    /// A realistic REPL *session*: state accumulates across successive inputs (the env is threaded),
    /// a mid-session error does NOT corrupt that state, and evaluation continues afterwards. This is
    /// the property the interactive loop relies on — each `eval_program` call mutates the same `env`.
    #[test]
    fn repl_session_persists_state_and_recovers_from_errors() {
        let mut env = ElabEnv::new();
        // Turn 1: declare Nat.
        assert_eq!(
            eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat"),
            vec!["ok".to_string()]
        );
        // Turn 2: a recursive definition referring to the earlier declaration.
        eval_program(
            &mut env,
            "(define-rec plus (Pi ((a Nat) (b Nat)) Nat) \
               (lam (a b) (match a [(Zero) b] [(Succ k) (Succ (plus k b))])))",
        )
        .expect("plus");
        // Turn 3: a genuine error — `plus` applied to a non-Nat. The session must surface it as a
        // rendered diagnostic, not a panic.
        let err = eval_program(&mut env, "(the Nat (plus Zero nope))").expect_err("nope unbound");
        assert!(err.starts_with("error: "), "rendered diagnostic: {err}");
        // Turn 4: the env is intact — both prior definitions survive and a good term still checks.
        assert!(env.global_term("plus").is_some(), "plus survived the error");
        let msgs = eval_program(&mut env, "(the Nat (plus (Succ Zero) (Succ Zero)))")
            .expect("good term after the error still checks");
        assert_eq!(msgs.len(), 1);
        assert!(msgs[0].contains('⊢'), "checked conclusion: {}", msgs[0]);
        // Turn 5: `:type` sees the accumulated session env.
        assert_eq!(
            blight_elab::infer_type_str(&env, "(plus Zero Zero)").expect("infers"),
            "Nat"
        );
    }

    /// Several forms submitted in one input each yield their own result line, in order.
    #[test]
    fn repl_multiple_forms_one_input_each_ok() {
        let mut env = ElabEnv::new();
        let msgs = eval_program(
            &mut env,
            "(defdata Nat () (Zero) (Succ (n Nat)))\n(define one Nat (Succ Zero))\n(the Nat one)",
        )
        .expect("three forms");
        assert_eq!(msgs.len(), 3, "one result line per form: {msgs:?}");
        assert_eq!(msgs[0], "ok");
        assert_eq!(msgs[1], "ok");
        assert!(
            msgs[2].contains('⊢'),
            "the third form is a checked conclusion: {}",
            msgs[2]
        );
    }

    /// `:load <file>` reads a real file of forms into the session env and reports the form count;
    /// a missing file reports an error rather than panicking.
    #[test]
    fn repl_load_command_reads_a_file() {
        let dir = std::env::temp_dir().join(format!("blight_replload_{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("scratch dir");
        let file = dir.join("session.bl");
        std::fs::write(
            &file,
            "(defdata Nat () (Zero) (Succ (n Nat)))\n(define two Nat (Succ (Succ Zero)))\n",
        )
        .expect("write session file");

        let mut env = ElabEnv::new();
        // `:load` does not exit the REPL and pulls the file's definitions into the env.
        assert!(!repl_command(
            &mut env,
            &format!(":load {}", file.display())
        ));
        assert!(
            env.global_term("two").is_some(),
            "`:load` brought the file's definitions into the session env"
        );
        // A non-existent path is handled gracefully (no panic, no exit).
        assert!(!repl_command(&mut env, ":load /no/such/blight/file.bl"));

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// `blight build file.bl -o bin` elaborates the file and produces a runnable native binary
    /// whose `main` evaluates to `Succ Zero` (printed as the numeral `1`).
    #[cfg(feature = "llvm")]
    #[test]
    fn build_command_produces_binary() {
        let dir = std::env::temp_dir().join(format!("blight_buildcli_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define main Nat (Succ Zero))\n";
        let file = dir.join("prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("prog");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ])
        .expect("build succeeds");
        assert_eq!(out, bin.to_string_lossy());
        assert!(bin.exists(), "binary was produced");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "binary runs");
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert_eq!(stdout.trim(), "1", "main = Succ Zero prints as 1");
    }

    /// `blight build --opt 3 …` runs the aggressive IR pipeline and still produces a correct binary
    /// (musttail survives the pipeline; result unchanged). Also exercises the `--opt=<level>` spelling
    /// and the rejection of an unknown level.
    #[cfg(feature = "llvm")]
    #[test]
    fn build_command_opt_flag() {
        let dir = std::env::temp_dir().join(format!("blight_buildopt_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define main Nat (Succ (Succ Zero)))\n";
        let file = dir.join("prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("prog_o3");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
            "--opt".to_string(),
            "3".to_string(),
        ])
        .expect("build with --opt 3 succeeds");
        assert_eq!(out, bin.to_string_lossy());
        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "binary runs");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            "2",
            "main = Succ (Succ Zero) prints as 2 at --opt 3"
        );

        // The `--opt=<level>` spelling parses too.
        assert!(parse_build_args(&["x.bl".into(), "--opt=2".into()])
            .is_ok_and(|o| o.opt == blight_codegen::OptLevel::Default));
        // An unknown level is rejected.
        assert!(parse_build_args(&["x.bl".into(), "--opt".into(), "O2".into()]).is_err());
    }

    /// A `main` that uses `(region r …)` builds and runs — regression for the missing `arena.c`
    /// link (M6 Phase C). The region scope makes the backend emit arena allocations, whose runtime
    /// (`bl_arena_*`) lives in `arena.c`; before the driver fix the link failed with undefined
    /// `bl_arena_*` symbols. `Rgn`/`region` come from the prelude (inlined here so the build needs
    /// no `(load …)` resolver).
    #[cfg(feature = "llvm")]
    #[test]
    fn build_command_compiles_region_main() {
        let dir = std::env::temp_dir().join(format!("blight_regionbuild_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (defdata Rgn () (rgn-tok))\n\
                   (define main Nat (region r (Succ Zero)))\n";
        let file = dir.join("region_prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("region_prog");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ])
        .expect("region-using main builds (arena.c is linked)");
        assert_eq!(out, bin.to_string_lossy());
        assert!(bin.exists(), "region binary was produced");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "region binary runs");
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert_eq!(
            stdout.trim(),
            "1",
            "main = (region r (Succ Zero)) prints as 1"
        );
    }

    /// `blight build --recheck` re-verifies every kernel-accepted judgement with the *independent*
    /// `blight-recheck` checker before emitting code, then still produces a runnable binary (M6
    /// Phase C: the host as seed + re-checker). A `Rejected` would abort the build; here all
    /// judgements agree, so the binary is produced and runs.
    #[cfg(feature = "llvm")]
    #[test]
    fn build_rechecks_before_emit() {
        let dir = std::env::temp_dir().join(format!("blight_recheckbuild_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        // A typed global (`two`) plus `main`, so `--recheck` independently re-checks more than just
        // a trivial literal.
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define two Nat (Succ (Succ Zero)))\n\
                   (define main Nat (Succ Zero))\n";
        let file = dir.join("prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("prog");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
            "--recheck".to_string(),
        ])
        .expect("build with --recheck succeeds (independent checker agrees)");
        assert_eq!(out, bin.to_string_lossy());
        assert!(bin.exists(), "binary produced after independent re-check");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "re-checked binary runs");
        assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "1");
    }

    /// A self-hosting round-trip oracle (M6 Phase C): compile a *non-trivial* `.bl` program — Nat
    /// arithmetic via a recursive `plus` — to native with `--recheck`, run it, and assert the
    /// printed result. This demonstrates the bootstrap host acting purely as seed + re-checker for
    /// a real program: the kernel checks it, the independent re-checker re-verifies it, then it
    /// compiles and runs with the expected numeric output.
    #[cfg(feature = "llvm")]
    #[test]
    fn self_host_seed_roundtrip() {
        let dir = std::env::temp_dir().join(format!("blight_selfhost_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        // plus 2 1 = 3.
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n\
                     (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))\n\
                   (define main Nat (plus (Succ (Succ Zero)) (Succ Zero)))\n";
        let file = dir.join("arith.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("arith");

        run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
            "--recheck".to_string(),
        ])
        .expect("the host (seed + re-checker) compiles and re-verifies the arithmetic program");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "round-trip binary runs");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            "3",
            "plus 2 1 evaluates to 3 natively"
        );
    }

    /// `blight build --target=wasm32` emits a WebAssembly object (no link). The codegen path
    /// retargets to `wasm32-unknown-unknown`; we assert the output begins with the WebAssembly
    /// object magic bytes `\0asm` (M6 D3).
    #[cfg(feature = "llvm")]
    #[test]
    fn emits_wasm_object_for_main() {
        let dir = std::env::temp_dir().join(format!("blight_wasm_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define main Nat (Succ (Succ Zero)))\n";
        let file = dir.join("wasm_prog.bl");
        std::fs::write(&file, src).unwrap();
        let obj = dir.join("wasm_prog.wasm");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            obj.to_string_lossy().to_string(),
            "--target=wasm32".to_string(),
        ])
        .expect("wasm32 object emission succeeds");
        assert_eq!(out, obj.to_string_lossy());
        assert!(obj.exists(), "wasm object was produced");

        let bytes = std::fs::read(&obj).expect("read wasm object");
        assert!(
            bytes.starts_with(&[0x00, 0x61, 0x73, 0x6d]),
            "output begins with the WebAssembly magic `\\0asm` (got {:?})",
            &bytes[..bytes.len().min(8)]
        );
    }

    /// End-to-end regression for the shipped examples (the user-visible `blight build … && ./out`
    /// flow): build the *real* `examples/*.bl` files — whose `(load "std/…")` forms resolve against
    /// the prelude **embedded in this binary**, so the build works from any directory with no source
    /// checkout — re-check them independently, run them, and assert their numeric output. This guards
    /// the three bugs that previously broke the examples: the prelude not being found from the CLI,
    /// the indexed-`Vec` eliminator miscompiling (method lambdas wrongly lowered to `Fix`), and the
    /// indexed-`Elim` motive the re-checker rejected.
    #[cfg(feature = "llvm")]
    fn build_and_run_example(name: &str, expected_stdout: &str) {
        build_and_run_example_opts(name, expected_stdout, true);
    }

    /// As [`build_and_run_example`], but `recheck` selects whether the independent re-checker runs
    /// during the native build. It defaults to on (the strong guarantee). It is turned off only for
    /// examples whose *concrete* result forces a pathologically large normal form through the
    /// re-checker — e.g. `palindrome.bl`, which compares a real word against its reverse where each
    /// letter is a ~100-deep unary-`Nat` codepoint (std/string.bl). The example's *definitions*
    /// still re-check via the load corpus (`examples.rs`); only forcing the giant concrete value is
    /// skipped here, since it is a normalization-cost issue (the honest unary-`Nat` tax), not a
    /// soundness rejection.
    #[cfg(feature = "llvm")]
    fn build_and_run_example_opts(name: &str, expected_stdout: &str, recheck: bool) {
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join(name);
        let dir = std::env::temp_dir().join(format!(
            "blight_example_{}_{}",
            name.replace('.', "_"),
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");

        // Build on a thread with a generous stack. Test threads default to a small (~2 MiB) stack,
        // but the build pipeline recurses structurally over the program term — and with strings
        // modeled as unary-`Nat` codepoint chains (std/string.bl), even a short literal is a deep
        // term. The real CLI runs the build on the main thread (default ~8 MiB), so this mirrors
        // that; it does not change the compiler, only the harness's stack budget.
        let mut build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        if recheck {
            build_args.push("--recheck".to_string());
        }
        let name_owned = name.to_string();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_build(&build_args).unwrap_or_else(|e| {
                    panic!("example {name_owned} builds (seed + independent re-checker): {e}")
                });
            })
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        assert!(bin.exists(), "example {name} produced a binary");

        let run = std::process::Command::new(&bin)
            .output()
            .unwrap_or_else(|e| panic!("run example {name}: {e}"));
        assert!(run.status.success(), "example {name} runs successfully");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            expected_stdout,
            "example {name} prints {expected_stdout}"
        );
    }

    /// As [`build_and_run_example_opts`] but feeds `stdin` to the built binary and compares the raw
    /// (untrimmed) stdout. Used for the `Console`-effect examples (echo/greet), whose output is
    /// produced by `perform print` and read back here exactly as written. These build without
    /// `--recheck` to keep this a lean runtime-execution test; `--recheck` agreement on effects is
    /// separately covered by the `*_example_loads` tests (effects are now re-checked at the type
    /// level, not declined).
    #[cfg(feature = "llvm")]
    fn build_and_run_example_stdin(name: &str, stdin: &str, expected_stdout: &str) {
        use std::io::Write;
        use std::process::Stdio;
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join(name);
        let dir = std::env::temp_dir().join(format!(
            "blight_example_{}_{}",
            name.replace('.', "_"),
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        let name_owned = name.to_string();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_build(&build_args)
                    .unwrap_or_else(|e| panic!("example {name_owned} builds: {e}"));
            })
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        assert!(bin.exists(), "example {name} produced a binary");

        let mut child = std::process::Command::new(&bin)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| panic!("spawn example {name}: {e}"));
        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(stdin.as_bytes())
            .unwrap();
        let run = child
            .wait_with_output()
            .unwrap_or_else(|e| panic!("run example {name}: {e}"));
        assert!(run.status.success(), "example {name} runs successfully");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            expected_stdout,
            "example {name} echoes its scripted stdin"
        );
    }

    /// P4.1 corpus / observational-invisibility: the mark-compact old generation must be invisible to
    /// a real compiled program. We build a GC-allocating example once, then run the *same* binary
    /// under both `BL_GC_OLDGEN` modes with a deliberately tiny heap (forcing repeated major
    /// collections / compactions), and assert identical stdout — the compaction changes only memory
    /// footprint, never an observable result.
    #[cfg(feature = "llvm")]
    fn assert_oldgen_modes_identical(name: &str, expected_stdout: &str) {
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join(name);
        let dir = std::env::temp_dir().join(format!(
            "blight_oldgen_{}_{}",
            name.replace('.', "_"),
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        let name_owned = name.to_string();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_build(&build_args)
                    .unwrap_or_else(|e| panic!("example {name_owned} builds: {e}"));
            })
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        assert!(bin.exists(), "example {name} produced a binary");

        // A tiny heap so even a modest allocator forces majors (and, in compact mode, compactions).
        let tiny = [
            ("BL_GC_OLD_BYTES", "65536"),
            ("BL_GC_NURSERY_BYTES", "16384"),
        ];
        let mut outs = Vec::new();
        for mode in ["semispace", "compact"] {
            let run = std::process::Command::new(&bin)
                .env("BL_GC_OLDGEN", mode)
                .envs(tiny.iter().copied())
                .output()
                .unwrap_or_else(|e| panic!("run example {name} ({mode}): {e}"));
            assert!(
                run.status.success(),
                "example {name} runs under BL_GC_OLDGEN={mode}"
            );
            let out = String::from_utf8_lossy(&run.stdout).trim().to_string();
            assert_eq!(
                out, expected_stdout,
                "example {name} ({mode}) prints {expected_stdout}"
            );
            outs.push(out);
        }
        assert_eq!(
            outs[0], outs[1],
            "example {name} must be bit-identical across the semi-space and compacting old generations"
        );
    }

    /// Tree allocation churn (`tree_sum`) is observationally identical under both old-generation modes.
    #[cfg(feature = "llvm")]
    #[test]
    fn oldgen_modes_identical_tree_sum() {
        assert_oldgen_modes_identical("tree_sum.bl", "6");
    }

    /// A linear non-tail list fold (`list_sum`) is observationally identical under both old-gen modes.
    #[cfg(feature = "llvm")]
    #[test]
    fn oldgen_modes_identical_list_sum() {
        assert_oldgen_modes_identical("list_sum.bl", "6");
    }

    // ===================================================================================
    // B1 — the standing differential-correctness harness (Blight Grand Arc, Phase 1).
    //
    // The zero-TCB performance mandate is: every backend fast path (the `Nat`/`Float` recognizer,
    // monomorphization, the SRA unbox pass, cross-object LTO, and — added by the Grand Arc — the
    // escaping-product *flattening* of A1) is a pure *representation* choice that MUST be
    // observationally identical to the slow, inductive semantics. A wrong optimization may only ever
    // produce a wrong *number*, never a false *proof*; this harness is the mechanical enforcement of
    // that promise. It compiles the real example corpus under every fast-path on/off configuration
    // and asserts the produced binary's stdout is *bit-identical* to the all-fast-paths-on build.
    //
    // The `BL_NO_*` flags are process-global env vars read inside `driver.rs`/`mono.rs` during the
    // build, and `cargo test` runs test fns on parallel threads — so toggling them must be serialized.
    // `DIFF_ENV_LOCK` makes the set-env → build → unset-env window mutually exclusive across the
    // whole test binary; the *run* of the produced binary is outside the lock (it reads no flags).
    // ===================================================================================

    /// The fast-path env flags this harness toggles. Each names a behavior-preserving backend
    /// optimization that is *documented bit-identical* against its inductive/slow fallback
    /// (docs/roadmap-post-m6.md: M20 `BL_NO_NATPRIM`, M27 `BL_NO_UNBOX`, M22 `BL_NO_LTO`, A1
    /// `BL_NO_FLATTEN`, A2 `BL_NO_STRPACK`, A3 `BL_NO_SPINEFUSE`, A4 `BL_NO_INLINE`, A5 region escape
    /// analysis `BL_NO_AUTOREGION`, P3 `BL_NO_ELIMLOOP`, P6.1 CSE `BL_NO_CSE`, P6.2 compile-time
    /// normalization `BL_NO_CTNORM`, P7 deforestation/fusion `BL_NO_FUSION`, P10 defunctionalization
    /// `BL_NO_DEFUNC`, the P10-follow-on capture-aware specialization `BL_NO_CAPSPEC`, and Arc II Wave
    /// 10 / P4 auto-parallelism `BL_NO_AUTOPAR` — analysis-only today, so trivially bit-identical; see
    /// `blight_codegen::autopar` module docs).
    /// `BL_NO_UNBOX`/`BL_NO_FLATTEN` also gate the A1′ *post-mono* layout
    /// pass (crates/blight-codegen/src/layout.rs), so the matrix covers it for free.
    ///
    /// `BL_NO_MONO` is *deliberately excluded*: monomorphization is a **bisecting diagnostic**, not a
    /// behavior-preserving A/B switch. It does correctness-critical work the rest of the pipeline can
    /// depend on (dictionary `Proj` resolution, known-closure specialization), so disabling it is not
    /// promised to be observationally identical — and indeed it is not: building `mergesort.bl` (a
    /// higher-order continuation-passing fuel sort) with `BL_NO_MONO` SIGBUSes in the
    /// un-monomorphized closure path, while every other corpus program is unaffected. That is a real
    /// latent backend bug in the un-specialized higher-order path, tracked separately from this
    /// harness (whose mandate is the *fast-path equivalence* guarantee, not mono's load-bearingness).
    #[cfg(feature = "llvm")]
    const DIFF_FLAGS: &[&str] = &[
        "BL_NO_NATPRIM",
        "BL_NO_UNBOX",
        "BL_NO_LTO",
        "BL_NO_FLATTEN",
        "BL_NO_STRPACK",
        "BL_NO_SPINEFUSE",
        "BL_NO_INLINE",
        "BL_NO_AUTOREGION",
        "BL_NO_ALIASMETA",
        "BL_NO_DIRECTCALL",
        "BL_NO_ARITYRAISE",
        "BL_NO_ELIMLOOP",
        "BL_NO_CSE",
        "BL_NO_CTNORM",
        "BL_NO_FUSION",
        "BL_NO_DEFUNC",
        "BL_NO_CAPSPEC",
        // Wave 10 / P4 auto-parallelism (crate::autopar): analysis-only today (see its module docs
        // for why the actual parallel-rewrite half is a documented, deferred sharpened negative), so
        // this flag currently only skips a diagnostic scan — trivially bit-identical either way. Kept
        // in the matrix per the roadmap's "new BL_NO_* flag per new pass" invariant so the day a real
        // rewrite lands behind it, this harness already covers it with zero further wiring.
        "BL_NO_AUTOPAR",
    ];

    /// Serializes the env-var-mutating build window (see the module comment). A plain `Mutex` over
    /// `()` — held only across set/build/unset, never across the subprocess run.
    #[cfg(feature = "llvm")]
    static DIFF_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// Build `name` into a fresh binary with exactly the env flags in `flags` set to `"1"` (all
    /// others cleared), run it (optionally feeding `stdin`), and return its raw stdout. The
    /// set-env/build/unset-env window is held under `DIFF_ENV_LOCK` so concurrent tests never observe
    /// a half-set flag environment. Builds without `--recheck` (this harness is about *runtime*
    /// behavior equivalence; the re-checker story is guarded by the load/recheck tests).
    #[cfg(feature = "llvm")]
    fn build_with_flags_and_run(name: &str, flags: &[&str], stdin: Option<&str>) -> String {
        use std::io::Write;
        use std::process::Stdio;

        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join(name);
        // A binary path unique to this (example, flag-set) so parallel configs never collide.
        let tag: String = if flags.is_empty() {
            "base".to_string()
        } else {
            flags
                .iter()
                .map(|f| f.trim_start_matches("BL_NO_").to_lowercase())
                .collect::<Vec<_>>()
                .join("_")
        };
        let dir = std::env::temp_dir().join(format!(
            "blight_diff_{}_{}_{}",
            name.replace(['.', '/'], "_"),
            tag,
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];

        // --- env-mutating window: serialized, and the build itself runs on a generous stack. ---
        {
            let _guard = DIFF_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
            for &f in DIFF_FLAGS {
                if flags.contains(&f) {
                    std::env::set_var(f, "1");
                } else {
                    std::env::remove_var(f);
                }
            }
            let res = std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || run_build(&build_args))
                .expect("spawn diff build thread")
                .join()
                .expect("diff build thread completes");
            // Always clear the flags before releasing the lock, even if the build failed.
            for &f in DIFF_FLAGS {
                std::env::remove_var(f);
            }
            res.unwrap_or_else(|e| panic!("diff build {name} with flags {flags:?}: {e}"));
        }
        assert!(
            bin.exists(),
            "diff build {name} with flags {flags:?} produced a binary"
        );

        // --- run (no flags read here, so it is outside the lock) ---
        let run = if let Some(input) = stdin {
            let mut child = std::process::Command::new(&bin)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .unwrap_or_else(|e| panic!("spawn diff run {name}: {e}"));
            child
                .stdin
                .as_mut()
                .unwrap()
                .write_all(input.as_bytes())
                .unwrap();
            child
                .wait_with_output()
                .unwrap_or_else(|e| panic!("run diff {name}: {e}"))
        } else {
            std::process::Command::new(&bin)
                .output()
                .unwrap_or_else(|e| panic!("run diff {name}: {e}"))
        };
        assert!(
            run.status.success(),
            "diff build {name} with flags {flags:?} runs successfully"
        );
        let _ = std::fs::remove_dir_all(&dir);
        String::from_utf8_lossy(&run.stdout).into_owned()
    }

    /// The differential corpus: `(example, optional-stdin)`. Deliberately the *runtime* examples
    /// (those with a `*_builds_and_runs` test), since the harness compares produced output. Mixes
    /// `Nat`/`Int`/`Float` arithmetic, structural & fuel recursion, indexed vectors, regions, the
    /// alloc-churn tree, strings, and effectful (Console/FileIO/Bytes/lexer) programs — i.e. every
    /// shape a fast-path rewrite could touch.
    #[cfg(feature = "llvm")]
    const DIFF_CORPUS: &[(&str, Option<&str>)] = &[
        ("hello_nat.bl", None),
        ("int_arith.bl", None),
        ("float_arith.bl", None),
        ("int_sum.bl", None),
        ("bench_sum.bl", None),
        ("list_sum.bl", None),
        ("listfold.bl", None),
        ("fib.bl", None),
        ("factorial.bl", None),
        ("minmax.bl", None),
        ("gcd.bl", None),
        ("collatz_steps.bl", None),
        ("either_compute.bl", None),
        ("region_scratch.bl", None),
        ("tree_sum.bl", None),
        ("elim_accum.bl", None),
        ("elim_linear.bl", None),
        ("list_sort.bl", None),
        ("hofold.bl", None),
        ("mergesort.bl", None),
        ("quicksort.bl", None),
        ("rle.bl", None),
        ("containers.bl", None),
        ("vec_head.bl", None),
        ("safe_tail.bl", None),
        ("vec_map.bl", None),
        ("zip_vec.bl", None),
        ("ackermann.bl", None),
        ("hello_string.bl", None),
        ("string_length.bl", None),
        ("string_reverse.bl", None),
        ("caesar.bl", None),
        ("ascii_box.bl", None),
        ("state_handler.bl", None),
        ("actor_pingpong.bl", None),
        ("effect_nontail.bl", None),
        ("echo.bl", Some("world\n")),
        ("greet.bl", Some("Ada\n")),
        ("game/guess.bl", Some("cat\ndog\n")),
        ("bytes_scratch.bl", None),
        ("array_scratch.bl", None),
        ("boxed_array_scratch.bl", None),
        ("paren_depth.bl", None),
        ("flat_pair.bl", None),
        ("flat_esc.bl", None),
    ];

    /// The fast-path flag configurations every corpus program is built under. The baseline is
    /// all-fast-paths-on (`&[]`); each other config disables exactly one fast path, plus one config
    /// disables *all* of them (the pure inductive/slow reference). Output under every config must
    /// equal the baseline — that is the differential bit-identity property.
    #[cfg(feature = "llvm")]
    fn diff_configs() -> Vec<Vec<&'static str>> {
        let mut configs: Vec<Vec<&'static str>> = vec![vec![]]; // baseline: everything on
        for &f in DIFF_FLAGS {
            configs.push(vec![f]); // each fast path off in isolation
        }
        configs.push(DIFF_FLAGS.to_vec()); // all fast paths off (slow reference)
        configs
    }

    /// **B1.** The standing differential-correctness harness. For every example in the corpus, the
    /// produced binary's output must be *identical* whether each backend fast path is on or off. A
    /// failure here is a miscompiling optimization (a wrong *number*) — caught before it can ever be
    /// mistaken for a proof. This is the safety net the Grand Arc's representation milestones (A1
    /// product flattening, A2 string-as-bytes, A3 loop fusion, A4 inliner) are gated on.
    ///
    /// Ignored by default because it compiles the whole corpus several times over (minutes with
    /// LLVM); run it explicitly with `cargo test --features llvm -- --ignored differential`.
    #[cfg(feature = "llvm")]
    #[test]
    #[ignore = "slow: builds the whole corpus under every fast-path flag combo; run with --ignored"]
    fn differential_fast_paths_are_bit_identical() {
        let configs = diff_configs();
        let mut failures: Vec<String> = Vec::new();
        for &(name, stdin) in DIFF_CORPUS {
            let baseline = build_with_flags_and_run(name, &[], stdin);
            for cfg in &configs[1..] {
                let got = build_with_flags_and_run(name, cfg, stdin);
                if got != baseline {
                    failures.push(format!(
                        "{name}: config {cfg:?} produced {got:?} but baseline produced {baseline:?}"
                    ));
                }
            }
        }
        assert!(
            failures.is_empty(),
            "differential fast-path mismatches (a miscompiling optimization):\n{}",
            failures.join("\n")
        );
    }

    /// A fast, non-ignored *smoke* slice of the differential harness: a handful of representative
    /// programs (an `Int` fold, the alloc-churn tree, a fuel recursion, a string op, and an
    /// effectful Bytes program) built with *all* fast paths off must still match the all-on build.
    /// This runs in the normal suite so a gross differential regression is caught without the full
    /// (minutes-long) sweep; the exhaustive per-flag matrix lives in the `#[ignore]`d test above.
    #[cfg(feature = "llvm")]
    #[test]
    fn differential_smoke_slow_path_matches() {
        let smoke: &[(&str, Option<&str>)] = &[
            ("int_sum.bl", None),
            ("tree_sum.bl", None),
            ("gcd.bl", None),
            ("string_reverse.bl", None),
            ("bytes_scratch.bl", None),
        ];
        let all_off = DIFF_FLAGS.to_vec();
        let mut failures: Vec<String> = Vec::new();
        for &(name, stdin) in smoke {
            let baseline = build_with_flags_and_run(name, &[], stdin);
            let slow = build_with_flags_and_run(name, &all_off, stdin);
            if baseline != slow {
                failures.push(format!(
                    "{name}: all-fast-paths-off produced {slow:?} but baseline produced {baseline:?}"
                ));
            }
        }
        assert!(
            failures.is_empty(),
            "differential smoke mismatches (a miscompiling optimization):\n{}",
            failures.join("\n")
        );
    }

    /// `hello_nat.bl`: `(2 * 3) + 1 = 7`, computed with `std/nat`'s `plus`/`mult`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_hello_nat_builds_and_runs() {
        build_and_run_example("hello_nat.bl", "7");
    }

    /// `foreign_answer.bl`: the FFI escape hatch (spec §7.6). `(foreign answer Nat
    /// "bl_foreign_answer")` postulates an opaque `Nat` whose C symbol (`runtime/prelude_rt.c`)
    /// builds and returns the unary `Nat` 42; `main` returns it, so the program prints `42` —
    /// produced entirely by trusted C and threaded back into checked code, linked automatically
    /// because the symbol lives in the always-linked prelude runtime. Built *without* `--recheck`:
    /// a `foreign` is outside the independent re-checker's certifiable fragment (it declines).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_foreign_answer_builds_and_runs() {
        build_and_run_example_opts("foreign_answer.bl", "42", false);
    }

    /// `f64_scratch.bl`: the UNVERIFIED IEEE-754 `F64` hatch (Wave 2 / L2, std/f64.bl), the other
    /// side of the trade-off from `Float`'s verified fixed-point rational (spec §7.6, Design B).
    /// `(((3.0 + 4.0) * 2.0) - 1.0) / 3.0`, negated and rounded (ties away from zero) = `-4`,
    /// computed entirely via `foreign` C `double` arithmetic threaded back into a checked `Int`.
    /// Built *without* `--recheck`, exactly like `foreign_answer.bl`: `F64` is outside the
    /// independent re-checker's certifiable fragment (it declines).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_f64_scratch_builds_and_runs() {
        build_and_run_example_opts("f64_scratch.bl", "-4", false);
    }

    /// `int_arith.bl`: native machine `Int` (M11). `(int* (int 100000) (int 100000))` lowers to a
    /// single hardware multiply on a `BL_INT` payload, so the product `10000000000` prints instantly
    /// — the headline contrast with the O(unary) `Nat` tower. Built *with* `--recheck`: `Int` is a
    /// primitive the independent re-checker certifies (unlike the `foreign` hatch).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_int_arith_builds_and_runs() {
        build_and_run_example("int_arith.bl", "10000000000");
    }

    /// `float_arith.bl`: the UNTRUSTED fixed-point `Float` library type (M23). `Float` is ordinary
    /// `Data` (`(mkfloat (mantissa Int))`, value scaled by 10^6), NOT a kernel primitive — so this
    /// grows zero trusted lines, yet the backend recognizer rewrites each `float-*` wrapper to an
    /// O(1) `bl_float_*` helper. The program computes `((2.5*4.0)-(10.0/4.0)) + (-1.25) = 6.25`,
    /// printed as the scaled mantissa `6250000`. Built *with* `--recheck`: the independent re-checker
    /// certifies it as plain `Int`/`Data` (a `Float` is in-fragment), confirming the zero-TCB claim.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_float_arith_builds_and_runs() {
        build_and_run_example("float_arith.bl", "6250000");
    }

    /// `int_sum.bl`: the machine-`Int` counterpart of `bench_sum.bl`. Folds `int-add` (std/int.bl)
    /// over a `List Int` of 800 ones, printing `800` with O(1) adds — the integer side of the
    /// unary-`Nat`-vs-`Int` benchmark in docs/benchmarks-game.md. Built with `--recheck` (Int/List
    /// are in-fragment).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_int_sum_builds_and_runs() {
        build_and_run_example("int_sum.bl", "800");
    }

    /// `bench_sum.bl`: the unary-`Nat` counterpart of `int_sum.bl` — `foldr plus` over 800 ones,
    /// so `main` evaluates to `Succ^800 Zero` and prints `800`. Same answer as `int_sum.bl`, but
    /// every `+` walks a `Succ` chain (the unary cost the benchmark narrative measures).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_bench_sum_builds_and_runs() {
        build_and_run_example("bench_sum.bl", "800");
    }

    /// `hello_string.bl`: a `String`-typed `main` prints as *text* (`hello`), end-to-end proof that
    /// the reader sugar + runtime `bl_print_string` path works. No kernel change.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_hello_string_builds_and_runs() {
        build_and_run_example("hello_string.bl", "hello");
    }

    /// `string_length.bl`: `string-length "hello" = 5`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_string_length_builds_and_runs() {
        build_and_run_example("string_length.bl", "5");
    }

    /// `string_reverse.bl`: `string-reverse "abc"` prints `cba`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_string_reverse_builds_and_runs() {
        build_and_run_example("string_reverse.bl", "cba");
    }

    /// `palindrome.bl`: `"level"` is a palindrome → `1`. Built without the re-checker (see
    /// `build_and_run_example_opts`): the concrete `string-eq word (reverse word)` normal form over
    /// real letters (~100-deep unary codepoints) is a normalization-cost blowup for the re-checker,
    /// not a soundness issue — the definitions re-check fine in the load corpus.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_palindrome_builds_and_runs() {
        build_and_run_example_opts("palindrome.bl", "1", false);
    }

    /// `caesar.bl`: shift `"abc"` by 1 → `bcd`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_caesar_builds_and_runs() {
        build_and_run_example("caesar.bl", "bcd");
    }

    /// `containers.bl`: builds a length-indexed `Vec Nat 2` and reads its length back, exercising the
    /// indexed-family eliminator end-to-end (the bug fixed here). Result: `2`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_containers_builds_and_runs() {
        build_and_run_example("containers.bl", "2");
    }

    /// `list_sum.bl`: `foldr plus 0 [1,2,3] = 6`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_list_sum_builds_and_runs() {
        build_and_run_example("list_sum.bl", "6");
    }

    /// `fib.bl`: structural Fibonacci, `fib 7 = 13` (0,1,1,2,3,5,8,13).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_fib_builds_and_runs() {
        build_and_run_example("fib.bl", "13");
    }

    /// `minmax.bl`: `plus (min 2 5) (max 2 5) = 2 + 5 = 7`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_minmax_builds_and_runs() {
        build_and_run_example("minmax.bl", "7");
    }

    /// `vec_head.bl`: a `Vec Nat 3`'s recovered length is `3`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_vec_head_builds_and_runs() {
        build_and_run_example("vec_head.bl", "3");
    }

    /// `safe_tail.bl`: the tail of a length-2 vector has length `1`. Built *with* `--recheck`: the
    /// dependent indexed motive `Vec A n` re-checks through the independent re-checker (no soundness
    /// alarm) before the binary is emitted.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_safe_tail_builds_and_runs() {
        build_and_run_example("safe_tail.bl", "1");
    }

    /// `vec_map.bl`: mapping over a length-2 vector preserves the length, so the result's recovered
    /// length is `2`. Built *with* `--recheck`: the length-preserving dependent indexed motive
    /// `Vec B n` re-checks independently before emit.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_vec_map_builds_and_runs() {
        build_and_run_example("vec_map.bl", "2");
    }

    /// `zip_vec.bl`: zipping two length-2 vectors yields a length-2 vector of pairs (recovered
    /// length `2`). Built *with* `--recheck`: the re-checker fully certifies zip-vec's higher-order
    /// eliminator motive (see `zip_vec_example_loads` in `examples.rs`, which asserts `Ok`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_zip_vec_builds_and_runs() {
        build_and_run_example("zip_vec.bl", "2");
    }

    /// `either_compute.bl`: an `Either`/`Maybe` pipeline that nets `4`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_either_compute_builds_and_runs() {
        build_and_run_example("either_compute.bl", "4");
    }

    /// `region_scratch.bl`: a `(region r …)` scratch computation returning `2`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_region_scratch_builds_and_runs() {
        build_and_run_example("region_scratch.bl", "2");
    }

    /// `tree_sum.bl`: sum of the `Nat`s in a binary search tree built by `tree-insert` = `6`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_tree_sum_builds_and_runs() {
        build_and_run_example("tree_sum.bl", "6");
    }

    /// `elim_linear.bl`: a non-tail linear `Nat` fold (`double-up n = 2·n`), the P3 (3b)
    /// reverse-then-fold elim-worklist shape. `double-up 20 = 40`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_elim_linear_builds_and_runs() {
        build_and_run_example("elim_linear.bl", "40");
    }

    /// `flat_pair.bl`: a nested `Pair (Pair Nat Nat) Nat` read only by leaf-drilling projections,
    /// `(2 + 3) + 1 = 6` — the A1 escaping-product-flattening differential coverage shape.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_flat_pair_builds_and_runs() {
        build_and_run_example("flat_pair.bl", "6");
    }

    /// `flat_esc.bl`: a cross-function escaping nested `Pair (Pair Nat Nat) Nat` whose `mk-pair`
    /// allocations the A1′ post-mono scalar-replacement pass (layout.rs) deletes after mono folds the
    /// producer into the consumer. `(1 + 2) + 3 = 6`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_flat_esc_builds_and_runs() {
        build_and_run_example("flat_esc.bl", "6");
    }

    /// `gcd.bl`: subtractive Euclidean GCD, `gcd 12 8 = 4` (fuel-bounded structural recursion).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_gcd_builds_and_runs() {
        build_and_run_example("gcd.bl", "4");
    }

    /// `collatz_steps.bl`: Collatz step count for `6` is `8` (6→3→10→5→16→8→4→2→1).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_collatz_steps_builds_and_runs() {
        build_and_run_example("collatz_steps.bl", "8");
    }

    /// `list_sort.bl`: insertion-sort `[3,1,2]` → `[1,2,3]`, whose head (smallest element) is `1`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_list_sort_builds_and_runs() {
        build_and_run_example("list_sort.bl", "1");
    }

    /// `hofold.bl`: a higher-order `iterate` applies a *capturing* closure `(adder (int 1))` to an
    /// `Int` accumulator 1000 times — each `(step acc)` is an indirect `bl_app`. This is the
    /// closure-indirection shape the P10 defunctionalization pass rewrites to a direct call; the
    /// `BL_NO_DEFUNC` differential A/B proves the rewrite is value-preserving. Result: 1000.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_hofold_builds_and_runs() {
        build_and_run_example("hofold.bl", "1000");
    }

    /// `ascii_box.bl`: a 3×3 grid of `#` built as a `String` and printed as text. The runtime emits
    /// a trailing newline after the last row; the harness `.trim()`s it, so the comparison is the
    /// three rows joined by newlines.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_ascii_box_builds_and_runs() {
        build_and_run_example("ascii_box.bl", "###\n###\n###");
    }

    /// `ackermann.bl`: the `force` (delay-eliminator) showcase. `parity` is a *non-structural*
    /// `define-rec` (it recurses on `n - 2`, two `Succ`s deep) so its result is a `Delay Nat`;
    /// `main` drives it with `(force (parity seven))`. Seven is odd, so the program prints `1`. This
    /// also runs under `--recheck`, so the independent re-checker accepts the forced delay layer.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_ackermann_builds_and_runs() {
        build_and_run_example("ackermann.bl", "1");
    }

    /// Regression: a `define-rec` whose recursion is genuinely *course-of-values* (the call is on a
    /// field reached by a **nested** match, two `Succ`s below the parameter) must compile to the
    /// sound `Later`-guarded partial path and compute the *right* value — both arms, not just the one
    /// the showcase happens to exercise.
    ///
    /// `parity` steps `n → n-2`; `ackermann.bl` only forces it at `seven` (odd → `1`). Two bugs hid
    /// behind that single odd sample: (1) the elaborator silently bound `parity (n-2)` to the *inner*
    /// eliminator's induction hypothesis, so `parity` compiled as a (wrong) structural recursion that
    /// returned `1` for *every* `n ≥ 1` — `parity 6` gave `1` instead of `0`; and (2) once the
    /// elaborator correctly rejected that binding and fell back to the `later`-guard, the *compiled*
    /// delay path stored an eagerly-evaluated value where `bl_force` expected a thunk closure, so any
    /// program that actually reached it crashed on a bogus function pointer. This test forces an
    /// **even** input, so it fails loudly under either bug (wrong value, or a crash), and passes only
    /// when the whole partial-recursion chain — elaborate → lower → force — is correct.
    #[cfg(feature = "llvm")]
    #[test]
    fn define_rec_course_of_values_parity_is_correct_on_even_input() {
        let src = "(load \"std/nat.bl\")\n\
            (define-rec parity (Pi ((n Nat)) (Delay Nat))\n\
              (lam (n) (match n\n\
                [(Zero) (now Zero)]\n\
                [(Succ m) (match m\n\
                   [(Zero) (now (Succ Zero))]\n\
                   [(Succ k) (parity k)])])))\n\
            ; six is even, so parity converges to 0 (the value HEAD miscompiled to 1).\n\
            (define six Nat (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))\n\
            (define main Nat (force (parity six)))\n";
        let dir = std::env::temp_dir().join(format!("blight_parity_even_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let srcpath = dir.join("parity_even.bl");
        std::fs::write(&srcpath, src).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            srcpath.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_build(&build_args).expect("parity_even builds"))
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        let run = std::process::Command::new(&bin)
            .output()
            .expect("run parity_even");
        assert!(
            run.status.success(),
            "parity_even runs without crashing (the delay thunk must be a real closure): {:?}",
            run.status
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            "0",
            "parity of an even number is 0 (course-of-values define-rec must not miscompile)"
        );
    }

    /// Regression (varying-leading-accumulator soundness): a left fold must actually thread its
    /// accumulator. The stdlib `foldl` was written as a direct structural recursion `foldl f (f acc
    /// x) xs` whose accumulator `acc` is a *leading* argument; the structural `Elim` fixes the leading
    /// parameters, so the elaborator silently dropped the `(f acc x)` update and `foldl` returned its
    /// initial seed unchanged — `foldl plus 0 [1,2,3]` computed `0`, not `6`. The kernel's type
    /// re-check could not see it (both are `Nat`) and the only stdlib test merely checked `foldl` was
    /// *defined*. `foldl` is now the total *foldl-via-foldr* (a function-valued right fold applied to
    /// the seed), and the elaborator rejects the original accumulator shape outright. This builds and
    /// runs a real left fold and asserts the summed value.
    #[cfg(feature = "llvm")]
    #[test]
    fn stdlib_foldl_threads_its_accumulator() {
        let src = "(load \"std/list_extra.bl\")\n\
            (define xs (List Nat)\n\
              (cons (Succ Zero) (cons (Succ (Succ Zero)) (cons (Succ (Succ (Succ Zero))) nil))))\n\
            (define main Nat (foldl Nat Nat plus Zero xs))\n";
        let dir = std::env::temp_dir().join(format!("blight_foldl_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let srcpath = dir.join("foldl_sum.bl");
        std::fs::write(&srcpath, src).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            srcpath.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || run_build(&build_args).expect("foldl_sum builds"))
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        let run = std::process::Command::new(&bin)
            .output()
            .expect("run foldl_sum");
        assert!(run.status.success(), "foldl_sum runs: {:?}", run.status);
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            "6",
            "foldl plus 0 [1,2,3] = 6 (the accumulator must be threaded, not dropped)"
        );
    }

    /// `state_handler.bl`: a compiled algebraic-effect deep handler. The body performs `get` in tail
    /// position; `handle` lowers each clause to a closure and installs them via the runtime's
    /// `bl_handle_clo` deep-handler trampoline. The `get` clause resumes with `3`, the `return`
    /// clause yields it, so the native binary prints `3`. (Built *without* `--recheck` here to keep
    /// this a lean runtime-execution test; `--recheck` agreement on effects is separately covered by
    /// `state_handler_example_loads` / `recheck_agrees_on_surface_effect_program` — effects are now
    /// re-checked at the type level, not declined.)
    #[cfg(feature = "llvm")]
    #[test]
    fn example_state_handler_builds_and_runs() {
        build_and_run_example_opts("state_handler.bl", "3", false);
    }

    /// `actor_pingpong.bl` (M16): the actor/CSP surface (std/actor.bl) run end-to-end. An
    /// `Actor`-effect program performs all four ops — `spawn`/`send`/`yield`/`receive` — under an
    /// inline cooperative single-core scheduler handler (the same deep-handler trampoline as the
    /// State handler). The handler resumes each (linear) op exactly once, delivering inbox `4`; the
    /// body binds it and returns `Succ 4`, so the program prints `5`. Built without `--recheck` here
    /// to keep this a lean runtime-execution test (effects are now re-checked at the type level, not
    /// declined; see `actor_pingpong_example_loads`). This is the runtime proof that the graded
    /// actor effect surface composes and executes natively.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_actor_pingpong_builds_and_runs() {
        build_and_run_example_opts("actor_pingpong.bl", "5", false);
    }

    /// `effect_nontail.bl`: a *general* (non-tail) algebraic-effect handler. The performed `get`s are
    /// ordinary sub-expressions of `(plus (perform get tt) (perform get tt))`, so the continuation
    /// must be captured across the application — a genuine delimited continuation. The native backend
    /// does this at runtime: every elimination site (`bl_app` for application, `bl_con_bubble` for
    /// construction) is OpNode-aware, so the effect bubbles out with the pending work composed onto
    /// its continuation, mirroring the kernel's `apply`/`replay`. Resuming every `get` with `2` yields
    /// `plus 2 2 = 4`. Built without `--recheck` here to keep this a lean runtime-execution test
    /// (effects are now re-checked at the type level, not declined; see
    /// `effect_nontail_example_loads`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_effect_nontail_builds_and_runs() {
        build_and_run_example_opts("effect_nontail.bl", "4", false);
    }

    /// `echo.bl`: the smallest `Console`-effect program — `read` a line, `print` it back. Exercises
    /// the native top-level Console handler (`bl_run_console`): `bl_program_entry` yields a bubbling
    /// `Console` OpNode tree, which the generated `main` folds against real stdio. With `world\n` on
    /// stdin it echoes `world` (no trailing newline — `print` adds none).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_echo_builds_and_runs() {
        build_and_run_example_stdin("echo.bl", "world\n", "world");
    }

    /// `greet.bl`: an interactive `Console` program — print a prompt, read a name, print a greeting.
    /// Exercises *sequenced* Console operations through the delimited-continuation machinery and the
    /// native top-level handler. With `Ada\n` on stdin it prints `Name: Hi, Ada!\n`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_greet_builds_and_runs() {
        build_and_run_example_stdin("greet.bl", "Ada\n", "Name: Hi, Ada!\n");
    }

    /// `game/guess.bl`: the interactive turn-based "guess the word" game — a fuel-bounded `Console`
    /// frame loop that reads a guess each turn, compares it to the secret with `string-eq`, and
    /// branches (win + stop, or hint + recurse). This exercises *recursion over an effectful
    /// computation* (`define-rec play : Nat -> (! Console Unit)`) driven through the native
    /// top-level Console handler and the delimited-continuation machinery. With the secret `"dog"`
    /// and `cat\ndog\n` on stdin, the player misses then wins.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_guess_game_builds_and_runs() {
        build_and_run_example_stdin(
            "game/guess.bl",
            "cat\ndog\n",
            "guess: nope, try again.\nguess: you win!\n",
        );
    }

    /// `file_roundtrip.bl` (C1): the smallest `FileIO`-effect program. `main : (! FileIO String)`
    /// `write-file`s a payload to a temp path, `read-file`s the whole file back, and returns its
    /// contents — folded by the same native top-level handler the Console examples use
    /// (`bl_run_console`, extended with `read-file`/`write-file`), then printed via `bl_print_string`.
    /// Proves the C1 effect end-to-end: the file actually hits disk and reads back byte-identically.
    /// Built without `--recheck` here to keep this a lean runtime-execution test (effects are now
    /// re-checked at the type level, not declined; see `file_roundtrip_example_loads`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_file_roundtrip_builds_and_runs() {
        build_and_run_example_opts("file_roundtrip.bl", "hello from blight FileIO", false);
    }

    /// `selfhost_check.bl` (S1, v0.1 roadmap arc S): the Blight-written front end checking source it
    /// reads back from disk. `main : (! (Console FileIO Bytes) Unit)` writes a well-typed toy source
    /// `(lam (x Base) x)` and an ill-typed `(lam (x Base) (x x))` to a scratch file, reads each back
    /// (`FileIO`), runs it through the self-hosted reader → transcoder → proof-carrying elaborator →
    /// ANF compiler (`Bytes`, all `.bl`), and prints the verdict (`Console`). The good source
    /// elaborates (acceptance is a typing proof) and lowers to a size-6 ANF; the ill-typed one has no
    /// typed elaboration, so the front end returns `nothing` → `REJECT`. This is the first end-to-end
    /// run of Blight's own front end over on-disk source. Run in a throwaway working directory so the
    /// scratch file the demo writes never lands in the repo. Built without `--recheck` to keep it a
    /// lean runtime-execution test (the effectful string front end is honestly *Declined*, not
    /// rejected, by the independent re-checker; the definitions still re-check via the load corpus).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_selfhost_check_builds_and_runs() {
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join("selfhost_check.bl");
        let dir =
            std::env::temp_dir().join(format!("blight_selfhost_check_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_build(&build_args).unwrap_or_else(|e| panic!("selfhost_check.bl builds: {e}"));
            })
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        assert!(bin.exists(), "selfhost_check.bl produced a binary");

        // Run in the throwaway dir so `selfhost_scratch.bl` is written there, not in the repo.
        let run = std::process::Command::new(&bin)
            .current_dir(&dir)
            .output()
            .unwrap_or_else(|e| panic!("run selfhost_check: {e}"));
        assert!(run.status.success(), "selfhost_check runs successfully");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            "OK size=6\nREJECT\n",
            "the Blight-written front end accepts the well-typed toy source (size-6 ANF) and \
             rejects the ill-typed one"
        );
    }

    /// `bytes_scratch.bl` (C2): the smallest `Bytes`-effect program. `main : (! Bytes Nat)` allocates
    /// a 4-byte runtime-backed buffer, writes byte 7 at index 2 via `set-byte`, reads it back with
    /// `get-byte`, and returns it — proving the mutable round-trip through the C-side buffer table
    /// (reached by an opaque `Int` handle) works end-to-end. Crucially this is also the regression
    /// guard for the `mono.rs` inliner fix: the handle `h` (the result of an effectful `new-bytes`)
    /// is used by *both* the `set` and the `get`, so an inliner that substituted the effectful arg at
    /// every use would `new-bytes` twice and read an empty buffer (→ 0). Prints **7**. Built without
    /// `--recheck` here to keep this a lean runtime-execution test (effects are now re-checked at
    /// the type level, not declined; see `bytes_scratch_example_loads`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_bytes_scratch_builds_and_runs() {
        build_and_run_example_opts("bytes_scratch.bl", "7", false);
    }

    /// `array_scratch.bl` (A3a): the smallest `Arrays`-effect program. `main : (! Arrays Int)`
    /// allocates a 4-element runtime-backed int array, writes `7` at index 2 via `set-elem`, reads it
    /// back with `get-elem`, and returns it — proving the mutable round-trip through the C-side
    /// int-array table (reached by an opaque `Int` handle) works end-to-end. Same regression shape as
    /// `bytes_scratch.bl`: the handle `h` (the result of an effectful `new-array`) is used by *both*
    /// the `set` and the `get`, so an inliner that substituted the effectful arg at every use would
    /// `new-array` twice and read a fresh, zeroed array (→ 0). Prints **7**. Built without `--recheck`
    /// here to keep this a lean runtime-execution test (effects are now re-checked at the type level,
    /// not declined; see `array_scratch_example_loads`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_array_scratch_builds_and_runs() {
        build_and_run_example_opts("array_scratch.bl", "7", false);
    }

    /// `boxed_array_scratch.bl` (A3b, roadmap Wave 10 / P1): the boxed-element sibling of
    /// `array_scratch.bl`. `main : (! Array Nat)` allocates a 3-element runtime-backed array of
    /// `Nat`s (every slot a genuine boxed/GC-traced value, not a raw machine word), writes `7` at
    /// index 1 via `set-boxed`, reads it back with `get-boxed`, and returns it — proving the
    /// rooted-handle-table + write-barrier design (`runtime/boxed_array.c`) round-trips correctly
    /// end-to-end, on top of the dedicated GC-stress proof in `runtime/tests/gc_test.c`. Prints **7**.
    /// Built without `--recheck` here (parameterized effects are re-checked at the type level, not
    /// declined; see `std_array_boxed_loads_in_isolation` for that surface-level coverage).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_boxed_array_scratch_builds_and_runs() {
        build_and_run_example_opts("boxed_array_scratch.bl", "7", false);
    }

    /// Layer 3 of P2's four-layer TDD (roadmap Wave 10 / P2, docs/design-wave4-gobars.md §5 item 4):
    /// compile `graphics_scratch.bl` (`main : (! Graphics Int)`) with the `graphics` cargo feature —
    /// the only test in this suite that links `runtime/graphics.c` + SDL2 — and run it with
    /// `SDL_VIDEODRIVER=dummy` (SDL's headless backend, no real display, no queued input events), so
    /// `poll-input`'s "no event pending" branch is the deterministic, concrete observable result the
    /// go-bar asks for (`-1`) from having actually driven window creation, a render pass, and a
    /// presented frame end to end — not a human watching a window. Skipped by default (only compiled
    /// when `--features llvm,graphics` is explicitly requested), since the ordinary `llvm`-only CI
    /// matrix never links SDL2.
    #[cfg(feature = "graphics")]
    #[test]
    fn example_graphics_scratch_builds_and_runs() {
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join("graphics_scratch.bl");
        let dir = std::env::temp_dir().join(format!(
            "blight_example_graphics_scratch_{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
            "--recheck".to_string(),
        ];
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_build(&build_args).unwrap_or_else(|e| {
                    panic!(
                        "example graphics_scratch.bl builds (seed + independent re-checker): {e}"
                    )
                });
            })
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        assert!(
            bin.exists(),
            "example graphics_scratch.bl produced a binary"
        );

        let run = std::process::Command::new(&bin)
            .env("SDL_VIDEODRIVER", "dummy")
            .output()
            .unwrap_or_else(|e| panic!("run example graphics_scratch.bl: {e}"));
        assert!(
            run.status.success(),
            "example graphics_scratch.bl runs successfully under SDL_VIDEODRIVER=dummy: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            "-1",
            "graphics_scratch.bl's headless poll-input observes no pending event"
        );
    }

    /// `map_scratch.bl`/`json_scratch.bl`/`regex_scratch.bl` (Wave 2 / L1): each dogfoods
    /// `std/test.bl` against one of `std/map.bl`/`std/json.bl`/`std/regex.bl`, with `main : Bool` the
    /// suite's `suite-all-passed` verdict. The naive kernel evaluator (`oracle.rs`'s
    /// `kernel_nf_decimal` shape) is far too slow to normalize a multi-case `TestSuite` — the same
    /// documented "large intermediate structure" exclusion `oracle.rs` already applies to e.g.
    /// `gcd`/`collatz` — so these are proved behaviorally by compiling and RUNNING the suite instead
    /// (native codegen, not the tree-walking interpreter). A `Bool`'s constructor-index printer
    /// (`bl_print`, prelude_rt.c) prints `false` (ctor 0, 0 fields) as `0` and `true` (ctor 1, 0
    /// fields) as `con#1`, so a passing (`true`) suite prints **con#1**. Built without `--recheck`:
    /// these programs are pure (no effect row), and `--recheck` agreement on the underlying stdlib
    /// modules is already covered by `std_map_loads_in_isolation`/`std_json_loads_in_isolation`/
    /// `std_regex_loads_in_isolation` (`crates/blight-repl/tests/stdlib.rs`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_map_scratch_builds_and_runs() {
        build_and_run_example_opts("map_scratch.bl", "con#1", false);
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn example_json_scratch_builds_and_runs() {
        build_and_run_example_opts("json_scratch.bl", "con#1", false);
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn example_regex_scratch_builds_and_runs() {
        build_and_run_example_opts("regex_scratch.bl", "con#1", false);
    }

    /// `clock_scratch.bl` (Wave 2 / L1, std/time.bl): the smallest `Clock`-effect program. `main :
    /// (! Clock Int)` takes two back-to-back `clock-now` readings and asserts the wall clock never
    /// runs backwards — phrased as the `Int`-valued flag `1 - (end < start)` since `Int` has no
    /// eliminator (see std/int.bl's header), which is deterministically `1` on any correctly
    /// functioning clock despite `now` itself reading the real, non-deterministic OS clock
    /// (`gettimeofday`, runtime/effects.c). Built without `--recheck` here to keep this a lean
    /// runtime-execution test (effects are now re-checked at the type level, not declined; see
    /// `clock_scratch_example_loads`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_clock_scratch_builds_and_runs() {
        build_and_run_example_opts("clock_scratch.bl", "1", false);
    }

    /// C3 self-hosting headliner (`paren_depth.bl` over `std/lexer.bl`): a byte scanner written
    /// entirely in `.bl`. `max-paren-depth "(a (b (c) d) (e))"` copies the string into a runtime `Bytes`
    /// buffer (`string->bytes` — a structural fill descending on the string spine with the write
    /// index as a *trailing* accumulator, so each per-step `set-byte` is sequenced correctly) and
    /// scans it with O(1) `get-byte` reads over a structural `Nat` fuel, tracking the running paren
    /// depth. The max nesting depth is **3**. This is also the end-to-end regression guard for three
    /// fixes uncovered building it: the `mono.rs` whole-program effect analysis (an effectful curried
    /// recursive call must not be dropped/duplicated), the `recognize.rs` `sub`-vs-`min`/`max`
    /// fingerprint disambiguation, and *not* bubbling closure captures (a structural eliminator's
    /// induction hypothesis is a suspended effectful comp that must resume on *apply*, not eagerly).
    /// Built without `--recheck` here to keep this a lean runtime-execution test (effects are now
    /// re-checked at the type level, not declined; see `paren_depth_example_loads`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_paren_depth_builds_and_runs() {
        build_and_run_example_opts("paren_depth.bl", "3", false);
    }

    /// Grand Arc SH1: the self-hosted `.bl` tokenizer + s-expression parser (std/parser.bl) end to
    /// end. `parse-string` copies `"(a (b c) d)"` into a `Bytes` buffer, tokenizes it (a structural-
    /// on-fuel effectful scan, the `scan-depth` shape), and parses the tokens with a pure total
    /// stack machine into a surface `BSexp` tree; `count-atoms` returns the atom count (`4`). Built
    /// without `--recheck` here to keep this a lean runtime-execution test (the tokenizer's effect
    /// is now re-checked at the type level too, not declined; see `parse_demo_example_loads`).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_parse_demo_builds_and_runs() {
        build_and_run_example_opts("parse_demo.bl", "4", false);
    }
}
