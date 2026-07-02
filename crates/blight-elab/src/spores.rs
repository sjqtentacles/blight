//! `spores` — the Blight package manager manifest + resolver (spec §8.2, §9 M6). UNTRUSTED.
//!
//! A *spore package* is described by a `spore.toml` manifest:
//!
//! ```toml
//! [package]
//! name = "demo"
//! version = "0.1.0"
//!
//! [dependencies]
//! std = { path = "../blight-prelude" }
//!
//! [lib]
//! modules = ["demo/main"]
//! ```
//!
//! - `[package]` names this package and (by convention) makes its own modules resolvable under that
//!   name, rooted at the manifest's directory.
//! - `[dependencies]` maps a dependency *package name* to a source root (currently a `path`).
//! - `[lib].modules` lists the package's own module identifiers (informational: the entry points a
//!   consumer is expected to `(import …)`).
//!
//! The [`PackageManifest`] turns this into a name→root map; [`PackageManifest::resolver`] yields a
//! closure suitable for [`crate::Program::with_resolver`]/[`crate::Program::with_package`] that maps
//! a module identifier `"pkg/sub/mod"` to the source text at `<root-of-pkg>/sub/mod.bl`.
//!
//! None of this is trusted: resolution only *finds source*; every form the loaded source produces
//! still bottoms out in the kernel via the spore re-check.
//!
//! ── A5: `version` and `git` dependencies ────────────────────────────────────────────────────────
//! A dependency entry is one of three shapes:
//!
//! ```toml
//! [dependencies]
//! local  = { path = "../local-pkg" }        # A2: a sibling on-disk package
//! remote = { version = "1.2.3" }            # A5: a registry package, by version
//! bleed  = { git = "https://…", rev = "…" } # A5: parsed, not yet resolvable — see below
//! ```
//!
//! A `version` dependency resolves to the local vendor cache
//! [`registry_cache_dir`]`(base_dir, dep_name, version)` — i.e.
//! `<base_dir>/.blight/registry/<dep_name>-<version>/` — which `blight add`'s registry form
//! ([`crate::registry::fetch_and_vendor`]) populates by fetching, extracting, and hash-verifying a
//! tarball *before* this crate ever reads a `.bl` file from it (see `registry.rs`). Resolution
//! itself never fetches anything: a `version` dependency whose cache directory is empty or missing
//! resolves the same way any other missing directory does (an `import` error naming the missing
//! module, or an empty `blight.lock` hash) — run `blight add` first.
//!
//! A `git` dependency resolves the same way a `version` dependency does (Wave 9 / T3): to a local
//! vendor-cache directory, [`git_cache_dir`]`(base_dir, dep_name, rev)` — i.e.
//! `<base_dir>/.blight/git/<dep_name>-<rev>/` (an unpinned dependency with no `rev` uses the
//! literal `HEAD` in place of a rev). Resolution itself still never fetches anything — exactly
//! like a `version` dependency, a `git` dependency whose cache directory is empty or missing
//! resolves the same way any other missing directory does (an `import` error naming the missing
//! module) — `blight add <name> --git <url> [--rev <rev>]` clones (and pins) it there first via a
//! subprocess `git` ([`fetch_git_dependency`]). There is no hash-verification story here the way
//! there is for registry tarballs: pinning a `rev` (a commit SHA) *is* the content-addressing —
//! `git checkout <rev>` either lands on exactly that content or fails outright.

use crate::ElabError;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// A `git` dependency's declared source, as parsed from `dep = { git = "…", rev = "…" }`. Kept
/// around only to produce an honest, specific error when something tries to resolve a module from
/// it (see the module doc's "A5: `version` and `git` dependencies" section) — there is no fetch
/// path for this yet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GitDep {
    pub url: String,
    pub rev: Option<String>,
}

/// The local vendor-cache directory a registry dependency `dep_name@version` resolves to, relative
/// to the manifest's own directory `base_dir`. Shared between manifest parsing (so `resolve_path`
/// finds it) and [`crate::registry::fetch_and_vendor`] (so `blight add`'s fetch writes to exactly
/// the path resolution expects) — this function is the single source of truth for that convention.
pub(crate) fn registry_cache_dir(base_dir: &Path, dep_name: &str, version: &str) -> PathBuf {
    base_dir
        .join(".blight")
        .join("registry")
        .join(format!("{dep_name}-{version}"))
}

/// The local vendor-cache directory a `git` dependency `dep_name` resolves to, relative to the
/// manifest's own directory `base_dir` — the git-fetch analog of [`registry_cache_dir`] (Wave 9 /
/// T3). `rev` defaults to the literal `"HEAD"` when the manifest didn't pin one, so an unpinned
/// git dependency still gets a stable (if not reproducible-across-refetches) cache path. Shared
/// between manifest parsing (so `resolve_path` finds it) and [`fetch_git_dependency`] (so `blight
/// add`'s git form clones to exactly the path resolution expects).
pub fn git_cache_dir(base_dir: &Path, dep_name: &str, rev: Option<&str>) -> PathBuf {
    let rev = rev.unwrap_or("HEAD");
    base_dir
        .join(".blight")
        .join("git")
        .join(format!("{dep_name}-{rev}"))
}

/// Fetch a `git` dependency's source into `dest` via a subprocess `git` (Wave 9 / T3): `git clone
/// <url> <dest>`, then (if `rev` is given) `git -C <dest> checkout <rev>`. `dest` is treated as a
/// cache exactly like the registry's: if it already exists and is non-empty, this is a no-op — a
/// re-`blight add` never re-clones over an already-vendored dependency. On any failure (missing
/// `git` executable, unreachable/invalid URL, unknown rev) `dest` is left exactly as it was before
/// the call (any partial clone is removed) and an error naming the underlying `git` failure is
/// returned.
///
/// Requires a `git` executable on `PATH` — the "vendor a subprocess rather than an in-process git
/// implementation" choice the module doc's dependency-scope note always flagged as the natural way
/// to close this gap, avoiding a much larger dependency tree (a Rust git implementation, or
/// libgit2 FFI) for what every developer's machine already has.
pub fn fetch_git_dependency(url: &str, rev: Option<&str>, dest: &Path) -> Result<(), ElabError> {
    let already_vendored = std::fs::read_dir(dest)
        .map(|mut entries| entries.next().is_some())
        .unwrap_or(false);
    if already_vendored {
        return Ok(());
    }
    let _ = std::fs::remove_dir_all(dest);
    if let Some(parent) = dest.parent() {
        std::fs::create_dir_all(parent).map_err(|e| {
            ElabError::BadForm(format!("git dependency: cannot create {parent:?}: {e}"))
        })?;
    }
    let clone = std::process::Command::new("git")
        .arg("clone")
        .arg("--quiet")
        .arg(url)
        .arg(dest)
        .output()
        .map_err(|e| ElabError::BadForm(format!("git dependency: cannot run `git clone`: {e}")))?;
    if !clone.status.success() {
        let _ = std::fs::remove_dir_all(dest);
        return Err(ElabError::BadForm(format!(
            "git dependency: `git clone {url}` failed: {}",
            String::from_utf8_lossy(&clone.stderr).trim()
        )));
    }
    if let Some(rev) = rev {
        let checkout = std::process::Command::new("git")
            .arg("-C")
            .arg(dest)
            .arg("checkout")
            .arg("--quiet")
            .arg(rev)
            .output()
            .map_err(|e| {
                ElabError::BadForm(format!("git dependency: cannot run `git checkout`: {e}"))
            })?;
        if !checkout.status.success() {
            let _ = std::fs::remove_dir_all(dest);
            return Err(ElabError::BadForm(format!(
                "git dependency: `git checkout {rev}` in {dest:?} failed: {}",
                String::from_utf8_lossy(&checkout.stderr).trim()
            )));
        }
    }
    Ok(())
}

/// A parsed `spore.toml`: this package's name + root, and each dependency's name + root directory.
#[derive(Debug, Clone)]
pub struct PackageManifest {
    /// This package's declared name.
    pub name: String,
    /// This package's version string (informational).
    pub version: String,
    /// The package's own module identifiers (informational entry points).
    pub modules: Vec<String>,
    /// Package-name → source-root directory, including this package and every `path`/`version`/
    /// `git` dependency (a `git` dependency's root is its [`git_cache_dir`] — see `git_deps` for
    /// the declared source that cache is expected to hold).
    roots: BTreeMap<String, PathBuf>,
    /// Package-name → `git` source, for dependencies declared with `git = "…"` (A5) — the URL/rev
    /// [`fetch_git_dependency`] clones from; see the module doc.
    git_deps: BTreeMap<String, GitDep>,
}

impl PackageManifest {
    /// Parse a `spore.toml` whose text is `src`, with `base_dir` the manifest's directory (used to
    /// resolve relative dependency `path`s and to root this package's own modules).
    pub fn parse(src: &str, base_dir: &Path) -> Result<Self, ElabError> {
        let value: toml::Value = src
            .parse()
            .map_err(|e| ElabError::BadForm(format!("spore.toml: invalid TOML: {e}")))?;

        let package = value
            .get("package")
            .and_then(|p| p.as_table())
            .ok_or_else(|| ElabError::BadForm("spore.toml: missing [package] table".into()))?;
        let name = package
            .get("name")
            .and_then(|n| n.as_str())
            .ok_or_else(|| {
                ElabError::BadForm("spore.toml: [package] needs a string `name`".into())
            })?
            .to_string();
        let version = package
            .get("version")
            .and_then(|v| v.as_str())
            .unwrap_or("0.0.0")
            .to_string();

        let mut roots: BTreeMap<String, PathBuf> = BTreeMap::new();
        let mut git_deps: BTreeMap<String, GitDep> = BTreeMap::new();
        // This package's own modules are rooted at the manifest directory.
        roots.insert(name.clone(), base_dir.to_path_buf());

        // [dependencies]: each entry is `{ path = "…" }`, `{ version = "…" }`, or
        // `{ git = "…", rev = "…" }` (A5 extends the original `path`-only format).
        if let Some(deps) = value.get("dependencies").and_then(|d| d.as_table()) {
            for (dep_name, spec) in deps {
                let table = spec.as_table().ok_or_else(|| {
                    ElabError::BadForm(format!(
                        "spore.toml: dependency `{dep_name}` must be a table \
                         (`{{ path = \"…\" }}`, `{{ version = \"…\" }}`, or `{{ git = \"…\" }}`)"
                    ))
                })?;
                if let Some(path) = table.get("path").and_then(|p| p.as_str()) {
                    roots.insert(dep_name.clone(), base_dir.join(path));
                } else if let Some(version) = table.get("version").and_then(|v| v.as_str()) {
                    roots.insert(
                        dep_name.clone(),
                        registry_cache_dir(base_dir, dep_name, version),
                    );
                } else if let Some(url) = table.get("git").and_then(|g| g.as_str()) {
                    let rev = table
                        .get("rev")
                        .and_then(|r| r.as_str())
                        .map(str::to_string);
                    roots.insert(
                        dep_name.clone(),
                        git_cache_dir(base_dir, dep_name, rev.as_deref()),
                    );
                    git_deps.insert(
                        dep_name.clone(),
                        GitDep {
                            url: url.to_string(),
                            rev,
                        },
                    );
                } else {
                    return Err(ElabError::BadForm(format!(
                        "spore.toml: dependency `{dep_name}` needs one of \
                         `path = \"…\"`, `version = \"…\"`, or `git = \"…\"`"
                    )));
                }
            }
        }

        let modules = value
            .get("lib")
            .and_then(|l| l.as_table())
            .and_then(|t| t.get("modules"))
            .and_then(|m| m.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| v.as_str().map(str::to_string))
                    .collect()
            })
            .unwrap_or_default();

        Ok(PackageManifest {
            name,
            version,
            modules,
            roots,
            git_deps,
        })
    }

    /// The declared `git` source for dependency `dep_name`, if it was declared with
    /// `git = "…"` rather than `path`/`version` (informational; there is no fetch path for it —
    /// see the module doc's "A5: `version` and `git` dependencies" section).
    pub fn git_dependency(&self, dep_name: &str) -> Option<&GitDep> {
        self.git_deps.get(dep_name)
    }

    /// Resolve a module identifier `"pkg/sub/mod"` to its on-disk source path
    /// `<root-of-pkg>/sub/mod.bl`. A bare `"mod"` (no `/`) is taken as a module of *this* package.
    pub fn resolve_path(&self, module: &str) -> Result<PathBuf, ElabError> {
        let (pkg, rest) = match module.split_once('/') {
            Some((p, r)) => (p, r),
            None => (self.name.as_str(), module),
        };
        let root = match self.roots.get(pkg) {
            Some(root) => root,
            None => {
                return Err(ElabError::BadForm(format!(
                    "import: no package `{pkg}` in spore.toml dependencies (module `{module}`)"
                )));
            }
        };
        // Allow callers to pass a `.bl` suffix or not.
        let rest = rest.strip_suffix(".bl").unwrap_or(rest);
        Ok(root.join(format!("{rest}.bl")))
    }

    /// Read a module's source text by identifier.
    pub fn resolve(&self, module: &str) -> Result<String, ElabError> {
        let path = self.resolve_path(module)?;
        std::fs::read_to_string(&path).map_err(|e| {
            ElabError::BadForm(format!(
                "import: cannot read module {module:?} at {path:?}: {e}"
            ))
        })
    }

    /// A resolver closure mapping a module identifier to source text, for `Program::with_resolver`.
    pub fn resolver(&self) -> impl Fn(&str) -> Result<String, ElabError> + '_ {
        move |module: &str| self.resolve(module)
    }

    /// Compute a [`LockEntry`] for this package and every declared dependency: each entry's `hash`
    /// is a deterministic digest over every `.bl` file under that package's root (sorted by
    /// relative path, so file *order* never affects the hash, only file *content and presence*).
    /// Entries are sorted by name for a stable, diff-friendly `blight.lock`.
    pub fn lock_entries(&self) -> Vec<LockEntry> {
        let mut entries: Vec<LockEntry> = self
            .roots
            .iter()
            .map(|(name, root)| LockEntry {
                name: name.clone(),
                root: root.clone(),
                hash: hash_bl_tree(root),
            })
            .collect();
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        entries
    }

    /// Render a set of lock entries as `blight.lock`'s TOML text.
    pub fn render_lock(entries: &[LockEntry]) -> String {
        let mut out = String::from(
            "# Generated by `blight`; do not edit by hand (see docs/roadmap-post-m6.md Wave 1 / A2).\n",
        );
        for e in entries {
            out.push_str("[[package]]\n");
            out.push_str(&format!("name = {:?}\n", e.name));
            out.push_str(&format!("root = {:?}\n", e.root.display().to_string()));
            out.push_str(&format!("hash = {:?}\n\n", e.hash));
        }
        out
    }

    /// Parse a `blight.lock` file's text back into its entries (used to detect drift: a
    /// dependency whose on-disk `.bl` tree no longer matches its recorded hash).
    pub fn parse_lock(src: &str) -> Result<Vec<LockEntry>, ElabError> {
        let value: toml::Value = src
            .parse()
            .map_err(|e| ElabError::BadForm(format!("blight.lock: invalid TOML: {e}")))?;
        let packages = value
            .get("package")
            .and_then(|p| p.as_array())
            .cloned()
            .unwrap_or_default();
        let mut out = Vec::with_capacity(packages.len());
        for pkg in &packages {
            let name = pkg
                .get("name")
                .and_then(|n| n.as_str())
                .ok_or_else(|| ElabError::BadForm("blight.lock: entry missing `name`".into()))?
                .to_string();
            let root = pkg
                .get("root")
                .and_then(|r| r.as_str())
                .ok_or_else(|| ElabError::BadForm("blight.lock: entry missing `root`".into()))?
                .to_string();
            let hash = pkg
                .get("hash")
                .and_then(|h| h.as_str())
                .ok_or_else(|| ElabError::BadForm("blight.lock: entry missing `hash`".into()))?
                .to_string();
            out.push(LockEntry {
                name,
                root: PathBuf::from(root),
                hash,
            });
        }
        Ok(out)
    }

    /// Compare this manifest's freshly computed lock entries against a previously written
    /// `blight.lock`'s text (Wave 9 / T3), and reject if any *dependency*'s on-disk `.bl` tree no
    /// longer matches the hash the lock recorded — e.g. a `path` dependency was edited after being
    /// locked, or a registry/`git` vendor cache was tampered with. This is the build-time half of
    /// the "hash-verified against `blight.lock`" invariant; [`crate::registry::fetch_and_vendor`]
    /// is the fetch-time half.
    ///
    /// The primary package (`self.name`) is exempt: its own source is expected to change during
    /// ordinary development, so editing it is never "drift". A dependency present in the fresh
    /// entries but absent from `lock_src` (a *newly added* dependency) is not drift either — only
    /// a hash mismatch on a name present in both counts. A `lock_src` that fails to parse is
    /// treated as "no lock yet" (`Ok`) rather than an error: this check's whole job is catching
    /// silent drift, not policing the lockfile's own format.
    pub fn check_lock_drift(&self, lock_src: &str) -> Result<(), ElabError> {
        let Ok(old_entries) = Self::parse_lock(lock_src) else {
            return Ok(());
        };
        let old_by_name: BTreeMap<&str, &LockEntry> =
            old_entries.iter().map(|e| (e.name.as_str(), e)).collect();
        let mut drifted = Vec::new();
        for entry in self.lock_entries() {
            if entry.name == self.name {
                continue;
            }
            if let Some(old) = old_by_name.get(entry.name.as_str()) {
                if old.hash != entry.hash {
                    drifted.push(format!(
                        "`{}` (locked hash {}, now {})",
                        entry.name, old.hash, entry.hash
                    ));
                }
            }
        }
        if drifted.is_empty() {
            return Ok(());
        }
        Err(ElabError::BadForm(format!(
            "blight.lock: drift detected in {} dependenc{} — the on-disk source no longer \
             matches the hash recorded in blight.lock: {}. If this is expected (e.g. you \
             intentionally updated a vendored dependency), delete blight.lock to relock; \
             otherwise this may indicate a tampered or corrupted dependency.",
            drifted.len(),
            if drifted.len() == 1 { "y" } else { "ies" },
            drifted.join(", ")
        )))
    }
}

/// Add (or update) a `[dependencies]` entry `dep_name = { path = "dep_path" }` in a `spore.toml`
/// document's text, returning the updated text (the `blight add` CLI subcommand's core logic).
///
/// If `existing` is `None` (no `spore.toml` yet in the current directory), a minimal manifest is
/// created first, naming the package `default_pkg_name`. Note this round-trips through
/// `toml::Value`, so any hand-written comments/formatting in an *edited* manifest are not
/// preserved — acceptable for what is otherwise a generated config file, but worth knowing before
/// running `blight add` on a manifest a human has lovingly formatted.
pub fn add_dependency(
    existing: Option<&str>,
    default_pkg_name: &str,
    dep_name: &str,
    dep_path: &str,
) -> Result<String, ElabError> {
    let mut dep_table = toml::value::Table::new();
    dep_table.insert("path".into(), toml::Value::String(dep_path.to_string()));
    add_dependency_entry(existing, default_pkg_name, dep_name, dep_table)
}

/// Add (or update) a `[dependencies]` entry `dep_name = { version = "version" }` in a `spore.toml`
/// document's text — the registry form of [`add_dependency`] (A5), used by `blight add`'s
/// `--version`/`--registry` form once [`crate::registry::fetch_and_vendor`] has already fetched and
/// hash-verified the package into its local vendor cache.
pub fn add_registry_dependency(
    existing: Option<&str>,
    default_pkg_name: &str,
    dep_name: &str,
    version: &str,
) -> Result<String, ElabError> {
    let mut dep_table = toml::value::Table::new();
    dep_table.insert("version".into(), toml::Value::String(version.to_string()));
    add_dependency_entry(existing, default_pkg_name, dep_name, dep_table)
}

/// Add (or update) a `[dependencies]` entry `dep_name = { git = "url", rev = "rev" }` (`rev` is
/// omitted when `None`) in a `spore.toml` document's text — the git form of [`add_dependency`]
/// (Wave 9 / T3), used by `blight add`'s `--git`/`--rev` form once [`fetch_git_dependency`] has
/// already cloned (and, if `rev` is given, checked out) the dependency into its local vendor
/// cache.
pub fn add_git_dependency(
    existing: Option<&str>,
    default_pkg_name: &str,
    dep_name: &str,
    url: &str,
    rev: Option<&str>,
) -> Result<String, ElabError> {
    let mut dep_table = toml::value::Table::new();
    dep_table.insert("git".into(), toml::Value::String(url.to_string()));
    if let Some(rev) = rev {
        dep_table.insert("rev".into(), toml::Value::String(rev.to_string()));
    }
    add_dependency_entry(existing, default_pkg_name, dep_name, dep_table)
}

/// Shared core of [`add_dependency`]/[`add_registry_dependency`]: insert `dep_table` as
/// `[dependencies].dep_name` in `existing`'s TOML text (creating a minimal manifest first if
/// `existing` is `None`), and re-render it.
///
/// This round-trips through `toml::Value`, so any hand-written comments/formatting in an *edited*
/// manifest are not preserved — acceptable for what is otherwise a generated config file, but worth
/// knowing before running `blight add` on a manifest a human has lovingly formatted.
fn add_dependency_entry(
    existing: Option<&str>,
    default_pkg_name: &str,
    dep_name: &str,
    dep_table: toml::value::Table,
) -> Result<String, ElabError> {
    let mut doc: toml::Value = match existing {
        Some(src) => src
            .parse()
            .map_err(|e| ElabError::BadForm(format!("spore.toml: invalid TOML: {e}")))?,
        None => {
            let mut package = toml::value::Table::new();
            package.insert(
                "name".into(),
                toml::Value::String(default_pkg_name.to_string()),
            );
            package.insert("version".into(), toml::Value::String("0.1.0".to_string()));
            let mut root = toml::value::Table::new();
            root.insert("package".into(), toml::Value::Table(package));
            toml::Value::Table(root)
        }
    };
    let root = doc
        .as_table_mut()
        .ok_or_else(|| ElabError::BadForm("spore.toml: not a table".into()))?;
    if !root.contains_key("package") {
        return Err(ElabError::BadForm(
            "spore.toml: missing [package] table (cannot add a dependency to it)".into(),
        ));
    }
    let deps = root
        .entry("dependencies")
        .or_insert_with(|| toml::Value::Table(toml::value::Table::new()))
        .as_table_mut()
        .ok_or_else(|| ElabError::BadForm("spore.toml: [dependencies] is not a table".into()))?;
    deps.insert(dep_name.to_string(), toml::Value::Table(dep_table));

    toml::to_string_pretty(&doc)
        .map_err(|e| ElabError::BadForm(format!("spore.toml: cannot serialize: {e}")))
}

/// A resolved dependency lock entry: package name, its resolved (as given in `spore.toml`) root
/// directory, and a content hash over every `.bl` file found under that root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockEntry {
    pub name: String,
    pub root: PathBuf,
    pub hash: String,
}

/// FNV-1a: a small, dependency-free, and — unlike `std`'s `DefaultHasher` — *specified* (not just
/// incidentally stable) 64-bit hash, appropriate for a lockfile that should keep meaning the same
/// thing across Rust toolchain upgrades.
fn fnv1a_feed(hash: &mut u64, bytes: &[u8]) {
    for &b in bytes {
        *hash ^= b as u64;
        *hash = hash.wrapping_mul(0x0000_0100_0000_01B3);
    }
}

/// Every `.bl` file under `root`, as paths relative to `root`, in sorted (deterministic) order.
/// Missing/unreadable roots yield an empty list rather than an error — a lock hash of "no files"
/// is itself meaningful (and `lock_entries` has no `Result` to propagate one through).
///
/// `pub(crate)` so [`crate::registry::publish`] (Wave 9 / T3) packages *exactly* the files
/// [`hash_bl_tree`] hashes — a published tarball must contain precisely the set of files its
/// recorded hash was computed over, or a consumer's `fetch_and_vendor` would (correctly) reject
/// it as tampered.
pub(crate) fn list_bl_files_relative(root: &Path) -> Vec<PathBuf> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, root, out);
            } else if path.extension().is_some_and(|ext| ext == "bl") {
                if let Ok(rel) = path.strip_prefix(root) {
                    out.push(rel.to_path_buf());
                }
            }
        }
    }
    let mut out = Vec::new();
    walk(root, root, &mut out);
    out.sort();
    out
}

/// Hash every `.bl` file under `root` (relative path, then length, then content, per file, in
/// sorted-path order) into a single 16-hex-digit digest.
///
/// `pub(crate)` so [`crate::registry::fetch_and_vendor`] can verify a freshly extracted package
/// against the *same* digest a registry index publishes and `blight.lock` records (A5) — one hash
/// function, three call sites, one meaning.
pub(crate) fn hash_bl_tree(root: &Path) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for rel in list_bl_files_relative(root) {
        fnv1a_feed(&mut hash, rel.to_string_lossy().as_bytes());
        if let Ok(content) = std::fs::read(root.join(&rel)) {
            fnv1a_feed(&mut hash, &content.len().to_le_bytes());
            fnv1a_feed(&mut hash, &content);
        }
    }
    format!("{hash:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_package_and_dependency_roots() {
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n\
             [dependencies]\nstd = { path = \"vendor/std\" }\n\
             [lib]\nmodules = [\"demo/main\"]",
            Path::new("/proj"),
        )
        .expect("parses");
        assert_eq!(m.name, "demo");
        assert_eq!(m.version, "0.1.0");
        assert_eq!(m.modules, vec!["demo/main".to_string()]);
        assert_eq!(
            m.resolve_path("std/nat").unwrap(),
            PathBuf::from("/proj/vendor/std/nat.bl")
        );
        // Own-package module, with and without a `pkg/` prefix and `.bl` suffix.
        assert_eq!(
            m.resolve_path("demo/main").unwrap(),
            PathBuf::from("/proj/main.bl")
        );
        assert_eq!(
            m.resolve_path("main.bl").unwrap(),
            PathBuf::from("/proj/main.bl")
        );
    }

    #[test]
    fn unknown_package_is_an_error() {
        let m = PackageManifest::parse("[package]\nname = \"demo\"\n", Path::new("/proj"))
            .expect("parses");
        let r = m.resolve_path("nope/mod");
        assert!(matches!(r, Err(ElabError::BadForm(ref s)) if s.contains("no package `nope`")));
    }

    // ---- A5: `version` and `git` dependencies -------------------------------------------------

    #[test]
    fn version_dependency_parses_and_resolves_to_the_registry_cache_dir() {
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n\
             [dependencies]\nremote = { version = \"1.2.3\" }\n",
            Path::new("/proj"),
        )
        .expect("a `version` dependency parses");
        assert_eq!(
            m.resolve_path("remote/mod").unwrap(),
            PathBuf::from("/proj/.blight/registry/remote-1.2.3/mod.bl"),
            "resolves to the conventional local vendor-cache path"
        );
    }

    #[test]
    fn version_dependency_actually_resolves_once_vendored() {
        // "resolves" end-to-end: once a file sits at the exact cache path `blight add`'s registry
        // form would have vendored it to, resolution reads it back with no further machinery.
        let pkg = TempPkg::new("version_resolve");
        pkg.write(".blight/registry/remote-1.2.3/mod.bl", "(the Unit Zero)");
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n\
             [dependencies]\nremote = { version = \"1.2.3\" }\n",
            &pkg.dir,
        )
        .expect("parses");
        assert_eq!(m.resolve("remote/mod").unwrap(), "(the Unit Zero)");
    }

    #[test]
    fn git_dependency_parses_and_resolves_to_the_git_cache_dir() {
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n\
             [dependencies]\nbleed = { git = \"https://example.com/bleed.git\", rev = \"abc123\" }\n",
            Path::new("/proj"),
        )
        .expect("a `git` dependency parses");
        assert_eq!(
            m.git_dependency("bleed"),
            Some(&GitDep {
                url: "https://example.com/bleed.git".to_string(),
                rev: Some("abc123".to_string()),
            })
        );
        assert_eq!(
            m.resolve_path("bleed/mod").unwrap(),
            PathBuf::from("/proj/.blight/git/bleed-abc123/mod.bl"),
            "resolves to the conventional local git-cache path (Wave 9 / T3)"
        );
    }

    #[test]
    fn git_dependency_without_rev_resolves_under_head() {
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n\
             [dependencies]\nbleed = { git = \"https://example.com/bleed.git\" }\n",
            Path::new("/proj"),
        )
        .expect("a `git` dependency without a rev parses");
        assert_eq!(
            m.resolve_path("bleed/mod").unwrap(),
            PathBuf::from("/proj/.blight/git/bleed-HEAD/mod.bl")
        );
    }

    #[test]
    fn git_dependency_actually_resolves_once_vendored() {
        // Same "resolves end-to-end once vendored" shape as the registry `version` dependency
        // test: once a file sits at the exact cache path `blight add --git` would have cloned to,
        // resolution reads it back with no further machinery.
        let pkg = TempPkg::new("git_resolve");
        pkg.write(".blight/git/bleed-abc123/mod.bl", "(the Unit Zero)");
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n\
             [dependencies]\nbleed = { git = \"https://example.com/bleed.git\", rev = \"abc123\" }\n",
            &pkg.dir,
        )
        .expect("parses");
        assert_eq!(m.resolve("bleed/mod").unwrap(), "(the Unit Zero)");
    }

    /// A minimal on-disk `file://`-clonable git repository fixture: `git init`, commit one file,
    /// return its directory + the commit SHA it landed on. Network-free (loopback git isn't even
    /// involved — `git clone` supports plain local paths directly), so `fetch_git_dependency`'s
    /// tests never touch the real network, matching this project's testing conventions.
    struct GitFixture {
        dir: PathBuf,
        rev: String,
    }
    impl GitFixture {
        fn new(tag: &str, file_name: &str, content: &str) -> GitFixture {
            let dir = std::env::temp_dir().join(format!(
                "blight_git_fixture_{tag}_{}_{}",
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
            std::fs::write(dir.join(file_name), content).unwrap();
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

    #[test]
    fn git_dep_resolves_at_rev() {
        let repo = GitFixture::new("resolves_at_rev", "mod.bl", "(the Unit Zero)");
        let dest = TempPkg::new("git_dep_resolves_at_rev_dest");
        let dest_dir = dest.dir.join("vendored");

        fetch_git_dependency(&repo.dir.to_string_lossy(), Some(&repo.rev), &dest_dir)
            .expect("clone + checkout at the pinned rev succeeds");
        assert_eq!(
            std::fs::read_to_string(dest_dir.join("mod.bl")).unwrap(),
            "(the Unit Zero)"
        );

        // Idempotent: fetching again into an already-vendored, non-empty destination is a no-op
        // (does not error, does not require network/re-clone).
        fetch_git_dependency(&repo.dir.to_string_lossy(), Some(&repo.rev), &dest_dir)
            .expect("re-fetching an already-vendored git dependency is a no-op");
    }

    #[test]
    fn git_dep_fetch_rejects_an_unknown_rev() {
        let repo = GitFixture::new("unknown_rev", "mod.bl", "(the Unit Zero)");
        let dest = TempPkg::new("git_dep_unknown_rev_dest");
        let dest_dir = dest.dir.join("vendored");

        let r = fetch_git_dependency(
            &repo.dir.to_string_lossy(),
            Some("0000000000000000000000000000000000dead"),
            &dest_dir,
        );
        assert!(r.is_err(), "an unresolvable rev must be a hard error");
        assert!(
            !dest_dir.exists(),
            "a failed checkout must not leave a partially-vendored directory behind"
        );
    }

    #[test]
    fn add_git_dependency_writes_manifest() {
        let out = add_git_dependency(
            None,
            "demo",
            "bleed",
            "https://example.com/bleed.git",
            Some("abc123"),
        )
        .expect("adds a git dep");
        let m = PackageManifest::parse(&out, Path::new("/proj")).expect("reparses");
        assert_eq!(
            m.git_dependency("bleed"),
            Some(&GitDep {
                url: "https://example.com/bleed.git".to_string(),
                rev: Some("abc123".to_string()),
            })
        );
        assert_eq!(
            m.resolve_path("bleed/x").unwrap(),
            PathBuf::from("/proj/.blight/git/bleed-abc123/x.bl")
        );
    }

    #[test]
    fn add_git_dependency_without_rev_omits_it() {
        let out = add_git_dependency(None, "demo", "bleed", "https://example.com/bleed.git", None)
            .expect("adds a git dep with no pinned rev");
        let m = PackageManifest::parse(&out, Path::new("/proj")).expect("reparses");
        assert_eq!(
            m.git_dependency("bleed"),
            Some(&GitDep {
                url: "https://example.com/bleed.git".to_string(),
                rev: None,
            })
        );
    }

    #[test]
    fn dependency_without_path_version_or_git_is_a_parse_error() {
        let r = PackageManifest::parse(
            "[package]\nname = \"demo\"\n[dependencies]\nbad = { branch = \"main\" }\n",
            Path::new("/proj"),
        );
        assert!(matches!(r, Err(ElabError::BadForm(ref s)) if s.contains("bad")));
    }

    // ---- `blight.lock` (Wave 1 / A2) ----------------------------------------------------------

    /// A scratch on-disk package tree under `std::env::temp_dir()`, cleaned up on drop, so lock
    /// tests exercise the real filesystem walk rather than an in-memory stand-in.
    struct TempPkg {
        dir: PathBuf,
    }
    impl TempPkg {
        fn new(tag: &str) -> TempPkg {
            let dir = std::env::temp_dir().join(format!(
                "blight_spores_lock_{tag}_{}_{}",
                std::process::id(),
                tag.len() // cheap uniqueness nudge across calls with same tag length collisions
            ));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            TempPkg { dir }
        }
        fn write(&self, rel: &str, content: &str) {
            let path = self.dir.join(rel);
            if let Some(parent) = path.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            std::fs::write(path, content).unwrap();
        }
    }
    impl Drop for TempPkg {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    #[test]
    fn lock_entries_cover_the_package_and_its_dependencies() {
        let pkg = TempPkg::new("entries");
        pkg.write("main.bl", "(the Unit Zero)");
        pkg.write("vendor/std/nat.bl", "(defdata Nat () (Zero))");
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n[dependencies]\nstd = { path = \"vendor/std\" }\n",
            &pkg.dir,
        )
        .expect("parses");
        let entries = m.lock_entries();
        let names: Vec<&str> = entries.iter().map(|e| e.name.as_str()).collect();
        assert_eq!(names, vec!["demo", "std"], "sorted by name: {names:?}");
        assert!(entries.iter().all(|e| !e.hash.is_empty()));
    }

    #[test]
    fn lock_hash_changes_when_a_dependency_file_changes() {
        let pkg = TempPkg::new("drift");
        pkg.write("main.bl", "(the Unit Zero)");
        let m = PackageManifest::parse("[package]\nname = \"demo\"\n", &pkg.dir).expect("parses");
        let before = m.lock_entries();

        pkg.write("main.bl", "(the Unit Zero) ; changed");
        let after = m.lock_entries();

        assert_ne!(
            before[0].hash, after[0].hash,
            "editing a tracked file must change the lock hash"
        );
    }

    #[test]
    fn lock_hash_is_stable_across_recomputation() {
        let pkg = TempPkg::new("stable");
        pkg.write("main.bl", "(the Unit Zero)");
        pkg.write("sub/mod.bl", "(define x (the Unit Zero))");
        let m = PackageManifest::parse("[package]\nname = \"demo\"\n", &pkg.dir).expect("parses");
        assert_eq!(
            m.lock_entries(),
            m.lock_entries(),
            "recomputing is deterministic"
        );
    }

    // ---- `blight add` (Wave 1 / A2) -----------------------------------------------------------

    #[test]
    fn add_dependency_creates_a_manifest_when_none_exists() {
        let out = add_dependency(None, "demo", "std", "../blight-prelude").expect("creates");
        let m = PackageManifest::parse(&out, Path::new("/proj")).expect("the result reparses");
        assert_eq!(m.name, "demo");
        assert_eq!(
            m.resolve_path("std/nat").unwrap(),
            PathBuf::from("/proj/../blight-prelude/nat.bl")
        );
    }

    #[test]
    fn add_dependency_preserves_existing_dependencies() {
        let existing = "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n\
                         [dependencies]\nfoo = { path = \"../foo\" }\n";
        let out = add_dependency(Some(existing), "demo", "bar", "../bar").expect("adds");
        let m = PackageManifest::parse(&out, Path::new("/proj")).expect("reparses");
        assert_eq!(
            m.resolve_path("foo/x").unwrap(),
            PathBuf::from("/proj/../foo/x.bl")
        );
        assert_eq!(
            m.resolve_path("bar/y").unwrap(),
            PathBuf::from("/proj/../bar/y.bl")
        );
    }

    #[test]
    fn add_dependency_updates_an_existing_entry() {
        let existing = "[package]\nname = \"demo\"\n\
                         [dependencies]\nfoo = { path = \"../old-foo\" }\n";
        let out = add_dependency(Some(existing), "demo", "foo", "../new-foo").expect("updates");
        let m = PackageManifest::parse(&out, Path::new("/proj")).expect("reparses");
        assert_eq!(
            m.resolve_path("foo/x").unwrap(),
            PathBuf::from("/proj/../new-foo/x.bl")
        );
    }

    #[test]
    fn add_dependency_rejects_a_manifest_without_a_package_table() {
        let r = add_dependency(Some("[dependencies]\n"), "demo", "foo", "../foo");
        assert!(matches!(r, Err(ElabError::BadForm(ref m)) if m.contains("[package]")));
    }

    #[test]
    fn add_registry_dependency_writes_a_version_entry() {
        let out =
            add_registry_dependency(None, "demo", "remote", "1.2.3").expect("adds a version dep");
        let m = PackageManifest::parse(&out, Path::new("/proj")).expect("reparses");
        assert_eq!(
            m.resolve_path("remote/x").unwrap(),
            PathBuf::from("/proj/.blight/registry/remote-1.2.3/x.bl")
        );
    }

    #[test]
    fn lockfile_drift_is_rejected() {
        let pkg = TempPkg::new("drift_reject");
        pkg.write("main.bl", "(the Unit Zero)");
        pkg.write("vendor/std/nat.bl", "(defdata Nat () (Zero))");
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n[dependencies]\nstd = { path = \"vendor/std\" }\n",
            &pkg.dir,
        )
        .expect("parses");

        // Lock the current (honest) state, then tamper with the dependency after the fact.
        let locked = PackageManifest::render_lock(&m.lock_entries());
        pkg.write(
            "vendor/std/nat.bl",
            "(defdata Nat () (Zero) (Succ (n Nat))) ; tampered",
        );

        let r = m.check_lock_drift(&locked);
        assert!(
            matches!(r, Err(ElabError::BadForm(ref s)) if s.contains("std") && s.contains("drift")),
            "a changed dependency must be reported as drift: {r:?}"
        );
    }

    #[test]
    fn lockfile_drift_ignores_the_primary_packages_own_changes() {
        // Editing the package you're actively developing is normal, not "drift" — only
        // *dependency* hash mismatches should reject.
        let pkg = TempPkg::new("drift_self_ok");
        pkg.write("main.bl", "(the Unit Zero)");
        let m = PackageManifest::parse("[package]\nname = \"demo\"\n", &pkg.dir).expect("parses");
        let locked = PackageManifest::render_lock(&m.lock_entries());

        pkg.write(
            "main.bl",
            "(the Unit Zero) ; edited during normal development",
        );
        assert!(m.check_lock_drift(&locked).is_ok());
    }

    #[test]
    fn lockfile_drift_ignores_newly_added_dependencies() {
        // A dependency added since the lock was last written isn't "drift" (nothing to compare
        // against) — it's simply new.
        let pkg = TempPkg::new("drift_new_dep_ok");
        pkg.write("main.bl", "(the Unit Zero)");
        let before = PackageManifest::parse("[package]\nname = \"demo\"\n", &pkg.dir).unwrap();
        let locked = PackageManifest::render_lock(&before.lock_entries());

        pkg.write("vendor/extra/mod.bl", "(the Unit Zero)");
        let after = PackageManifest::parse(
            "[package]\nname = \"demo\"\n[dependencies]\nextra = { path = \"vendor/extra\" }\n",
            &pkg.dir,
        )
        .unwrap();
        assert!(after.check_lock_drift(&locked).is_ok());
    }

    #[test]
    fn lockfile_drift_ok_when_dependency_is_unchanged() {
        let pkg = TempPkg::new("drift_unchanged_ok");
        pkg.write("main.bl", "(the Unit Zero)");
        pkg.write("vendor/std/nat.bl", "(defdata Nat () (Zero))");
        let m = PackageManifest::parse(
            "[package]\nname = \"demo\"\n[dependencies]\nstd = { path = \"vendor/std\" }\n",
            &pkg.dir,
        )
        .unwrap();
        let locked = PackageManifest::render_lock(&m.lock_entries());
        assert!(m.check_lock_drift(&locked).is_ok());
    }

    #[test]
    fn render_and_parse_lock_round_trip() {
        let pkg = TempPkg::new("roundtrip");
        pkg.write("main.bl", "(the Unit Zero)");
        let m = PackageManifest::parse("[package]\nname = \"demo\"\n", &pkg.dir).expect("parses");
        let entries = m.lock_entries();
        let rendered = PackageManifest::render_lock(&entries);
        let parsed = PackageManifest::parse_lock(&rendered).expect("blight.lock parses");
        assert_eq!(parsed, entries);
    }
}
