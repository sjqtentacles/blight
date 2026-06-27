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

use crate::ElabError;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// A parsed `spore.toml`: this package's name + root, and each dependency's name + root directory.
#[derive(Debug, Clone)]
pub struct PackageManifest {
    /// This package's declared name.
    pub name: String,
    /// This package's version string (informational).
    pub version: String,
    /// The package's own module identifiers (informational entry points).
    pub modules: Vec<String>,
    /// Package-name → source-root directory, including this package and every dependency.
    roots: BTreeMap<String, PathBuf>,
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
        // This package's own modules are rooted at the manifest directory.
        roots.insert(name.clone(), base_dir.to_path_buf());

        // [dependencies]: each entry is `dep = { path = "..." }` (relative to `base_dir`).
        if let Some(deps) = value.get("dependencies").and_then(|d| d.as_table()) {
            for (dep_name, spec) in deps {
                let path = spec
                    .as_table()
                    .and_then(|t| t.get("path"))
                    .and_then(|p| p.as_str())
                    .ok_or_else(|| {
                        ElabError::BadForm(format!(
                            "spore.toml: dependency `{dep_name}` needs a `path = \"…\"`"
                        ))
                    })?;
                let root = base_dir.join(path);
                roots.insert(dep_name.clone(), root);
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
        })
    }

    /// Resolve a module identifier `"pkg/sub/mod"` to its on-disk source path
    /// `<root-of-pkg>/sub/mod.bl`. A bare `"mod"` (no `/`) is taken as a module of *this* package.
    pub fn resolve_path(&self, module: &str) -> Result<PathBuf, ElabError> {
        let (pkg, rest) = match module.split_once('/') {
            Some((p, r)) => (p, r),
            None => (self.name.as_str(), module),
        };
        let root = self.roots.get(pkg).ok_or_else(|| {
            ElabError::BadForm(format!(
                "import: no package `{pkg}` in spore.toml dependencies (module `{module}`)"
            ))
        })?;
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
}
