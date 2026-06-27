//! `spores` package-manager acceptance (spec §8.2, §9 M6): a `spore.toml` manifest resolves module
//! identifiers, and the `(import "pkg/mod")` form is idempotent and cycle-checked. Black-box: the
//! `blight-elab` public `Program`/`PackageManifest` API only.

use blight_elab::{ElabEnv, Outcome, PackageManifest, Program};
use std::path::{Path, PathBuf};

/// Absolute path to `crates/blight-prelude/std` (the root of the `std` package).
fn prelude_dir() -> PathBuf {
    PathBuf::from(format!(
        "{}/../blight-prelude/std",
        env!("CARGO_MANIFEST_DIR")
    ))
}

/// Create a unique temp dir for a test fixture and return it.
fn temp_dir(tag: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    dir.push(format!(
        "blight-spores-{tag}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// A manifest that resolves `std/<mod>` against the real prelude std tree loads a dependency
/// module's source through the resolver.
#[test]
fn spores_resolver_loads_dependency() {
    let prelude = prelude_dir();
    let toml = format!(
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\n\
         [dependencies]\nstd = {{ path = {:?} }}\n",
        prelude.to_string_lossy()
    );
    let manifest = PackageManifest::parse(&toml, Path::new("/unused")).expect("manifest parses");
    // The resolver maps `std/nat` to `<prelude>/std/nat.bl` and returns its source.
    let src = manifest.resolve("std/nat").expect("resolves std/nat");
    assert!(
        src.contains("(defdata Nat"),
        "resolved source is std/nat.bl"
    );
}

/// A manifest-backed `Program` imports a std module and the imported definitions are in scope.
#[test]
fn import_resolves_std() {
    let prelude = prelude_dir();
    let toml = format!(
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\n\
         [dependencies]\nstd = {{ path = {:?} }}\n",
        prelude.to_string_lossy()
    );
    let manifest = PackageManifest::parse(&toml, Path::new("/unused")).expect("manifest parses");
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_package(&mut env, manifest);
        prog.run("(import \"std/nat\")\n(the Nat (plus (Succ Zero) (Succ Zero)))")
            .expect("imports std/nat and uses plus")
    };
    assert!(
        matches!(outcomes.last(), Some(Outcome::Checked(_))),
        "the use of the imported `plus` is kernel-checked"
    );
    assert!(
        env.global_term("plus").is_some(),
        "plus is imported into scope"
    );
}

/// Importing the same module twice splices it once: the second `(import …)` is a no-op, so a module
/// carrying an `(instance …)` does not trigger an overlapping-instance error on re-import.
#[test]
fn import_is_idempotent() {
    let dir = temp_dir("idem");
    // A module with an instance: re-splicing it would be an overlapping-instance error.
    std::fs::write(
        dir.join("ord.bl"),
        "(defdata Nat () (Zero) (Succ (n Nat)))\n\
         (class Show)\n\
         (define Show (Pi ((a (Type 0))) (Type 0)) (lam (a) (Pi ((x a)) Nat)))\n\
         (instance (Show Nat) (lam (n) n))",
    )
    .unwrap();
    let toml = format!(
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\n\
         [dependencies]\napp_dep = {{ path = {:?} }}\n",
        dir.to_string_lossy()
    );
    let manifest = PackageManifest::parse(&toml, Path::new("/unused")).expect("manifest parses");
    let mut env = ElabEnv::new();
    let result = {
        let mut prog = Program::with_package(&mut env, manifest);
        // Import twice — directly and via a second top-level import.
        prog.run("(import \"app_dep/ord\")\n(import \"app_dep/ord\")")
    };
    assert!(
        result.is_ok(),
        "the second import is a no-op (no overlapping-instance error): {result:?}"
    );
    assert!(env.is_class("Show"), "Show class registered exactly once");
}

/// Two modules that import each other are a cycle; the importer reports it instead of looping.
#[test]
fn import_cycle_detected() {
    let dir = temp_dir("cycle");
    std::fs::write(dir.join("a.bl"), "(import \"app/b\")").unwrap();
    std::fs::write(dir.join("b.bl"), "(import \"app/a\")").unwrap();
    // The package's own name is `app`, rooted at `dir`, so `app/a` and `app/b` resolve here.
    let toml = "[package]\nname = \"app\"\nversion = \"0.1.0\"\n";
    let manifest = PackageManifest::parse(toml, &dir).expect("manifest parses");
    let mut env = ElabEnv::new();
    let result = {
        let mut prog = Program::with_package(&mut env, manifest);
        prog.run("(import \"app/a\")")
    };
    assert!(
        matches!(result, Err(blight_elab::ElabError::BadForm(ref m)) if m.contains("cycle")),
        "an import cycle is detected and reported: {result:?}"
    );
}
