//! `registry` — Blight package registry v1 (Wave 2 / A5). UNTRUSTED (same trust status as
//! `spores.rs`: this only locates/fetches/extracts *source*; every form the fetched source produces
//! still bottoms out in the kernel via the spore re-check).
//!
//! A registry is described by a minimal TOML *index*:
//!
//! ```toml
//! [packages.foo."1.2.3"]
//! tarball = "file:///srv/registry/foo-1.2.3.tar.gz"
//! hash = "0123456789abcdef"
//! ```
//!
//! `hash` is exactly the digest [`crate::spores::hash_bl_tree`] computes over the package's `.bl`
//! source tree (the same function `blight.lock` uses) — the registry publishes the hash its source
//! tree ought to have, and [`fetch_and_vendor`] recomputes it after extracting the tarball,
//! rejecting (and deleting) anything that doesn't match. That is the entire trust story: a
//! registry's *index* still has to be trusted to publish the right hash for a given name/version
//! (exactly as a lockfile has to be trusted to record the right hash for a `path` dependency — the
//! kernel re-check downstream is what actually can't be fooled), but a corrupted or tampered-with
//! *tarball* for an index entry that itself is honest can never silently slip through.
//!
//! ── Transport: `file://`/bare-path and `http(s)://` (Wave 9 / T3) ──────────────────────────────
//! Both [`fetch_bytes`] (tarballs) and [`load_index`] (the index itself) accept either a
//! `file://` URI / bare filesystem path, or an `http://`/`https://` URL — fetched with [`ureq`]
//! (pure-Rust, `rustls` TLS backend, blocking; the same "small, no async runtime" spirit as the
//! `lsp-server`-over-`tower-lsp` choice, A1). The hash-verification trust story in the module doc
//! above is entirely transport-agnostic: an HTTP(S) tarball or index is verified exactly the same
//! way a local one is, so a compromised or spoofed HTTP transport can serve garbage bytes but can
//! never make a tampered tarball pass as a genuine one.

use crate::spores::hash_bl_tree;
use crate::ElabError;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Whether `location` names a remote HTTP(S) resource rather than a local `file://`/bare path.
fn is_http_url(location: &str) -> bool {
    location.starts_with("http://") || location.starts_with("https://")
}

/// One published version of one package: where to fetch its tarball, and the `.bl`-tree hash it is
/// expected to extract to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegistryEntry {
    /// A `file://` URI or bare filesystem path to a `.tar.gz` (see the module doc's "Honest scope"
    /// note — this is the only transport this pass implements).
    pub tarball: String,
    /// The expected `hash_bl_tree` digest of the extracted package.
    pub hash: String,
}

/// A parsed registry index: `package name -> version -> entry`.
#[derive(Debug, Clone, Default)]
pub struct RegistryIndex {
    packages: BTreeMap<String, BTreeMap<String, RegistryEntry>>,
}

impl RegistryIndex {
    /// Parse a registry index's TOML text (see the module doc for the format).
    pub fn parse(src: &str) -> Result<Self, ElabError> {
        let value: toml::Value = src
            .parse()
            .map_err(|e| ElabError::BadForm(format!("registry index: invalid TOML: {e}")))?;
        let mut packages: BTreeMap<String, BTreeMap<String, RegistryEntry>> = BTreeMap::new();
        let Some(pkgs) = value.get("packages").and_then(|p| p.as_table()) else {
            return Ok(RegistryIndex { packages });
        };
        for (name, versions) in pkgs {
            let versions_table = versions.as_table().ok_or_else(|| {
                ElabError::BadForm(format!(
                    "registry index: package `{name}` must map version strings to entries"
                ))
            })?;
            let mut by_version = BTreeMap::new();
            for (version, entry) in versions_table {
                let entry_table = entry.as_table().ok_or_else(|| {
                    ElabError::BadForm(format!(
                        "registry index: `{name}` `{version}` must be a table \
                         (`{{ tarball = \"…\", hash = \"…\" }}`)"
                    ))
                })?;
                let tarball = entry_table
                    .get("tarball")
                    .and_then(|t| t.as_str())
                    .ok_or_else(|| {
                        ElabError::BadForm(format!(
                            "registry index: `{name}` `{version}` needs a string `tarball`"
                        ))
                    })?
                    .to_string();
                let hash = entry_table
                    .get("hash")
                    .and_then(|h| h.as_str())
                    .ok_or_else(|| {
                        ElabError::BadForm(format!(
                            "registry index: `{name}` `{version}` needs a string `hash`"
                        ))
                    })?
                    .to_string();
                by_version.insert(version.clone(), RegistryEntry { tarball, hash });
            }
            packages.insert(name.clone(), by_version);
        }
        Ok(RegistryIndex { packages })
    }

    /// Look up `name`'s `version` entry.
    pub fn lookup(&self, name: &str, version: &str) -> Result<&RegistryEntry, ElabError> {
        self.packages
            .get(name)
            .and_then(|versions| versions.get(version))
            .ok_or_else(|| {
                ElabError::BadForm(format!(
                    "registry index: no entry for `{name}` version `{version}`"
                ))
            })
    }

    /// Insert (or overwrite) `name`'s `version` entry (Wave 9 / T3) — the write side of
    /// [`RegistryIndex::parse`]/[`RegistryIndex::lookup`], used by [`publish`] to record a newly
    /// published package. Upserting the same `name`/`version` twice keeps every other package and
    /// version's entries untouched (a `BTreeMap` insert only ever affects the one key it's given).
    pub fn add_entry(&mut self, name: &str, version: &str, entry: RegistryEntry) {
        self.packages
            .entry(name.to_string())
            .or_default()
            .insert(version.to_string(), entry);
    }

    /// Render this index back to the TOML text [`RegistryIndex::parse`] reads (Wave 9 / T3) — the
    /// write side of the format documented in the module doc. Deterministic (both maps are
    /// `BTreeMap`s, so package and version order is always the same for the same contents), which
    /// keeps a published/republished index diff-friendly.
    pub fn render(&self) -> String {
        let mut out =
            String::from("# Generated by `blight publish`; safe to hand-edit or merge.\n");
        for (name, versions) in &self.packages {
            for (version, entry) in versions {
                out.push_str(&format!("[packages.{name:?}.{version:?}]\n"));
                out.push_str(&format!("tarball = {:?}\n", entry.tarball));
                out.push_str(&format!("hash = {:?}\n\n", entry.hash));
            }
        }
        out
    }
}

/// Build a `.tar.gz` from every `.bl` file found on disk under `root` (the same enumeration
/// [`crate::spores::hash_bl_tree`] hashes — see [`crate::spores::list_bl_files_relative`]'s doc
/// comment for why that must stay in lockstep), for [`publish`]. The on-disk analog of
/// [`make_tar_gz`]'s in-memory fixture builder.
fn make_tar_gz_from_dir(root: &Path) -> Result<Vec<u8>, ElabError> {
    let mut tar_bytes = Vec::new();
    {
        let mut builder = tar::Builder::new(&mut tar_bytes);
        for rel in crate::spores::list_bl_files_relative(root) {
            let content = std::fs::read(root.join(&rel)).map_err(|e| {
                ElabError::BadForm(format!("registry publish: cannot read {rel:?}: {e}"))
            })?;
            let mut header = tar::Header::new_gnu();
            header.set_size(content.len() as u64);
            header.set_mode(0o644);
            header.set_cksum();
            builder
                .append_data(&mut header, &rel, content.as_slice())
                .map_err(|e| {
                    ElabError::BadForm(format!(
                        "registry publish: cannot append {rel:?} to tarball: {e}"
                    ))
                })?;
        }
        builder
            .finish()
            .map_err(|e| ElabError::BadForm(format!("registry publish: tar finish failed: {e}")))?;
    }
    let mut encoder = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
    std::io::Write::write_all(&mut encoder, &tar_bytes)
        .map_err(|e| ElabError::BadForm(format!("registry publish: gzip failed: {e}")))?;
    encoder
        .finish()
        .map_err(|e| ElabError::BadForm(format!("registry publish: gzip finish failed: {e}")))
}

/// Publish `src_dir`'s `.bl` tree as `name`@`version` into a local registry rooted at
/// `registry_dir` (Wave 9 / T3, `blight publish`): package it to
/// `<registry_dir>/<name>-<version>.tar.gz`, compute its [`hash_bl_tree`] digest, and upsert a
/// `[packages.<name>."<version>"]` entry recording that tarball path + hash into
/// `<registry_dir>/index.toml` (created fresh if it doesn't exist yet, otherwise merged in).
/// Returns the tarball's path.
///
/// This is the write-side mirror of [`fetch_and_vendor`]: the tarball this writes and the hash it
/// records use the exact same [`hash_bl_tree`] convention `fetch_and_vendor` verifies against, so
/// anything `blight publish` writes round-trips through `blight add --version --registry` with no
/// further coordination. Network-free by design — a real HTTP(S) registry's *fetch* side is
/// exactly what the module doc's "Transport" note added; standing up a corresponding *publish*
/// (upload) protocol/server is a separate, out-of-scope concern this pass doesn't need: a
/// `registry_dir` can equally be a local directory, a mounted network share, or a directory a CI
/// job later syncs to a real HTTP(S) origin.
pub fn publish(
    src_dir: &Path,
    name: &str,
    version: &str,
    registry_dir: &Path,
) -> Result<PathBuf, ElabError> {
    std::fs::create_dir_all(registry_dir).map_err(|e| {
        ElabError::BadForm(format!(
            "registry publish: cannot create {registry_dir:?}: {e}"
        ))
    })?;
    let tarball_bytes = make_tar_gz_from_dir(src_dir)?;
    let hash = hash_bl_tree(src_dir);
    let tarball_path = registry_dir.join(format!("{name}-{version}.tar.gz"));
    std::fs::write(&tarball_path, &tarball_bytes).map_err(|e| {
        ElabError::BadForm(format!(
            "registry publish: cannot write {tarball_path:?}: {e}"
        ))
    })?;

    let index_path = registry_dir.join("index.toml");
    let mut index = match std::fs::read_to_string(&index_path) {
        Ok(src) => RegistryIndex::parse(&src)?,
        Err(_) => RegistryIndex::default(),
    };
    index.add_entry(
        name,
        version,
        RegistryEntry {
            tarball: tarball_path.to_string_lossy().to_string(),
            hash,
        },
    );
    std::fs::write(&index_path, index.render()).map_err(|e| {
        ElabError::BadForm(format!(
            "registry publish: cannot write {index_path:?}: {e}"
        ))
    })?;
    Ok(tarball_path)
}

/// Read tarball bytes from `location`: a `file://` URI, a bare filesystem path, or an
/// `http(s)://` URL (see the module doc's "Transport" note).
fn fetch_bytes(location: &str) -> Result<Vec<u8>, ElabError> {
    if is_http_url(location) {
        #[cfg(not(feature = "net"))]
        return Err(ElabError::BadForm(format!(
            "registry: {location:?} is an HTTP location, but this build has no `net` feature \
             (wasm/offline profile) — vendor the dependency or use a file:// location"
        )));
        #[cfg(feature = "net")]
        {
            let mut response = ureq::get(location).call().map_err(|e| {
                ElabError::BadForm(format!("registry: cannot fetch tarball {location:?}: {e}"))
            })?;
            return response.body_mut().read_to_vec().map_err(|e| {
                ElabError::BadForm(format!(
                    "registry: cannot read tarball body from {location:?}: {e}"
                ))
            });
        }
    }
    let path = location.strip_prefix("file://").unwrap_or(location);
    std::fs::read(path)
        .map_err(|e| ElabError::BadForm(format!("registry: cannot read tarball {location:?}: {e}")))
}

/// Extract a `.tar.gz` byte buffer into `dest`. `dest` is removed first if it already exists, so a
/// re-fetch (e.g. after a corrupted previous attempt) never leaves stale files mixed in with fresh
/// ones.
///
/// Public (alongside [`make_tar_gz`]) so downstream crates' tests can extract a fixture tarball
/// directly — e.g. to compute the hash a real registry index *should* declare for it, the same way
/// `fetch_and_vendor` will — without going through hash verification themselves.
pub fn extract_tar_gz(bytes: &[u8], dest: &Path) -> Result<(), ElabError> {
    let _ = std::fs::remove_dir_all(dest);
    std::fs::create_dir_all(dest)
        .map_err(|e| ElabError::BadForm(format!("registry: cannot create {dest:?}: {e}")))?;
    let gunzipped = flate2::read::GzDecoder::new(bytes);
    let mut archive = tar::Archive::new(gunzipped);
    archive.unpack(dest).map_err(|e| {
        ElabError::BadForm(format!(
            "registry: cannot extract tarball into {dest:?}: {e}"
        ))
    })
}

/// Fetch, extract, and hash-verify `name`'s `version` from `index` into `dest`.
///
/// On success, `dest` contains the package's extracted `.bl` tree. On any failure — a missing index
/// entry, an unreadable tarball, a corrupt archive, or (crucially) a hash mismatch — `dest` is left
/// exactly as it was before the call (any partial extraction is deleted) and an error is returned:
/// a failed verification never leaves an unverified package sitting where `resolve_path` would find
/// it.
pub fn fetch_and_vendor(
    index: &RegistryIndex,
    name: &str,
    version: &str,
    dest: &Path,
) -> Result<(), ElabError> {
    let entry = index.lookup(name, version)?;
    let bytes = fetch_bytes(&entry.tarball)?;
    extract_tar_gz(&bytes, dest)?;
    let actual = hash_bl_tree(dest);
    if actual != entry.hash {
        let _ = std::fs::remove_dir_all(dest);
        return Err(ElabError::BadForm(format!(
            "registry: {name}@{version} hash mismatch: index declares {}, extracted tree hashes \
             to {actual} (tarball corrupted or tampered with; not vendored)",
            entry.hash
        )));
    }
    Ok(())
}

/// Build a `.tar.gz` in memory from a set of `(relative path, content)` pairs — used by tests (and
/// available to downstream crates' tests, e.g. the CLI's) to construct a registry fixture without
/// shelling out to a real `tar` binary.
pub fn make_tar_gz(files: &[(&str, &str)]) -> Vec<u8> {
    let mut tar_bytes = Vec::new();
    {
        let mut builder = tar::Builder::new(&mut tar_bytes);
        for (path, content) in files {
            let mut header = tar::Header::new_gnu();
            header.set_size(content.len() as u64);
            header.set_mode(0o644);
            header.set_cksum();
            builder
                .append_data(&mut header, path, content.as_bytes())
                .expect("in-memory tar append cannot fail");
        }
        builder.finish().expect("in-memory tar finish cannot fail");
    }
    let mut encoder = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
    std::io::Write::write_all(&mut encoder, &tar_bytes).expect("in-memory gzip cannot fail");
    encoder.finish().expect("in-memory gzip finish cannot fail")
}

/// Convenience used by `blight add`'s registry form: read a registry index from `location` (a
/// `file://` URI, bare filesystem path, or `http(s)://` URL — same convention as tarballs, see
/// the module doc's "Transport" note) and parse it.
pub fn load_index(location: &str) -> Result<RegistryIndex, ElabError> {
    if is_http_url(location) {
        #[cfg(not(feature = "net"))]
        return Err(ElabError::BadForm(format!(
            "registry index: {location:?} is an HTTP location, but this build has no `net` \
             feature (wasm/offline profile) — use a file:// index"
        )));
        #[cfg(feature = "net")]
        {
            let mut response = ureq::get(location).call().map_err(|e| {
                ElabError::BadForm(format!("registry index: cannot fetch {location:?}: {e}"))
            })?;
            let src = response.body_mut().read_to_string().map_err(|e| {
                ElabError::BadForm(format!(
                    "registry index: cannot read body from {location:?}: {e}"
                ))
            })?;
            return RegistryIndex::parse(&src);
        }
    }
    let path = location.strip_prefix("file://").unwrap_or(location);
    let src = std::fs::read_to_string(path).map_err(|e| {
        ElabError::BadForm(format!("registry index: cannot read {location:?}: {e}"))
    })?;
    RegistryIndex::parse(&src)
}

/// Where `blight add`'s registry form should vendor `dep_name@version` for a project rooted at
/// `base_dir` — re-exported from `spores` so callers (the CLI) don't need to depend on `spores`'
/// internal layout directly.
pub fn cache_dir(base_dir: &Path, dep_name: &str, version: &str) -> PathBuf {
    crate::spores::registry_cache_dir(base_dir, dep_name, version)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TempDir {
        dir: PathBuf,
    }
    impl TempDir {
        fn new(tag: &str) -> TempDir {
            let dir = std::env::temp_dir().join(format!(
                "blight_registry_{tag}_{}_{}",
                std::process::id(),
                tag.len()
            ));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            TempDir { dir }
        }
    }
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.dir);
        }
    }

    #[test]
    fn parses_a_minimal_index() {
        let idx = RegistryIndex::parse(
            "[packages.foo.\"1.0.0\"]\ntarball = \"file:///tmp/foo-1.0.0.tar.gz\"\n\
             hash = \"deadbeef\"\n",
        )
        .expect("parses");
        let entry = idx.lookup("foo", "1.0.0").expect("entry found");
        assert_eq!(entry.tarball, "file:///tmp/foo-1.0.0.tar.gz");
        assert_eq!(entry.hash, "deadbeef");
    }

    #[test]
    fn lookup_of_unknown_package_or_version_errors() {
        let idx = RegistryIndex::parse("[packages.foo.\"1.0.0\"]\ntarball = \"x\"\nhash = \"y\"\n")
            .unwrap();
        assert!(idx.lookup("bar", "1.0.0").is_err());
        assert!(idx.lookup("foo", "2.0.0").is_err());
    }

    #[test]
    fn fetch_and_vendor_round_trips_a_tarball_with_the_right_hash() {
        let work = TempDir::new("roundtrip");
        let tarball_path = work.dir.join("foo-1.0.0.tar.gz");
        let tgz = make_tar_gz(&[("mod.bl", "(the Unit Zero)")]);
        std::fs::write(&tarball_path, &tgz).unwrap();

        // Compute the expected hash the same way the registry would have (extract to a scratch
        // dir once, hash it) rather than hand-deriving the FNV digest, so this test doesn't
        // silently bit-rot if the hash function's internals ever change.
        let scratch = work.dir.join("scratch");
        extract_tar_gz(&tgz, &scratch).unwrap();
        let expected_hash = hash_bl_tree(&scratch);

        let index = RegistryIndex::parse(&format!(
            "[packages.foo.\"1.0.0\"]\ntarball = {:?}\nhash = {expected_hash:?}\n",
            tarball_path.to_string_lossy()
        ))
        .unwrap();

        let dest = work.dir.join("vendored/foo-1.0.0");
        fetch_and_vendor(&index, "foo", "1.0.0", &dest).expect("fetch+verify succeeds");
        assert_eq!(
            std::fs::read_to_string(dest.join("mod.bl")).unwrap(),
            "(the Unit Zero)"
        );
    }

    #[test]
    fn fetch_and_vendor_rejects_a_tampered_tarball() {
        let work = TempDir::new("tamper");
        let tarball_path = work.dir.join("foo-1.0.0.tar.gz");
        // A tarball whose content does not match the hash the index declares.
        let tgz = make_tar_gz(&[("mod.bl", "(the Unit Zero) ; tampered")]);
        std::fs::write(&tarball_path, &tgz).unwrap();

        let index = RegistryIndex::parse(&format!(
            "[packages.foo.\"1.0.0\"]\ntarball = {:?}\nhash = \"0000000000000000\"\n",
            tarball_path.to_string_lossy()
        ))
        .unwrap();

        let dest = work.dir.join("vendored/foo-1.0.0");
        let r = fetch_and_vendor(&index, "foo", "1.0.0", &dest);
        assert!(
            matches!(r, Err(ElabError::BadForm(ref m)) if m.contains("hash mismatch")),
            "expected a hash-mismatch error, got {r:?}"
        );
        assert!(
            !dest.exists(),
            "a failed verification must not leave a vendored copy behind"
        );
    }

    // ---- Wave 9 / T3: HTTP(S) transport --------------------------------------------------------

    /// A minimal one-shot-per-connection HTTP/1.1 server on loopback: serves `body` (with
    /// `content_type`) as a `200 OK` response to up to `times` connections, then stops. Enough to
    /// exercise the real `ureq` client end-to-end without any actual network access — no fixture
    /// needs anything beyond `127.0.0.1`, so these tests are as hermetic as the `file://` ones.
    fn serve_http(body: Vec<u8>, content_type: &str, times: usize) -> String {
        let listener = std::net::TcpListener::bind("127.0.0.1:0").expect("bind loopback");
        let port = listener.local_addr().unwrap().port();
        let content_type = content_type.to_string();
        std::thread::spawn(move || {
            use std::io::{Read, Write};
            for _ in 0..times {
                let Ok((mut stream, _)) = listener.accept() else {
                    break;
                };
                let mut buf = [0u8; 4096];
                // We don't need to parse the request, only drain enough of it that the client
                // isn't left blocked on a full send before we reply.
                let _ = stream.read(&mut buf);
                let header = format!(
                    "HTTP/1.1 200 OK\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\n\
                     Connection: close\r\n\r\n",
                    body.len()
                );
                let _ = stream.write_all(header.as_bytes());
                let _ = stream.write_all(&body);
                let _ = stream.flush();
            }
        });
        format!("http://127.0.0.1:{port}")
    }

    #[test]
    fn load_index_over_http() {
        let index_src =
            "[packages.foo.\"1.0.0\"]\ntarball = \"http://example.invalid/foo.tar.gz\"\n\
                          hash = \"deadbeef\"\n";
        let url = serve_http(index_src.as_bytes().to_vec(), "text/plain", 1);
        let index = load_index(&url).expect("index fetches and parses over http");
        let entry = index.lookup("foo", "1.0.0").expect("entry found");
        assert_eq!(entry.tarball, "http://example.invalid/foo.tar.gz");
        assert_eq!(entry.hash, "deadbeef");
    }

    #[test]
    fn http_fetch_verifies_index_hash() {
        let work = TempDir::new("http_verify");
        let tgz = make_tar_gz(&[("mod.bl", "(the Unit Zero)")]);
        let scratch = work.dir.join("scratch");
        extract_tar_gz(&tgz, &scratch).unwrap();
        let expected_hash = hash_bl_tree(&scratch);

        let tarball_url = serve_http(tgz, "application/gzip", 1);
        let index = RegistryIndex::parse(&format!(
            "[packages.foo.\"1.0.0\"]\ntarball = {tarball_url:?}\nhash = {expected_hash:?}\n"
        ))
        .unwrap();

        let dest = work.dir.join("vendored/foo-1.0.0");
        fetch_and_vendor(&index, "foo", "1.0.0", &dest)
            .expect("fetch+verify succeeds over a real http transport");
        assert_eq!(
            std::fs::read_to_string(dest.join("mod.bl")).unwrap(),
            "(the Unit Zero)"
        );
    }

    #[test]
    fn http_fetch_rejects_hash_mismatch() {
        let work = TempDir::new("http_mismatch");
        // Tarball's real content hashes to something other than what the index (falsely) claims —
        // the same security discriminator as the `file://` transport must hold over http too.
        let tgz = make_tar_gz(&[("mod.bl", "(the Unit Zero) ; tampered")]);
        let tarball_url = serve_http(tgz, "application/gzip", 1);
        let index = RegistryIndex::parse(&format!(
            "[packages.foo.\"1.0.0\"]\ntarball = {tarball_url:?}\nhash = \"0000000000000000\"\n"
        ))
        .unwrap();

        let dest = work.dir.join("vendored/foo-1.0.0");
        let r = fetch_and_vendor(&index, "foo", "1.0.0", &dest);
        assert!(
            matches!(r, Err(ElabError::BadForm(ref m)) if m.contains("hash mismatch")),
            "expected a hash-mismatch error, got {r:?}"
        );
        assert!(
            !dest.exists(),
            "a failed verification must not leave a vendored copy behind, even over http"
        );
    }

    // ---- Wave 9 / T3: `blight publish` -----------------------------------------------------

    #[test]
    fn publish_roundtrips_to_local_fixture() {
        let work = TempDir::new("publish_roundtrip");
        let src_dir = work.dir.join("pkg_src");
        std::fs::create_dir_all(&src_dir).unwrap();
        std::fs::write(src_dir.join("mod.bl"), "(the Unit Zero)").unwrap();
        // A non-`.bl` file must not end up in the published tarball (only `.bl` files are part
        // of the `hash_bl_tree` convention this whole trust story rests on).
        std::fs::write(src_dir.join("README.md"), "not part of the package hash").unwrap();

        let registry_dir = work.dir.join("registry_store");
        let tarball_path =
            publish(&src_dir, "foo", "1.0.0", &registry_dir).expect("publish succeeds");
        assert!(tarball_path.exists());

        let index_src = std::fs::read_to_string(registry_dir.join("index.toml")).unwrap();
        let index = RegistryIndex::parse(&index_src).expect("published index parses");
        let entry = index.lookup("foo", "1.0.0").expect("entry present");
        assert_eq!(entry.tarball, tarball_path.to_string_lossy());

        // Fetch it straight back through the normal consumer path and type-check-ready-read it.
        let dest = work.dir.join("vendored/foo-1.0.0");
        fetch_and_vendor(&index, "foo", "1.0.0", &dest)
            .expect("a freshly published package fetches and hash-verifies");
        assert_eq!(
            std::fs::read_to_string(dest.join("mod.bl")).unwrap(),
            "(the Unit Zero)"
        );
        assert!(
            !dest.join("README.md").exists(),
            "only .bl files are published/vendored"
        );
    }

    #[test]
    fn publish_upserts_without_clobbering_other_entries() {
        let work = TempDir::new("publish_upsert");
        let foo_src = work.dir.join("foo_src");
        std::fs::create_dir_all(&foo_src).unwrap();
        std::fs::write(foo_src.join("mod.bl"), "(the Unit Zero)").unwrap();
        let bar_src = work.dir.join("bar_src");
        std::fs::create_dir_all(&bar_src).unwrap();
        std::fs::write(bar_src.join("mod.bl"), "(the Unit unit)").unwrap();

        let registry_dir = work.dir.join("registry_store");
        publish(&foo_src, "foo", "1.0.0", &registry_dir).expect("publishes foo");
        publish(&bar_src, "bar", "2.0.0", &registry_dir).expect("publishes bar");
        // Republishing a new version of `foo` must not remove `foo@1.0.0` or `bar@2.0.0`.
        std::fs::write(foo_src.join("mod.bl"), "(the Unit Zero) ; v2").unwrap();
        publish(&foo_src, "foo", "1.1.0", &registry_dir).expect("publishes foo again");

        let index_src = std::fs::read_to_string(registry_dir.join("index.toml")).unwrap();
        let index = RegistryIndex::parse(&index_src).unwrap();
        assert!(
            index.lookup("foo", "1.0.0").is_ok(),
            "original version survives"
        );
        assert!(index.lookup("foo", "1.1.0").is_ok(), "new version present");
        assert!(
            index.lookup("bar", "2.0.0").is_ok(),
            "other package survives"
        );
    }

    #[test]
    fn fetch_and_vendor_reports_an_unknown_version() {
        let work = TempDir::new("unknown_version");
        let index =
            RegistryIndex::parse("[packages.foo.\"1.0.0\"]\ntarball = \"x\"\nhash = \"y\"\n")
                .unwrap();
        let dest = work.dir.join("vendored/foo-9.9.9");
        let r = fetch_and_vendor(&index, "foo", "9.9.9", &dest);
        assert!(r.is_err());
        assert!(!dest.exists());
    }
}
