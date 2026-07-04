//! R3 (release engineering): the `blight` binary reports its version.
//!
//! Two independent pins, both red before R3:
//!
//!   * `--version`/`-V` is wired at all (before R3 the flag falls through to the REPL);
//!   * the workspace is at the `0.1.0` release version (before R3 it is `0.0.0`).
//!
//! They are split deliberately so a future release bumps exactly one line
//! (`release_version_is_0_1_0`) alongside the CHANGELOG, while the flag-mechanism pin stays stable
//! across bumps.

use std::process::{Command, Stdio};

fn blight() -> Command {
    Command::new(env!("CARGO_BIN_EXE_blight"))
}

#[test]
#[ignore = "R3 red: `--version` flag + 0.1.0 bump not yet landed; un-ignored in R3 green"]
fn version_flag_prints_package_version() {
    let expected = format!("blight {}", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V"] {
        let out = blight()
            .arg(flag)
            .stdin(Stdio::null())
            .output()
            .expect("spawn blight");
        assert!(
            out.status.success(),
            "`blight {flag}` should exit 0, got {:?}",
            out.status
        );
        assert_eq!(
            String::from_utf8_lossy(&out.stdout).trim(),
            expected,
            "`blight {flag}` should print `{expected}` on stdout",
        );
    }
}

#[test]
#[ignore = "R3 red: workspace still at 0.0.0; un-ignored in R3 green"]
fn release_version_is_0_1_0() {
    // R3 release pin — this is the v0.1.0 release. Bump this line with the CHANGELOG on the next
    // release; it exists so the version can never silently drift away from the published tag.
    assert_eq!(env!("CARGO_PKG_VERSION"), "0.1.0");
}
