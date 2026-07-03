//! R2 headless smoke: build the wasm cdylib and drive it with node exactly as the page's Web
//! Worker does (playground/smoke.mjs). Ignored by default — it shells out to cargo + node — and
//! run explicitly by the wasm CI job.

#[test]
#[ignore = "R2: builds the wasm artifact and needs node; run explicitly (CI wasm job)"]
fn wasm_checker_smoke_via_node() {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");
    let build = std::process::Command::new("cargo")
        .args([
            "build",
            "-p",
            "blight-playground",
            "--release",
            "--target",
            "wasm32-unknown-unknown",
        ])
        .current_dir(root)
        .status()
        .expect("spawn cargo build");
    assert!(build.success(), "wasm build succeeds");
    let out = std::process::Command::new("node")
        .args(["playground/smoke.mjs"])
        .current_dir(root)
        .output()
        .expect("spawn node smoke");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success() && stdout.contains("SMOKE OK"),
        "smoke passes:\nstdout: {stdout}\nstderr: {stderr}"
    );
}
