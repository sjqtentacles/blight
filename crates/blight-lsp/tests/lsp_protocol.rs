//! End-to-end protocol tests: spawn the real `blight-lsp` binary and speak raw
//! `Content-Length`-framed JSON-RPC over its stdio, exactly as a real editor client would. This
//! catches process-lifecycle bugs (e.g. hanging on `exit`) that in-process unit tests cannot.

use serde_json::{json, Value};
use std::io::{BufReader, Read, Write};
use std::process::{Child, Command, Stdio};
use std::time::Duration;

struct Server {
    child: Child,
    stdin: std::process::ChildStdin,
    stdout: BufReader<std::process::ChildStdout>,
}

impl Server {
    fn spawn() -> Server {
        let mut child = Command::new(env!("CARGO_BIN_EXE_blight-lsp"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn blight-lsp");
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Server {
            child,
            stdin,
            stdout,
        }
    }

    fn send(&mut self, msg: &Value) {
        let body = serde_json::to_vec(msg).unwrap();
        write!(self.stdin, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        self.stdin.write_all(&body).unwrap();
        self.stdin.flush().unwrap();
    }

    fn recv(&mut self) -> Value {
        let mut header = Vec::new();
        loop {
            let mut byte = [0u8; 1];
            self.stdout.read_exact(&mut byte).expect("read header byte");
            header.push(byte[0]);
            if header.ends_with(b"\r\n\r\n") {
                break;
            }
        }
        let header_str = String::from_utf8_lossy(&header);
        let len: usize = header_str
            .lines()
            .find_map(|l| {
                l.to_ascii_lowercase()
                    .strip_prefix("content-length:")
                    .map(|v| v.trim().to_string())
            })
            .expect("Content-Length header")
            .parse()
            .expect("valid length");
        let mut body = vec![0u8; len];
        self.stdout.read_exact(&mut body).expect("read body");
        serde_json::from_slice(&body).expect("valid JSON")
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn initialize(server: &mut Server) {
    server.send(&json!({
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {"processId": null, "rootUri": null, "capabilities": {}}
    }));
    let resp = server.recv();
    assert_eq!(resp["id"], 1);
    assert!(resp["result"]["capabilities"]["hoverProvider"]
        .as_bool()
        .unwrap_or(false));
    server.send(&json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}));
}

#[test]
fn reports_a_diagnostic_per_failing_form_over_the_wire() {
    let mut server = Server::spawn();
    initialize(&mut server);

    let uri = "file:///tmp/blight_lsp_protocol_test_diag.bl";
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1,
            "text": "(defdata Nat () (Zero) (Succ (n Nat)))\n(the Nat undefined-one)\n(the Nat undefined-two)"
        }}
    }));
    let diag = server.recv();
    assert_eq!(diag["method"], "textDocument/publishDiagnostics");
    let diags = diag["params"]["diagnostics"].as_array().unwrap();
    assert_eq!(diags.len(), 2, "{diags:?}");
}

#[test]
fn hover_and_definition_work_over_the_wire() {
    let mut server = Server::spawn();
    initialize(&mut server);

    let uri = "file:///tmp/blight_lsp_protocol_test_hover.bl";
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1,
            "text": "(defdata Nat () (Zero) (Succ (n Nat)))\n(define one (the Nat (Succ Zero)))"
        }}
    }));
    let _diag = server.recv(); // no errors expected, but still published (empty array).

    // Hover over "Zero" on line 0.
    let zero_col = "(defdata Nat () (".len() as u64;
    server.send(&json!({
        "jsonrpc": "2.0", "id": 2, "method": "textDocument/hover",
        "params": {"textDocument": {"uri": uri}, "position": {"line": 0, "character": zero_col}}
    }));
    let hover = server.recv();
    let value = hover["result"]["contents"]["value"].as_str().unwrap_or("");
    assert!(value.contains("Nat"), "{value}");

    // Go to definition on "Nat" inside `(the Nat (Succ Zero))` on line 1.
    let nat_col = "(define one (the ".len() as u64;
    server.send(&json!({
        "jsonrpc": "2.0", "id": 3, "method": "textDocument/definition",
        "params": {"textDocument": {"uri": uri}, "position": {"line": 1, "character": nat_col}}
    }));
    let def = server.recv();
    let range = &def["result"]["range"];
    assert_eq!(range["start"]["line"], 0, "{def:?}");
}

// ---- Wave 9 / T1 (LSP v2) protocol tests ------------------------------------------------------

/// An unbound name nested inside a top-level form is underlined at the identifier itself, not the
/// whole `(the ...)` form — the deferred "inline sub-expression diagnostics" half of T1.
#[test]
fn diagnostic_points_at_subexpression_span() {
    let mut server = Server::spawn();
    initialize(&mut server);

    let uri = "file:///tmp/blight_lsp_protocol_test_subspan.bl";
    let text = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                (the Nat (lam (x) (Succ undefined-thing)))";
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1, "text": text
        }}
    }));
    let diag = server.recv();
    let diags = diag["params"]["diagnostics"].as_array().unwrap();
    assert_eq!(diags.len(), 1, "{diags:?}");
    let range = &diags[0]["range"];
    // "undefined-thing" starts partway through line 1; it must not be underlined from column 0
    // (the whole-form fallback) — it starts well past the `(the Nat (lam (x) (Succ ` prefix.
    let expected_col = "(the Nat (lam (x) (Succ ".len() as u64;
    assert_eq!(range["start"]["line"], 1, "{diags:?}");
    assert_eq!(range["start"]["character"], expected_col, "{diags:?}");
}

/// Hovering a `let`-bound local reports its type, recovered by re-elaborating its right-hand side
/// standalone — the local-variable-hover half of T1 (globals-only was the Wave 1 MVP).
#[test]
fn hover_reports_local_binder_type() {
    let mut server = Server::spawn();
    initialize(&mut server);

    let uri = "file:///tmp/blight_lsp_protocol_test_local_hover.bl";
    let text = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                (the Nat (let ((v (Succ Zero))) v))";
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1, "text": text
        }}
    }));
    let _diag = server.recv();

    // Hover over the final `v` (the body of the `let`), on line 1.
    let v_col = text.rfind('v').unwrap() as u64 - text.rfind('\n').unwrap() as u64 - 1;
    server.send(&json!({
        "jsonrpc": "2.0", "id": 2, "method": "textDocument/hover",
        "params": {"textDocument": {"uri": uri}, "position": {"line": 1, "character": v_col}}
    }));
    let hover = server.recv();
    let value = hover["result"]["contents"]["value"].as_str().unwrap_or("");
    assert!(value.contains("Nat"), "{value}");
}

/// Renaming a `lam`-bound local updates its declaration and every unshadowed use.
#[test]
fn rename_updates_all_bound_occurrences() {
    let mut server = Server::spawn();
    initialize(&mut server);

    let uri = "file:///tmp/blight_lsp_protocol_test_rename.bl";
    let text = "(lam (x) (pair x x))";
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1, "text": text
        }}
    }));
    let _diag = server.recv();

    let decl_col = text.find("(x)").unwrap() as u64 + 1;
    server.send(&json!({
        "jsonrpc": "2.0", "id": 2, "method": "textDocument/rename",
        "params": {
            "textDocument": {"uri": uri},
            "position": {"line": 0, "character": decl_col},
            "newName": "y"
        }
    }));
    let resp = server.recv();
    let edits = resp["result"]["changes"][uri]
        .as_array()
        .unwrap_or_else(|| {
            panic!("expected an edit list for {uri}: {resp:?}");
        });
    assert_eq!(edits.len(), 3, "decl + two uses: {edits:?}");
    for e in edits {
        assert_eq!(e["newText"], "y");
    }
}

/// A rename that would let a nested binder capture an occurrence is refused with an error
/// response, never silently applied.
#[test]
fn rename_refuses_capturing_shadow() {
    let mut server = Server::spawn();
    initialize(&mut server);

    let uri = "file:///tmp/blight_lsp_protocol_test_rename_capture.bl";
    let text = "(lam (x) (lam (y) x))";
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1, "text": text
        }}
    }));
    let _diag = server.recv();

    let decl_col = text.find("(x)").unwrap() as u64 + 1;
    server.send(&json!({
        "jsonrpc": "2.0", "id": 2, "method": "textDocument/rename",
        "params": {
            "textDocument": {"uri": uri},
            "position": {"line": 0, "character": decl_col},
            "newName": "y"
        }
    }));
    let resp = server.recv();
    assert!(
        resp["error"].is_object(),
        "expected an error response: {resp:?}"
    );
}

/// Go-to-definition follows a `(load "path")` into an on-disk file and resolves into *that*
/// file's own coordinates, rather than stopping at the `(load ...)` form.
#[test]
fn jump_resolves_into_load_target() {
    let dir = std::env::temp_dir().join(format!(
        "blight_lsp_protocol_jump_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let other_src = "(defdata Nat () (Zero) (Succ (n Nat)))";
    std::fs::write(dir.join("other.bl"), other_src).unwrap();
    let main_src = "(load \"other.bl\")\n(define one (the Nat Zero))";
    let main_path = dir.join("main.bl");
    std::fs::write(&main_path, main_src).unwrap();
    let uri = format!("file://{}", main_path.to_str().unwrap());

    let mut server = Server::spawn();
    initialize(&mut server);
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1, "text": main_src
        }}
    }));
    let _diag = server.recv();

    // Go to definition on "Nat" inside `(the Nat Zero)` on line 1 — defined in other.bl.
    let nat_col = "(define one (the ".len() as u64;
    server.send(&json!({
        "jsonrpc": "2.0", "id": 2, "method": "textDocument/definition",
        "params": {"textDocument": {"uri": uri}, "position": {"line": 1, "character": nat_col}}
    }));
    let def = server.recv();
    let target_uri = def["result"]["uri"].as_str().unwrap_or_else(|| {
        panic!("expected a cross-file location: {def:?}");
    });
    assert!(
        target_uri.ends_with("other.bl"),
        "expected the jump to land in other.bl, got {target_uri}"
    );
    assert_eq!(def["result"]["range"]["start"]["line"], 0, "{def:?}");

    std::fs::remove_dir_all(&dir).ok();
}

/// The real bug this guards against: a server that only breaks its message loop on `exit` (or
/// only unblocks via `io_threads.join()`, which waits for stdin EOF) can hang indefinitely if the
/// client doesn't immediately close its end of the pipe after sending `exit` — which is common,
/// since nothing in the spec *requires* the client to close it right away.
#[test]
fn shutdown_then_exit_terminates_promptly() {
    let mut server = Server::spawn();
    initialize(&mut server);

    server.send(&json!({"jsonrpc": "2.0", "id": 9, "method": "shutdown", "params": null}));
    let resp = server.recv();
    assert_eq!(resp["id"], 9);
    assert!(resp["result"].is_null());

    server.send(&json!({"jsonrpc": "2.0", "method": "exit", "params": null}));

    // Deliberately do NOT close stdin — a real client isn't required to, and the server must not
    // depend on it to terminate.
    let deadline = std::time::Instant::now() + Duration::from_secs(5);
    loop {
        if let Ok(Some(status)) = server.child.try_wait() {
            assert!(status.success(), "{status:?}");
            return;
        }
        if std::time::Instant::now() > deadline {
            panic!("blight-lsp did not exit within 5s of the `exit` notification");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

// ---- E8 protocol tests: formatting + completion ------------------------------------------------

/// E8: the initialize handshake advertises the two new capabilities, a messy buffer formats to
/// the shared canonicalizer's output as one whole-document edit, and completion offers globals
/// and keywords — all over the real wire.
#[test]
fn formatting_and_completion_work_over_the_wire() {
    let mut server = Server::spawn();

    // Inline (rather than via the shared `initialize` helper) to assert the E8 capabilities.
    server.send(&json!({
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {"processId": null, "rootUri": null, "capabilities": {}}
    }));
    let resp = server.recv();
    assert!(resp["result"]["capabilities"]["documentFormattingProvider"]
        .as_bool()
        .unwrap_or(false));
    assert!(
        resp["result"]["capabilities"]["completionProvider"].is_object(),
        "{resp:?}"
    );
    server.send(&json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}));

    let uri = "file:///tmp/blight_lsp_protocol_test_e8.bl";
    server.send(&json!({
        "jsonrpc": "2.0", "method": "textDocument/didOpen",
        "params": {"textDocument": {
            "uri": uri, "languageId": "blight", "version": 1,
            "text": "(defdata Nat () (Zero) (Succ (n Nat)))\n(  define one   (the Nat Zero) )\n"
        }}
    }));
    let _diag = server.recv();

    // Formatting: one whole-document edit whose text is the canonical form.
    server.send(&json!({
        "jsonrpc": "2.0", "id": 2, "method": "textDocument/formatting",
        "params": {"textDocument": {"uri": uri},
                   "options": {"tabSize": 2, "insertSpaces": true}}
    }));
    let fmt = server.recv();
    let edits = fmt["result"].as_array().unwrap();
    assert_eq!(edits.len(), 1, "{fmt:?}");
    let new_text = edits[0]["newText"].as_str().unwrap();
    assert!(
        new_text.contains("(define one (the Nat Zero))"),
        "canonicalized: {new_text}"
    );

    // Completion at the end of the buffer: a defined global, a constructor, and a keyword.
    server.send(&json!({
        "jsonrpc": "2.0", "id": 3, "method": "textDocument/completion",
        "params": {"textDocument": {"uri": uri}, "position": {"line": 2, "character": 0}}
    }));
    let completion = server.recv();
    let items = completion["result"].as_array().unwrap();
    let labels: Vec<&str> = items.iter().filter_map(|i| i["label"].as_str()).collect();
    for expected in ["one", "Succ", "define"] {
        assert!(
            labels.contains(&expected),
            "completion offers `{expected}`; got {labels:?}"
        );
    }
}
