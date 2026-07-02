//! Phase 5b: the two-PROCESS distributed ping/pong, driven end-to-end over loopback TCP.
//!
//! This spawns the `pingpong` example as two genuinely separate OS processes — `pong` and `ping` —
//! and asserts their transcripts agree. It is the integration-level proof that `std/actor.bl`'s
//! `send`/`receive` surface, interpreted by the untrusted `blight-net` distributed scheduler
//! ([`Router`]), carries addressed messages across a real socket between separate address spaces.
//! There is no shared memory: the only channel is the TCP stream, so a passing test means the
//! data-only wire format and the addressing envelope round-trip across the process boundary.
//!
//! We invoke the example through `cargo run --example` (using the `$CARGO` the harness exports) so
//! the test needs no knowledge of target paths and works under `cargo test` on any profile.

use std::io::{BufRead, BufReader};
use std::process::{Child, Command, Stdio};

fn cargo() -> String {
    std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string())
}

/// Spawn `cargo run -p blight-net --example pingpong -- <role-args>` with stdout piped.
fn spawn_role(args: &[&str]) -> Child {
    Command::new(cargo())
        .args([
            "run",
            "-q",
            "-p",
            "blight-net",
            "--example",
            "pingpong",
            "--",
        ])
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("spawn pingpong example process")
}

fn read_lines(child: &mut Child) -> Vec<String> {
    let out = child.stdout.take().expect("child stdout");
    BufReader::new(out)
        .lines()
        .map(|l| l.expect("read line"))
        .collect()
}

/// End-to-end: `pong` binds an ephemeral port and prints it; `ping` connects to that port; they
/// exchange `ROUNDS` ping/pong messages across loopback TCP as two separate processes. We assert
/// each side received the expected counter sequence and that both ran to completion.
#[test]
fn two_process_pingpong_over_loopback_tcp() {
    const ROUNDS: u32 = 4;
    let rounds = ROUNDS.to_string();

    // Start pong first and read its advertised port (the first PORT line).
    let mut pong = spawn_role(&["pong", &rounds]);
    let pong_out = pong.stdout.take().expect("pong stdout");
    let mut pong_reader = BufReader::new(pong_out);

    let port = loop {
        let mut line = String::new();
        let n = pong_reader.read_line(&mut line).expect("read pong line");
        assert!(n != 0, "pong exited before advertising a PORT");
        if let Some(p) = line.trim().strip_prefix("PORT ") {
            break p.to_string();
        }
        // `cargo run` may print build chatter to stdout under some configs; skip non-PORT lines.
    };

    // Now connect ping to pong's port.
    let mut ping = spawn_role(&["ping", &rounds, &port]);

    // Collect the remaining transcripts from both processes.
    let mut pong_lines: Vec<String> = Vec::new();
    for line in pong_reader.lines() {
        pong_lines.push(line.expect("pong line"));
    }
    let ping_lines = read_lines(&mut ping);

    let pong_status = pong.wait().expect("pong wait");
    let ping_status = ping.wait().expect("ping wait");
    assert!(
        pong_status.success(),
        "pong process failed: {pong_status:?}"
    );
    assert!(
        ping_status.success(),
        "ping process failed: {ping_status:?}"
    );

    let pong_recv: Vec<&String> = pong_lines
        .iter()
        .filter(|l| l.starts_with("PINGPONG pong recv "))
        .collect();
    let ping_recv: Vec<&String> = ping_lines
        .iter()
        .filter(|l| l.starts_with("PINGPONG ping recv "))
        .collect();

    // ping sends 0,2,4,6 ; pong receives those and replies +1 -> 1,3,5,7 ; ping receives those.
    assert_eq!(
        pong_recv,
        vec![
            "PINGPONG pong recv 0",
            "PINGPONG pong recv 2",
            "PINGPONG pong recv 4",
            "PINGPONG pong recv 6",
        ],
        "pong must receive ping's even counters in order"
    );
    assert_eq!(
        ping_recv,
        vec![
            "PINGPONG ping recv 1",
            "PINGPONG ping recv 3",
            "PINGPONG ping recv 5",
            "PINGPONG ping recv 7",
        ],
        "ping must receive pong's incremented replies in order"
    );

    assert!(
        pong_lines.iter().any(|l| l == "PINGPONG pong done 7"),
        "pong ran to completion (last reply 7); got {pong_lines:?}"
    );
    assert!(
        ping_lines.iter().any(|l| l == "PINGPONG ping done 7"),
        "ping ran to completion (last reply 7); got {ping_lines:?}"
    );
}
