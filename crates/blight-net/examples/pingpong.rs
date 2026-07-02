//! `pingpong` — a two-PROCESS distributed-actor ping/pong over loopback TCP (M19b), UNTRUSTED.
//!
//! This is the end-to-end proof for Phase 5b of the "full autism" sweep: two *separate OS processes*
//! play the two actors of `std/actor.bl`'s `send`/`receive` surface, with messages crossing a real
//! TCP socket — not two threads sharing an address space. Each process is a distributed `Actor`
//! scheduler: it owns a [`Router`] (the addressing layer) and interprets a `send` op as
//! [`Router::send_to`] and a `receive` op as [`Router::recv_from`]. The kernel never sees any of this
//! (no `blight-kernel` dependency, no `foreign` axiom); the wire bytes are the same data-only
//! `serialize.c`-compatible blob the in-process worker pool copies between heaps.
//!
//! Protocol: the message is a `Nat`-as-`Int` round counter.
//!   * `pong` binds first, prints its chosen ephemeral port (so the parent/peer can find it), accepts
//!     one connection, then loops: receive `n`, reply `n + 1`, until it has replied `rounds` times.
//!   * `ping` connects to the given port, then loops: send `n`, receive the reply `n + 1`, advancing
//!     `n` by 2 each round (ping holds the even counters, pong the odd), for `rounds` rounds.
//!
//! Both print one `PINGPONG <role> recv <value>` line per delivered message and a final
//! `PINGPONG <role> done <final>` line; the integration test (`tests/pingpong_process.rs`) spawns
//! both and asserts the transcripts line up — proving the addressed messages crossed the socket in
//! order and that the linear `receive` continuation was resumed exactly once per message.
//!
//! Usage (the test drives these; runnable by hand too):
//!   cargo run -p blight-net --example pingpong -- pong  <rounds>            # prints PORT <p>, then plays
//!   cargo run -p blight-net --example pingpong -- ping  <rounds> <port>     # connects to 127.0.0.1:<port>

use blight_net::{ActorAddr, Listener, NodeId, Router, Transport, Value};
use std::io::Write;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let role = args.get(1).map(String::as_str).unwrap_or("");
    match role {
        "pong" => {
            let rounds: u32 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(4);
            run_pong(rounds);
        }
        "ping" => {
            let rounds: u32 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(4);
            let port: u16 = args
                .get(3)
                .and_then(|s| s.parse().ok())
                .expect("ping needs a <port> to connect to");
            run_ping(rounds, port);
        }
        _ => {
            eprintln!("usage: pingpong (pong <rounds> | ping <rounds> <port>)");
            std::process::exit(2);
        }
    }
}

/// The actor id we address on each node (single actor per node in this demo).
const ACTOR: u64 = 0;

/// `pong`: bind, advertise the port, accept one peer, then echo `n -> n+1` for `rounds` messages.
fn run_pong(rounds: u32) {
    let listener = Listener::bind("127.0.0.1:0").expect("pong bind");
    let port = listener.local_addr().expect("pong addr").port();
    // The parent (test) reads this line to learn the ephemeral port to hand to `ping`.
    println!("PORT {port}");
    std::io::stdout().flush().ok();

    let mut router = Router::new();
    let ping_node = NodeId::new("ping");
    router.link(ping_node.clone(), listener.accept().expect("pong accept"));

    let mut last = 0i64;
    for _ in 0..rounds {
        let (_actor, payload) = router.recv_from(&ping_node).expect("pong recv");
        let n = expect_int(payload);
        println!("PINGPONG pong recv {n}");
        let reply = n + 1;
        router
            .send_to(&ActorAddr::new(ping_node.clone(), ACTOR), Value::Int(reply))
            .expect("pong send");
        last = reply;
    }
    println!("PINGPONG pong done {last}");
    std::io::stdout().flush().ok();
}

/// `ping`: connect to pong, then `send n` / `receive n+1` for `rounds` rounds, advancing by 2.
fn run_ping(rounds: u32, port: u16) {
    let mut router = Router::new();
    let pong_node = NodeId::new("pong");
    let transport = connect_with_retry(port);
    router.link(pong_node.clone(), transport);

    let mut n = 0i64;
    let mut last = 0i64;
    for _ in 0..rounds {
        router
            .send_to(&ActorAddr::new(pong_node.clone(), ACTOR), Value::Int(n))
            .expect("ping send");
        let (_actor, payload) = router.recv_from(&pong_node).expect("ping recv");
        let reply = expect_int(payload);
        println!("PINGPONG ping recv {reply}");
        // pong returned n+1; advance our counter past pong's reply for the next round.
        n = reply + 1;
        last = reply;
    }
    println!("PINGPONG ping done {last}");
    std::io::stdout().flush().ok();
}

/// `ping` may start before `pong`'s listener is ready; retry briefly so the demo is robust without a
/// shared rendezvous beyond the advertised port.
fn connect_with_retry(port: u16) -> Transport {
    let addr = format!("127.0.0.1:{port}");
    for _ in 0..200 {
        if let Ok(t) = Transport::connect(&addr) {
            return t;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    panic!("ping could not connect to {addr}");
}

fn expect_int(v: Value) -> i64 {
    match v {
        Value::Int(n) => n,
        other => panic!("expected an Int message, got {other:?}"),
    }
}
