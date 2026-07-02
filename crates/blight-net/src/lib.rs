//! `blight-net` — a **data-only distributed transport** for Blight (M19), as *untrusted* Rust.
//!
//! ## Trust boundary (the "max-autism" constraint)
//!
//! This crate is deliberately **outside the trusted computing base**:
//!
//! - It has **no dependency on `blight-kernel`** and proposes **no kernel terms**. The kernel never
//!   sees a socket, a thread, or a serialized byte. There are therefore **zero new `foreign`
//!   axioms** (Blight's `foreign` is the one hatch that *grows* the TCB; we use none here) and the
//!   `git diff crates/blight-kernel` for this milestone is empty.
//! - It only moves **first-order data values** (the Erlang model). The wire format is byte-for-byte
//!   the same structural layout the runtime's `serialize.c` produces (M18): a pre-order walk of the
//!   7-tag object layout, restricted to the data tags `Con`/`Tuple`/`Int`. Closures and effect
//!   op-nodes carry a raw function pointer meaningful in one address space only, so they are *not*
//!   representable here — exactly mirroring `serialize.c`'s data-only rejection.
//!
//! ## How it reuses `std/actor.bl`
//!
//! A program performs the ordinary `Actor` effects (`send` / `receive`, declared in
//! `std/actor.bl`). A *distributed scheduler handler* — untrusted runtime/tower code, like the
//! cooperative single-core handler — interprets `send msg` by encoding `msg` with [`Value::encode`]
//! and writing it to a [`Transport`], and interprets `receive` by reading the next framed value off
//! the transport and resuming the (linear) continuation with it. The kernel-checked grade on those
//! ops (resume-exactly-once for the linear ops) is unchanged whether the peer is on another worker
//! thread (M17) or another machine (here): only the transport differs. See
//! [`Transport::send_value`] / [`Transport::recv_value`].
//!
//! ## Wire format (must match `runtime/serialize.c`)
//!
//! Per node, little-endian: `tag: u32`, `nfields: u32`, `aux: u64`, then `nfields` children in
//! pre-order. A `NULL` child is the sentinel tag `0xFFFF_FFFF`. Messages on a [`Transport`] are
//! length-prefixed with a `u32` byte count so a stream carries a sequence of values.

use std::io::{self, Read, Write};
use std::net::{TcpListener, TcpStream, ToSocketAddrs};

/// The data tags shared with the runtime's object layout (`blight_rt.h` `BlTag`). Only the
/// first-order data subset is transportable.
pub const TAG_CON: u32 = 0;
pub const TAG_TUPLE: u32 = 1;
pub const TAG_INT: u32 = 5;
/// Sentinel emitted for a `NULL` child slot (mirrors `serialize.c` `BL_BLOB_NULL_TAG`).
pub const TAG_NULL: u32 = 0xFFFF_FFFF;

/// A first-order Blight data value, the only thing this transport can carry. Mirrors the
/// serializable subset of the runtime's `BlValue`:
/// - `Con { ctor, fields }` — a data constructor (`aux` = constructor index);
/// - `Tuple(fields)` — an anonymous product;
/// - `Int(i64)` — a machine integer.
///
/// `None` children (empty constructor/tuple slots use no children; an explicit absent child is
/// `Value::Null`) round-trip through the `TAG_NULL` sentinel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Con {
        ctor: u64,
        fields: Vec<Value>,
    },
    Tuple(Vec<Value>),
    Int(i64),
    /// An explicit null child slot (the runtime represents an uninitialized field as a NULL pointer).
    Null,
}

#[derive(Debug)]
pub enum NetError {
    Io(io::Error),
    /// The bytes did not decode to a well-formed value (truncated, or a non-data tag on the wire).
    Malformed(String),
}

impl std::fmt::Display for NetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NetError::Io(e) => write!(f, "io error: {e}"),
            NetError::Malformed(m) => write!(f, "malformed message: {m}"),
        }
    }
}
impl std::error::Error for NetError {}
impl From<io::Error> for NetError {
    fn from(e: io::Error) -> Self {
        NetError::Io(e)
    }
}

impl Value {
    /// Serialize to the runtime-compatible byte blob (same layout as `serialize.c`).
    pub fn encode(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.encode_into(&mut buf);
        buf
    }

    fn encode_into(&self, buf: &mut Vec<u8>) {
        match self {
            Value::Null => buf.extend_from_slice(&TAG_NULL.to_le_bytes()),
            Value::Int(n) => {
                buf.extend_from_slice(&TAG_INT.to_le_bytes());
                buf.extend_from_slice(&0u32.to_le_bytes()); // nfields
                buf.extend_from_slice(&(*n as u64).to_le_bytes()); // aux
            }
            Value::Con { ctor, fields } => {
                buf.extend_from_slice(&TAG_CON.to_le_bytes());
                buf.extend_from_slice(&(fields.len() as u32).to_le_bytes());
                buf.extend_from_slice(&ctor.to_le_bytes());
                for c in fields {
                    c.encode_into(buf);
                }
            }
            Value::Tuple(fields) => {
                buf.extend_from_slice(&TAG_TUPLE.to_le_bytes());
                buf.extend_from_slice(&(fields.len() as u32).to_le_bytes());
                buf.extend_from_slice(&0u64.to_le_bytes()); // aux unused for tuples
                for c in fields {
                    c.encode_into(buf);
                }
            }
        }
    }

    /// Deserialize a value from a byte blob (the inverse of [`Value::encode`]). Errors on truncation
    /// or a non-data tag.
    pub fn decode(bytes: &[u8]) -> Result<Value, NetError> {
        let mut pos = 0usize;
        let v = Value::decode_at(bytes, &mut pos)?;
        Ok(v)
    }

    fn decode_at(bytes: &[u8], pos: &mut usize) -> Result<Value, NetError> {
        let tag = read_u32(bytes, pos)?;
        if tag == TAG_NULL {
            return Ok(Value::Null);
        }
        let nfields = read_u32(bytes, pos)?;
        let aux = read_u64(bytes, pos)?;
        match tag {
            TAG_INT => {
                if nfields != 0 {
                    return Err(NetError::Malformed("Int with fields".into()));
                }
                Ok(Value::Int(aux as i64))
            }
            TAG_CON => {
                let mut fields = Vec::with_capacity(child_capacity(nfields, bytes.len()));
                for _ in 0..nfields {
                    fields.push(Value::decode_at(bytes, pos)?);
                }
                Ok(Value::Con { ctor: aux, fields })
            }
            TAG_TUPLE => {
                let mut fields = Vec::with_capacity(child_capacity(nfields, bytes.len()));
                for _ in 0..nfields {
                    fields.push(Value::decode_at(bytes, pos)?);
                }
                Ok(Value::Tuple(fields))
            }
            other => Err(NetError::Malformed(format!(
                "non-data tag {other} on the wire (data-only transport)"
            ))),
        }
    }
}

/// A safe pre-allocation size for a node's children. `nfields` comes straight off the wire and is
/// attacker-controlled (up to `u32::MAX`), so we must NOT `Vec::with_capacity(nfields)` directly — a
/// 16-byte frame claiming 4 billion children would force a multi-gigabyte allocation (a trivial OOM
/// DoS). Every child occupies at least a 4-byte tag, so a well-formed frame can hold at most
/// `remaining / 4` children; capping the reservation there keeps decoding bounded by the *actual*
/// input size. An over-claimed count still errors, just via the truncation check in the read loop.
fn child_capacity(nfields: u32, total_len: usize) -> usize {
    (nfields as usize).min(total_len / 4)
}

fn read_u32(bytes: &[u8], pos: &mut usize) -> Result<u32, NetError> {
    if *pos + 4 > bytes.len() {
        return Err(NetError::Malformed("truncated u32".into()));
    }
    let v = u32::from_le_bytes(bytes[*pos..*pos + 4].try_into().unwrap());
    *pos += 4;
    Ok(v)
}

fn read_u64(bytes: &[u8], pos: &mut usize) -> Result<u64, NetError> {
    if *pos + 8 > bytes.len() {
        return Err(NetError::Malformed("truncated u64".into()));
    }
    let v = u64::from_le_bytes(bytes[*pos..*pos + 8].try_into().unwrap());
    *pos += 8;
    Ok(v)
}

/// A point-to-point transport carrying length-prefixed data values over a TCP stream. This is the
/// untrusted network layer a distributed `Actor` scheduler handler installs in place of the
/// in-process worker-pool queue (M17): `send`/`receive` move the *same* serialized values, just over
/// a socket instead of across thread-local heaps.
pub struct Transport {
    stream: TcpStream,
}

impl Transport {
    /// Connect to a listening peer.
    pub fn connect<A: ToSocketAddrs>(addr: A) -> Result<Transport, NetError> {
        Ok(Transport {
            stream: TcpStream::connect(addr)?,
        })
    }

    /// Wrap an already-accepted stream.
    pub fn from_stream(stream: TcpStream) -> Transport {
        Transport { stream }
    }

    /// Send a value: a `u32` little-endian length prefix followed by the encoded blob. This is the
    /// transport side of the `Actor` `send` op.
    pub fn send_value(&mut self, v: &Value) -> Result<(), NetError> {
        let blob = v.encode();
        let len = blob.len() as u32;
        self.stream.write_all(&len.to_le_bytes())?;
        self.stream.write_all(&blob)?;
        self.stream.flush()?;
        Ok(())
    }

    /// Receive the next value (blocks until a full frame arrives). The transport side of `receive`.
    pub fn recv_value(&mut self) -> Result<Value, NetError> {
        let mut len_buf = [0u8; 4];
        self.stream.read_exact(&mut len_buf)?;
        let len = u32::from_le_bytes(len_buf) as usize;
        let mut blob = vec![0u8; len];
        self.stream.read_exact(&mut blob)?;
        Value::decode(&blob)
    }
}

/// ── Remote addressing (M19a) ─────────────────────────────────────────────────────────────────────
///
/// The bare [`Transport`] is point-to-point: it can only talk to the one peer it is connected to. A
/// distributed actor program, though, performs `send`/`receive` against *named* peers ("send this to
/// the `pong` actor on node `B`"). [`NodeId`] / [`ActorAddr`] are that addressing layer, and
/// [`Router`] is the untrusted *distributed scheduler handler* state: it owns one [`Transport`] per
/// reachable node and routes a `send msg` op to the right socket by address, exactly mirroring how
/// the in-process worker pool routes a message to the right thread-local mailbox. No kernel term, no
/// `foreign` axiom: addresses are plain data, routing is plain Rust over the existing data-only
/// wire format.
///
/// A logical node name in the distributed system (e.g. `"ping"`, `"pong"`). Cheap to clone and used
/// as the routing key in a [`Router`].
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub String);

impl NodeId {
    pub fn new(name: impl Into<String>) -> NodeId {
        NodeId(name.into())
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// The address of a remote actor: which node it lives on, plus a node-local actor id (the `Nat`
/// actor id from `std/actor.bl`'s `spawn`). The distributed scheduler resolves the `node` to a
/// transport via the [`Router`] and tags the wire message with `actor` so the receiving node can
/// deliver it to the right mailbox.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ActorAddr {
    pub node: NodeId,
    pub actor: u64,
}

impl ActorAddr {
    pub fn new(node: NodeId, actor: u64) -> ActorAddr {
        ActorAddr { node, actor }
    }
}

/// Routing table for a distributed actor scheduler: a map from [`NodeId`] to the open [`Transport`]
/// reaching that node. This is the untrusted state a distributed `Actor` handler threads through its
/// continuation in place of the single-core mailbox `Nat` (see `std/actor.bl`): `send` looks up the
/// destination node's transport and writes the (addressed) value; `recv` reads the next framed value
/// off a node's transport. Every value crossing it is the same data-only [`Value`] blob the runtime's
/// `serialize.c` produces, so a message can equally be delivered to another thread (M17) or another
/// machine (here) with no change to the checked program.
#[derive(Default)]
pub struct Router {
    links: std::collections::HashMap<NodeId, Transport>,
}

impl Router {
    pub fn new() -> Router {
        Router {
            links: std::collections::HashMap::new(),
        }
    }

    /// Register the transport reaching `node` (e.g. after `Transport::connect` or `Listener::accept`
    /// has identified the peer). A later `link` for the same node replaces the prior transport.
    pub fn link(&mut self, node: NodeId, transport: Transport) {
        self.links.insert(node, transport);
    }

    /// Whether a transport to `node` is registered.
    pub fn is_linked(&self, node: &NodeId) -> bool {
        self.links.contains_key(node)
    }

    /// The set of currently reachable nodes (sorted for determinism).
    pub fn nodes(&self) -> Vec<NodeId> {
        let mut ns: Vec<NodeId> = self.links.keys().cloned().collect();
        ns.sort();
        ns
    }

    /// The `Actor` `send` op, distributed form: route `msg` to `addr`'s node. The actor id is carried
    /// in the wire frame as a `Tuple(Int actor, msg)` envelope so the receiving node can demultiplex
    /// to the right local mailbox — still a plain data value, so the wire format is unchanged.
    pub fn send_to(&mut self, addr: &ActorAddr, msg: Value) -> Result<(), NetError> {
        let t = self.links.get_mut(&addr.node).ok_or_else(|| {
            NetError::Malformed(format!("no transport linked for node {}", addr.node))
        })?;
        t.send_value(&envelope(addr.actor, msg))
    }

    /// The `Actor` `receive` op, distributed form: read the next addressed message that arrived from
    /// `node`, returning the destination local actor id and the payload. Blocks until a frame arrives.
    pub fn recv_from(&mut self, node: &NodeId) -> Result<(u64, Value), NetError> {
        let t = self
            .links
            .get_mut(node)
            .ok_or_else(|| NetError::Malformed(format!("no transport linked for node {node}")))?;
        let framed = t.recv_value()?;
        open_envelope(framed)
    }
}

/// Wrap a payload as the addressed wire envelope `Tuple(Int actor, payload)`.
fn envelope(actor: u64, payload: Value) -> Value {
    Value::Tuple(vec![Value::Int(actor as i64), payload])
}

/// Inverse of [`envelope`]: split an addressed frame back into `(actor_id, payload)`.
fn open_envelope(framed: Value) -> Result<(u64, Value), NetError> {
    match framed {
        Value::Tuple(mut fields) if fields.len() == 2 => {
            let payload = fields.pop().unwrap();
            match fields.pop().unwrap() {
                Value::Int(actor) => Ok((actor as u64, payload)),
                other => Err(NetError::Malformed(format!(
                    "envelope actor id must be Int, got {other:?}"
                ))),
            }
        }
        other => Err(NetError::Malformed(format!(
            "expected a 2-field addressed envelope, got {other:?}"
        ))),
    }
}

/// A listener that accepts peer connections, each becoming a [`Transport`].
pub struct Listener {
    inner: TcpListener,
}

impl Listener {
    pub fn bind<A: ToSocketAddrs>(addr: A) -> Result<Listener, NetError> {
        Ok(Listener {
            inner: TcpListener::bind(addr)?,
        })
    }

    /// The bound local address (useful when binding to port 0 to get an ephemeral port).
    pub fn local_addr(&self) -> Result<std::net::SocketAddr, NetError> {
        Ok(self.inner.local_addr()?)
    }

    /// Accept one peer connection.
    pub fn accept(&self) -> Result<Transport, NetError> {
        let (stream, _addr) = self.inner.accept()?;
        Ok(Transport::from_stream(stream))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_values() -> Vec<Value> {
        vec![
            Value::Int(0),
            Value::Int(-42),
            Value::Int(1_234_567),
            Value::Null,
            // (just 7): Con(ctor=1, [Int 7])
            Value::Con {
                ctor: 1,
                fields: vec![Value::Int(7)],
            },
            // nothing: Con(ctor=0, [])
            Value::Con {
                ctor: 0,
                fields: vec![],
            },
            // a pair tuple of nested cons
            Value::Tuple(vec![
                Value::Con {
                    ctor: 1,
                    fields: vec![Value::Int(99)],
                },
                Value::Con {
                    ctor: 0,
                    fields: vec![],
                },
            ]),
            // a 200-element cons-list terminated by nil
            {
                let mut list = Value::Con {
                    ctor: 0,
                    fields: vec![],
                };
                for i in 0..200i64 {
                    list = Value::Con {
                        ctor: 1,
                        fields: vec![Value::Int(i), list],
                    };
                }
                list
            },
        ]
    }

    /// `encode` then `decode` reproduces the value exactly (the wire-format round-trip; this is the
    /// Rust mirror of the C `serialize_test.c` round-trip, sharing the same byte layout).
    #[test]
    fn encode_decode_round_trips() {
        for v in sample_values() {
            let blob = v.encode();
            let back = Value::decode(&blob).expect("decode");
            assert_eq!(v, back, "round-trip must be exact");
        }
    }

    /// A non-data tag on the wire is rejected (data-only transport).
    #[test]
    fn rejects_non_data_tag() {
        // tag = 2 (BL_CLOSURE), nfields=0, aux=0
        let mut blob = Vec::new();
        blob.extend_from_slice(&2u32.to_le_bytes());
        blob.extend_from_slice(&0u32.to_le_bytes());
        blob.extend_from_slice(&0u64.to_le_bytes());
        match Value::decode(&blob) {
            Err(NetError::Malformed(_)) => {}
            other => panic!("expected Malformed for a closure tag, got {other:?}"),
        }
    }

    /// Truncated input is rejected, never panics.
    #[test]
    fn rejects_truncated() {
        assert!(matches!(
            Value::decode(&[0u8, 1, 2]),
            Err(NetError::Malformed(_))
        ));
    }

    /// End-to-end over a real loopback TCP socket: a server thread echoes back the successor of an
    /// Int it receives; the client sends a value and reads the reply. Proves the `Actor`
    /// `send`/`receive` transport works across the socket boundary with zero shared state — the
    /// distributed analogue of the M17 worker-pool message copy.
    #[test]
    fn tcp_send_receive_round_trips() {
        let listener = Listener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().expect("addr");

        let server = std::thread::spawn(move || {
            let mut t = listener.accept().expect("accept");
            // Receive a list of messages, reply to each with its successor (Int + 1).
            for _ in 0..3 {
                match t.recv_value().expect("recv") {
                    Value::Int(n) => t.send_value(&Value::Int(n + 1)).expect("send reply"),
                    other => panic!("server expected Int, got {other:?}"),
                }
            }
        });

        let mut client = Transport::connect(addr).expect("connect");
        for n in [10i64, 20, 30] {
            client.send_value(&Value::Int(n)).expect("send");
            let reply = client.recv_value().expect("recv reply");
            assert_eq!(reply, Value::Int(n + 1));
        }
        server.join().expect("server thread");
    }

    /// A structured (non-scalar) message survives the socket: send a small constructor tree and get
    /// it echoed verbatim.
    #[test]
    fn tcp_structured_message_round_trips() {
        let listener = Listener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().expect("addr");
        let msg = Value::Tuple(vec![
            Value::Con {
                ctor: 1,
                fields: vec![Value::Int(7)],
            },
            Value::Int(-1),
        ]);
        let expected = msg.clone();

        let server = std::thread::spawn(move || {
            let mut t = listener.accept().expect("accept");
            let got = t.recv_value().expect("recv");
            t.send_value(&got).expect("echo");
        });

        let mut client = Transport::connect(addr).expect("connect");
        client.send_value(&msg).expect("send");
        let echoed = client.recv_value().expect("recv");
        assert_eq!(echoed, expected);
        server.join().expect("server thread");
    }

    /// **Byte-compatibility with `runtime/serialize.c`.** The wire format must match the C runtime's
    /// blob layout exactly, byte-for-byte, so a value serialized by a native worker (`serialize.c`)
    /// decodes here and vice-versa. This golden-bytes test locks the layout: per node
    /// `{tag: u32, nfields: u32, aux: u64}` little-endian, pre-order. `Int(7)` is
    /// `05 00 00 00 | 00 00 00 00 | 07 00 00 00 00 00 00 00`; a `Con{ctor=1,[Int 7]}` prefixes
    /// `00 00 00 00 | 01 00 00 00 | 01 00 00 00 00 00 00 00`.
    #[test]
    fn wire_format_matches_serialize_c_layout() {
        assert_eq!(
            Value::Int(7).encode(),
            vec![
                0x05, 0, 0, 0, // tag = BL_INT (5)
                0, 0, 0, 0, // nfields = 0
                0x07, 0, 0, 0, 0, 0, 0, 0, // aux = 7
            ]
        );
        assert_eq!(
            (Value::Con {
                ctor: 1,
                fields: vec![Value::Int(7)],
            })
            .encode(),
            vec![
                0x00, 0, 0, 0, // tag = BL_CON (0)
                0x01, 0, 0, 0, // nfields = 1
                0x01, 0, 0, 0, 0, 0, 0, 0, // aux = ctor index 1
                // child Int(7):
                0x05, 0, 0, 0, 0, 0, 0, 0, 0x07, 0, 0, 0, 0, 0, 0, 0,
            ]
        );
        // The NULL-child sentinel is 0xFFFFFFFF (mirrors serialize.c BL_BLOB_NULL_TAG).
        assert_eq!(Value::Null.encode(), vec![0xFF, 0xFF, 0xFF, 0xFF]);
    }

    /// The addressed envelope round-trips: `send_to` wraps `(actor, payload)`, `recv_from` unwraps to
    /// exactly that pair. This is the unit of remote addressing the distributed scheduler routes on.
    #[test]
    fn router_addresses_and_delivers_to_the_right_actor() {
        let listener = Listener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().expect("addr");
        let node_b = NodeId::new("B");

        // Server node "B" echoes back (actor_id, payload) so the client can assert routing survived.
        let server = std::thread::spawn(move || {
            let mut router = Router::new();
            router.link(NodeId::new("A"), listener.accept().expect("accept"));
            let a = NodeId::new("A");
            let (actor, payload) = router.recv_from(&a).expect("recv");
            // Reply on the SAME socket, re-addressing to whoever the message named.
            router
                .send_to(&ActorAddr::new(a, actor), payload)
                .expect("reply");
        });

        let mut router = Router::new();
        router.link(node_b.clone(), Transport::connect(addr).expect("connect"));
        assert_eq!(router.nodes(), vec![node_b.clone()]);

        let target = ActorAddr::new(node_b.clone(), 7);
        let msg = Value::Con {
            ctor: 1,
            fields: vec![Value::Int(123)],
        };
        router.send_to(&target, msg.clone()).expect("send_to");
        let (actor, payload) = router.recv_from(&node_b).expect("recv_from");
        assert_eq!(actor, 7, "the local actor id survived the round-trip");
        assert_eq!(payload, msg, "the payload survived verbatim");
        server.join().expect("server thread");
    }

    /// Sending to an unlinked node is a clean error, never a panic — the scheduler can surface it.
    #[test]
    fn router_send_to_unlinked_node_errors() {
        let mut router = Router::new();
        let r = router.send_to(&ActorAddr::new(NodeId::new("ghost"), 0), Value::Int(1));
        assert!(matches!(r, Err(NetError::Malformed(_))));
    }

    /// Receiving from an unlinked node is the symmetric clean error (the `send` side is covered
    /// above; this pins the `recv` side so neither half can panic on a missing transport).
    #[test]
    fn router_recv_from_unlinked_node_errors() {
        let mut router = Router::new();
        let r = router.recv_from(&NodeId::new("ghost"));
        assert!(matches!(r, Err(NetError::Malformed(_))));
    }

    /// **OOM-DoS guard.** A tiny frame whose header claims a colossal child count must be rejected
    /// (truncation) — NOT honoured by pre-allocating gigabytes. `decode` returns `Malformed`
    /// promptly; before the `child_capacity` cap this would attempt a `Vec::with_capacity(u32::MAX)`.
    #[test]
    fn decode_rejects_oversized_field_count_without_oom() {
        // tag = TAG_CON (0), nfields = u32::MAX, aux = 0, and NO child bytes follow.
        let mut blob = Vec::new();
        blob.extend_from_slice(&TAG_CON.to_le_bytes());
        blob.extend_from_slice(&u32::MAX.to_le_bytes());
        blob.extend_from_slice(&0u64.to_le_bytes());
        match Value::decode(&blob) {
            Err(NetError::Malformed(_)) => {}
            other => panic!("expected Malformed for an over-claimed field count, got {other:?}"),
        }
        // Same for a tuple header.
        let mut tup = Vec::new();
        tup.extend_from_slice(&TAG_TUPLE.to_le_bytes());
        tup.extend_from_slice(&u32::MAX.to_le_bytes());
        tup.extend_from_slice(&0u64.to_le_bytes());
        assert!(matches!(Value::decode(&tup), Err(NetError::Malformed(_))));
        // The capacity helper never exceeds what the buffer could possibly hold.
        assert_eq!(
            child_capacity(u32::MAX, 16),
            4,
            "16 bytes ⇒ at most 4 children"
        );
        assert_eq!(
            child_capacity(2, 1_000),
            2,
            "honest small counts pass through"
        );
    }

    /// A `TAG_INT` node carrying a non-zero field count is malformed (an Int is a leaf scalar).
    #[test]
    fn decode_rejects_int_with_fields() {
        let mut blob = Vec::new();
        blob.extend_from_slice(&TAG_INT.to_le_bytes());
        blob.extend_from_slice(&1u32.to_le_bytes()); // nfields = 1 (illegal for Int)
        blob.extend_from_slice(&0u64.to_le_bytes());
        match Value::decode(&blob) {
            Err(NetError::Malformed(m)) => assert!(m.contains("Int"), "names the issue: {m}"),
            other => panic!("expected Malformed for an Int-with-fields, got {other:?}"),
        }
    }

    /// A peer that closes the socket before sending a full frame yields an `Io` error on `recv`, not
    /// a panic — the transport surfaces a dropped connection to the scheduler.
    #[test]
    fn recv_on_closed_peer_errors() {
        let listener = Listener::bind("127.0.0.1:0").expect("bind");
        let addr = listener.local_addr().expect("addr");
        let server = std::thread::spawn(move || {
            // Accept then immediately drop the stream — no frame is ever sent.
            let _t = listener.accept().expect("accept");
        });
        let mut client = Transport::connect(addr).expect("connect");
        match client.recv_value() {
            Err(NetError::Io(_)) => {}
            other => panic!("expected an Io error on a closed peer, got {other:?}"),
        }
        server.join().expect("server thread");
    }

    /// A malformed (non-envelope) frame is rejected by `open_envelope`, not silently mis-delivered.
    #[test]
    fn open_envelope_rejects_non_envelope() {
        assert!(matches!(
            open_envelope(Value::Int(5)),
            Err(NetError::Malformed(_))
        ));
        assert!(matches!(
            open_envelope(Value::Tuple(vec![Value::Null, Value::Int(0)])),
            Err(NetError::Malformed(_))
        ));
    }
}
