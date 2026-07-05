//! Shared whole-program closure-flow analysis (0-CFA) underlying both [`crate::defunc`] (P10
//! devirtualization) and [`crate::capspec`] (capture-aware specialization).
//!
//! This is exactly the analysis [`crate::defunc`] originally carried privately, extracted so a
//! second consumer can reuse the identical, already-proven flow graph instead of re-deriving it:
//! it builds the finite universe of first-class function values (every [`crate::anf::Comp::MkClosure`]
//! site) and propagates closure identity through `let`-copies, function parameters, environment
//! slots, **tuple fields** (the elim-loop packs a loop's live variables into a state `Tuple`, read
//! back with `Proj`), call arguments → callee parameters, and callee returns → call results.
//! Anything that escapes to an unanalyzable consumer (`Foreign`, an effect `Op`/`Handle`, an
//! unknown-callee apply, a delay, or a data constructor) is treated conservatively as **open**.
//!
//! Two extensions beyond `defunc`'s original private use:
//! - **Closure sites** (`Av::clo_sites` / `Cfa::clo_fields`): each [`crate::anf::Comp::MkClosure`]
//!   of a *known* lifted function is additionally recorded as a distinct site with its capture
//!   nodes, mirroring the existing tuple-`sites`/`fields` mechanism. `defunc` ignores this (it only
//!   needs the *name* a value may be a closure over, via `Av::fns`); `capspec` needs the specific
//!   allocation site to read back its capture values.
//! - **Constant-literal lattice** (`Av::const_lit`): a flat 3-point lattice (`Bottom` / `Lit(_)` /
//!   `Top`) seeded at closed, capture-free literal computations (`IntLit`/`NatLit`/`StrLit`/a
//!   nullary `Con`) and propagated by the *same* `Av::join` every other component uses — including
//!   through the existing `Cstr::Call`/`Cstr::GlobalCall` argument→parameter edge, which is exactly
//!   how a captured value (itself a callee's *parameter*, e.g. `adder`'s `k`) learns the constant
//!   passed at its call site(s). Two distinct literals reaching the same node join to `Top` (not
//!   specializable) — this is what makes a multi-call-site lifted function safely decline.

use crate::anf::{AnfFunc, AnfProgram, Atom, Comp, Tail};
use std::collections::{BTreeSet, HashMap};

/// A node in the flow graph (a binding occurrence, parameter, env slot, return, or construction).
pub(crate) type Node = usize;

/// The constant-literal lattice a node's value may occupy (see the module doc's "Constant-literal
/// lattice" section). `Lit` holds a closed, capture-free literal [`Comp`]: `IntLit`, `NatLit`,
/// `StrLit`, or a nullary `Con`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) enum ConstLit {
    /// No literal has reached this node yet.
    #[default]
    Bottom,
    /// Exactly one literal value has reached this node so far.
    Lit(Comp),
    /// Two or more distinct literals (or a non-literal value) reached this node: not specializable.
    Top,
}

impl ConstLit {
    /// Join `other` into `self`; return whether `self` changed. Monotone: `Bottom < Lit(_) < Top`,
    /// and two different `Lit`s join to `Top`.
    fn join(&mut self, other: &ConstLit) -> bool {
        match (&*self, other) {
            (_, ConstLit::Bottom) => false,
            (ConstLit::Bottom, ConstLit::Lit(l)) => {
                *self = ConstLit::Lit(l.clone());
                true
            }
            (ConstLit::Bottom, ConstLit::Top) => {
                *self = ConstLit::Top;
                true
            }
            (ConstLit::Lit(a), ConstLit::Lit(b)) => {
                if a == b {
                    false
                } else {
                    *self = ConstLit::Top;
                    true
                }
            }
            (ConstLit::Lit(_), ConstLit::Top) => {
                *self = ConstLit::Top;
                true
            }
            (ConstLit::Top, _) => false,
        }
    }
}

/// The abstract value of a node: the set of lifted-function closures it may hold, the set of
/// construction (tuple) sites it may be, whether it may also be an unanalyzable ("open") value,
/// the set of *closure* construction sites it may be, and the constant-literal lattice value.
/// A node is *devirtualizable as `L`* (defunc) iff its value is exactly `{L}` with no sites and not
/// open. A node is *capture-specializable* (capspec) iff it is exactly one closure site whose
/// captures are all constant.
#[derive(Clone, Default, PartialEq, Eq)]
pub(crate) struct Av {
    pub fns: BTreeSet<String>,
    pub sites: BTreeSet<Node>,
    pub open: bool,
    pub clo_sites: BTreeSet<Node>,
    pub const_lit: ConstLit,
}

impl Av {
    /// Join `other` into `self`; return whether `self` grew.
    fn join(&mut self, other: &Av) -> bool {
        let mut changed = false;
        for f in &other.fns {
            if self.fns.insert(f.clone()) {
                changed = true;
            }
        }
        for s in &other.sites {
            if self.sites.insert(*s) {
                changed = true;
            }
        }
        if other.open && !self.open {
            self.open = true;
            changed = true;
        }
        for s in &other.clo_sites {
            if self.clo_sites.insert(*s) {
                changed = true;
            }
        }
        if self.const_lit.join(&other.const_lit) {
            changed = true;
        }
        changed
    }
}

/// A flow constraint between nodes (a sound, monotone transfer applied to fixpoint).
pub(crate) enum Cstr {
    /// `to ⊇ from`.
    Copy { to: Node, from: Node },
    /// `node` is the closure of lifted function `name` (its value includes `{name}`).
    Closure { node: Node, name: String },
    /// `node` is a tuple construction site (its value includes the site `node`).
    Site { node: Node },
    /// `node` is a *closure* construction site of a known lifted function (its value includes the
    /// closure site `node`; the target name + capture nodes are recorded in `Cfa::clo_fields`).
    ClosureSite { node: Node },
    /// `node` is unconditionally open.
    Open { node: Node },
    /// `node` carries the constant literal `lit` (seeded at a literal-producing computation).
    Lit { node: Node, lit: Comp },
    /// `node` is definitely **not** a single tracked literal (seeded at any value-producing
    /// computation that isn't one of the tracked literal forms — a tuple, a non-nullary
    /// constructor, a closure, an arithmetic primitive, a delay, …). Without this, such a node's
    /// `const_lit` would default to (and could stay) `Bottom` forever, which the join treats as an
    /// *identity* (`Bottom` joined with anything leaves the other side unchanged) — so if the *same*
    /// node is also reached by an actual literal from a different flow edge (e.g. two different
    /// dynamic values flow to a function's single context-insensitive parameter node, one of which
    /// happens to be literal), the literal would win by default instead of correctly joining to
    /// `Top`. `Bottom` must mean *no producer reached this node yet*, never *a live, non-literal
    /// value reached it* — this constraint is exactly the difference.
    NotLit { node: Node },
    /// `to ⊇ field `idx` of every tuple site in `tup`'s value` (open if `tup` is open).
    Proj { to: Node, tup: Node, idx: usize },
    /// An indirect apply: `res ⊇ ret(L)` and `param(L) ⊇ arg` for every `L` in `head`'s value; if
    /// `head` is open (unknown callee) `res` becomes open and `arg` escapes.
    Call { res: Node, head: Node, arg: Node },
    /// A direct apply to a known captureless global `callee`: `res ⊇ ret(callee)`, `param(callee) ⊇ arg`.
    GlobalCall { res: Node, callee: usize, arg: Node },
    /// `node`'s value escapes to an unanalyzable consumer: every function reachable from it (through
    /// its closures and, transitively, the fields of its tuple sites) has its parameter opened.
    Escape { node: Node },
}

/// The whole-program closure-flow analyzer.
pub(crate) struct Cfa {
    n_nodes: usize,
    /// Per-function (index into `prog.funcs`) parameter and return nodes.
    pub param: Vec<Node>,
    pub ret: Vec<Node>,
    /// The program-entry return node (the result is printed, never applied).
    #[allow(dead_code)]
    entry_ret: Node,
    /// `(function index, env slot) → node`, created on demand.
    env_slot: HashMap<(usize, usize), Node>,
    /// A single shared open node (for `Atom::Global`/`Atom::Erased` heads).
    open_node: Node,
    pub func_index: HashMap<String, usize>,
    /// Tuple sites → their field source nodes.
    fields: HashMap<Node, Vec<Node>>,
    /// Closure sites (of a *known* lifted function) → (target name, capture source nodes), in the
    /// same left-to-right order as the `MkClosure` capture list (so index `k` is the source for
    /// that function's `EnvRef(k)`).
    pub clo_fields: HashMap<Node, (String, Vec<Node>)>,
    cstrs: Vec<Cstr>,
    /// The head node of every rewritable indirect apply, in deterministic traversal order
    /// (`Comp::Call` and `Tail::TailCall`). A rewrite pass consumes the matching decision by index.
    pub call_heads: Vec<Node>,
}

impl Cfa {
    fn fresh(&mut self) -> Node {
        let n = self.n_nodes;
        self.n_nodes += 1;
        n
    }

    fn env_slot_node(&mut self, func: usize, slot: usize) -> Node {
        if let Some(&n) = self.env_slot.get(&(func, slot)) {
            return n;
        }
        let n = self.fresh();
        self.env_slot.insert((func, slot), n);
        n
    }

    /// The node an atom reads in function `curfn` (`None` = program entry).
    fn atom_node(&mut self, a: &Atom, scope: &[Node], curfn: Option<usize>) -> Node {
        match a {
            Atom::Var(i) => scope[scope.len() - 1 - *i],
            Atom::EnvRef(k) => match curfn {
                Some(f) => self.env_slot_node(f, *k),
                None => self.open_node,
            },
            Atom::Global(_) | Atom::Erased => self.open_node,
        }
    }

    /// Generate constraints for a computation bound to `node` in `curfn` under `scope`.
    fn comp(&mut self, c: &Comp, node: Node, scope: &[Node], curfn: Option<usize>) {
        match c {
            Comp::Atom(a) => {
                let from = self.atom_node(a, scope, curfn);
                self.cstrs.push(Cstr::Copy { to: node, from });
            }
            Comp::MkClosure(name, caps, _) => {
                self.cstrs.push(Cstr::Closure {
                    node,
                    name: name.clone(),
                });
                self.cstrs.push(Cstr::NotLit { node });
                if let Some(&fi) = self.func_index.get(name) {
                    let mut cap_nodes = Vec::with_capacity(caps.len());
                    for (i, cap) in caps.iter().enumerate() {
                        let from = self.atom_node(cap, scope, curfn);
                        let to = self.env_slot_node(fi, i);
                        self.cstrs.push(Cstr::Copy { to, from });
                        cap_nodes.push(from);
                    }
                    self.clo_fields.insert(node, (name.clone(), cap_nodes));
                    self.cstrs.push(Cstr::ClosureSite { node });
                } else {
                    // Unknown lifted target: its captures escape (it could call them arbitrarily).
                    for cap in caps {
                        let n = self.atom_node(cap, scope, curfn);
                        self.cstrs.push(Cstr::Escape { node: n });
                    }
                }
            }
            Comp::Call(f, a) => {
                let head = self.atom_node(f, scope, curfn);
                let arg = self.atom_node(a, scope, curfn);
                self.cstrs.push(Cstr::Call {
                    res: node,
                    head,
                    arg,
                });
                self.call_heads.push(head);
            }
            Comp::CallGlobal(name, a) => {
                let arg = self.atom_node(a, scope, curfn);
                if let Some(&callee) = self.func_index.get(name) {
                    self.cstrs.push(Cstr::GlobalCall {
                        res: node,
                        callee,
                        arg,
                    });
                } else {
                    self.cstrs.push(Cstr::Open { node });
                    self.cstrs.push(Cstr::Escape { node: arg });
                }
            }
            // Produced only by `defunc`; never present in capspec's pre-defunc input, and opaque
            // (not re-analyzed) if this CFA is ever run again after defunc.
            Comp::CallKnown(_, _, _) => {}
            Comp::Tuple(args, _) => {
                self.cstrs.push(Cstr::Site { node });
                self.cstrs.push(Cstr::NotLit { node });
                let field_nodes: Vec<Node> = args
                    .iter()
                    .map(|a| self.atom_node(a, scope, curfn))
                    .collect();
                self.fields.insert(node, field_nodes);
            }
            Comp::Proj(i, a) => {
                let tup = self.atom_node(a, scope, curfn);
                self.cstrs.push(Cstr::Proj {
                    to: node,
                    tup,
                    idx: *i,
                });
            }
            Comp::Con(name, args, alloc) => {
                // We do not track closure flow through data constructors precisely: a closure
                // stored in a `Con` can be re-extracted by a `Case` (whose binders we treat as
                // open), so to stay sound any closure put into a non-nullary constructor escapes
                // (its parameter opens). A *nullary* `Con` (no args) carries no closure and is
                // itself a closed constant, so it seeds the constant-literal lattice instead.
                if args.is_empty() {
                    self.cstrs.push(Cstr::Lit {
                        node,
                        lit: Comp::Con(name.clone(), Vec::new(), *alloc),
                    });
                } else {
                    self.cstrs.push(Cstr::NotLit { node });
                    for a in args {
                        let n = self.atom_node(a, scope, curfn);
                        self.cstrs.push(Cstr::Escape { node: n });
                    }
                }
            }
            Comp::Op { arg, .. } => {
                // An effect operation: result comes from a handler (open), and the operand escapes to
                // the (analyzed-or-runtime) handler/continuation.
                self.cstrs.push(Cstr::Open { node });
                let n = self.atom_node(arg, scope, curfn);
                self.cstrs.push(Cstr::Escape { node: n });
            }
            Comp::Foreign(_, arg) => {
                self.cstrs.push(Cstr::Open { node });
                if let Some(a) = arg {
                    let n = self.atom_node(a, scope, curfn);
                    self.cstrs.push(Cstr::Escape { node: n });
                }
            }
            Comp::Now(a, _) | Comp::Later(a, _) => {
                // A delay value (forced later via the trampoline, whose result we treat as open). Be
                // conservative: a closure wrapped in a delay escapes, and the delay value itself is
                // never one of our tracked literal forms.
                self.cstrs.push(Cstr::NotLit { node });
                let n = self.atom_node(a, scope, curfn);
                self.cstrs.push(Cstr::Escape { node: n });
            }
            Comp::IntLit(n) => {
                if std::env::var_os("BL_CAPSPEC_DEBUG").is_some() {
                    eprintln!("  [cfa] node={node} <- IntLit({n})");
                }
                self.cstrs.push(Cstr::Lit {
                    node,
                    lit: Comp::IntLit(*n),
                });
            }
            Comp::NatLit(n) => {
                if std::env::var_os("BL_CAPSPEC_DEBUG").is_some() {
                    eprintln!("  [cfa] node={node} <- NatLit({n})");
                }
                self.cstrs.push(Cstr::Lit {
                    node,
                    lit: Comp::NatLit(*n),
                });
            }
            Comp::StrLit(cps) => {
                self.cstrs.push(Cstr::Lit {
                    node,
                    lit: Comp::StrLit(cps.clone()),
                });
            }
            // Pure non-closure scalars: contribute no closure flow, but the *result* is a computed
            // machine-word value, never one of our tracked literal forms (we do not constant-fold
            // arithmetic here) — it must not default to `Bottom`, or it could wrongly inherit an
            // unrelated literal via a later join (see `Cstr::NotLit`'s doc).
            Comp::IntPrim { .. } | Comp::NatPrim { .. } | Comp::FloatPrim { .. } => {
                self.cstrs.push(Cstr::NotLit { node });
            }
        }
    }

    /// Generate constraints for a tail expression in `curfn` (`None` = entry) under `scope`.
    fn tail(&mut self, t: &Tail, scope: &mut Vec<Node>, curfn: Option<usize>) {
        let ret = match curfn {
            Some(f) => self.ret[f],
            None => self.entry_ret,
        };
        match t {
            Tail::Ret(a) => {
                let from = self.atom_node(a, scope, curfn);
                self.cstrs.push(Cstr::Copy { to: ret, from });
            }
            Tail::Let(comp, rest) => {
                let node = self.fresh();
                self.comp(comp, node, scope, curfn);
                scope.push(node);
                self.tail(rest, scope, curfn);
                scope.pop();
            }
            Tail::TailCall(f, a) => {
                let head = self.atom_node(f, scope, curfn);
                let arg = self.atom_node(a, scope, curfn);
                self.cstrs.push(Cstr::Call {
                    res: ret,
                    head,
                    arg,
                });
                self.call_heads.push(head);
            }
            Tail::TailCallGlobal(name, a) => {
                let arg = self.atom_node(a, scope, curfn);
                if let Some(&callee) = self.func_index.get(name) {
                    self.cstrs.push(Cstr::GlobalCall {
                        res: ret,
                        callee,
                        arg,
                    });
                } else {
                    self.cstrs.push(Cstr::Open { node: ret });
                    self.cstrs.push(Cstr::Escape { node: arg });
                }
            }
            // Produced only by `defunc`; see the `Comp::CallKnown` note above.
            Tail::TailCallKnown(_, _, _) => {}
            Tail::Jump(a) => {
                // Re-enter the current function with a new argument tuple.
                let from = self.atom_node(a, scope, curfn);
                if let Some(f) = curfn {
                    let to = self.param[f];
                    self.cstrs.push(Cstr::Copy { to, from });
                }
            }
            Tail::Trampoline(a) => {
                // The forced value is the function's result; it is opaque.
                self.cstrs.push(Cstr::Open { node: ret });
                let n = self.atom_node(a, scope, curfn);
                self.cstrs.push(Cstr::Escape { node: n });
            }
            Tail::Case(_scrut, arms) => {
                for arm in arms {
                    // Constructor-field binders are treated as open (we do not track closure flow
                    // through data constructors — see `Comp::Con`).
                    for _ in 0..arm.binders {
                        let b = self.fresh();
                        self.cstrs.push(Cstr::Open { node: b });
                        scope.push(b);
                    }
                    self.tail(&arm.body, scope, curfn);
                    for _ in 0..arm.binders {
                        scope.pop();
                    }
                }
            }
            // `if-zero` binds no variables; analyze both branch continuations.
            Tail::IfZero(_scrut, then_, else_) => {
                self.tail(then_, scope, curfn);
                self.tail(else_, scope, curfn);
            }
            Tail::Region(body) => self.tail(body, scope, curfn),
            Tail::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                // The handler result is opaque; the handler/return/op clauses are closures the runtime
                // invokes with values we cannot see, so they escape.
                self.cstrs.push(Cstr::Open { node: ret });
                for atom in std::iter::once(body)
                    .chain(std::iter::once(return_clause))
                    .chain(op_clauses.iter().map(|(_, c)| c))
                {
                    let n = self.atom_node(atom, scope, curfn);
                    self.cstrs.push(Cstr::Escape { node: n });
                }
            }
        }
    }

    /// Solve the constraint system to its least fixpoint.
    fn solve(&mut self) -> Vec<Av> {
        let mut sol = vec![Av::default(); self.n_nodes];
        loop {
            let mut changed = false;
            for c in &self.cstrs {
                match c {
                    Cstr::Copy { to, from } => {
                        if to != from {
                            let src = sol[*from].clone();
                            changed |= sol[*to].join(&src);
                        }
                    }
                    Cstr::Closure { node, name } => {
                        if sol[*node].fns.insert(name.clone()) {
                            changed = true;
                        }
                    }
                    Cstr::Site { node } => {
                        if sol[*node].sites.insert(*node) {
                            changed = true;
                        }
                    }
                    Cstr::ClosureSite { node } => {
                        if sol[*node].clo_sites.insert(*node) {
                            changed = true;
                        }
                    }
                    Cstr::Open { node } => {
                        if !sol[*node].open {
                            sol[*node].open = true;
                            changed = true;
                        }
                        // An "open" (unanalyzable-source) value can never be proven a single tracked
                        // literal either — fold this into the same constraint so every existing
                        // `Cstr::Open` site (Case-arm binders, `Op`/`Foreign`/`Handle`/`Trampoline`
                        // results, an unknown `CallGlobal` target, the shared `open_node`) is covered
                        // for free.
                        if sol[*node].const_lit.join(&ConstLit::Top) {
                            changed = true;
                        }
                    }
                    Cstr::Lit { node, lit } => {
                        if sol[*node].const_lit.join(&ConstLit::Lit(lit.clone())) {
                            changed = true;
                        }
                    }
                    Cstr::NotLit { node } => {
                        if sol[*node].const_lit.join(&ConstLit::Top) {
                            changed = true;
                        }
                    }
                    Cstr::Proj { to, tup, idx } => {
                        let tv = sol[*tup].clone();
                        if tv.open {
                            if !sol[*to].open {
                                sol[*to].open = true;
                                changed = true;
                            }
                            if sol[*to].const_lit.join(&ConstLit::Top) {
                                changed = true;
                            }
                        }
                        for s in &tv.sites {
                            if let Some(flds) = self.fields.get(s) {
                                if let Some(&fnode) = flds.get(*idx) {
                                    let fv = sol[fnode].clone();
                                    changed |= sol[*to].join(&fv);
                                } else {
                                    // Out-of-range projection of this site (shape mismatch): be safe.
                                    if !sol[*to].open {
                                        sol[*to].open = true;
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                    Cstr::Call { res, head, arg } => {
                        let hv = sol[*head].clone();
                        for l in &hv.fns {
                            if let Some(&fi) = self.func_index.get(l) {
                                let arg_v = sol[*arg].clone();
                                changed |= sol[self.param[fi]].join(&arg_v);
                                let ret_v = sol[self.ret[fi]].clone();
                                changed |= sol[*res].join(&ret_v);
                            }
                        }
                        if hv.open {
                            if !sol[*res].open {
                                sol[*res].open = true;
                                changed = true;
                            }
                            if sol[*res].const_lit.join(&ConstLit::Top) {
                                changed = true;
                            }
                            changed |=
                                escape(&mut sol, &self.fields, &self.param, &self.func_index, *arg);
                        }
                    }
                    Cstr::GlobalCall { res, callee, arg } => {
                        let arg_v = sol[*arg].clone();
                        changed |= sol[self.param[*callee]].join(&arg_v);
                        let ret_v = sol[self.ret[*callee]].clone();
                        changed |= sol[*res].join(&ret_v);
                    }
                    Cstr::Escape { node } => {
                        changed |=
                            escape(&mut sol, &self.fields, &self.param, &self.func_index, *node);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        sol
    }
}

/// Open the parameter of every function reachable from `node` (its closures, and transitively the
/// fields of its tuple sites). Returns whether anything changed.
fn escape(
    sol: &mut [Av],
    fields: &HashMap<Node, Vec<Node>>,
    param: &[Node],
    func_index: &HashMap<String, usize>,
    node: Node,
) -> bool {
    let mut changed = false;
    let mut seen_sites: BTreeSet<Node> = BTreeSet::new();
    let mut work = vec![node];
    while let Some(n) = work.pop() {
        let v = sol[n].clone();
        for l in &v.fns {
            if let Some(&fi) = func_index.get(l) {
                if !sol[param[fi]].open {
                    sol[param[fi]].open = true;
                    changed = true;
                }
            }
        }
        for s in &v.sites {
            if seen_sites.insert(*s) {
                if let Some(flds) = fields.get(s) {
                    work.extend(flds.iter().copied());
                }
            }
        }
    }
    changed
}

/// Build the whole-program flow graph for `prog` and solve it to its least fixpoint. Returns the
/// analyzer (whose `call_heads`/`clo_fields`/`func_index` a decision pass consumes) and the
/// per-node solution.
pub(crate) fn build(prog: &AnfProgram) -> (Cfa, Vec<Av>) {
    let n = prog.funcs.len();
    let mut func_index = HashMap::new();
    for (i, f) in prog.funcs.iter().enumerate() {
        func_index.insert(f.name.clone(), i);
    }
    let mut cfa = Cfa {
        n_nodes: 0,
        param: Vec::with_capacity(n),
        ret: Vec::with_capacity(n),
        entry_ret: 0,
        env_slot: HashMap::new(),
        open_node: 0,
        func_index,
        fields: HashMap::new(),
        clo_fields: HashMap::new(),
        cstrs: Vec::new(),
        call_heads: Vec::new(),
    };
    for _ in 0..n {
        let p = cfa.fresh();
        cfa.param.push(p);
    }
    for _ in 0..n {
        let r = cfa.fresh();
        cfa.ret.push(r);
    }
    cfa.entry_ret = cfa.fresh();
    cfa.open_node = cfa.fresh();
    cfa.cstrs.push(Cstr::Open {
        node: cfa.open_node,
    });

    // Build constraints: each function body (scope = [param]) and the program entry (scope = []).
    for (i, f) in prog.funcs.iter().enumerate() {
        let mut scope = vec![cfa.param[i]];
        cfa.tail(&f.body, &mut scope, Some(i));
    }
    {
        let mut scope = Vec::new();
        cfa.tail(&prog.entry, &mut scope, None);
    }

    let sol = cfa.solve();
    (cfa, sol)
}

/// Look up a function's `AnfFunc` by name (a small linear scan; the whole-program function count
/// is small enough that a `HashMap` would not measurably help the one-shot decision passes).
pub(crate) fn func_by_name<'a>(prog: &'a AnfProgram, name: &str) -> Option<&'a AnfFunc> {
    prog.funcs.iter().find(|f| f.name == name)
}
