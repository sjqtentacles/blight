//! P10 follow-on — capture-aware specialization (untrusted backend, spec §7.1).
//!
//! [`crate::defunc`] devirtualizes a singleton-flow indirect apply to a direct
//! [`crate::anf::Comp::CallKnown`]/[`crate::anf::Tail::TailCallKnown`], dropping the closure-header
//! function-pointer load — but the closure object is still passed as the environment, so the callee
//! still pays a per-call **environment load** for each capture (`Atom::EnvRef(k)` → a GEP + load off
//! the closure's fields) and LTO still sees an indirection-free but *un-inlinable* call to a function
//! whose body reads through a heap pointer. When a capture is provably a single closed **constant**
//! across every flow path (e.g. `(adder (int 1))`'s captured `k = 1`), that load is pure overhead:
//! the callee could instead be specialized with the literal baked in directly, becoming captureless.
//!
//! This pass runs the same whole-program 0-CFA [`crate::cfa`] provides (shared with `defunc`), which
//! additionally tracks (a) the specific *closure-construction site* a value may be (not just which
//! function it may be a closure over) and (b) a flat constant-literal lattice per node, joined through
//! `let`-copies **and** the call argument→parameter edge — which is how a captured value (itself the
//! capturing function's own *parameter*) learns the constant(s) passed to it at its call site(s). Two
//! distinct literals reaching the same node join to *top*, so a multi-call-site capturing function
//! (whose capture varies) safely declines.
//!
//! When an apply's head resolves to **exactly one** closure-construction site, targeting a **known,
//! non-recursive** lifted function `L`, all of whose captures resolve to a single constant literal,
//! we synthesize a captureless clone `L$cap$<n>` — `L`'s body with every `EnvRef(k)` replaced by a
//! `let`-bound copy of the literal — and rewrite the apply to a direct, null-env
//! [`crate::anf::Comp::CallGlobal`]/[`crate::anf::Tail::TailCallGlobal`] of the clone. Clones are
//! deduplicated by `(L, captures)`, so every call site with the same constants shares one clone.
//!
//! **Runs *before* `defunc`** (`driver.rs`): `defunc`'s output `CallKnown`/`TailCallKnown` are opaque
//! to this analysis (mirroring how they are opaque to `defunc`'s own re-analysis), so capspec must see
//! the original `Call`/`TailCall` heads. `defunc` then devirtualizes whatever indirect applies remain
//! (calls whose closure isn't fully constant, or that resolve to more than one target).
//!
//! This is **value-preserving**: substituting a capture whose value the CFA fixpoint proves is
//! *always* exactly one literal cannot change any observable result, and the clone is byte-identical
//! in behavior to the original closure applied with that literal capture. Recursion is scoped out of
//! v1 (a self-recursive `L`'s clone would need its own self-calls remapped to the clone, tracked as a
//! follow-on); a non-constant loop-invariant capture would need an uncurried multi-arg calling
//! convention (the separately-tracked A3′ work), also out of scope. The safety net is the
//! `BL_NO_CAPSPEC` differential A/B (`DIFF_FLAGS`) — a bug here is a wrong number the harness catches,
//! never a false proof or a use-after-free. Zero kernel/re-checker surface is added.
//!
//! Pipeline position: an ANF→ANF pass run immediately after `anf::normalize` and *before* `defunc`,
//! gated by `BL_NO_CAPSPEC`.

use crate::anf::{AnfFunc, AnfProgram, Atom, Comp, Tail, TailArm};
use crate::cfa::{self, ConstLit};
use std::collections::HashMap;

/// Rewrite pass: replace the `i`-th recorded apply (in the same deterministic order the analysis
/// recorded heads) with a direct, null-env `CallGlobal`/`TailCallGlobal` of the specialized clone
/// when `decisions[i]` names one.
struct Rewriter {
    decisions: Vec<Option<String>>,
    idx: usize,
}

impl Rewriter {
    fn comp(&mut self, c: &Comp) -> Comp {
        match c {
            Comp::Call(_f, a) => {
                let d = self.decisions[self.idx].clone();
                self.idx += 1;
                match d {
                    Some(clone_name) => Comp::CallGlobal(clone_name, a.clone()),
                    None => c.clone(),
                }
            }
            _ => c.clone(),
        }
    }

    fn tail(&mut self, t: &Tail) -> Tail {
        match t {
            Tail::Let(comp, rest) => {
                let c = self.comp(comp);
                let r = self.tail(rest);
                Tail::Let(c, Box::new(r))
            }
            Tail::TailCall(_f, a) => {
                let d = self.decisions[self.idx].clone();
                self.idx += 1;
                match d {
                    Some(clone_name) => Tail::TailCallGlobal(clone_name, a.clone()),
                    None => t.clone(),
                }
            }
            Tail::Case(scrut, arms) => Tail::Case(
                scrut.clone(),
                arms.iter()
                    .map(|arm| TailArm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: self.tail(&arm.body),
                    })
                    .collect(),
            ),
            Tail::IfZero(scrut, then_, else_) => Tail::IfZero(
                scrut.clone(),
                Box::new(self.tail(then_)),
                Box::new(self.tail(else_)),
            ),
            Tail::Region(body) => Tail::Region(Box::new(self.tail(body))),
            // Terminal / no embedded rewritable apply. `CallKnown`/`TailCallKnown` never appear in
            // capspec's pre-defunc input, but are matched here defensively (identity) in case of a
            // future pipeline reorder or a direct unit-test call on post-defunc ANF.
            Tail::Ret(_)
            | Tail::Jump(_)
            | Tail::TailCallGlobal(_, _)
            | Tail::TailCallKnown(_, _, _)
            | Tail::Trampoline(_)
            | Tail::Handle { .. } => t.clone(),
        }
    }
}

/// Shift a free atom `Var(i)` at local binder depth `depth` by `m` (an original body embedded under
/// `m` freshly-prepended outer `let`s), and resolve an `EnvRef(k)` — no longer meaningful once the
/// clone is captureless — to the `k`-th materialized literal's `let` slot. See the module doc: the
/// clone is `Let(lits[0], Let(lits[1], …, Let(lits[m-1], shifted_body)))`, so from `shifted_body`'s
/// own root, `lits[m-1]` is the innermost binder (`Var(0)`) and `lits[0]` the outermost among them
/// (`Var(m-1)`) — i.e. `lits[k]` sits at `Var(m-1-k)` at depth 0, or `Var(depth + m-1-k)` at local
/// depth `depth`.
fn shift_atom(a: &Atom, depth: usize, m: usize) -> Atom {
    match a {
        Atom::Var(i) if *i >= depth => Atom::Var(i + m),
        Atom::Var(i) => Atom::Var(*i),
        Atom::EnvRef(k) => Atom::Var(depth + m - 1 - k),
        Atom::Global(g) => Atom::Global(g.clone()),
        Atom::Erased => Atom::Erased,
    }
}

fn shift_comp(c: &Comp, depth: usize, m: usize) -> Comp {
    let sa = |a: &Atom| shift_atom(a, depth, m);
    match c {
        Comp::Atom(a) => Comp::Atom(sa(a)),
        Comp::MkClosure(name, caps, alloc) => {
            Comp::MkClosure(name.clone(), caps.iter().map(sa).collect(), *alloc)
        }
        Comp::Call(f, a) => Comp::Call(sa(f), sa(a)),
        Comp::CallGlobal(name, a) => Comp::CallGlobal(name.clone(), sa(a)),
        Comp::CallKnown(name, env, a) => Comp::CallKnown(name.clone(), sa(env), sa(a)),
        Comp::Con(name, args, alloc) => {
            Comp::Con(name.clone(), args.iter().map(sa).collect(), *alloc)
        }
        Comp::Tuple(args, alloc) => Comp::Tuple(args.iter().map(sa).collect(), *alloc),
        Comp::Proj(i, a) => Comp::Proj(*i, sa(a)),
        Comp::Now(a, alloc) => Comp::Now(sa(a), *alloc),
        Comp::Later(a, alloc) => Comp::Later(sa(a), *alloc),
        Comp::Op { effect, op, arg } => Comp::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: sa(arg),
        },
        Comp::Foreign(s, arg) => Comp::Foreign(s.clone(), arg.as_ref().map(sa)),
        Comp::IntLit(n) => Comp::IntLit(*n),
        Comp::NatLit(n) => Comp::NatLit(*n),
        Comp::StrLit(v) => Comp::StrLit(v.clone()),
        Comp::IntPrim { op, lhs, rhs } => Comp::IntPrim {
            op: *op,
            lhs: sa(lhs),
            rhs: sa(rhs),
        },
        Comp::NatPrim { op, lhs, rhs } => Comp::NatPrim {
            op: *op,
            lhs: sa(lhs),
            rhs: rhs.as_ref().map(sa),
        },
        Comp::FloatPrim { op, lhs, rhs } => Comp::FloatPrim {
            op: *op,
            lhs: sa(lhs),
            rhs: rhs.as_ref().map(sa),
        },
    }
}

fn shift_tail(t: &Tail, depth: usize, m: usize) -> Tail {
    let sa = |a: &Atom| shift_atom(a, depth, m);
    match t {
        Tail::Ret(a) => Tail::Ret(sa(a)),
        Tail::Let(c, rest) => Tail::Let(
            shift_comp(c, depth, m),
            Box::new(shift_tail(rest, depth + 1, m)),
        ),
        Tail::TailCall(f, a) => Tail::TailCall(sa(f), sa(a)),
        Tail::Jump(a) => Tail::Jump(sa(a)),
        Tail::TailCallGlobal(name, a) => Tail::TailCallGlobal(name.clone(), sa(a)),
        Tail::TailCallKnown(name, env, a) => Tail::TailCallKnown(name.clone(), sa(env), sa(a)),
        Tail::Case(scrut, arms) => Tail::Case(
            sa(scrut),
            arms.iter()
                .map(|arm| TailArm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: shift_tail(&arm.body, depth + arm.binders, m),
                })
                .collect(),
        ),
        // `if-zero` binds no variables — branches shift at the same depth.
        Tail::IfZero(scrut, then_, else_) => Tail::IfZero(
            sa(scrut),
            Box::new(shift_tail(then_, depth, m)),
            Box::new(shift_tail(else_, depth, m)),
        ),
        Tail::Trampoline(a) => Tail::Trampoline(sa(a)),
        Tail::Region(body) => Tail::Region(Box::new(shift_tail(body, depth, m))),
        Tail::Handle {
            body,
            return_clause,
            op_clauses,
        } => Tail::Handle {
            body: sa(body),
            return_clause: sa(return_clause),
            op_clauses: op_clauses.iter().map(|(n, a)| (n.clone(), sa(a))).collect(),
        },
    }
}

/// Synthesize a captureless clone of `body` (a lifted function's body, whose free `Var`s reference
/// only its own parameter and local binders) with every `EnvRef(k)` replaced by a materialized copy
/// of `lits[k]`. See [`shift_atom`] for the index derivation.
fn specialize_body(body: &Tail, lits: &[Comp]) -> Tail {
    let m = lits.len();
    let shifted = shift_tail(body, 0, m);
    lits.iter()
        .rev()
        .fold(shifted, |acc, lit| Tail::Let(lit.clone(), Box::new(acc)))
}

/// Capture-aware specialization: for each apply whose head resolves to exactly one
/// closure-construction site of a known, non-recursive function with all-constant captures,
/// synthesize (and share, by `(L, captures)`) a captureless specialized clone and rewrite the apply
/// to a direct `CallGlobal`/`TailCallGlobal` of it.
pub fn capspec(prog: &AnfProgram) -> AnfProgram {
    let (cfa, sol) = cfa::build(prog);
    let recursive: std::collections::HashSet<&str> = prog
        .funcs
        .iter()
        .filter(|f| f.recursive)
        .map(|f| f.name.as_str())
        .collect();

    let mut clones: Vec<AnfFunc> = Vec::new();
    // `Comp` doesn't derive `Hash` (its `Atom`/`ConName`/etc. fields don't either), so dedup by a
    // small linear scan instead of a `HashMap` key — the number of distinct specializable closure
    // allocation sites in a program is tiny, so this is not a hot path.
    let mut clone_names: Vec<((String, Vec<Comp>), String)> = Vec::new();
    let mut next_id: HashMap<String, usize> = HashMap::new();
    let mut decisions: Vec<Option<String>> = Vec::with_capacity(cfa.call_heads.len());

    for &h in &cfa.call_heads {
        let v = &sol[h];
        if std::env::var_os("BL_CAPSPEC_DEBUG").is_some() {
            eprintln!(
                "head={h} open={} sites={:?} clo_sites={:?} fns={:?}",
                v.open, v.sites, v.clo_sites, v.fns
            );
        }
        let mut decision: Option<String> = None;
        if !v.open && v.sites.is_empty() && v.clo_sites.len() == 1 {
            let csite = *v.clo_sites.iter().next().unwrap();
            if let Some((name, caps)) = cfa.clo_fields.get(&csite) {
                if !recursive.contains(name.as_str()) {
                    if let Some(func) = cfa::func_by_name(prog, name) {
                        // Require every capture to resolve to a single constant literal. (A capture
                        // the callee never actually reads via `EnvRef` could safely be anything, but
                        // requiring all of them constant is a simpler, still-sound restriction — it
                        // never accepts an unsound specialization, only occasionally declines one
                        // that would have been fine.)
                        let mut lits: Vec<Comp> = Vec::with_capacity(caps.len());
                        let mut all_lit = true;
                        for &cap_node in caps {
                            if std::env::var_os("BL_CAPSPEC_DEBUG").is_some() {
                                eprintln!(
                                    "  cap_node={cap_node} const_lit={:?}",
                                    sol[cap_node].const_lit
                                );
                            }
                            match &sol[cap_node].const_lit {
                                ConstLit::Lit(c) => lits.push(c.clone()),
                                _ => {
                                    all_lit = false;
                                    break;
                                }
                            }
                        }
                        if all_lit {
                            let key = (name.clone(), lits.clone());
                            let existing = clone_names
                                .iter()
                                .find(|(k, _)| *k == key)
                                .map(|(_, n)| n.clone());
                            let clone_name = match existing {
                                Some(n) => n,
                                None => {
                                    let id = next_id.entry(name.clone()).or_insert(0);
                                    let n = format!("{name}$cap${id}");
                                    *id += 1;
                                    let body = specialize_body(&func.body, &lits);
                                    clones.push(AnfFunc {
                                        name: n.clone(),
                                        recursive: false,
                                        body,
                                    });
                                    clone_names.push((key, n.clone()));
                                    n
                                }
                            };
                            decision = Some(clone_name);
                        }
                    }
                }
            }
        }
        decisions.push(decision);
    }

    // Nothing to do? Return the program unchanged (cheap identity).
    if decisions.iter().all(Option::is_none) {
        return prog.clone();
    }

    let mut rw = Rewriter { decisions, idx: 0 };
    let mut funcs: Vec<AnfFunc> = prog
        .funcs
        .iter()
        .map(|f| AnfFunc {
            name: f.name.clone(),
            recursive: f.recursive,
            body: rw.tail(&f.body),
        })
        .collect();
    let entry = rw.tail(&prog.entry);
    debug_assert_eq!(
        rw.idx,
        rw.decisions.len(),
        "rewrite visited every recorded apply"
    );
    funcs.extend(clones);

    AnfProgram {
        funcs,
        entry,
        con_tags: prog.con_tags.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Alloc;
    use blight_kernel::IntPrimOp;

    /// `adder_inner(env, a) = a + env[0]` — the lifted closure body `hofold_int.bl`'s `(adder k)`
    /// compiles to (one capture, used once as `IntPrim::Add`'s rhs).
    fn adder_inner(recursive: bool) -> AnfFunc {
        AnfFunc {
            name: "adder_inner".into(),
            recursive,
            body: Tail::Let(
                Comp::IntPrim {
                    op: IntPrimOp::Add,
                    lhs: Atom::Var(0),
                    rhs: Atom::EnvRef(0),
                },
                Box::new(Tail::Ret(Atom::Var(0))),
            ),
        }
    }

    /// `Let(one = IntLit(1), Let(clo = MkClosure(adder_inner, [one]), Let(arg = IntLit(n),
    /// TailCall(clo, arg))))` — one call site of `(adder 1)` applied to the literal `n`. `cap` lets a
    /// test swap in a non-constant capture atom instead of the freshly-bound literal.
    fn one_call_site(n: i64, cap: Atom) -> Tail {
        Tail::Let(
            Comp::IntLit(1),
            Box::new(Tail::Let(
                Comp::MkClosure("adder_inner".into(), vec![cap], Alloc::Gc),
                Box::new(Tail::Let(
                    Comp::IntLit(n),
                    Box::new(Tail::TailCall(Atom::Var(1), Atom::Var(0))),
                )),
            )),
        )
    }

    /// Two independent call sites (each its own `MkClosure` allocation), both capturing the literal
    /// `1` over `adder_inner`, applied to different arguments (`5` and `7`) via non-tail `Call`s.
    fn two_call_sites() -> Tail {
        let inner = Tail::Ret(Atom::Var(0));
        let inner = Tail::Let(Comp::Call(Atom::Var(1), Atom::Var(0)), Box::new(inner)); // r2
        let inner = Tail::Let(Comp::IntLit(7), Box::new(inner)); // arg2
        let inner = Tail::Let(
            Comp::MkClosure("adder_inner".into(), vec![Atom::Var(0)], Alloc::Gc),
            Box::new(inner),
        ); // clo2, captures one2
        let inner = Tail::Let(Comp::IntLit(1), Box::new(inner)); // one2
        let inner = Tail::Let(Comp::Call(Atom::Var(1), Atom::Var(0)), Box::new(inner)); // r1
        let inner = Tail::Let(Comp::IntLit(5), Box::new(inner)); // arg1
        let inner = Tail::Let(
            Comp::MkClosure("adder_inner".into(), vec![Atom::Var(0)], Alloc::Gc),
            Box::new(inner),
        ); // clo1, captures one1
        Tail::Let(Comp::IntLit(1), Box::new(inner)) // one1
    }

    fn atom_has_envref(a: &Atom) -> bool {
        matches!(a, Atom::EnvRef(_))
    }

    fn comp_has_envref(c: &Comp) -> bool {
        match c {
            Comp::Atom(a) => atom_has_envref(a),
            Comp::MkClosure(_, caps, _) => caps.iter().any(atom_has_envref),
            Comp::Call(f, a) => atom_has_envref(f) || atom_has_envref(a),
            Comp::CallGlobal(_, a) => atom_has_envref(a),
            Comp::CallKnown(_, e, a) => atom_has_envref(e) || atom_has_envref(a),
            Comp::Con(_, args, _) | Comp::Tuple(args, _) => args.iter().any(atom_has_envref),
            Comp::Proj(_, a) | Comp::Now(a, _) | Comp::Later(a, _) => atom_has_envref(a),
            Comp::Op { arg, .. } => atom_has_envref(arg),
            Comp::IntPrim { lhs, rhs, .. } => atom_has_envref(lhs) || atom_has_envref(rhs),
            Comp::NatPrim { lhs, rhs, .. } | Comp::FloatPrim { lhs, rhs, .. } => {
                atom_has_envref(lhs) || rhs.as_ref().is_some_and(atom_has_envref)
            }
            Comp::Foreign(_, arg) => arg.as_ref().is_some_and(atom_has_envref),
            Comp::IntLit(_) | Comp::NatLit(_) | Comp::StrLit(_) => false,
        }
    }

    /// Walk past a chain of `Tail::Let`s to the final non-`Let` tail expression.
    fn innermost_tail(t: &Tail) -> &Tail {
        let mut cur = t;
        while let Tail::Let(_, rest) = cur {
            cur = rest;
        }
        cur
    }

    /// Does any `Atom::EnvRef` occur anywhere in `t`?
    fn contains_envref(t: &Tail) -> bool {
        match t {
            Tail::Ret(a) | Tail::Jump(a) | Tail::Trampoline(a) => atom_has_envref(a),
            Tail::Let(c, rest) => comp_has_envref(c) || contains_envref(rest),
            Tail::TailCall(f, a) => atom_has_envref(f) || atom_has_envref(a),
            Tail::TailCallGlobal(_, a) => atom_has_envref(a),
            Tail::TailCallKnown(_, e, a) => atom_has_envref(e) || atom_has_envref(a),
            Tail::Case(scrut, arms) => {
                atom_has_envref(scrut) || arms.iter().any(|arm| contains_envref(&arm.body))
            }
            Tail::IfZero(scrut, then_, else_) => {
                atom_has_envref(scrut) || contains_envref(then_) || contains_envref(else_)
            }
            Tail::Region(b) => contains_envref(b),
            Tail::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                atom_has_envref(body)
                    || atom_has_envref(return_clause)
                    || op_clauses.iter().any(|(_, a)| atom_has_envref(a))
            }
        }
    }

    /// A singleton-flow apply whose closure's only capture is a constant literal specializes: the
    /// site becomes a null-env `TailCallGlobal` of a new captureless clone, and the clone's body
    /// contains no `EnvRef` (every capture read was materialized as a `let`-bound literal).
    #[test]
    fn specializes_constant_capture() {
        let prog = AnfProgram {
            funcs: vec![adder_inner(false)],
            entry: one_call_site(5, Atom::Var(0)),
            con_tags: Default::default(),
        };
        let out = capspec(&prog);
        assert_eq!(
            out.funcs.len(),
            2,
            "gained exactly one specialized clone: {:?}",
            out.funcs
        );
        let clone = out
            .funcs
            .iter()
            .find(|f| f.name != "adder_inner")
            .expect("clone present");
        assert!(
            !clone.recursive,
            "the clone is captureless (not self-recursive)"
        );
        assert!(
            !contains_envref(&clone.body),
            "the clone reads no EnvRef: {:?}",
            clone.body
        );
        match innermost_tail(&out.entry) {
            Tail::TailCallGlobal(name, Atom::Var(_)) => assert_eq!(name, &clone.name),
            other => panic!("expected TailCallGlobal(clone, arg), got {other:?}"),
        }
    }

    /// Two call sites (two distinct `MkClosure` allocations) that specialize to the same `(L,
    /// captures)` key share one clone.
    #[test]
    fn dedups_identical_specializations() {
        let prog = AnfProgram {
            funcs: vec![adder_inner(false)],
            entry: two_call_sites(),
            con_tags: Default::default(),
        };
        let out = capspec(&prog);
        let clone_count = out.funcs.iter().filter(|f| f.name != "adder_inner").count();
        assert_eq!(
            clone_count, 1,
            "identical (L, captures) share one clone: {:?}",
            out.funcs
        );
    }

    /// A capture that is not a single constant literal (here, an unanalyzable `Global` atom) must
    /// decline: no clone is synthesized and the apply is left as an ordinary `TailCall`.
    #[test]
    fn declines_non_constant_capture() {
        let prog = AnfProgram {
            funcs: vec![adder_inner(false)],
            entry: one_call_site(5, Atom::Global("mystery".into())),
            con_tags: Default::default(),
        };
        let out = capspec(&prog);
        assert_eq!(out.funcs.len(), 1, "no clone synthesized: {:?}", out.funcs);
        assert!(
            matches!(innermost_tail(&out.entry), Tail::TailCall(_, _)),
            "apply left as an ordinary TailCall: {:?}",
            out.entry
        );
    }

    /// A self-recursive `L` must decline (v1 scope guard — see the module doc): the clone would need
    /// its self-calls remapped, which this pass does not attempt.
    #[test]
    fn declines_recursive_target() {
        let prog = AnfProgram {
            funcs: vec![adder_inner(true)],
            entry: one_call_site(5, Atom::Var(0)),
            con_tags: Default::default(),
        };
        let out = capspec(&prog);
        assert_eq!(out.funcs.len(), 1, "no clone synthesized: {:?}", out.funcs);
        assert!(
            matches!(innermost_tail(&out.entry), Tail::TailCall(_, _)),
            "apply left as an ordinary TailCall: {:?}",
            out.entry
        );
    }

    /// Regression for a real CFA soundness bug the `BL_NO_CAPSPEC` differential harness caught on
    /// `mergesort.bl`/`bytes_scratch.bl`/`greet.bl`: a capture that is itself some function `h`'s
    /// *parameter* — a node the whole-program (context-insensitive) analysis shares across **every**
    /// call site of `h` — must decline when even one of those call sites passes a genuinely dynamic
    /// (non-literal) value, not just when two call sites disagree on *which* literal. The bug was
    /// that non-literal-producing computations (arithmetic, non-nullary constructors, tuples,
    /// closures, delays) left their result node's `const_lit` at the lattice default `Bottom`
    /// instead of explicitly `Top`; `Bottom` is a join *identity*, so a later literal-valued call
    /// site would silently "win" instead of correctly joining to `Top`. Here `h`'s parameter is fed
    /// a literal `IntLit(9)` from one call site and an `IntPrim::Add` result (never a tracked
    /// literal, since we don't constant-fold arithmetic) from another; `h`'s internal apply — whose
    /// capture is that shared parameter — must be left unspecialized.
    #[test]
    fn declines_when_shared_capture_param_also_reaches_a_dynamic_value() {
        // h(p) = let clo = MkClosure(adder_inner, [p]) in TailCall(clo, 9)
        let h = AnfFunc {
            name: "h".into(),
            recursive: false,
            body: Tail::Let(
                Comp::MkClosure("adder_inner".into(), vec![Atom::Var(0)], Alloc::Gc),
                Box::new(Tail::Let(
                    Comp::IntLit(9),
                    Box::new(Tail::TailCall(Atom::Var(1), Atom::Var(0))),
                )),
            ),
        };
        // entry: h(5) [literal]; h(1+2) [dynamic, never a tracked literal]
        let entry = Tail::Let(
            Comp::IntLit(5),
            Box::new(Tail::Let(
                Comp::CallGlobal("h".into(), Atom::Var(0)),
                Box::new(Tail::Let(
                    Comp::IntLit(1),
                    Box::new(Tail::Let(
                        Comp::IntLit(2),
                        Box::new(Tail::Let(
                            Comp::IntPrim {
                                op: IntPrimOp::Add,
                                lhs: Atom::Var(1),
                                rhs: Atom::Var(0),
                            },
                            Box::new(Tail::Let(
                                Comp::CallGlobal("h".into(), Atom::Var(0)),
                                Box::new(Tail::Ret(Atom::Var(0))),
                            )),
                        )),
                    )),
                )),
            )),
        );
        let prog = AnfProgram {
            funcs: vec![adder_inner(false), h],
            entry,
            con_tags: Default::default(),
        };
        let out = capspec(&prog);
        assert_eq!(
            out.funcs.len(),
            2,
            "no clone synthesized — the shared capture param is Top, not a single Lit: {:?}",
            out.funcs.iter().map(|f| &f.name).collect::<Vec<_>>()
        );
        let h_out = out.funcs.iter().find(|f| f.name == "h").expect("h present");
        assert!(
            matches!(innermost_tail(&h_out.body), Tail::TailCall(_, _)),
            "h's internal apply is left as an ordinary TailCall: {:?}",
            h_out.body
        );
    }

    /// An open (unanalyzable) call head — a bare `Global` reference never built via a statically
    /// visible `MkClosure` — must decline.
    #[test]
    fn declines_open_head() {
        let prog = AnfProgram {
            funcs: vec![adder_inner(false)],
            entry: Tail::Let(
                Comp::IntLit(5),
                Box::new(Tail::TailCall(
                    Atom::Global("adder_inner".into()),
                    Atom::Var(0),
                )),
            ),
            con_tags: Default::default(),
        };
        let out = capspec(&prog);
        assert_eq!(out.funcs.len(), 1, "no clone synthesized: {:?}", out.funcs);
        assert!(matches!(
            out.entry,
            Tail::Let(_, ref rest) if matches!(**rest, Tail::TailCall(_, _))
        ));
    }
}
