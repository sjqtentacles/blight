//! Region escape analysis (spec §3.5) — **UNTRUSTED**.
//!
//! This is the tower-level "interpretation of the grading spine" the spec calls for: a
//! behavior-preserving backend pass that reads the region structure ([`Cir::Region`] scopes
//! introduced by [`crate::lower`]) and decides, for each allocation inside a scope, whether it
//! can be bump-allocated in the region's arena ([`Alloc::Arena`]) or must stay on the
//! garbage-collected heap ([`Alloc::Gc`]). It never changes the *value* a program computes — a
//! wrong `Arena` choice would be a memory-safety **bug** (use-after-free), never an unsoundness in
//! the type theory, so the analysis is deliberately **conservative**: an allocation is moved to the
//! arena only when it *provably* does not outlive its enclosing region scope.
//!
//! ## What "does not escape" means here
//! An allocation inside a `(region r …)` scope escapes if, after the scope's `bl_arena_leave`, a
//! live pointer to it could still be reachable. Three ways that happens, all treated as escapes:
//!  1. **Returned** — it is (or is part of) the region body's *result value*. The body's tail
//!     position is an escaping position, and so is every constructor/tuple field of an escaping
//!     value (an escaping record keeps its fields alive).
//!  2. **Captured by a closure** — it appears inside a `λ` body. A closure may be returned or
//!     stored, so anything it captures may outlive the scope; we conservatively treat the entire
//!     `Lam`/`Fix` body as escaping.
//!  3. **Stored into an escaping structure** — modelled by (1): a field of an escaping `Con`/`Tuple`
//!     is itself escaping.
//!
//! Everything else inside the scope — intermediate scratch bound by a `let` and merely *consumed*
//! (projected, matched, passed to a call as a transient) — is non-escaping and becomes `Arena`.
//!
//! ## Scope discipline
//! The analysis only flips allocations that are **lexically inside** a `Cir::Region` node and in a
//! non-escaping position relative to that region. Allocations outside any region, or in an escaping
//! position, keep their default `Gc` tag. Nested regions are handled by the innermost scope.

use crate::ir::{Alloc, Arm, Cir, Func, Program};

/// Run the region escape analysis over a whole pre-closure-conversion program, returning a new
/// program with eligible allocations retagged [`Alloc::Arena`]. Pure and total.
pub fn analyze_program(prog: &Program) -> Program {
    Program {
        funcs: prog
            .funcs
            .iter()
            .map(|f| Func {
                name: f.name.clone(),
                recursive: f.recursive,
                body: analyze(&f.body),
            })
            .collect(),
        entry: analyze(&prog.entry),
    }
}

/// Analyze a single expression. Outside any region scope nothing changes; the work happens when we
/// descend into a [`Cir::Region`], where we switch to the in-region walk with the body in escaping
/// (result) position.
pub fn analyze(c: &Cir) -> Cir {
    match c {
        // Entering a region scope: the body is in the region's *result* (escaping) position, but
        // allocations it merely uses internally can still be arena'd. Walk the body in-region.
        Cir::Region(body) => Cir::Region(Box::new(walk(body, /*escaping=*/ true))),

        // Outside a region, recurse structurally without retagging (allocations stay Gc), but we
        // must still find any *nested* region scopes deeper in the tree.
        _ => map_children(c, analyze),
    }
}

/// Walk an expression that is lexically inside a region scope. `escaping` says whether the value
/// produced *here* outlives the scope (and so any allocation node we are sitting on must stay Gc).
///
/// The recursion threads `escaping` down: a `let`'s bound value is non-escaping scratch; a `let`'s
/// body inherits the position; an escaping `Con`/`Tuple`'s fields stay escaping; a `λ` body is
/// always escaping (closure capture). A nested `Region` resets to its own result position.
fn walk(c: &Cir, escaping: bool) -> Cir {
    match c {
        // ---- allocation nodes: the heart of the analysis ----
        Cir::Con(name, args, _) => {
            let alloc = if escaping { Alloc::Gc } else { Alloc::Arena };
            // A *field* of an arena object can be projected back out and returned, outliving the
            // scope. We cannot cheaply prove it won't, so fields are analyzed in escaping position:
            // the record itself lives in the arena, but the things it points at stay GC unless they
            // are themselves non-escaping scratch decided elsewhere. This keeps `Proj`-and-return
            // sound (the projected value is a GC object).
            let args = args.iter().map(|a| walk(a, true)).collect();
            Cir::Con(name.clone(), args, alloc)
        }
        Cir::Tuple(args, _) => {
            let alloc = if escaping { Alloc::Gc } else { Alloc::Arena };
            let args = args.iter().map(|a| walk(a, true)).collect();
            Cir::Tuple(args, alloc)
        }
        Cir::Now(e, _) => {
            let alloc = if escaping { Alloc::Gc } else { Alloc::Arena };
            Cir::Now(Box::new(walk(e, true)), alloc)
        }
        Cir::Later(e, _) => {
            // A `later` thunk drives the delay trampoline and routinely escapes the local scope by
            // construction (spec §7.3 / the recursion interplay note). Conservatively keep it Gc
            // and treat its body as escaping.
            Cir::Later(Box::new(walk(e, true)), Alloc::Gc)
        }
        Cir::MkClosure(name, caps, _) => {
            // A closure value may be returned/stored; keep it Gc and treat its captures as escaping.
            let caps = caps.iter().map(|c| walk(c, true)).collect();
            Cir::MkClosure(name.clone(), caps, Alloc::Gc)
        }

        // ---- binding / sequencing: scratch is non-escaping unless the body returns the binder ----
        Cir::Let(v, body) => {
            // The bound value is local scratch *unless* the body lets it escape: i.e. the binder
            // (de Bruijn 0 inside `body`) reaches an escaping position of `body`. If it does, the
            // bound value outlives the scope and must stay Gc; otherwise it is arena-able.
            let binder_escapes = escaping && var_reaches_escaping(body, 0);
            let v2 = walk(v, /*escaping=*/ binder_escapes);
            let body2 = walk(body, escaping);
            Cir::Let(Box::new(v2), Box::new(body2))
        }

        // ---- closures: their bodies escape (capture) ----
        Cir::Lam(b) => Cir::Lam(Box::new(walk(b, true))),
        Cir::Fix(b) => Cir::Fix(Box::new(walk(b, true))),

        // ---- elimination / control: the scrutinee is consumed (non-escaping), arms inherit ----
        Cir::Case(scrut, arms) => {
            let scrut2 = walk(scrut, false);
            let arms2 = arms
                .iter()
                .map(|a| Arm {
                    con: a.con.clone(),
                    binders: a.binders,
                    body: walk(&a.body, escaping),
                })
                .collect();
            Cir::Case(Box::new(scrut2), arms2)
        }
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(walk(e, escaping))),
        Cir::Force(e) => Cir::Force(Box::new(walk(e, escaping))),

        // An application's head and argument are consumed by the call; the *result* inherits the
        // position. We cannot see the callee body here, so we treat the argument as escaping
        // (it may be retained by the callee) — conservative.
        Cir::App(f, a) => Cir::App(Box::new(walk(f, true)), Box::new(walk(a, true))),
        Cir::CallClosure(f, a) => {
            Cir::CallClosure(Box::new(walk(f, true)), Box::new(walk(a, true)))
        }

        // A nested region scope resets to its own result position.
        Cir::Region(body) => Cir::Region(Box::new(walk(body, true))),

        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            // An effect operand escapes into the (possibly long-lived) handler/continuation.
            arg: Box::new(walk(arg, true)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(walk(body, escaping)),
            return_clause: Box::new(walk(return_clause, escaping)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), walk(e, true)))
                .collect(),
        },

        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(walk(lhs, false)),
            rhs: Box::new(walk(rhs, false)),
        },

        // Leaves carry no allocation. A foreign C call's result is GC-allocated by the callee.
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::Foreign(_)
        | Cir::IntLit(_) => c.clone(),
    }
}

/// Conservatively decide whether the local binder `v` (a de Bruijn index, relative to the current
/// scope) can reach an **escaping position** of `c` — meaning a value built from it could outlive
/// the enclosing region. We over-approximate: any free occurrence of `v` in an escaping subposition
/// counts. Escaping positions mirror [`walk`]'s `escaping=true` propagation: the tail/result of the
/// expression, fields of an escaping `Con`/`Tuple`/`Now`, the body of any `Lam`/`Fix` (capture),
/// `App`/`CallClosure`/`Op` operands, and `later` bodies. Non-escaping (consuming) positions —
/// `Case` scrutinee, `Proj`/`Force` subject, a `let`'s scratch value — do not count on their own.
///
/// Soundness: returning `true` whenever unsure keeps the bound value on the GC heap (safe). The
/// `depth`-adjusted index tracks `v` under the binders introduced by `Lam`/`Fix`/`Let`/`Case` arms.
fn var_reaches_escaping(c: &Cir, v: usize) -> bool {
    // `esc`: are we currently in an escaping position? `v`: the index we are tracking at this depth.
    fn go(c: &Cir, v: usize, esc: bool) -> bool {
        match c {
            Cir::Var(i) => esc && *i == v,
            Cir::Global(_) | Cir::EnvRef(_) | Cir::Erased | Cir::Foreign(_) | Cir::IntLit(_) => {
                false
            }
            // A closure capturing `v` lets it escape; its body is escaping and `v` shifts under the
            // λ's parameter binder.
            Cir::Lam(b) | Cir::Fix(b) => go(b, v + 1, true),
            Cir::App(f, a) | Cir::CallClosure(f, a) => go(f, v, true) || go(a, v, true),
            Cir::IntPrim { lhs, rhs, .. } => go(lhs, v, false) || go(rhs, v, false),
            Cir::Let(val, body) => {
                // The scratch value position is non-escaping; the body inherits `esc`, under +1.
                go(val, v, false) || go(body, v + 1, esc)
            }
            Cir::Con(_, args, _) | Cir::Tuple(args, _) => args.iter().any(|a| go(a, v, esc)),
            Cir::Now(e, _) => go(e, v, esc),
            Cir::Later(e, _) => go(e, v, true),
            Cir::Proj(_, e) => go(e, v, false),
            Cir::Force(e) => go(e, v, esc),
            Cir::Case(s, arms) => {
                // Scrutinee consumes (non-escaping); each arm inherits `esc` under its binders.
                go(s, v, false) || arms.iter().any(|a| go(&a.body, v + a.binders, esc))
            }
            Cir::Region(b) => go(b, v, true),
            Cir::MkClosure(_, caps, _) => caps.iter().any(|c| go(c, v, true)),
            Cir::Op { arg, .. } => go(arg, v, true),
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                go(body, v, esc)
                    || go(return_clause, v, esc)
                    || op_clauses.iter().any(|(_, e)| go(e, v, true))
            }
        }
    }
    go(c, v, true)
}

/// Structurally rebuild `c`, applying `f` to each immediate `Cir` child. Used by [`analyze`] to find
/// nested regions without retagging allocations outside any region.
fn map_children(c: &Cir, f: fn(&Cir) -> Cir) -> Cir {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::Foreign(_)
        | Cir::IntLit(_) => c.clone(),
        Cir::Lam(b) => Cir::Lam(Box::new(f(b))),
        Cir::Fix(b) => Cir::Fix(Box::new(f(b))),
        Cir::App(g, a) => Cir::App(Box::new(f(g)), Box::new(f(a))),
        Cir::CallClosure(g, a) => Cir::CallClosure(Box::new(f(g)), Box::new(f(a))),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: Box::new(f(rhs)),
        },
        Cir::Let(v, b) => Cir::Let(Box::new(f(v)), Box::new(f(b))),
        Cir::Con(n, args, al) => Cir::Con(n.clone(), args.iter().map(f).collect(), *al),
        Cir::Tuple(args, al) => Cir::Tuple(args.iter().map(f).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(f(e))),
        Cir::Now(e, al) => Cir::Now(Box::new(f(e)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(f(e)), *al),
        Cir::Force(e) => Cir::Force(Box::new(f(e))),
        Cir::MkClosure(n, caps, al) => Cir::MkClosure(n.clone(), caps.iter().map(f).collect(), *al),
        Cir::Region(b) => Cir::Region(Box::new(f(b))),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(f(s)),
            arms.iter()
                .map(|a| Arm {
                    con: a.con.clone(),
                    binders: a.binders,
                    body: f(&a.body),
                })
                .collect(),
        ),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(f(arg)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(f(body)),
            return_clause: Box::new(f(return_clause)),
            op_clauses: op_clauses.iter().map(|(n, e)| (n.clone(), f(e))).collect(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::ConName;

    fn con(name: &str, args: Vec<Cir>) -> Cir {
        Cir::con(ConName(name.into()), args)
    }

    /// Outside any region, every allocation keeps its default `Gc` tag.
    #[test]
    fn no_region_keeps_gc() {
        let c = con("Zero", vec![]);
        let out = analyze(&c);
        assert!(matches!(out, Cir::Con(_, _, Alloc::Gc)));
    }

    /// An allocation that *is* the region's result value escapes the scope → stays `Gc`.
    #[test]
    fn escaping_alloc_stays_gc() {
        // (region r  (Con "Pair" [Zero, Zero]))   — the pair is returned, so it escapes.
        let body = con("Pair", vec![con("Zero", vec![]), con("Zero", vec![])]);
        let region = Cir::Region(Box::new(body));
        let out = analyze(&region);
        let Cir::Region(inner) = out else {
            panic!("expected a region scope");
        };
        assert!(
            matches!(*inner, Cir::Con(_, _, Alloc::Gc)),
            "the returned allocation must stay on the GC heap: {inner:?}"
        );
    }

    /// An allocation used only as local scratch (a `let`-bound value the body merely projects, not
    /// returns) becomes `Arena`.
    #[test]
    fn local_alloc_becomes_arena() {
        // (region r  (let scratch = Tuple[Zero, Zero] in (Proj 0 scratch)))
        // The tuple is scratch; only a projection of it is returned (a Var/Proj carries no alloc).
        let scratch = Cir::tuple(vec![con("Zero", vec![]), con("Zero", vec![])]);
        let body = Cir::Let(
            Box::new(scratch),
            Box::new(Cir::Proj(0, Box::new(Cir::Var(0)))),
        );
        let region = Cir::Region(Box::new(body));
        let out = analyze(&region);
        let Cir::Region(inner) = out else {
            panic!("expected a region scope");
        };
        let Cir::Let(bound, _) = *inner else {
            panic!("expected a let");
        };
        assert!(
            matches!(*bound, Cir::Tuple(_, Alloc::Arena)),
            "the scratch tuple must be arena-allocated: {bound:?}"
        );
    }

    /// A value returned from the region (in tail position) escapes — even through a `let` body.
    #[test]
    fn returned_value_escapes() {
        // (region r  (let scratch = Zero in (Con "Box" [<the returned Con>])))
        // The returned `Con "Box"` is in the let body's tail/escaping position → Gc.
        let body = Cir::Let(
            Box::new(con("Zero", vec![])),
            Box::new(con("Box", vec![Cir::Var(0)])),
        );
        let region = Cir::Region(Box::new(body));
        let out = analyze(&region);
        let Cir::Region(inner) = out else {
            panic!("expected a region scope");
        };
        let Cir::Let(_, retbody) = *inner else {
            panic!("expected a let");
        };
        assert!(
            matches!(*retbody, Cir::Con(_, _, Alloc::Gc)),
            "the returned constructor must stay GC: {retbody:?}"
        );
    }

    /// An allocation captured by a closure may outlive the scope → stays `Gc`.
    #[test]
    fn closure_capture_escapes() {
        // (region r  (let _ = (λ. Con "Cap" [Zero]) in Zero))
        // The Con inside the λ body is closure-captured → must stay Gc despite being in a non-tail
        // (scratch) let position.
        let lam = Cir::Lam(Box::new(con("Cap", vec![con("Zero", vec![])])));
        let body = Cir::Let(Box::new(lam), Box::new(con("Zero", vec![])));
        let region = Cir::Region(Box::new(body));
        let out = analyze(&region);
        let Cir::Region(inner) = out else {
            panic!("expected a region scope");
        };
        let Cir::Let(bound, _) = *inner else {
            panic!("expected a let");
        };
        let Cir::Lam(lam_body) = *bound else {
            panic!("expected a lambda");
        };
        assert!(
            matches!(*lam_body, Cir::Con(_, _, Alloc::Gc)),
            "an allocation inside a closure body must stay GC: {lam_body:?}"
        );
    }
}
