//! Wave 6 / C3 — the transient-consumption (linearity) analysis substrate. **UNTRUSTED.**
//!
//! The gating research for both interprocedural arenas (P5.2) and RC-in-place-reuse (P5.1): a
//! sound, checkable analysis proving a heap value is *fully consumed* — read exactly once, in a
//! position that does not retain it — before falling dead, so a later pass can (but is never
//! required to) reclaim its cell early instead of waiting for the collector. The QTT grades already
//! in the kernel (`blight_kernel::semiring::Grade`, spec §3) are the linguistic ancestor of this
//! idea — "used exactly once" is precisely grade `1` — but grades are erased before codegen ever
//! sees a term (`blight_kernel::erase`; the ANF `Atom`/`Comp`/`Tail` in `anf.rs` have no notion of
//! grade at all). This module re-derives an analogous "used exactly once, non-retaining" judgement
//! *structurally* over the untrusted ANF, the one place Language and Performance share a mechanism
//! without growing the kernel by a single line.
//!
//! **This module computes a query. It does not free anything.** No allocation is reclaimed early
//! anywhere in the pipeline as a result of this analysis; wiring an actual arena-clone (P5.2) or
//! in-place-reuse (P5.1) pass on top of [`is_transiently_consumed`] is future, separately-gated
//! work. Run today, this module is **inert**: [`analyze`] only classifies, and the pipeline hook
//! ([`crate::driver`]) that runs it during a real compile returns the program byte-for-byte
//! unchanged, so its presence cannot affect what any program computes (the differential matrix is
//! bit-identical *by construction*, gated by `BL_NO_LINEARITY`).
//!
//! # The judgement
//!
//! For the freshly-bound variable a `let` introduces (de Bruijn index `0` in the ANF continuation
//! that follows it — see [`is_transiently_consumed`]), we classify every syntactic occurrence in
//! that continuation as either:
//!
//! - **consuming** — a `Proj` reading a field out of it, or the scrutinee of a `Case` (a structural
//!   match reads the header/tag and hands the fields to the taken arm as fresh bindings; the
//!   scrutinized cell itself is not retained beyond the match), or
//! - **retaining** — anything else: returned (`Ret`), stored as a field of another `Con`/`Tuple`,
//!   captured by a closure (`MkClosure`) or a delay (`Now`/`Later`), passed to a call
//!   (`Call`/`CallGlobal`/`CallKnown`/`TailCall*`/`Jump`), handed to an effect/FFI boundary
//!   (`Op`/`Foreign`), captured by a handler (`Handle`), or re-bound to another name
//!   (`Comp::Atom`, an alias this analysis deliberately does not chase — see "Conservatism" below).
//!
//! A value is [`Verdict::Linear`] iff it has **exactly one** occurrence in its continuation and that
//! occurrence is consuming. Zero occurrences is [`Verdict::Dead`] (unused — not a load-bearing
//! judgement for this analysis; a later dead-code pass's problem). Two-or-more occurrences, or any
//! single retaining occurrence, is [`Verdict::Shared`] — the conservative default.
//!
//! `Case` branches are mutually exclusive at runtime (exactly one arm's body ever executes for a
//! given scrutinee), so occurrences across *different* arms are combined with [`branch_combine`]
//! (a "meet": `Shared` beats `Linear` beats `Dead`) rather than [`seq_combine`] (which would
//! wrongly double-count a value used once in each of two arms that never both run).
//!
//! # Conservatism (the soundness contract)
//!
//! This analysis is **whole-function-local** — it never looks inside a callee. Any occurrence that
//! crosses a call boundary (as an argument, a capture, an effect payload, or a handler clause) is
//! *retaining*, full stop, even though the callee might turn around and consume it linearly itself.
//! This is strictly conservative (it can under-approximate `Linear`, never over-approximate it) and
//! is exactly the "unblocks P5.2" boundary: proving cross-call linearity is the *harder*,
//! interprocedural problem P5.2 is deferred on (`docs/roadmap-post-m6.md` P5.2), not this substrate.
//!
//! Likewise, `Comp::Atom` (a pure re-binding, `let y = x in …`) is treated as *retaining* rather
//! than followed as an alias: this is simple, sound, and conservative, at the cost of missing some
//! linear values that flow through a rename before their real consuming use. A later refinement
//! could chase these aliases to recover precision; it is not required for soundness.
//!
//! # Testing
//!
//! `mod tests` below is the "unit corpus... covers the lattice" the C3 go-bar asks for: a
//! `Linear` case (single consuming use), a `Shared` case via an escaping use (the conservative
//! fallback the go-bar requires to hold), and shapes covering every retaining position, every
//! `Case`-branch combination, and the sequential double-use case.

use crate::anf::{AnfProgram, Atom, Comp, Tail};
use std::collections::HashMap;

/// The result of classifying one `let`-bound value's occurrences within its continuation.
/// See the module doc for the precise judgement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// No occurrence at all — not a target for early reclamation (nothing reads it), and not a
    /// judgement this analysis makes any promise about either way.
    Dead,
    /// Exactly one occurrence, in a non-retaining (consuming) position: a sound candidate for the
    /// caller to reclaim early once it fully executes that one occurrence.
    Linear,
    /// More than one occurrence, or a single occurrence that retains the value. The conservative
    /// default: never free early.
    Shared,
}

/// Sequential combination: `a` and `b` are two *independent, always-reached* facts about the same
/// variable (e.g. an occurrence in a `Let`'s head computation, and another in its continuation; or
/// the `Case` scrutinee and a use inside the taken arm). If both report an occurrence, that is two
/// total uses — never linear.
fn seq_combine(a: Verdict, b: Verdict) -> Verdict {
    match (a, b) {
        (Verdict::Dead, x) | (x, Verdict::Dead) => x,
        _ => Verdict::Shared,
    }
}

/// Branch combination: `a` and `b` are facts about the same variable in two *mutually exclusive*
/// `Case` arms (at runtime at most one of them ever executes). `Shared` is absorbing (a possible
/// runtime path retains the value, so no static verdict can promise otherwise); otherwise `Linear`
/// beats `Dead` (used, linearly, on whichever arm is actually taken).
fn branch_combine(a: Verdict, b: Verdict) -> Verdict {
    match (a, b) {
        (Verdict::Shared, _) | (_, Verdict::Shared) => Verdict::Shared,
        (Verdict::Linear, _) | (_, Verdict::Linear) => Verdict::Linear,
        (Verdict::Dead, Verdict::Dead) => Verdict::Dead,
    }
}

fn atom_is(target: usize, a: &Atom) -> bool {
    matches!(a, Atom::Var(i) if *i == target)
}

/// A reference to `target` found here always retains the value (see the module doc's list of
/// retaining positions).
fn atom_retaining(target: usize, a: &Atom) -> Verdict {
    if atom_is(target, a) {
        Verdict::Shared
    } else {
        Verdict::Dead
    }
}

/// A reference to `target` found here, and *only* here, fully (and only) consumes it.
fn atom_consuming(target: usize, a: &Atom) -> Verdict {
    if atom_is(target, a) {
        Verdict::Linear
    } else {
        Verdict::Dead
    }
}

fn atoms_retaining(target: usize, atoms: &[Atom]) -> Verdict {
    atoms
        .iter()
        .map(|a| atom_retaining(target, a))
        .fold(Verdict::Dead, seq_combine)
}

fn atom_opt_retaining(target: usize, a: &Option<Atom>) -> Verdict {
    a.as_ref()
        .map(|a| atom_retaining(target, a))
        .unwrap_or(Verdict::Dead)
}

/// Classify occurrences of `target` (a de Bruijn index into `comp`'s ambient scope — `comp` binds
/// no new variables itself, its atoms all refer to the scope it is evaluated in) within one `Comp`.
fn comp_use(target: usize, comp: &Comp) -> Verdict {
    match comp {
        // A pure re-binding: conservatively retaining rather than alias-chased (module doc).
        Comp::Atom(a) => atom_retaining(target, a),
        Comp::MkClosure(_, atoms, _) => atoms_retaining(target, atoms),
        Comp::Call(f, a) => seq_combine(atom_retaining(target, f), atom_retaining(target, a)),
        Comp::CallGlobal(_, a) => atom_retaining(target, a),
        Comp::CallKnown(_, env, a) => {
            seq_combine(atom_retaining(target, env), atom_retaining(target, a))
        }
        Comp::Con(_, atoms, _) => atoms_retaining(target, atoms),
        Comp::Tuple(atoms, _) => atoms_retaining(target, atoms),
        // The one consuming position: reading a field out of an aggregate does not retain the
        // aggregate itself.
        Comp::Proj(_, a) => atom_consuming(target, a),
        Comp::Now(a, _) => atom_retaining(target, a),
        Comp::Later(a, _) => atom_retaining(target, a),
        Comp::Op { arg, .. } => atom_retaining(target, arg),
        Comp::Foreign(_, arg) => atom_opt_retaining(target, arg),
        Comp::IntLit(_) | Comp::NatLit(_) | Comp::StrLit(_) => Verdict::Dead,
        Comp::IntPrim { lhs, rhs, .. } => {
            seq_combine(atom_retaining(target, lhs), atom_retaining(target, rhs))
        }
        Comp::NatPrim { lhs, rhs, .. } => {
            seq_combine(atom_retaining(target, lhs), atom_opt_retaining(target, rhs))
        }
        Comp::FloatPrim { lhs, rhs, .. } => {
            seq_combine(atom_retaining(target, lhs), atom_opt_retaining(target, rhs))
        }
    }
}

/// Classify occurrences of `target` (a de Bruijn index into `t`'s ambient scope) within a `Tail`.
/// `target` is re-based at each binder `t` introduces: `+1` per `Let`, `+ arm.binders` per `Case`
/// arm entered. `Region` introduces no binder (it only brackets a body).
fn classify(target: usize, t: &Tail) -> Verdict {
    match t {
        Tail::Ret(a) => atom_retaining(target, a),
        Tail::Let(comp, rest) => {
            let here = comp_use(target, comp);
            let there = classify(target + 1, rest);
            seq_combine(here, there)
        }
        Tail::TailCall(f, a) => {
            seq_combine(atom_retaining(target, f), atom_retaining(target, a))
        }
        // A jump re-enters the current function as its own new argument: we do not track
        // usage across loop iterations, so any flow into the new argument is conservatively
        // retaining.
        Tail::Jump(a) => atom_retaining(target, a),
        Tail::TailCallGlobal(_, a) => atom_retaining(target, a),
        Tail::TailCallKnown(_, env, a) => {
            seq_combine(atom_retaining(target, env), atom_retaining(target, a))
        }
        Tail::Case(scrut, arms) => {
            let scrut_use = atom_consuming(target, scrut);
            let arms_use = arms
                .iter()
                .map(|arm| classify(target + arm.binders, &arm.body))
                .fold(Verdict::Dead, branch_combine);
            seq_combine(scrut_use, arms_use)
        }
        // The extent of a trampolined delay is not tracked; conservatively retaining.
        Tail::Trampoline(a) => atom_retaining(target, a),
        Tail::Region(body) => classify(target, body),
        Tail::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            let mut v = seq_combine(
                atom_retaining(target, body),
                atom_retaining(target, return_clause),
            );
            for (_, clo) in op_clauses {
                v = seq_combine(v, atom_retaining(target, clo));
            }
            v
        }
    }
}

/// The core query: given the ANF continuation `rest` of a `let` that just bound a fresh value (so
/// the new value is `Atom::Var(0)` inside `rest`), is that value *transiently consumed* — used
/// exactly once, in a position that does not retain it — within `rest`?
///
/// This is the exact call shape a future arena/RC pass makes at every allocation site: given
/// `Tail::Let(Comp::Con(..) | Comp::Tuple(..) | Comp::Now(..) | Comp::Later(..), rest)`, ask
/// `is_transiently_consumed(rest)` to decide whether reclaiming that cell as soon as its one
/// consuming use finishes is sound. **Nothing in this codebase calls this to actually free memory
/// yet** — see the module doc. Exercised directly by this module's unit tests; not yet called by
/// any pipeline consumer (that is exactly the future P5.1/P5.2 work this substrate unblocks).
pub fn is_transiently_consumed(rest: &Tail) -> bool {
    matches!(classify(0, rest), Verdict::Linear)
}

/// Whole-program classification, purely for the pipeline's inert self-check and its `BL_LINEARITY_STATS`
/// diagnostic (see [`crate::driver`]): every `let`-binding in every function body and the entry,
/// classified against its own continuation. Never consulted to change codegen output.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct LinearityStats {
    pub dead: usize,
    pub linear: usize,
    pub shared: usize,
}

fn count_tail(t: &Tail, stats: &mut LinearityStats) {
    if let Tail::Let(_comp, rest) = t {
        match classify(0, rest) {
            Verdict::Dead => stats.dead += 1,
            Verdict::Linear => stats.linear += 1,
            Verdict::Shared => stats.shared += 1,
        }
        count_tail(rest, stats);
        // A `Let`'s head computation can itself contain no further `Tail` (ANF keeps `Comp`
        // flat), so there is nothing further to recurse into on the `comp` side.
        return;
    }
    match t {
        Tail::Case(_, arms) => {
            for arm in arms {
                count_tail(&arm.body, stats);
            }
        }
        Tail::Region(body) => count_tail(body, stats),
        Tail::Ret(_)
        | Tail::TailCall(_, _)
        | Tail::Jump(_)
        | Tail::TailCallGlobal(_, _)
        | Tail::TailCallKnown(_, _, _)
        | Tail::Trampoline(_)
        | Tail::Handle { .. }
        | Tail::Let(_, _) => {}
    }
}

/// Run the whole-program analysis (see [`LinearityStats`]). A diagnostic/self-check surface, not a
/// codegen decision.
pub fn analyze(prog: &AnfProgram) -> HashMap<String, LinearityStats> {
    let mut by_func = HashMap::new();
    for f in &prog.funcs {
        let mut stats = LinearityStats::default();
        count_tail(&f.body, &mut stats);
        by_func.insert(f.name.clone(), stats);
    }
    let mut entry_stats = LinearityStats::default();
    count_tail(&prog.entry, &mut entry_stats);
    by_func.insert(String::new(), entry_stats);
    by_func
}

/// The `BL_NO_LINEARITY`-gated pipeline hook (see `crate::driver`): runs [`analyze`] over the real
/// program as a self-check (it must never panic on any well-formed ANF program — a soundness
/// substrate that crashes the compiler is worse than useless) and, when `BL_LINEARITY_STATS` is
/// set, prints the per-function `Linear`/`Shared`/`Dead` counts to stderr. Returns `prog` completely
/// unchanged either way: this pass is an **identity transform** on the IR, so it is trivially
/// bit-identical whether it runs or not, satisfying the differential gate without needing to wait
/// for a real consumer (P5.1/P5.2) to exist.
pub fn analyze_gated(prog: AnfProgram) -> AnfProgram {
    if std::env::var_os("BL_NO_LINEARITY").is_some() {
        return prog;
    }
    let stats = analyze(&prog);
    if std::env::var_os("BL_LINEARITY_STATS").is_some() {
        let mut names: Vec<_> = stats.keys().cloned().collect();
        names.sort();
        for name in names {
            let s = &stats[&name];
            let label = if name.is_empty() { "<entry>" } else { name.as_str() };
            eprintln!(
                "BL_LINEARITY_STATS func={label} linear={} shared={} dead={}",
                s.linear, s.shared, s.dead
            );
        }
    }
    prog
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::anf::TailArm;
    use crate::ir::Alloc;
    use blight_kernel::ConName;

    fn con(name: &str, atoms: Vec<Atom>) -> Comp {
        Comp::Con(ConName(name.into()), atoms, Alloc::Gc)
    }

    /// `let p = Con(...) in let field = proj 0 p in Ret field` — the sole occurrence of `p` is a
    /// `Proj`, and the projected field (a fresh, unrelated binding) is what escapes, not `p` itself:
    /// proven `Linear`.
    #[test]
    fn single_use_value_proven_linear() {
        let rest = Tail::Let(
            Comp::Proj(0, Atom::Var(0)), // proj 0 p  (p is target Var(0) here)
            Box::new(Tail::Ret(Atom::Var(0))), // returns `field`, shifted to Var(0); NOT `p`
        );
        assert!(
            is_transiently_consumed(&rest),
            "a value read by exactly one Proj and never referenced again must be Linear"
        );
    }

    /// `let p = Con(...) in p` (returned) — the sole occurrence retains `p`: `Shared`, never
    /// `Linear`, no matter how few occurrences there are. This is the conservatism the go-bar
    /// requires: an unprovable (here: actively escaping) value must stay `Shared`.
    #[test]
    fn escaping_value_not_proven_linear() {
        let rest = Tail::Ret(Atom::Var(0));
        assert!(
            !is_transiently_consumed(&rest),
            "a returned (escaping) value must never be classified Linear"
        );
    }

    /// `let p = Con(...) in <dead, never referenced>` — zero occurrences is `Dead`, not `Linear`
    /// (this analysis makes no promise about unused bindings either way).
    #[test]
    fn unused_value_is_dead_not_linear() {
        let rest = Tail::Ret(Atom::Global("main".into()));
        assert!(
            !is_transiently_consumed(&rest),
            "an unreferenced binding is Dead, not Linear"
        );
        assert_eq!(classify(0, &rest), Verdict::Dead);
    }

    /// `let p = Con(...) in con "Pair" [p, p]` — used twice (as two fields of the SAME
    /// construction): two occurrences, both retaining. `Shared`.
    #[test]
    fn used_twice_in_same_construction_is_shared() {
        let rest = Tail::Let(
            con("Pair", vec![Atom::Var(0), Atom::Var(0)]),
            Box::new(Tail::Ret(Atom::Var(0))),
        );
        assert!(!is_transiently_consumed(&rest));
    }

    /// `let p = Con(...) in let a = proj 0 p in let b = proj 1 p in <a, b unused>` — `p` is
    /// projected TWICE (both fields read). Two occurrences ⇒ `Shared`, even though semantically the
    /// cell is fully drained after both projections. This is the documented conservative gap: v1
    /// only proves linearity for a *single* consuming occurrence.
    #[test]
    fn projected_twice_is_conservatively_shared() {
        let rest = Tail::Let(
            Comp::Proj(0, Atom::Var(0)), // proj 0 p  (p = Var(0) here)
            Box::new(Tail::Let(
                Comp::Proj(1, Atom::Var(1)), // proj 1 p  (p shifted to Var(1) under the new let)
                Box::new(Tail::Ret(Atom::Global("done".into()))),
            )),
        );
        assert!(
            !is_transiently_consumed(&rest),
            "two Projs of the same value is two uses, conservatively Shared"
        );
    }

    /// `let p = Con(...) in case p of [C0 () -> <p unused>] [C1 () -> <p unused>]` — the scrutinee
    /// is a consuming use with nothing else referencing `p` in either (mutually exclusive) arm:
    /// `Linear`.
    #[test]
    fn case_scrutinee_alone_is_linear() {
        let rest = Tail::Case(
            Atom::Var(0),
            vec![
                TailArm {
                    con: ConName("C0".into()),
                    binders: 0,
                    body: Tail::Ret(Atom::Global("a".into())),
                },
                TailArm {
                    con: ConName("C1".into()),
                    binders: 0,
                    body: Tail::Ret(Atom::Global("b".into())),
                },
            ],
        );
        assert!(is_transiently_consumed(&rest));
    }

    /// `let p = Con(...) in case p of [C0 () -> Ret p]` — the scrutinee is consuming, but `p` is
    /// referenced *again* inside the taken arm's body (retaining, via `Ret`): two total uses on
    /// that path. `Shared`.
    #[test]
    fn case_scrutinee_plus_arm_reference_is_shared() {
        let rest = Tail::Case(
            Atom::Var(0),
            vec![TailArm {
                con: ConName("C0".into()),
                binders: 0,
                body: Tail::Ret(Atom::Var(0)), // `p` still Var(0): C0 binds no fields
            }],
        );
        assert!(!is_transiently_consumed(&rest));
    }

    /// A value used `Linear`ly in one arm and not at all (`Dead`) in the sibling arm is still
    /// overall `Linear` — the two arms are mutually exclusive, so "linear in whichever one runs"
    /// is a sound whole-site verdict.
    #[test]
    fn linear_in_one_arm_dead_in_the_other_is_linear() {
        // `p` is target `0` on entry to `rest`. `rest` opens with an unrelated `scrutinee` binding
        // (a DIFFERENT variable than `p`, so the case arms are free to reference `p` independently
        // of the already-consumed scrutinee), which shifts `p` to index `1` inside the case:
        //   let scrutinee = ... in case scrutinee of
        //     C0 () -> let _ = proj 0 p in Ret "x"   -- p consumed exactly once here
        //     C1 () -> Ret "y"                        -- p unused here
        let rest = Tail::Let(
            Comp::Atom(Atom::Global("scrutinee".into())),
            Box::new(Tail::Case(
                Atom::Var(0), // the freshly-bound scrutinee, NOT `p` (now shifted to Var(1))
                vec![
                    TailArm {
                        con: ConName("C0".into()),
                        binders: 0,
                        body: Tail::Let(Comp::Proj(0, Atom::Var(1)), Box::new(Tail::Ret(Atom::Global("x".into())))),
                    },
                    TailArm {
                        con: ConName("C1".into()),
                        binders: 0,
                        body: Tail::Ret(Atom::Global("y".into())), // `p` unused on this path
                    },
                ],
            )),
        );
        assert!(
            is_transiently_consumed(&rest),
            "Linear in the taken arm, Dead in the other, must combine to Linear"
        );
    }

    /// A value used `Linear`ly in one arm and `Shared`ly (escaping) in the sibling arm cannot be
    /// given a single sound static verdict better than `Shared` — `Shared` is absorbing.
    #[test]
    fn linear_in_one_arm_shared_in_the_other_is_shared() {
        let rest = Tail::Let(
            Comp::Atom(Atom::Global("scrutinee".into())),
            Box::new(Tail::Case(
                Atom::Var(0),
                vec![
                    TailArm {
                        con: ConName("C0".into()),
                        binders: 0,
                        body: Tail::Let(
                            Comp::Proj(0, Atom::Var(1)),
                            Box::new(Tail::Ret(Atom::Global("x".into()))),
                        ),
                    },
                    TailArm {
                        con: ConName("C1".into()),
                        binders: 0,
                        body: Tail::Ret(Atom::Var(1)), // `p` escapes on this path
                    },
                ],
            )),
        );
        assert!(!is_transiently_consumed(&rest));
    }

    /// Every retaining position individually disqualifies linearity, even as the *sole* occurrence:
    /// `MkClosure` capture, `Con`/`Tuple` field, `Call`/`CallGlobal`/`CallKnown` argument or
    /// callee-env, `TailCall`/`TailCallGlobal`/`TailCallKnown`/`Jump`, `Now`/`Later`, `Op`,
    /// `Foreign`, and a plain re-binding (`Comp::Atom`).
    #[test]
    fn every_retaining_position_disqualifies_linearity() {
        let done = || Box::new(Tail::Ret(Atom::Global("done".into())));
        let cases: Vec<(&str, Tail)> = vec![
            (
                "MkClosure capture",
                Tail::Let(
                    Comp::MkClosure("f".into(), vec![Atom::Var(0)], Alloc::Gc),
                    done(),
                ),
            ),
            (
                "Con field",
                Tail::Let(con("Wrap", vec![Atom::Var(0)]), done()),
            ),
            (
                "Tuple field",
                Tail::Let(Comp::Tuple(vec![Atom::Var(0)], Alloc::Gc), done()),
            ),
            (
                "Call argument",
                Tail::Let(
                    Comp::Call(Atom::Global("f".into()), Atom::Var(0)),
                    done(),
                ),
            ),
            (
                "CallGlobal argument",
                Tail::Let(Comp::CallGlobal("f".into(), Atom::Var(0)), done()),
            ),
            (
                "CallKnown env",
                Tail::Let(
                    Comp::CallKnown("f".into(), Atom::Var(0), Atom::Global("a".into())),
                    done(),
                ),
            ),
            ("TailCall argument", Tail::TailCall(Atom::Global("f".into()), Atom::Var(0))),
            ("Jump argument", Tail::Jump(Atom::Var(0))),
            (
                "TailCallGlobal argument",
                Tail::TailCallGlobal("f".into(), Atom::Var(0)),
            ),
            (
                "TailCallKnown env",
                Tail::TailCallKnown("f".into(), Atom::Var(0), Atom::Global("a".into())),
            ),
            ("Now", Tail::Let(Comp::Now(Atom::Var(0), Alloc::Gc), done())),
            ("Later", Tail::Let(Comp::Later(Atom::Var(0), Alloc::Gc), done())),
            (
                "Op arg",
                Tail::Let(
                    Comp::Op {
                        effect: "State".into(),
                        op: "put".into(),
                        arg: Atom::Var(0),
                    },
                    done(),
                ),
            ),
            (
                "Foreign arg",
                Tail::Let(Comp::Foreign("f".into(), Some(Atom::Var(0))), done()),
            ),
            (
                "re-binding (Comp::Atom)",
                Tail::Let(Comp::Atom(Atom::Var(0)), done()),
            ),
            (
                "Trampoline",
                Tail::Trampoline(Atom::Var(0)),
            ),
            (
                "Handle body",
                Tail::Handle {
                    body: Atom::Var(0),
                    return_clause: Atom::Global("ret".into()),
                    op_clauses: vec![],
                },
            ),
        ];
        for (label, rest) in cases {
            assert!(
                !is_transiently_consumed(&rest),
                "{label}: a retaining occurrence must never be classified Linear"
            );
        }
    }

    /// `Region` brackets a body without shifting de Bruijn indices: a value consumed exactly once
    /// inside a region scope is still `Linear`.
    #[test]
    fn region_does_not_shift_indices() {
        let inner = Tail::Let(Comp::Proj(0, Atom::Var(0)), Box::new(Tail::Ret(Atom::Global("done".into()))));
        let rest = Tail::Region(Box::new(inner));
        assert!(is_transiently_consumed(&rest));
    }

    /// The whole-program [`analyze`] entry point must never panic on a small realistic program and
    /// must produce counts consistent with hand-verified expectations — the "self-check can't crash
    /// the compiler" contract [`analyze_gated`] leans on.
    #[test]
    fn analyze_counts_a_small_program_without_panicking() {
        // entry = let p = Con("Pair", []) in proj 0 p  (one Linear binding)
        let entry = Tail::Let(
            con("Pair", vec![]),
            Box::new(Tail::Let(
                Comp::Proj(0, Atom::Var(0)),
                Box::new(Tail::Ret(Atom::Var(0))), // the projected field escapes: this 2nd let is Shared
            )),
        );
        let prog = AnfProgram {
            funcs: vec![],
            entry,
            con_tags: Default::default(),
        };
        let stats = analyze(&prog);
        let entry_stats = stats.get("").expect("entry stats recorded");
        assert_eq!(entry_stats.linear, 1, "the Pair binding is Linear (proj'd once, no other use)");
        assert_eq!(entry_stats.shared, 1, "the projected field binding escapes via Ret: Shared");
        assert_eq!(entry_stats.dead, 0);
    }

    /// [`analyze_gated`] is the identity on the IR (it only ever classifies + optionally logs),
    /// with or without `BL_NO_LINEARITY` set — the differential-invisibility contract.
    #[test]
    fn analyze_gated_is_always_identity_on_the_program() {
        let entry = Tail::Let(con("Leaf", vec![]), Box::new(Tail::Ret(Atom::Var(0))));
        let prog = AnfProgram {
            funcs: vec![],
            entry,
            con_tags: Default::default(),
        };
        let with_analysis = analyze_gated(prog.clone());
        assert_eq!(with_analysis, prog, "analyze_gated must not alter the program");

        // SAFETY (test-only): scoped to this process's test thread; no other test in this crate
        // reads/writes BL_NO_LINEARITY concurrently within the same test binary run serially by
        // default, and we restore it immediately after.
        let prior = std::env::var_os("BL_NO_LINEARITY");
        unsafe {
            std::env::set_var("BL_NO_LINEARITY", "1");
        }
        let gated_off = analyze_gated(prog.clone());
        match prior {
            Some(v) => unsafe { std::env::set_var("BL_NO_LINEARITY", v) },
            None => unsafe { std::env::remove_var("BL_NO_LINEARITY") },
        }
        assert_eq!(gated_off, prog, "BL_NO_LINEARITY must also leave the program untouched (it's a no-op path)");
    }
}
