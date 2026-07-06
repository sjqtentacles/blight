//! P6.1 — common-subexpression elimination / value numbering over `Cir`.
//!
//! When the same *pure* computation is built more than once in the same straight-line, eagerly
//! evaluated region of a body, this pass binds it to a single `let` and shares the result, so the
//! work (and any allocation it performs) happens once. Classic shape:
//! ```text
//!   (f x) + (f x)        =>   let t = f x in t + t
//!   (mk a) , (mk a)      =>   let t = mk a in (t, t)
//! ```
//! It is a pure backend *representation* optimization: the kernel and re-checker only ever see the
//! un-shared inductive term, the result is observationally identical, and it is gated by `BL_NO_CSE`
//! and wired into the B1 differential A/B matrix (DIFF_FLAGS) as the bit-identity safety net.
//!
//! ## Soundness (why sharing is observationally invisible)
//! Sharing a subterm `s` between two occurrences changes *when/how often* `s` is evaluated, so it is
//! only safe when that is unobservable. We fire only when **both** of these hold:
//!   1. **`s` is pure** — it contains no effect node (`Op`/`Handle`/`Force`/`Foreign`). A `perform`,
//!      a handler, a delay `force`, or an opaque FFI call could each run a side effect (or diverge
//!      under a handler) a *different number of times* if shared, so they are never deduplicated.
//!   2. **the hoist region is effect-free** — `s`'s occurrences live in a maximal region of the node
//!      reached only through *unconditional, eager, binder-free* positions (an application's
//!      operands, a constructor/tuple's fields, a primitive's operands, a `let`'s bound expression,
//!      a `case`'s scrutinee, …) and that region contains no effect node. This is exactly the set of
//!      positions evaluated, in full, before the node yields — so binding `s` to a leading `let`
//!      evaluates it *exactly when it would have been* and reorders it only against other pure work.
//!      We never cross a binder (a `λ`/`fix`/`later`, nor a `case` arm or `let` body): those delay or
//!      conditionalize evaluation, so a syntactically-equal subterm under one is a *different* value
//!      (different de Bruijn scope) and must not be shared.
//!
//! Under both conditions, sharing preserves the value, the set of effects (none are moved across),
//! and termination (a diverging pure `s` diverges in either order, before any later effect runs).
//!
//! ## Placement
//! Runs after [`crate::unbox`]/[`crate::flatten`] and before [`crate::region`]/[`crate::closure`],
//! on the de Bruijn `Cir`. Allocations are still all `Alloc::Gc` here (region analysis has not run),
//! so a shared `let` binding is a plain heap value the later passes handle unchanged.

use crate::ir::{Arm, Cir};
use crate::lower::shift_free;

/// Run CSE over a whole pre-closure-conversion `Cir` term.
pub fn cse(c: &Cir) -> Cir {
    // Top-down: share repeated pure subterms in *this* node's own eager region first, then recurse
    // into every child for the deeper (under-binder) scopes. Order matters for correctness: doing
    // children first would let a parent's region descend into a `let` we just introduced in a child
    // and re-count its bound value — re-hoisting an already-shared subterm and compounding nested
    // `let`s. Hoisting the outer region before any inner `let` exists avoids that entirely.
    let hoisted = if region_effect_free(c) {
        local_hoist(c)
    } else {
        c.clone()
    };
    map_children(&hoisted, cse)
}

/// Hoist the most valuable repeated pure subterm of `c`'s eager region into a leading `let`, then
/// recurse on the rewritten body to share any further repeats. Caller guarantees the region is
/// effect-free, which the rewrite preserves (it only ever replaces a pure subterm with a variable).
fn local_hoist(c: &Cir) -> Cir {
    match best_candidate(c) {
        None => c.clone(),
        Some(cand) => {
            // Insert one binder in front of `c`: every free variable of `c` shifts up by one, and
            // every region occurrence of `cand` becomes the new binding (de Bruijn 0). `cand` itself
            // lives at `c`'s *outer* depth (it crosses no binder), so it is the `let`'s bound value
            // unshifted.
            let shifted_node = shift_free(c, 1);
            let shifted_cand = shift_free(&cand, 1);
            let body = replace_region(&shifted_node, &shifted_cand);
            let body = local_hoist(&body);
            Cir::Let(Box::new(cand), Box::new(body))
        }
    }
}

/// The pure, beneficial subterm that repeats most-valuably in `c`'s eager region: among subterms
/// that occur at least twice, the structurally largest (sharing it subsumes any repeats nested
/// inside it). `None` when nothing pure repeats.
fn best_candidate(c: &Cir) -> Option<Cir> {
    let mut counts: Vec<(Cir, usize)> = Vec::new();
    collect_region(c, &mut |sub| {
        if !is_candidate(sub) {
            return;
        }
        if let Some(entry) = counts.iter_mut().find(|(k, _)| k == sub) {
            entry.1 += 1;
        } else {
            counts.push((sub.clone(), 1));
        }
    });
    counts
        .into_iter()
        .filter(|(_, n)| *n >= 2)
        .max_by_key(|(k, _)| size(k))
        .map(|(k, _)| k)
}

/// Is `c` worth sharing (it allocates or computes), pure (safe to share), and *not* a job that
/// belongs to another pass?
///
/// Excluded:
///   * trivial atoms (`Var`/`Global`/`EnvRef`/literals/`Erased`) — binding them saves no work;
///   * the delay wrappers `Now`/`Later` — the trampoline substrate, cheap, best left untouched;
///   * **β-redexes / partial applications** — an application whose spine head is a `Lam`/`Fix`.
///     Pre-closure the program is full of `App(Lam, …)` redexes the inliner/monomorphizer will
///     β-reduce and specialize; pre-binding one to a shared `let` both fights that and, when the
///     application is *under-saturated*, manufactures a closure that never existed (and may capture
///     a grade-`0` `Erased` argument as a runtime value) — exactly the shape that mis-runs. Sharing
///     is for genuine *values* (allocations, primitives, calls to a function *value*), not redexes;
///   * anything containing `Erased` — a grade-`0` poison placeholder that must never be reified.
fn is_candidate(c: &Cir) -> bool {
    let beneficial = match c {
        // A call is shareable only when its head is a real function *value*, not a `Lam`/`Fix`
        // awaiting β-reduction by the inliner.
        Cir::App(..) => {
            let (head, _) = c.unapply();
            !matches!(head, Cir::Lam(_) | Cir::Fix(_))
        }
        Cir::CallClosure(f, _) => !matches!(f.as_ref(), Cir::Lam(_) | Cir::Fix(_)),
        Cir::Con(..)
        | Cir::Tuple(..)
        | Cir::Flat { .. }
        | Cir::Proj(..)
        | Cir::FlatProj { .. }
        | Cir::IntPrim { .. }
        | Cir::NatPrim { .. }
        | Cir::FloatPrim { .. }
        | Cir::MkClosure(..) => true,
        _ => false,
    };
    beneficial && is_pure(c) && !contains_erased(c)
}

/// Does `c` mention the grade-`0` poison placeholder [`Cir::Erased`] anywhere? Such a term is only
/// well-defined in a position a later pass deletes; it must never be hoisted into a value binding.
fn contains_erased(c: &Cir) -> bool {
    if matches!(c, Cir::Erased) {
        return true;
    }
    let mut found = false;
    for_each_child(c, &mut |child| {
        if !found {
            found = contains_erased(child);
        }
    });
    found
}

/// Does `c` contain *no* effect node anywhere (`Op`/`Handle`/`Force`/`Foreign`)? Only such terms may
/// be shared: an effect performed/forced a different number of times is observable.
fn is_pure(c: &Cir) -> bool {
    if is_effect_node(c) {
        return false;
    }
    let mut pure = true;
    for_each_child(c, &mut |child| {
        if pure {
            pure = is_pure(child);
        }
    });
    pure
}

/// A node whose evaluation can run a side effect (or diverge under a handler): never shared, and a
/// boundary for the hoist region.
fn is_effect_node(c: &Cir) -> bool {
    matches!(
        c,
        Cir::Op { .. } | Cir::Handle { .. } | Cir::Force(_) | Cir::Foreign(..)
    )
}

/// Is `c`'s eager region (the unconditional, binder-free positions reached from `c`) free of effect
/// nodes? If so, hoisting a pure subterm to a leading `let` cannot reorder it across an effect.
fn region_effect_free(c: &Cir) -> bool {
    for child in region_children(c) {
        if is_effect_node(child) || !region_effect_free(child) {
            return false;
        }
    }
    true
}

/// The immediate sub-positions of `c` that are evaluated **unconditionally, eagerly, and under no
/// new binder** — the same depth as `c`. These define the hoist region (collection + replacement
/// both walk exactly this structure). A `let` exposes only its bound expression (the body is under a
/// binder); a `case` only its scrutinee (the arms are under binders); `λ`/`fix`/`later` and the
/// effect/flattened nodes are boundaries and contribute nothing.
fn region_children(c: &Cir) -> Vec<&Cir> {
    match c {
        Cir::App(f, a) | Cir::CallClosure(f, a) => vec![f, a],
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().collect()
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Region(e) => vec![e],
        Cir::IntPrim { lhs, rhs, .. } => vec![lhs, rhs],
        Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
            let mut v: Vec<&Cir> = vec![lhs];
            if let Some(r) = rhs {
                v.push(r);
            }
            v
        }
        // A binder gates the body/arms out of the region; only the pre-binder slot stays.
        Cir::Let(v, _body) => vec![v],
        Cir::Case(s, _arms) => vec![s],
        _ => vec![],
    }
}

/// Visit every region subterm of `c` (its [`region_children`], transitively).
fn collect_region(c: &Cir, visit: &mut impl FnMut(&Cir)) {
    for child in region_children(c) {
        visit(child);
        collect_region(child, visit);
    }
}

/// Replace every region occurrence of `target` in `c` with de Bruijn 0 (the freshly inserted `let`
/// binder). Mirrors [`region_children`] exactly: descends only through region positions and leaves
/// everything under a binder untouched. A matched subterm is replaced whole (we do not descend into
/// it), so the largest chosen candidate subsumes any repeats nested inside it.
fn replace_region(c: &Cir, target: &Cir) -> Cir {
    if c == target {
        return Cir::Var(0);
    }
    let rep = |x: &Cir| replace_region(x, target);
    match c {
        Cir::App(f, a) => Cir::App(Box::new(rep(f)), Box::new(rep(a))),
        Cir::CallClosure(f, a) => Cir::CallClosure(Box::new(rep(f)), Box::new(rep(a))),
        Cir::Con(n, args, al) => Cir::Con(n.clone(), args.iter().map(rep).collect(), *al),
        Cir::Tuple(args, al) => Cir::Tuple(args.iter().map(rep).collect(), *al),
        Cir::MkClosure(n, env, al) => Cir::MkClosure(n.clone(), env.iter().map(rep).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(rep(e))),
        Cir::Now(e, al) => Cir::Now(Box::new(rep(e)), *al),
        Cir::Region(e) => Cir::Region(Box::new(rep(e))),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(rep(lhs)),
            rhs: Box::new(rep(rhs)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(rep(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(rep(r))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(rep(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(rep(r))),
        },
        // Only the bound expression / scrutinee is in the region; the binder-introducing parts are
        // copied verbatim (their de Bruijn scope differs, so an equal-looking subterm there is a
        // different value).
        Cir::Let(v, body) => Cir::Let(Box::new(rep(v)), body.clone()),
        Cir::Case(s, arms) => Cir::Case(Box::new(rep(s)), arms.clone()),
        _ => c.clone(),
    }
}

/// Structural node count (used to prefer the largest repeated candidate).
fn size(c: &Cir) -> usize {
    let mut n = 1usize;
    for_each_child(c, &mut |child| n += size(child));
    n
}

/// Visit every immediate `Cir` child of `c` (no de Bruijn tracking; for structural predicates).
fn for_each_child(c: &Cir, f: &mut impl FnMut(&Cir)) {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => {}
        Cir::Foreign(_, arg) => {
            if let Some(a) = arg {
                f(a);
            }
        }
        Cir::Lam(b) | Cir::Fix(b) => f(b),
        Cir::App(a, b) | Cir::Let(a, b) | Cir::CallClosure(a, b) => {
            f(a);
            f(b);
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            for a in args {
                f(a);
            }
        }
        Cir::Case(s, arms) => {
            f(s);
            for arm in arms {
                f(&arm.body);
            }
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            f(e)
        }
        Cir::Op { arg, .. } => f(arg),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            f(body);
            f(return_clause);
            for (_, e) in op_clauses {
                f(e);
            }
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => {
            f(scrut);
            f(then_);
            f(else_);
        }
        Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
            f(lhs);
            if let Some(r) = rhs {
                f(r);
            }
        }
        Cir::Flat { fields, .. } => {
            for fl in fields {
                fl.any_cir(|x| {
                    f(x);
                    false
                });
            }
        }
        Cir::FlatProj { layout, scrut, .. } => {
            f(scrut);
            for fl in layout {
                fl.any_cir(|x| {
                    f(x);
                    false
                });
            }
        }
    }
}

/// Structural map applying `f` to every immediate child, preserving binders (each child is rewritten
/// in its own scope; `f` — here `cse` — works relative to each child's own depth 0).
fn map_children(c: &Cir, f: fn(&Cir) -> Cir) -> Cir {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(sym.clone(), arg.as_ref().map(|a| Box::new(f(a)))),
        Cir::Lam(b) => Cir::Lam(Box::new(f(b))),
        Cir::Fix(b) => Cir::Fix(Box::new(f(b))),
        Cir::App(g, a) => Cir::App(Box::new(f(g)), Box::new(f(a))),
        Cir::Let(v, b) => Cir::Let(Box::new(f(v)), Box::new(f(b))),
        Cir::Con(name, args, al) => Cir::Con(name.clone(), args.iter().map(&f).collect(), *al),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(f(s)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: f(&arm.body),
                })
                .collect(),
        ),
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(&f).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(f(e))),
        Cir::Now(e, al) => Cir::Now(Box::new(f(e)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(f(e)), *al),
        Cir::Force(e) => Cir::Force(Box::new(f(e))),
        Cir::Region(e) => Cir::Region(Box::new(f(e))),
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
        Cir::MkClosure(name, env, al) => {
            Cir::MkClosure(name.clone(), env.iter().map(&f).collect(), *al)
        }
        Cir::CallClosure(g, a) => Cir::CallClosure(Box::new(f(g)), Box::new(f(a))),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: Box::new(f(rhs)),
        },
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => Cir::IfZero {
            scrut: Box::new(f(scrut)),
            then_: Box::new(f(then_)),
            else_: Box::new(f(else_)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(f(r))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(f(r))),
        },
        Cir::Flat {
            tag,
            fields,
            total_slots,
            alloc,
        } => Cir::Flat {
            tag: tag.clone(),
            fields: fields.iter().map(|fl| fl.map_cir(f)).collect(),
            total_slots: *total_slots,
            alloc: *alloc,
        },
        Cir::FlatProj {
            index,
            layout,
            scrut,
        } => Cir::FlatProj {
            index: *index,
            layout: layout.iter().map(|fl| fl.map_cir(f)).collect(),
            scrut: Box::new(f(scrut)),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Alloc;
    use blight_kernel::{ConName, IntPrimOp};

    fn app(f: Cir, a: Cir) -> Cir {
        Cir::App(Box::new(f), Box::new(a))
    }
    fn add(lhs: Cir, rhs: Cir) -> Cir {
        Cir::IntPrim {
            op: IntPrimOp::Add,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }
    fn con(name: &str, args: Vec<Cir>) -> Cir {
        Cir::Con(ConName(name.into()), args, Alloc::Gc)
    }

    /// A repeated pure application `(f x) + (f x)` collapses to one shared `let`, with the de Bruijn
    /// indices preserved: the bound value references the *outer* `x`, and both operands become the
    /// new binding (index 0).
    #[test]
    fn shares_repeated_pure_application() {
        let fx = app(Cir::Global("f".into()), Cir::Var(0));
        let node = add(fx.clone(), fx.clone());
        let got = cse(&node);
        let expected = Cir::Let(
            Box::new(app(Cir::Global("f".into()), Cir::Var(0))),
            Box::new(add(Cir::Var(0), Cir::Var(0))),
        );
        assert_eq!(got, expected);
    }

    /// A repeated pure allocation `(C x, C x)` is built once and shared (one fewer allocation).
    #[test]
    fn shares_repeated_allocation() {
        let cx = con("C", vec![Cir::Var(0)]);
        let node = Cir::Tuple(vec![cx.clone(), cx.clone()], Alloc::Gc);
        let got = cse(&node);
        let expected = Cir::Let(
            Box::new(con("C", vec![Cir::Var(0)])),
            Box::new(Cir::Tuple(vec![Cir::Var(0), Cir::Var(0)], Alloc::Gc)),
        );
        assert_eq!(got, expected);
    }

    /// Counter-test: an effectful subterm is **never** deduplicated. `force e` (and likewise
    /// `perform`/`handle`) repeated stays repeated, because sharing it would force/run it a
    /// different number of times.
    #[test]
    fn never_dedups_force() {
        let forced = Cir::Force(Box::new(app(Cir::Global("g".into()), Cir::Var(0))));
        let node = add(forced.clone(), forced.clone());
        let got = cse(&node);
        // The repeated `force` survives verbatim — but the *pure* `g x` inside each `force` is not
        // hoisted across the effect boundary either (only one occurrence is visible per region).
        assert_eq!(got, node);
    }

    /// Counter-test: a repeated `perform` is never shared.
    #[test]
    fn never_dedups_op() {
        let op = Cir::Op {
            effect: "Console".into(),
            op: "print".into(),
            arg: Box::new(Cir::Var(0)),
        };
        let node = add(op.clone(), op.clone());
        assert_eq!(cse(&node), node);
    }

    /// A trivial atom (a bare variable) is not hoisted: binding it saves no work.
    #[test]
    fn does_not_hoist_trivial_atom() {
        let node = add(Cir::Var(0), Cir::Var(0));
        assert_eq!(cse(&node), node);
    }

    /// A subterm that occurs only once is left alone.
    #[test]
    fn single_occurrence_untouched() {
        let node = add(app(Cir::Global("f".into()), Cir::Var(0)), Cir::Var(1));
        assert_eq!(cse(&node), node);
    }

    /// Sharing never crosses a `case` binder: the same syntactic `(f y)` in two arms is a *different*
    /// value (each arm binds its own locals), and the arms are conditional, so it must not be hoisted
    /// out of the `case`.
    #[test]
    fn does_not_hoist_across_case_arms() {
        let arm_body = app(Cir::Global("f".into()), Cir::Var(1));
        let node = Cir::Case(
            Box::new(Cir::Var(0)),
            vec![
                Arm {
                    con: ConName("A".into()),
                    binders: 2,
                    body: arm_body.clone(),
                },
                Arm {
                    con: ConName("B".into()),
                    binders: 2,
                    body: arm_body.clone(),
                },
            ],
        );
        assert_eq!(cse(&node), node);
    }

    /// Sharing under a binder still works *within* that binder's scope: a repeat inside one `case`
    /// arm is shared, and the bound value's free index is the arm-local one (de Bruijn correctness
    /// under the recursion into arm bodies).
    #[test]
    fn shares_within_a_single_scope() {
        let fy = app(Cir::Global("f".into()), Cir::Var(1));
        let arm_body = add(fy.clone(), fy.clone());
        let node = Cir::Case(
            Box::new(Cir::Var(0)),
            vec![Arm {
                con: ConName("A".into()),
                binders: 2,
                body: arm_body,
            }],
        );
        let got = cse(&node);
        let expected = Cir::Case(
            Box::new(Cir::Var(0)),
            vec![Arm {
                con: ConName("A".into()),
                binders: 2,
                body: Cir::Let(
                    Box::new(app(Cir::Global("f".into()), Cir::Var(1))),
                    Box::new(add(Cir::Var(0), Cir::Var(0))),
                ),
            }],
        );
        assert_eq!(got, expected);
    }
}
