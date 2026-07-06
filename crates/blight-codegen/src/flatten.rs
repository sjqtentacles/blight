//! A1 — escaping-product flattening (the M27 sibling for products that *do* escape).
//!
//! [`crate::unbox`] (SRA) only ever *deletes* a product that is built and immediately consumed in
//! place. A product that escapes — returned, stored in another record, passed to a call — survives
//! as a heap object, and if one of its fields is itself a small product the result is a *chain of
//! allocations and pointer indirections* (`treesum`'s `Pair (Pair a b) c`, the lexer's nested
//! state records). This pass inlines a fixed-arity, pure, never-matched child product's slots
//! directly into its escaping parent ([`Cir::Flat`]), so the pair becomes **one** wider object and
//! a `parent.outer.inner` read becomes **one** load at a computed offset instead of two.
//!
//! ## Soundness (why this is bit-identical, the M27-revert lesson)
//! Flattening changes the runtime *representation* of a product, never its meaning, and only when
//! the change is unobservable. We fire only when ALL hold for a child field of a freshly-built
//! parent product:
//!   1. the child is a **literal** product built inline (`Con`/`Tuple` node in argument position),
//!      with a statically-known arity;
//!   2. the child constructor is **never `case`-matched** anywhere — flattening erases the child's
//!      own object (and thus its tag), so a `Case` on it could not dispatch. We approximate this by
//!      requiring the child to be a *tuple* or a *single-constructor* product whose only consumers
//!      in the program are projections (conservative: any `Case` on the child's con name vetoes);
//!   3. the parent does not escape into a context that inspects its physical layout other than
//!      through `Proj` (the GC sees a uniform all-pointer object either way — A1d — so escape is
//!      fine; only a `Case` that assumes the *un*-flattened field count would break, which (2)
//!      rules out).
//!
//! Because every flattened slot is still a `BlValue` pointer, the precise GC tracer's uniform
//! `nfields`-pointer walk handles the wider object with **no tracer change**.
//!
//! ## Gate & status
//! Gated by `BL_NO_FLATTEN` (the B1 differential corpus A/B is the safety net) and wired into the
//! differential matrix. **Status: proven-safe substrate, does not yet fire.** The conservative
//! rewrite below is *strictly subsumed by M27 [`crate::unbox`]*: the only shape it can prove safe
//! locally — a `let`-bound literal product all of whose uses are projection chains — is exactly what
//! unbox already handles *better*, by deleting the allocation outright (a `Proj`-chain counts as an
//! in-place destructure, so unbox substitutes the literal and the chain constant-folds). The genuine
//! win is the *escaping* case (a nested product returned from a recursive function / passed to a
//! call), but there the parent's physical layout must agree with **every** reader — including readers
//! in other functions this local pass cannot see — so making it bit-identical is a **whole-program,
//! post-monomorphization layout-assignment** problem (the documented A1′ follow-up). This file lands
//! the *proven* IR/analysis/lowering substrate and the differential gate so that future global pass
//! is already safety-netted; see `docs/roadmap-post-m6.md` (A1) for the full disposition.

use crate::ir::{Alloc, Arm, Cir, FlatField};
use blight_kernel::ConName;

/// Run the flattening pass over a whole pre-closure-conversion `Cir` term.
pub fn flatten(c: &Cir) -> Cir {
    rewrite(c)
}

/// Bottom-up rewrite: flatten children first (so an inner flatten exposes a parent opportunity),
/// then attempt to flatten a `let`-bound escaping product at this node.
fn rewrite(c: &Cir) -> Cir {
    let rebuilt = map_children(c, rewrite);
    match &rebuilt {
        // The one shape we flatten: `let p = <parent product> in body`, where the parent product is
        // a pure literal `Con`/`Tuple` with at least one *flattenable nested field* (itself a pure
        // literal product), and **every** free use of `p` (de Bruijn 0) in `body` is a projection
        // chain that drills all the way through the `Nested` layers to a `Leaf`. That guard is the
        // soundness contract: it means the nested sub-products are *never observed as whole values*
        // and `p` is never `case`-matched or passed somewhere that reads it with the un-flattened
        // layout — so splicing their slots into the parent (`Cir::Flat`) and rewriting each chain to
        // one `FlatProj` at the computed physical offset is unobservable. (A future widening can
        // admit whole-parent escape once all readers agree on the flat layout; this first cut stays
        // local-and-provable, the M27-revert discipline.)
        Cir::Let(v, body) => {
            if let Some(layout) = flattenable_layout(v) {
                if uses_only_drill_to_leaf(body, 0, &layout) {
                    let flat = build_flat(v, &layout);
                    let new_body = rewrite_projections(body, 0, &layout);
                    return Cir::Let(Box::new(flat), Box::new(new_body));
                }
            }
            rebuilt
        }
        _ => rebuilt,
    }
}

/// A *flattenable* parent product is a pure literal `Con`/`Tuple` at least one of whose fields is
/// itself a pure literal product. Returns the per-logical-field layout (a `Leaf` for a scalar field,
/// a `Nested` carrying the inlined child slots for a flattened sub-product). `None` if the node is
/// not a product, is impure, or has no nested product to inline (so flattening would be a no-op).
fn flattenable_layout(v: &Cir) -> Option<Vec<FlatField>> {
    let (_, fields) = product_parts(v)?;
    if !fields.iter().all(is_pure_value) {
        return None;
    }
    let mut any_nested = false;
    let layout: Vec<FlatField> = fields
        .iter()
        .map(|f| match nested_layout(f) {
            Some(field) => {
                any_nested = true;
                field
            }
            None => FlatField::Leaf(Box::new(f.clone())),
        })
        .collect();
    if any_nested {
        Some(layout)
    } else {
        None
    }
}

/// If `f` is itself a pure literal product, describe it as an inlined `Nested` field (recursively
/// flattening *its* nested children too). Otherwise `None` (it stays a `Leaf`).
fn nested_layout(f: &Cir) -> Option<FlatField> {
    let (tag, fields) = product_parts(f)?;
    if !fields.iter().all(is_pure_value) {
        return None;
    }
    let slots = fields
        .iter()
        .map(|c| nested_layout(c).unwrap_or_else(|| FlatField::Leaf(Box::new(c.clone()))))
        .collect();
    Some(FlatField::Nested { tag, slots })
}

/// Decompose a product node into `(tag, fields)` — `Some(con)` for a `Con`, `None` for a `Tuple`.
fn product_parts(c: &Cir) -> Option<(Option<ConName>, &[Cir])> {
    match c {
        Cir::Con(name, fields, _) => Some((Some(name.clone()), fields)),
        Cir::Tuple(fields, _) => Some((None, fields)),
        _ => None,
    }
}

/// The parent product's allocation tag (`Alloc`), defaulting to `Gc`.
fn product_alloc(c: &Cir) -> Alloc {
    match c {
        Cir::Con(_, _, al) | Cir::Tuple(_, al) => *al,
        _ => Alloc::Gc,
    }
}

/// Build the flattened `Cir::Flat` for a parent product `v` under the computed `layout`.
fn build_flat(v: &Cir, layout: &[FlatField]) -> Cir {
    let (tag, _) = product_parts(v).expect("build_flat on a non-product");
    let total_slots = layout.iter().map(FlatField::width).sum();
    Cir::Flat {
        tag,
        fields: layout.to_vec(),
        total_slots,
        alloc: product_alloc(v),
    }
}

/// Is `c` exactly the de Bruijn variable `k`?
fn is_var(c: &Cir, k: usize) -> bool {
    matches!(c, Cir::Var(j) if *j == k)
}

/// Same settled-pure-value predicate as [`crate::unbox`]: a variable/global/env-ref/literal is
/// already evaluated, a `Lam`/`MkClosure` is a value, a `Tuple`/`Con` is pure iff every field is.
/// Everything else may perform an effect or its elimination is load-bearing.
fn is_pure_value(c: &Cir) -> bool {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_)
        | Cir::Lam(_)
        | Cir::MkClosure(..) => true,
        Cir::Tuple(fields, _) | Cir::Con(_, fields, _) => fields.iter().all(is_pure_value),
        _ => false,
    }
}

/// Peel a maximal projection chain rooted at `Var k`. `Proj(i_m, … Proj(i_0, Var k))` yields the
/// index list `[i_0, …, i_m]` (outermost-product field first). Returns `None` if `c` is not such a
/// chain (its innermost operand is not `Var k`). The returned `Cir` ref is the chain's outermost
/// `Proj` so the caller knows the whole node was consumed.
fn peel_chain(c: &Cir, k: usize) -> Option<Vec<usize>> {
    match c {
        Cir::Proj(i, e) => {
            if is_var(e, k) {
                Some(vec![*i])
            } else {
                let mut inner = peel_chain(e, k)?;
                inner.push(*i);
                Some(inner)
            }
        }
        _ => None,
    }
}

/// Walk a chain of logical indices through `layout`, returning the *physical leaf slot offset* if and
/// only if the chain drills exactly to a `Leaf`. `None` if the chain stops on a `Nested` (reads a
/// whole sub-product — not allowed in this first cut) or runs off the end / off a leaf.
fn resolve_chain(layout: &[FlatField], chain: &[usize]) -> Option<usize> {
    let (&first, rest) = chain.split_first()?;
    if first >= layout.len() {
        return None;
    }
    // Physical base = total width of all logical fields before `first`.
    let base: usize = layout[..first].iter().map(FlatField::width).sum();
    match &layout[first] {
        FlatField::Leaf(_) => {
            // A leaf must be the end of the chain.
            if rest.is_empty() {
                Some(base)
            } else {
                None
            }
        }
        FlatField::Nested { slots, .. } => {
            // Must continue descending into the nested slots.
            if rest.is_empty() {
                None
            } else {
                resolve_chain(slots, rest).map(|inner| base + inner)
            }
        }
    }
}

/// Does **every** free occurrence of de Bruijn `k` in `c` appear only as the root of a projection
/// chain that [`resolve_chain`] accepts (drills through the flattened layers to a leaf)? A bare
/// `Var k`, a `Case` on `k`, or a chain that stops on a nested sub-product all return `false`.
fn uses_only_drill_to_leaf(c: &Cir, k: usize, layout: &[FlatField]) -> bool {
    match c {
        // A projection whose innermost operand is `Var k`: it must be an accepted full chain.
        Cir::Proj(_, _) => {
            if let Some(chain) = peel_chain(c, k) {
                resolve_chain(layout, &chain).is_some()
            } else {
                // Not rooted at `k`; recurse into the projected expression normally.
                if let Cir::Proj(_, e) = c {
                    uses_only_drill_to_leaf(e, k, layout)
                } else {
                    unreachable!()
                }
            }
        }
        // Any bare occurrence of `k` elsewhere escapes / is observed whole: decline.
        Cir::Var(j) => *j != k,
        Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => true,
        Cir::Foreign(_, arg) => arg
            .as_ref()
            .map(|a| uses_only_drill_to_leaf(a, k, layout))
            .unwrap_or(true),
        Cir::Lam(b) | Cir::Fix(b) => uses_only_drill_to_leaf(b, k + 1, layout),
        Cir::App(g, a) | Cir::CallClosure(g, a) => {
            uses_only_drill_to_leaf(g, k, layout) && uses_only_drill_to_leaf(a, k, layout)
        }
        Cir::Let(v, b) => {
            uses_only_drill_to_leaf(v, k, layout) && uses_only_drill_to_leaf(b, k + 1, layout)
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().all(|a| uses_only_drill_to_leaf(a, k, layout))
        }
        Cir::Case(s, arms) => {
            uses_only_drill_to_leaf(s, k, layout)
                && arms
                    .iter()
                    .all(|arm| uses_only_drill_to_leaf(&arm.body, k + arm.binders, layout))
        }
        Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            uses_only_drill_to_leaf(e, k, layout)
        }
        Cir::Op { arg, .. } => uses_only_drill_to_leaf(arg, k, layout),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            uses_only_drill_to_leaf(body, k, layout)
                && uses_only_drill_to_leaf(return_clause, k + 1, layout)
                && op_clauses
                    .iter()
                    .all(|(_, e)| uses_only_drill_to_leaf(e, k + 2, layout))
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            uses_only_drill_to_leaf(lhs, k, layout) && uses_only_drill_to_leaf(rhs, k, layout)
        }
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => {
            uses_only_drill_to_leaf(scrut, k, layout)
                && uses_only_drill_to_leaf(then_, k, layout)
                && uses_only_drill_to_leaf(else_, k, layout)
        }
        Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
            uses_only_drill_to_leaf(lhs, k, layout)
                && rhs
                    .as_ref()
                    .map(|r| uses_only_drill_to_leaf(r, k, layout))
                    .unwrap_or(true)
        }
        Cir::Flat { fields, .. } => fields.iter().all(|fl| flatfield_uses_drill(fl, k, layout)),
        Cir::FlatProj {
            layout: l, scrut, ..
        } => {
            l.iter().all(|fl| flatfield_uses_drill(fl, k, layout))
                && uses_only_drill_to_leaf(scrut, k, layout)
        }
    }
}

/// Recurse [`uses_only_drill_to_leaf`] into the `Cir` leaves embedded in an already-flattened field
/// (so the analysis is total even on idempotent re-runs).
fn flatfield_uses_drill(f: &FlatField, k: usize, layout: &[FlatField]) -> bool {
    match f {
        FlatField::Leaf(c) => uses_only_drill_to_leaf(c, k, layout),
        FlatField::Nested { slots, .. } => slots.iter().all(|s| flatfield_uses_drill(s, k, layout)),
    }
}

/// Rewrite every projection chain rooted at de Bruijn `k` into a single [`Cir::FlatProj`] at the
/// chain's resolved physical leaf offset, threading `k` correctly under binders. Assumes
/// [`uses_only_drill_to_leaf`] already validated `c` (so every chain resolves).
fn rewrite_projections(c: &Cir, k: usize, layout: &[FlatField]) -> Cir {
    match c {
        Cir::Proj(i, e) => {
            if let Some(chain) = peel_chain(c, k) {
                let offset = resolve_chain(layout, &chain)
                    .expect("uses_only_drill_to_leaf guaranteed a resolvable chain");
                Cir::FlatProj {
                    index: offset,
                    layout: layout.to_vec(),
                    scrut: Box::new(Cir::Var(k)),
                }
            } else {
                Cir::Proj(*i, Box::new(rewrite_projections(e, k, layout)))
            }
        }
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(
            sym.clone(),
            arg.as_ref()
                .map(|a| Box::new(rewrite_projections(a, k, layout))),
        ),
        Cir::Lam(b) => Cir::Lam(Box::new(rewrite_projections(b, k + 1, layout))),
        Cir::Fix(b) => Cir::Fix(Box::new(rewrite_projections(b, k + 1, layout))),
        Cir::App(g, a) => Cir::App(
            Box::new(rewrite_projections(g, k, layout)),
            Box::new(rewrite_projections(a, k, layout)),
        ),
        Cir::CallClosure(g, a) => Cir::CallClosure(
            Box::new(rewrite_projections(g, k, layout)),
            Box::new(rewrite_projections(a, k, layout)),
        ),
        Cir::Let(v, b) => Cir::Let(
            Box::new(rewrite_projections(v, k, layout)),
            Box::new(rewrite_projections(b, k + 1, layout)),
        ),
        Cir::Con(name, args, al) => Cir::Con(
            name.clone(),
            args.iter()
                .map(|a| rewrite_projections(a, k, layout))
                .collect(),
            *al,
        ),
        Cir::Tuple(args, al) => Cir::Tuple(
            args.iter()
                .map(|a| rewrite_projections(a, k, layout))
                .collect(),
            *al,
        ),
        Cir::MkClosure(name, args, al) => Cir::MkClosure(
            name.clone(),
            args.iter()
                .map(|a| rewrite_projections(a, k, layout))
                .collect(),
            *al,
        ),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(rewrite_projections(s, k, layout)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: rewrite_projections(&arm.body, k + arm.binders, layout),
                })
                .collect(),
        ),
        Cir::Now(e, al) => Cir::Now(Box::new(rewrite_projections(e, k, layout)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(rewrite_projections(e, k, layout)), *al),
        Cir::Force(e) => Cir::Force(Box::new(rewrite_projections(e, k, layout))),
        Cir::Region(e) => Cir::Region(Box::new(rewrite_projections(e, k, layout))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(rewrite_projections(arg, k, layout)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(rewrite_projections(body, k, layout)),
            return_clause: Box::new(rewrite_projections(return_clause, k + 1, layout)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), rewrite_projections(e, k + 2, layout)))
                .collect(),
        },
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(rewrite_projections(lhs, k, layout)),
            rhs: Box::new(rewrite_projections(rhs, k, layout)),
        },
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => Cir::IfZero {
            scrut: Box::new(rewrite_projections(scrut, k, layout)),
            then_: Box::new(rewrite_projections(then_, k, layout)),
            else_: Box::new(rewrite_projections(else_, k, layout)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(rewrite_projections(lhs, k, layout)),
            rhs: rhs
                .as_ref()
                .map(|r| Box::new(rewrite_projections(r, k, layout))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(rewrite_projections(lhs, k, layout)),
            rhs: rhs
                .as_ref()
                .map(|r| Box::new(rewrite_projections(r, k, layout))),
        },
        Cir::Flat {
            tag,
            fields,
            total_slots,
            alloc,
        } => Cir::Flat {
            tag: tag.clone(),
            fields: fields
                .iter()
                .map(|fl| fl.map_cir(|x| rewrite_projections(x, k, layout)))
                .collect(),
            total_slots: *total_slots,
            alloc: *alloc,
        },
        Cir::FlatProj {
            index,
            layout: l,
            scrut,
        } => Cir::FlatProj {
            index: *index,
            layout: l
                .iter()
                .map(|fl| fl.map_cir(|x| rewrite_projections(x, k, layout)))
                .collect(),
            scrut: Box::new(rewrite_projections(scrut, k, layout)),
        },
    }
}

/// Apply `f` to each immediate child of `c`, rebuilding the node (the standard bottom-up driver,
/// mirroring the one in [`crate::unbox`]). `Flat`/`FlatProj` are handled so the pass is idempotent.
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
        Cir::Con(name, args, al) => Cir::Con(name.clone(), args.iter().map(f).collect(), *al),
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
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(f).collect(), *al),
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
            Cir::MkClosure(name.clone(), env.iter().map(f).collect(), *al)
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
        // The pass is idempotent: re-running over already-flattened nodes recurses into their
        // embedded `Cir`s and rebuilds. (flatten normally runs once, before closure conversion.)
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
    use blight_kernel::ConName;

    fn con(name: &str, args: Vec<Cir>) -> Cir {
        Cir::con(ConName(name.into()), args)
    }

    /// `let p = mk-outer (mk-inner a b) c` where the body only ever drills `p` to leaves:
    /// `((p.0).0) , ((p.0).1) , (p.1)` — flattens to one 3-slot `Flat` and three `FlatProj`s at
    /// physical offsets 0, 1, 2. The intermediate `mk-inner` cell is gone.
    #[test]
    fn flattens_nested_product_drilled_to_leaves() {
        let inner = con(
            "mk-inner",
            vec![Cir::Global("a".into()), Cir::Global("b".into())],
        );
        let outer = con("mk-outer", vec![inner, Cir::Global("c".into())]);
        // body, with `p` = de Bruijn 0: read all three leaves and tuple them up.
        let read00 = Cir::Proj(0, Box::new(Cir::Proj(0, Box::new(Cir::Var(0)))));
        let read01 = Cir::Proj(1, Box::new(Cir::Proj(0, Box::new(Cir::Var(0)))));
        let read1 = Cir::Proj(1, Box::new(Cir::Var(0)));
        let body = Cir::tuple(vec![read00, read01, read1]);
        let term = Cir::Let(Box::new(outer), Box::new(body));

        let out = flatten(&term);
        let Cir::Let(v, b) = &out else {
            panic!("expected a Let, got {out:?}");
        };
        // The bound value is now a 3-slot Flat tagged `mk-outer`.
        match v.as_ref() {
            Cir::Flat {
                tag, total_slots, ..
            } => {
                assert_eq!(tag.as_ref().map(|c| c.0.as_str()), Some("mk-outer"));
                assert_eq!(*total_slots, 3);
            }
            other => panic!("expected Flat, got {other:?}"),
        }
        // Every leaf read became a single FlatProj at its physical offset.
        let Cir::Tuple(reads, _) = b.as_ref() else {
            panic!("expected tuple body, got {b:?}");
        };
        let offsets: Vec<usize> = reads
            .iter()
            .map(|r| match r {
                Cir::FlatProj { index, .. } => *index,
                other => panic!("expected FlatProj, got {other:?}"),
            })
            .collect();
        assert_eq!(offsets, vec![0, 1, 2]);
    }

    /// Declines when `p` escapes as a whole value (returned bare): a downstream reader would expect
    /// the un-flattened layout. The term is returned structurally unchanged.
    #[test]
    fn declines_when_parent_escapes_whole() {
        let inner = con(
            "mk-inner",
            vec![Cir::Global("a".into()), Cir::Global("b".into())],
        );
        let outer = con("mk-outer", vec![inner, Cir::Global("c".into())]);
        let body = Cir::Var(0); // p escapes whole
        let term = Cir::Let(Box::new(outer), Box::new(body));
        assert!(matches!(flatten(&term), Cir::Let(v, _) if matches!(v.as_ref(), Cir::Con(..))));
    }

    /// Declines when a nested sub-product is read *as a whole* (`p.0`, not drilled further): that
    /// value has no standalone cell once flattened, so we must not fire.
    #[test]
    fn declines_when_nested_read_whole() {
        let inner = con(
            "mk-inner",
            vec![Cir::Global("a".into()), Cir::Global("b".into())],
        );
        let outer = con("mk-outer", vec![inner, Cir::Global("c".into())]);
        let body = Cir::Proj(0, Box::new(Cir::Var(0))); // reads the whole inner pair
        let term = Cir::Let(Box::new(outer), Box::new(body));
        assert!(matches!(flatten(&term), Cir::Let(v, _) if matches!(v.as_ref(), Cir::Con(..))));
    }

    /// Declines when `p` is `case`-matched: the match dispatches on the parent's *un-flattened* tag
    /// and field count.
    #[test]
    fn declines_when_parent_matched() {
        let inner = con(
            "mk-inner",
            vec![Cir::Global("a".into()), Cir::Global("b".into())],
        );
        let outer = con("mk-outer", vec![inner, Cir::Global("c".into())]);
        let body = Cir::Case(
            Box::new(Cir::Var(0)),
            vec![Arm {
                con: ConName("mk-outer".into()),
                binders: 2,
                body: Cir::Var(0),
            }],
        );
        let term = Cir::Let(Box::new(outer), Box::new(body));
        assert!(matches!(flatten(&term), Cir::Let(v, _) if matches!(v.as_ref(), Cir::Con(..))));
    }

    /// Declines a flat (non-nested) product — flattening would be a no-op, so we leave it for the
    /// ordinary lowering (no spurious `Flat` nodes).
    #[test]
    fn declines_when_no_nested_field() {
        let outer = con(
            "mk-outer",
            vec![Cir::Global("a".into()), Cir::Global("b".into())],
        );
        let body = Cir::Proj(0, Box::new(Cir::Var(0)));
        let term = Cir::Let(Box::new(outer), Box::new(body));
        assert!(matches!(flatten(&term), Cir::Let(v, _) if matches!(v.as_ref(), Cir::Con(..))));
    }

    /// The `k` index tracks correctly under an intervening binder: `let p = … in (lam (… p.0.0 …))`.
    /// Inside the lambda `p` is de Bruijn 1, and its drilled read must still flatten.
    #[test]
    fn tracks_binder_depth_under_lambda() {
        let inner = con(
            "mk-inner",
            vec![Cir::Global("a".into()), Cir::Global("b".into())],
        );
        let outer = con("mk-outer", vec![inner, Cir::Global("c".into())]);
        // body = lam x. ((p.0).1) ; p is Var(1) under the lambda.
        let read = Cir::Proj(1, Box::new(Cir::Proj(0, Box::new(Cir::Var(1)))));
        let body = Cir::Lam(Box::new(read));
        let term = Cir::Let(Box::new(outer), Box::new(body));
        let out = flatten(&term);
        let Cir::Let(v, b) = &out else {
            panic!("expected Let")
        };
        assert!(matches!(v.as_ref(), Cir::Flat { total_slots: 3, .. }));
        let Cir::Lam(inner_body) = b.as_ref() else {
            panic!("expected lam")
        };
        match inner_body.as_ref() {
            Cir::FlatProj { index, scrut, .. } => {
                assert_eq!(*index, 1);
                assert!(matches!(scrut.as_ref(), Cir::Var(1)));
            }
            other => panic!("expected FlatProj over Var(1), got {other:?}"),
        }
    }
}
