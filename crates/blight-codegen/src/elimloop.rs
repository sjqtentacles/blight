//! `elimloop.rs` — the P3 (3a) tail-accumulator elim-loop transform, a `Cir -> Cir` pass.
//!
//! The eager eliminator [`crate::lower::lower_elim_fn`] produces the canonical catamorphism
//! `Fix(Lam(Case(Var0, arms)))` whose recursive arm computes its induction hypothesis with an
//! **eager, non-tail** self-call `App(self, field)`. With a function-typed motive (an accumulator
//! fold like `sum-go fuel idx acc`) the curried unary shape descends the whole spine on the C stack
//! before applying the accumulators, so a `fuel`-deep input SIGSEGVs.
//!
//! This pass recognizes that canonical worker and, when every recursive arm uses its IH **exactly
//! once, in tail position, saturated to the `k` accumulators**, rewrites it into a bounded-stack
//! accumulator loop (threaded as a state record through a self-`Jump`). It reuses the proven
//! [`crate::lower::build_elim_loop`] transform — this pass's only job is to **recover** the
//! per-constructor shape and the (un-shifted) methods structurally from the worker's arms.
//!
//! ## Why a separate pass, after `recognize`
//! The M20 fast-`Nat` recognizer ([`crate::recognize`]) folds the prelude `plus`/`mult`/`sub`/`pred`
//! eliminators to O(1) `NatPrim` ops by matching their `Fix(Lam(Case))` fingerprint. If the elim-loop
//! transform ran at lower time it would rewrite *those* eliminators first, destroying the fingerprint
//! and forcing the O(n) eliminator back (so an inner `plus acc idx` would recurse `acc`-deep). Running
//! strictly **after** `recognize` (which has already replaced arithmetic eliminators with `NatPrim`)
//! leaves only genuine catamorphisms (like `sum-go`) for this pass to loop-ify.
//!
//! ## Zero TCB
//! Like every backend pass this runs downstream of kernel checking; a bug here is a wrong *number*
//! (caught by the `BL_NO_ELIMLOOP` differential), never a false *proof*. Gated by `BL_NO_ELIMLOOP`.

use crate::ir::{Arm, Cir};
use crate::lower::{build_elim_loop, cir_uses, count_leading_lams, shift_cir_down, CtorShape};

/// Run the elim-loop transform over `c`. When `enabled` is false this is the identity (the
/// `BL_NO_ELIMLOOP` bit-identical reference).
pub fn elim_loop(c: &Cir, enabled: bool) -> Cir {
    if !enabled {
        return c.clone();
    }
    go(c)
}

/// Bottom-up rewrite: transform children first (so a nested eliminator inside a method body is
/// looped before the enclosing one consumes it), then attempt the transform at this node. The
/// builder a successful transform produces has the **same free variables at the same indices** as the
/// `Fix(Lam(Case))` worker it replaces (see [`crate::lower::build_elim_loop`]), so the walker needs
/// no de Bruijn bookkeeping.
fn go(c: &Cir) -> Cir {
    let c = map_children(c, &mut go);
    try_transform(&c).unwrap_or(c)
}

/// If `c` is a canonical `lower_elim_fn` worker `Fix(Lam(Case(Var0, arms)))` whose arms are the eager
/// method-application spines, recover the per-constructor shape + un-shifted methods and run
/// [`build_elim_loop`]. Returns the loop builder on success, or `None` to leave `c` unchanged.
fn try_transform(c: &Cir) -> Option<Cir> {
    let (ctors, methods) = recover_canonical_eliminator(c)?;
    build_elim_loop(&ctors, &methods)
        .or_else(|| crate::elimworklist::build_elim_worklist(&ctors, &methods))
}

/// If `c` is a canonical `lower_elim_fn` worker `Fix(Lam(Case(Var0, arms)))`, recover its
/// per-constructor shapes + un-shifted (bare) methods — the same structural recovery
/// [`try_transform`] uses before attempting a loop rewrite, exposed for [`crate::autopar`] (P4,
/// roadmap Wave 10), which needs the identical `(CtorShape, method)` pairs to recognize a
/// **tree-shaped** (`nrec >= 2`) divide-and-conquer arm — a shape both [`build_elim_loop`] (3a,
/// `nrec <= 1`) and [`crate::elimworklist::build_elim_worklist`] (3b, single-recursive-field only)
/// decline, so it survives this pass unrewritten and is exactly what `autopar`'s analysis looks for.
pub(crate) fn recover_canonical_eliminator(c: &Cir) -> Option<(Vec<CtorShape>, Vec<Cir>)> {
    let Cir::Fix(lam) = c else { return None };
    let Cir::Lam(case) = lam.as_ref() else {
        return None;
    };
    let Cir::Case(scrut, arms) = case.as_ref() else {
        return None;
    };
    // The eager eliminator scrutinizes the `Lam`'s parameter directly.
    if !matches!(scrut.as_ref(), Cir::Var(0)) {
        return None;
    }

    let mut ctors: Vec<CtorShape> = Vec::with_capacity(arms.len());
    let mut methods: Vec<Cir> = Vec::with_capacity(arms.len());
    for arm in arms {
        let (shape, method) = recover_arm(arm)?;
        ctors.push(shape);
        methods.push(method);
    }
    Some((ctors, methods))
}

/// Recover one constructor's `(CtorShape, un-shifted method)` from an eager arm. The eager arm body
/// is the application spine `head field0 [ih0] field1 [ih1] …` where `head` is the method shifted up
/// by `2 + nfields` (past `self`, `scrut`, and the field binders), each `field_j` is `Var(nfields-1-j)`
/// and each `ih` is `App(Var(self_idx), Var(field))` for a recursive field. We read the recursive-field
/// flags off the spine and un-shift `head` back to the bare method.
fn recover_arm(arm: &Arm) -> Option<(CtorShape, Cir)> {
    let nfields = arm.binders;
    let self_idx = nfields + 1; // within the arm: fields 0..nfields-1, scrut=nfields, self=nfields+1
    let (head, applied) = peel_spine(&arm.body);

    // Read the per-field recursive flags off the applied-argument list, consuming an IH argument
    // right after each recursive field. The reconstructed field count must match the arm's binders.
    let mut is_rec = Vec::with_capacity(nfields);
    let mut i = 0usize;
    while i < applied.len() {
        let field_is_rec = i + 1 < applied.len() && is_ih(applied[i + 1], self_idx);
        is_rec.push(field_is_rec);
        i += if field_is_rec { 2 } else { 1 };
    }
    if is_rec.len() != nfields {
        return None;
    }

    // `head` must be the captured method: it references *no* binder introduced by the eliminator
    // (fields/scrut/self, i.e. indices `0..2+nfields`). If it does, this is not a canonical eager
    // arm — bail rather than corrupt indices by un-shifting.
    if (0..nfields + 2).any(|i| cir_uses(head, i)) {
        return None;
    }
    // The method abstracts at least `nfields + nrec` binders (fields + IHs); the rest are the motive
    // accumulators handled by `build_elim_loop`.
    let nrec = is_rec.iter().filter(|&&r| r).count();
    if count_leading_lams(head) < nfields + nrec {
        return None;
    }

    // Un-shift the method back to its own scope (`lower_elim_fn` shifted it up by `2 + nfields`).
    let mut method = head.clone();
    for _ in 0..nfields + 2 {
        method = shift_cir_down(&method, 0);
    }
    Some((
        CtorShape {
            name: arm.con.clone(),
            is_rec,
        },
        method,
    ))
}

/// Peel an application spine `(((h a0) a1) … a_{n-1})` into `(h, [a0, a1, …, a_{n-1}])`.
fn peel_spine(c: &Cir) -> (&Cir, Vec<&Cir>) {
    let mut args = Vec::new();
    let mut cur = c;
    while let Cir::App(f, a) = cur {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

/// Is `c` an induction-hypothesis application `App(Var(self_idx), Var(_))` (the eager `self field`)?
fn is_ih(c: &Cir, self_idx: usize) -> bool {
    matches!(c, Cir::App(f, a)
        if matches!(f.as_ref(), Cir::Var(i) if *i == self_idx)
            && matches!(a.as_ref(), Cir::Var(_)))
}

/// Rebuild `c` with `f` applied to each immediate child `Cir` (no de Bruijn tracking — the transform
/// is index-preserving). Mirrors the structural coverage of `lower::shift_cir`.
fn map_children(c: &Cir, f: &mut impl FnMut(&Cir) -> Cir) -> Cir {
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
        Cir::App(a, b) => Cir::App(Box::new(f(a)), Box::new(f(b))),
        Cir::Let(v, b) => Cir::Let(Box::new(f(v)), Box::new(f(b))),
        Cir::CallClosure(a, b) => Cir::CallClosure(Box::new(f(a)), Box::new(f(b))),
        Cir::Con(name, args, al) => Cir::Con(name.clone(), args.iter().map(f).collect(), *al),
        Cir::Tuple(args, al) => Cir::Tuple(args.iter().map(f).collect(), *al),
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
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: Box::new(f(rhs)),
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
            fields: fields.iter().map(|fl| fl.map_cir(|x| f(x))).collect(),
            total_slots: *total_slots,
            alloc: *alloc,
        },
        Cir::FlatProj {
            index,
            layout,
            scrut,
        } => Cir::FlatProj {
            index: *index,
            layout: layout.iter().map(|fl| fl.map_cir(|x| f(x))).collect(),
            scrut: Box::new(f(scrut)),
        },
    }
}
