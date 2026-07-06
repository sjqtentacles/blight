//! `unbox.rs` — the zero-TCB product scalar-replacement-of-aggregates pass (M27).
//!
//! A `Cir -> Cir` rewrite that *eliminates the heap allocation* of a small fixed-arity product
//! (a `Tuple`/record or a constructor `Con`) when that product is built only to be **immediately
//! consumed in place** — projected (`Proj i e`) or eliminated (`Case (Con …) arms`) — and so never
//! escapes its construction. This is the strongest form of "unbox a small product": instead of
//! laying the fields out inline in a parent allocation, we delete the allocation entirely and feed
//! the field values straight to the consumer (M21 immediates "into registers", extended past
//! scalars).
//!
//! ## Why this is sound without growing the TCB (and without touching the GC)
//! Each rewrite is an ordinary **product β-reduction** — `fst (a, b) ≡ a`, `match (mk c x y) …`
//! selects the `c` arm with `x`/`y` bound — which the operational semantics already validate. It
//! runs in the untrusted backend, downstream of checking: the kernel and the re-checker only ever
//! see the original `Tuple`/`Con` + `Proj`/`Case`. A bug here can only ever produce a wrong *value*
//! (caught by the bit-identical A/B differential corpus, `BL_NO_UNBOX`), never a false *proof*. And
//! because the allocation is *removed* rather than *re-laid-out*, the GC tracer is untouched — there
//! is no flattened layout to mis-trace (the highest-stakes hazard the milestone flags is avoided by
//! construction).
//!
//! ## Why it is conservative (the soundness guard)
//! A field of the product can be an *effectful* or *allocating* expression whose evaluation order or
//! occurrence is observable (`(perform op a, b)`, `(f x, g y)`). Deleting the product and inlining a
//! selected field would drop the *other* fields' effects, or duplicate/reorder a field used twice.
//! So a rewrite fires **only when every sibling field is a settled pure value** — a variable, a
//! global/env reference, a literal, a lambda/closure, or a (recursively) pure product — i.e. nothing
//! that performs an effect or whose elimination is load-bearing. Under that guard, projecting one
//! field and discarding the rest is observationally identical to building-then-projecting, and
//! substituting the fields into the matched arm is capture-avoiding β. Anything else falls back to
//! the unchanged build-then-consume lowering: never a miscompile, only a missed optimization.

use crate::ir::{Arm, Cir};

/// Eliminate every in-place-consumed small product allocation in `c` (see the module docs). Runs
/// bottom-up so a product exposed by an inner rewrite (e.g. `fst (fst ((a,b),c))`) is folded too.
pub fn unbox(c: &Cir) -> Cir {
    // Rebuild children first (bottom-up), then attempt a fold at this node.
    let rebuilt = map_children(c, unbox);
    match &rebuilt {
        // `Proj i (Tuple/Con [f0..fn])` with all-pure fields ≡ `fi`: the product never had to exist.
        Cir::Proj(i, e) => match e.as_ref() {
            Cir::Tuple(fields, _) | Cir::Con(_, fields, _)
                if *i < fields.len() && fields.iter().all(is_pure_value) =>
            {
                fields[*i].clone()
            }
            _ => rebuilt,
        },
        // `Case (Con c [f0..fn]) arms` with all-pure fields ≡ the `c` arm's body with the fields
        // substituted for its binders (product β). The constructor's fields map to the arm binders
        // by the lowering convention (lower.rs): field `j` is de Bruijn `nfields-1-j` inside the arm.
        Cir::Case(scrut, arms) => match scrut.as_ref() {
            Cir::Con(con, fields, _) if fields.iter().all(is_pure_value) => {
                fold_case(con, fields, arms).unwrap_or(rebuilt)
            }
            _ => rebuilt,
        },
        // A `let`-bound pure literal product *whose every use is an in-place destructure* —
        // `let p = (a,b)` / `App(λ. body, (a,b))` where `body` only ever feeds `p` to a `Proj`/`Case`
        // — is substituted into `body` so each consumer becomes a `Proj/Case (Con …)` the rules above
        // then fold, deleting the allocation. The "every use destructures it" guard means the product
        // is never left live (no duplicated allocation), so this is a pure win, never a pessimization.
        // The elaborator's `Elim`-on-a-literal lowering is exactly this shape (`pair-fst (mk-pair …)`
        // → `App(λ. … Case(Var0,…), mk-pair-literal)`), so it covers projecting a freshly-built pair.
        Cir::App(g, a) => match g.as_ref() {
            Cir::Lam(body) if is_pure_literal_product(a) && all_uses_destructure(body, 0) => {
                // Substitute the literal product for the binder, then re-unbox so the exposed
                // `Proj/Case (Con …)` redexes fold.
                unbox(&subst(body, std::slice::from_ref(a), 0))
            }
            _ => rebuilt,
        },
        Cir::Let(v, body) if is_pure_literal_product(v) && all_uses_destructure(body, 0) => {
            unbox(&subst(body, std::slice::from_ref(v), 0))
        }
        _ => rebuilt,
    }
}

/// Fold `Case (Con con fields) arms` to the matching arm's β-reduced body, if that arm binds exactly
/// the constructor's kept fields (no induction-hypothesis binders the literal scrutinee can't fill).
fn fold_case(con: &blight_kernel::ConName, fields: &[Cir], arms: &[Arm]) -> Option<Cir> {
    let arm = arms.iter().find(|a| a.con == *con)?;
    // Only fire when the arm binds exactly the constructor's kept fields (no extra IH binders). A
    // recursive-field constructor's arm binds an IH the literal scrutinee can't supply; its
    // scrutinee is a value anyway, so no allocation is saved there. Leave it generic.
    if arm.binders == fields.len() {
        Some(subst_fields(&arm.body, fields))
    } else {
        None
    }
}

/// Is `c` a pure literal product (`Tuple`/`Con`) — every field a settled pure value — i.e. an
/// allocation we may freely substitute because doing so adds no effect and (under the use guard)
/// removes the allocation entirely?
fn is_pure_literal_product(c: &Cir) -> bool {
    matches!(c, Cir::Tuple(fields, _) | Cir::Con(_, fields, _) if fields.iter().all(is_pure_value))
}

/// Does every free occurrence of de Bruijn variable `k` in `c` appear *only* as the immediate
/// operand of a `Proj` or the scrutinee of a `Case`? If so, substituting a literal product for `k`
/// makes each such use a `Proj/Case (Con …)` that [`unbox`] folds — so the product is never left
/// live, and the substitution can only remove allocations. A use anywhere else (returned, passed to
/// a call, stored in another product, …) would keep the product alive (and substituting could
/// duplicate the allocation), so we decline.
fn all_uses_destructure(c: &Cir, k: usize) -> bool {
    match c {
        // The two *good* uses: `k` consumed in place. (Its sub-expressions are checked by recursion
        // via the catch-all below, which also covers a `Proj`/`Case` whose scrutinee is NOT `Var(k)`.)
        Cir::Proj(_, e) if is_var(e, k) => true,
        Cir::Case(s, arms) if is_var(s, k) => arms.iter().all(|arm| {
            // Inside an arm the binder shifts under `arm.binders` new binders.
            all_uses_destructure(&arm.body, k + arm.binders)
        }),
        // A bare occurrence of `k` anywhere else is an escaping (non-destructuring) use: decline.
        Cir::Var(j) => *j != k,
        Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => true,
        Cir::Foreign(_, arg) => arg
            .as_ref()
            .map(|a| all_uses_destructure(a, k))
            .unwrap_or(true),
        Cir::Lam(b) | Cir::Fix(b) => all_uses_destructure(b, k + 1),
        Cir::App(g, a) | Cir::CallClosure(g, a) => {
            all_uses_destructure(g, k) && all_uses_destructure(a, k)
        }
        Cir::Let(v, b) => all_uses_destructure(v, k) && all_uses_destructure(b, k + 1),
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().all(|a| all_uses_destructure(a, k))
        }
        Cir::Case(s, arms) => {
            all_uses_destructure(s, k)
                && arms
                    .iter()
                    .all(|arm| all_uses_destructure(&arm.body, k + arm.binders))
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            all_uses_destructure(e, k)
        }
        Cir::Op { arg, .. } => all_uses_destructure(arg, k),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            all_uses_destructure(body, k)
                && all_uses_destructure(return_clause, k + 1)
                && op_clauses
                    .iter()
                    .all(|(_, e)| all_uses_destructure(e, k + 2))
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            all_uses_destructure(lhs, k) && all_uses_destructure(rhs, k)
        }
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => {
            all_uses_destructure(scrut, k)
                && all_uses_destructure(then_, k)
                && all_uses_destructure(else_, k)
        }
        Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
            all_uses_destructure(lhs, k)
                && rhs
                    .as_ref()
                    .map(|r| all_uses_destructure(r, k))
                    .unwrap_or(true)
        }
        // `Flat`/`FlatProj` bind no variables, so every embedded slot value sits at depth `k`.
        Cir::Flat { fields, .. } => fields
            .iter()
            .all(|fl| !fl.any_cir(|c| !all_uses_destructure(c, k))),
        Cir::FlatProj { layout, scrut, .. } => {
            all_uses_destructure(scrut, k)
                && layout
                    .iter()
                    .all(|fl| !fl.any_cir(|c| !all_uses_destructure(c, k)))
        }
    }
}

/// Is `c` exactly the de Bruijn variable `k`?
fn is_var(c: &Cir, k: usize) -> bool {
    matches!(c, Cir::Var(j) if *j == k)
}

/// Is `c` a settled pure value — safe to drop (if an unselected sibling) or to substitute for a
/// matched binder — with no observable effect, allocation-ordering, or duplication hazard? A
/// variable/global/env-ref is already evaluated; a literal is a constant; a `Lam`/`MkClosure` is a
/// value; a `Tuple`/`Con` is pure iff every field is (recursively). Everything else — any
/// application, `perform`/`force`, `case`/`handle`, projection, `fix`, region, `let` — can perform an
/// effect or its elimination is load-bearing, so it is treated as impure and blocks the fold.
fn is_pure_value(c: &Cir) -> bool {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => true,
        // A bare lambda/closure is a value (a heap closure would still allocate, but we are not
        // *removing* it here — only deciding whether dropping/substituting it changes meaning; a
        // value is safe to substitute, and a closure substituted into a single use is duplicated at
        // most as often as the binder, which the `single use` arms below already respect).
        Cir::Lam(_) | Cir::MkClosure(..) => true,
        Cir::Tuple(fields, _) | Cir::Con(_, fields, _) => fields.iter().all(is_pure_value),
        // A flattened product is a value exactly like the `Con`/`Tuple` it stands for: pure iff every
        // embedded slot value is pure. (A1: `Flat` only appears if pre-mono `flatten` fired; keeping
        // `unbox` total over it lets the A1′ post-mono re-run be order-independent.)
        Cir::Flat { fields, .. } => fields.iter().all(|fl| !fl.any_cir(|c| !is_pure_value(c))),
        // Pure, *non-trapping* machine arithmetic with pure operands is a settled value for the
        // purposes of SRA: dropping an unselected sibling or substituting a selected field changes no
        // observable behaviour (no effect, no allocation-ordering hazard, and — crucially — no trap).
        // `Nat` ops are all total (truncated `sub`/`pred`); for `Int`/`Float` we exclude `Div` (the
        // only divide-by-zero trap) so we never delete a sibling whose evaluation could fault. This is
        // what lets post-mono `unbox` delete the `Proj`-of-`Con` chains monomorphization exposes
        // (e.g. `fst (fst (mk-pair (mk-pair (a+0) (b+0)) (c+0)))`). Bit-identical, gated `BL_NO_UNBOX`.
        Cir::NatPrim { lhs, rhs, .. } => {
            is_pure_value(lhs) && rhs.as_ref().map(|r| is_pure_value(r)).unwrap_or(true)
        }
        Cir::IntPrim { op, lhs, rhs } => {
            !matches!(op, blight_kernel::IntPrimOp::Div) && is_pure_value(lhs) && is_pure_value(rhs)
        }
        Cir::FloatPrim { op, lhs, rhs } => {
            !matches!(op, crate::ir::FloatPrimOp::Div)
                && is_pure_value(lhs)
                && rhs.as_ref().map(|r| is_pure_value(r)).unwrap_or(true)
        }
        _ => false,
    }
}

/// Substitute the constructor's `fields` for the innermost `n = fields.len()` de Bruijn binders of an
/// arm `body`, producing the β-reduced body with no remaining reference to those binders and every
/// outer free variable shifted down by `n`. Field `j` is the value for de Bruijn `n-1-j` (the
/// lowering convention from lower.rs: the first constructor field is the *outermost* of the arm's
/// binders). Capture-avoiding: each substituted field is shifted up by the number of binders crossed.
fn subst_fields(body: &Cir, fields: &[Cir]) -> Cir {
    let n = fields.len();
    // `sigma[k]` is the replacement for de Bruijn `k` (0 = innermost). Binder `k` matches field
    // `n-1-k`.
    let sigma: Vec<Cir> = (0..n).map(|k| fields[n - 1 - k].clone()).collect();
    subst(body, &sigma, 0)
}

/// Core substitution. Replaces de Bruijn `depth + k` with `sigma[k]` (shifted up by `depth`), and
/// shifts any free variable at or above `depth + n` down by `n` (the `n` consumed binders are gone).
/// Variables strictly below `depth` are local to `body` and untouched.
fn subst(c: &Cir, sigma: &[Cir], depth: usize) -> Cir {
    let n = sigma.len();
    match c {
        Cir::Var(i) => {
            if *i < depth {
                // A binder local to the substituted region: unchanged.
                Cir::Var(*i)
            } else if *i < depth + n {
                // A consumed binder: replace with its field value, lifted past the `depth` binders
                // crossed to reach this occurrence.
                shift_cir(&sigma[*i - depth], depth)
            } else {
                // A genuinely free outer variable: the `n` consumed binders no longer sit beneath it.
                Cir::Var(*i - n)
            }
        }
        Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(
            sym.clone(),
            arg.as_ref().map(|a| Box::new(subst(a, sigma, depth))),
        ),
        Cir::Lam(b) => Cir::Lam(Box::new(subst(b, sigma, depth + 1))),
        Cir::Fix(b) => Cir::Fix(Box::new(subst(b, sigma, depth + 1))),
        Cir::App(f, a) => Cir::App(
            Box::new(subst(f, sigma, depth)),
            Box::new(subst(a, sigma, depth)),
        ),
        Cir::Let(v, b) => Cir::Let(
            Box::new(subst(v, sigma, depth)),
            Box::new(subst(b, sigma, depth + 1)),
        ),
        Cir::Con(name, args, al) => Cir::Con(
            name.clone(),
            args.iter().map(|a| subst(a, sigma, depth)).collect(),
            *al,
        ),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(subst(s, sigma, depth)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: subst(&arm.body, sigma, depth + arm.binders),
                })
                .collect(),
        ),
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(|e| subst(e, sigma, depth)).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(subst(e, sigma, depth))),
        Cir::Now(e, al) => Cir::Now(Box::new(subst(e, sigma, depth)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(subst(e, sigma, depth)), *al),
        Cir::Force(e) => Cir::Force(Box::new(subst(e, sigma, depth))),
        Cir::Region(e) => Cir::Region(Box::new(subst(e, sigma, depth))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(subst(arg, sigma, depth)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(subst(body, sigma, depth)),
            // The return clause binds 1 var; each op clause binds `x` then `k` (2 vars).
            return_clause: Box::new(subst(return_clause, sigma, depth + 1)),
            op_clauses: op_clauses
                .iter()
                .map(|(name, e)| (name.clone(), subst(e, sigma, depth + 2)))
                .collect(),
        },
        Cir::MkClosure(name, env, al) => Cir::MkClosure(
            name.clone(),
            env.iter().map(|e| subst(e, sigma, depth)).collect(),
            *al,
        ),
        Cir::CallClosure(f, a) => Cir::CallClosure(
            Box::new(subst(f, sigma, depth)),
            Box::new(subst(a, sigma, depth)),
        ),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(subst(lhs, sigma, depth)),
            rhs: Box::new(subst(rhs, sigma, depth)),
        },
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => Cir::IfZero {
            scrut: Box::new(subst(scrut, sigma, depth)),
            then_: Box::new(subst(then_, sigma, depth)),
            else_: Box::new(subst(else_, sigma, depth)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(subst(lhs, sigma, depth)),
            rhs: rhs.as_ref().map(|r| Box::new(subst(r, sigma, depth))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(subst(lhs, sigma, depth)),
            rhs: rhs.as_ref().map(|r| Box::new(subst(r, sigma, depth))),
        },
        // `Flat`/`FlatProj` introduce no binders: substitute each embedded value at the same `depth`.
        Cir::Flat {
            tag,
            fields,
            total_slots,
            alloc,
        } => Cir::Flat {
            tag: tag.clone(),
            fields: fields
                .iter()
                .map(|fl| fl.map_cir(|c| subst(c, sigma, depth)))
                .collect(),
            total_slots: *total_slots,
            alloc: *alloc,
        },
        Cir::FlatProj {
            index,
            layout,
            scrut,
        } => Cir::FlatProj {
            index: *index,
            layout: layout
                .iter()
                .map(|fl| fl.map_cir(|c| subst(c, sigma, depth)))
                .collect(),
            scrut: Box::new(subst(scrut, sigma, depth)),
        },
    }
}

/// Shift every free de Bruijn variable (index `>= 0` under `cutoff` binders) of `c` up by `by`.
/// Used to lift a substituted field value past the binders crossed to reach its use site.
fn shift_cir(c: &Cir, by: usize) -> Cir {
    fn go(c: &Cir, by: usize, cutoff: usize) -> Cir {
        match c {
            Cir::Var(i) => {
                if *i >= cutoff {
                    Cir::Var(i + by)
                } else {
                    Cir::Var(*i)
                }
            }
            Cir::Global(_)
            | Cir::Erased
            | Cir::EnvRef(_)
            | Cir::IntLit(_)
            | Cir::NatLit(_)
            | Cir::StrLit(_) => c.clone(),
            Cir::Foreign(sym, arg) => Cir::Foreign(
                sym.clone(),
                arg.as_ref().map(|a| Box::new(go(a, by, cutoff))),
            ),
            Cir::Lam(b) => Cir::Lam(Box::new(go(b, by, cutoff + 1))),
            Cir::Fix(b) => Cir::Fix(Box::new(go(b, by, cutoff + 1))),
            Cir::App(f, a) => Cir::App(Box::new(go(f, by, cutoff)), Box::new(go(a, by, cutoff))),
            Cir::Let(v, b) => {
                Cir::Let(Box::new(go(v, by, cutoff)), Box::new(go(b, by, cutoff + 1)))
            }
            Cir::Con(name, args, al) => Cir::Con(
                name.clone(),
                args.iter().map(|a| go(a, by, cutoff)).collect(),
                *al,
            ),
            Cir::Case(s, arms) => Cir::Case(
                Box::new(go(s, by, cutoff)),
                arms.iter()
                    .map(|arm| Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: go(&arm.body, by, cutoff + arm.binders),
                    })
                    .collect(),
            ),
            Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(|e| go(e, by, cutoff)).collect(), *al),
            Cir::Proj(i, e) => Cir::Proj(*i, Box::new(go(e, by, cutoff))),
            Cir::Now(e, al) => Cir::Now(Box::new(go(e, by, cutoff)), *al),
            Cir::Later(e, al) => Cir::Later(Box::new(go(e, by, cutoff)), *al),
            Cir::Force(e) => Cir::Force(Box::new(go(e, by, cutoff))),
            Cir::Region(e) => Cir::Region(Box::new(go(e, by, cutoff))),
            Cir::Op { effect, op, arg } => Cir::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(arg, by, cutoff)),
            },
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => Cir::Handle {
                body: Box::new(go(body, by, cutoff)),
                return_clause: Box::new(go(return_clause, by, cutoff + 1)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(name, e)| (name.clone(), go(e, by, cutoff + 2)))
                    .collect(),
            },
            Cir::MkClosure(name, env, al) => Cir::MkClosure(
                name.clone(),
                env.iter().map(|e| go(e, by, cutoff)).collect(),
                *al,
            ),
            Cir::CallClosure(f, a) => {
                Cir::CallClosure(Box::new(go(f, by, cutoff)), Box::new(go(a, by, cutoff)))
            }
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, cutoff)),
                rhs: Box::new(go(rhs, by, cutoff)),
            },
            // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
            Cir::IfZero {
                scrut,
                then_,
                else_,
            } => Cir::IfZero {
                scrut: Box::new(go(scrut, by, cutoff)),
                then_: Box::new(go(then_, by, cutoff)),
                else_: Box::new(go(else_, by, cutoff)),
            },
            Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, cutoff)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, by, cutoff))),
            },
            Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, cutoff)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, by, cutoff))),
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
                    .map(|fl| fl.map_cir(|c| go(c, by, cutoff)))
                    .collect(),
                total_slots: *total_slots,
                alloc: *alloc,
            },
            Cir::FlatProj {
                index,
                layout,
                scrut,
            } => Cir::FlatProj {
                index: *index,
                layout: layout
                    .iter()
                    .map(|fl| fl.map_cir(|c| go(c, by, cutoff)))
                    .collect(),
                scrut: Box::new(go(scrut, by, cutoff)),
            },
        }
    }
    if by == 0 {
        c.clone()
    } else {
        go(c, by, 0)
    }
}

/// Apply `f` to each immediate child of `c`, rebuilding the node (bottom-up traversal driver).
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
        Cir::Flat {
            tag,
            fields,
            total_slots,
            alloc,
        } => Cir::Flat {
            tag: tag.clone(),
            fields: fields.iter().map(|fl| fl.map_cir(&f)).collect(),
            total_slots: *total_slots,
            alloc: *alloc,
        },
        Cir::FlatProj {
            index,
            layout,
            scrut,
        } => Cir::FlatProj {
            index: *index,
            layout: layout.iter().map(|fl| fl.map_cir(&f)).collect(),
            scrut: Box::new(f(scrut)),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::ConName;

    fn pair(a: Cir, b: Cir) -> Cir {
        Cir::tuple(vec![a, b])
    }
    fn mk_pair(a: Cir, b: Cir) -> Cir {
        Cir::con(ConName("mk-pair".into()), vec![a, b])
    }

    /// `fst (a, b)` with pure fields collapses to `a` — the tuple is never allocated.
    #[test]
    fn proj_of_pure_tuple_collapses() {
        let t = Cir::Proj(0, Box::new(pair(Cir::Var(3), Cir::Var(4))));
        assert_eq!(unbox(&t), Cir::Var(3));
        let t2 = Cir::Proj(1, Box::new(pair(Cir::Var(3), Cir::Var(4))));
        assert_eq!(unbox(&t2), Cir::Var(4));
    }

    /// `snd (mk-pair a b)` over a single-constructor data product collapses likewise.
    #[test]
    fn proj_of_pure_con_collapses() {
        let t = Cir::Proj(
            1,
            Box::new(mk_pair(Cir::Global("g".into()), Cir::NatLit(7))),
        );
        assert_eq!(unbox(&t), Cir::NatLit(7));
    }

    /// The fold MUST NOT fire when an *unselected* sibling field is effectful: dropping it would
    /// erase its `perform`. The projection (and its allocation) survives.
    #[test]
    fn proj_preserves_effectful_sibling() {
        let eff = Cir::Op {
            effect: "E".into(),
            op: "get".into(),
            arg: Box::new(Cir::Erased),
        };
        // `fst (a, perform get)` — selecting `a` would drop the effect, so leave the tuple intact.
        let t = Cir::Proj(0, Box::new(pair(Cir::Var(0), eff)));
        assert!(matches!(unbox(&t), Cir::Proj(0, _)));
    }

    /// `match (mk-pair x y) [(mk-pair a b) → <body using a,b>]` β-reduces to the body with `x`/`y`
    /// substituted for the arm binders, and the surrounding tuple is gone. Field `j` is de Bruijn
    /// `n-1-j`, so in the 2-field arm `Var0`=second field (`y`), `Var1`=first field (`x`).
    #[test]
    fn case_of_pure_con_beta_reduces() {
        // body = `(Var1, Var0)` = `(x, y)` rebuilt; after subst it becomes `(Glob x, Nat y)`.
        let body = pair(Cir::Var(1), Cir::Var(0));
        let case = Cir::Case(
            Box::new(mk_pair(Cir::Global("x".into()), Cir::NatLit(9))),
            vec![Arm {
                con: ConName("mk-pair".into()),
                binders: 2,
                body,
            }],
        );
        assert_eq!(unbox(&case), pair(Cir::Global("x".into()), Cir::NatLit(9)));
    }

    /// β-reduction shifts genuinely-free outer variables down by the consumed binder count. An arm
    /// body referencing an outer `Var2` (above its 2 binders) becomes `Var0` once the product is gone.
    #[test]
    fn case_beta_shifts_outer_free_vars() {
        let body = Cir::Var(2); // outer free var, sitting above the 2 arm binders
        let case = Cir::Case(
            Box::new(mk_pair(Cir::Var(0), Cir::Var(1))),
            vec![Arm {
                con: ConName("mk-pair".into()),
                binders: 2,
                body,
            }],
        );
        assert_eq!(unbox(&case), Cir::Var(0));
    }

    /// The fold must NOT fire on a recursive-field constructor whose arm binds an induction
    /// hypothesis the literal scrutinee can't supply (`binders != nfields`): leave it generic.
    #[test]
    fn case_skips_arm_with_extra_ih_binders() {
        let case = Cir::Case(
            Box::new(Cir::con(ConName("Succ".into()), vec![Cir::Var(0)])),
            vec![Arm {
                con: ConName("Succ".into()),
                binders: 2, // field + IH
                body: Cir::Var(0),
            }],
        );
        assert!(matches!(unbox(&case), Cir::Case(_, _)));
    }

    /// A nested in-place product folds fully bottom-up: `fst (fst ((a,b), c))` → `a`.
    #[test]
    fn nested_projection_folds_fully() {
        let inner = pair(Cir::Var(5), Cir::Var(6));
        let outer = pair(inner, Cir::Var(7));
        let t = Cir::Proj(0, Box::new(Cir::Proj(0, Box::new(outer))));
        assert_eq!(unbox(&t), Cir::Var(5));
    }

    /// An *escaping* product (returned, not consumed in place) is left untouched — the allocation is
    /// load-bearing. Here the tuple is the whole term.
    #[test]
    fn escaping_product_is_preserved() {
        let t = pair(Cir::Var(0), Cir::Var(1));
        assert_eq!(unbox(&t), t);
    }

    /// The elaborator's `Elim`-on-a-literal lowering: `pair-fst (mk-pair x y)` becomes
    /// `App(λ. Case(Var0, [mk-pair → Var1]), mk-pair-literal)` — a let-bound literal product whose
    /// only use destructures it. M27 substitutes the literal and folds the `Case`, deleting the alloc.
    #[test]
    fn let_bound_literal_product_destructured_folds() {
        // body = `match Var0 [(mk-pair a b) → a]`; with the arm convention `a` = `Var1`.
        let body = Cir::Case(
            Box::new(Cir::Var(0)),
            vec![Arm {
                con: ConName("mk-pair".into()),
                binders: 2,
                body: Cir::Var(1),
            }],
        );
        let term = Cir::App(
            Box::new(Cir::Lam(Box::new(body))),
            Box::new(mk_pair(Cir::Global("x".into()), Cir::NatLit(8))),
        );
        // Substituting the pair and folding the match yields the first field, `x`.
        assert_eq!(unbox(&term), Cir::Global("x".into()));
    }

    /// `let p = (a,b) in fst p` folds away the binding and the allocation, leaving `a`. The bound
    /// value's free vars refer to the *outer* scope, so substituting it back out is index-preserving.
    #[test]
    fn let_form_literal_product_projection_folds() {
        let term = Cir::Let(
            Box::new(pair(Cir::Var(4), Cir::Var(5))),
            Box::new(Cir::Proj(0, Box::new(Cir::Var(0)))),
        );
        assert_eq!(unbox(&term), Cir::Var(4));
    }

    /// The let-substitution MUST NOT fire when a use *escapes* (the product would stay live and be
    /// duplicated): `let p = (a,b) in (p, fst p)` keeps `p` returned in the first component.
    #[test]
    fn let_bound_product_with_escaping_use_is_preserved() {
        let term = Cir::Let(
            Box::new(pair(Cir::Var(0), Cir::Var(1))),
            Box::new(pair(Cir::Var(0), Cir::Proj(0, Box::new(Cir::Var(0))))),
        );
        // `p` (Var0) appears bare in the outer pair → escaping → no substitution.
        assert!(matches!(unbox(&term), Cir::Let(_, _)));
    }
}
