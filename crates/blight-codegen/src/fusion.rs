//! `fusion.rs` — zero-TCB deforestation of the `foldr`/`map` build-then-fold pipeline (P7).
//!
//! A `Cir -> Cir` rewrite that recognizes the canonical single-consumer shortcut
//! `foldr f z (map g xs)` and fuses it to `foldr (λx acc. f (g x) acc) z xs`, eliminating the
//! intermediate mapped list entirely — every `cons` cell `map` would build (and the GC traffic to
//! reclaim it) is gone, replaced by composing `g` into `f`'s element argument.
//!
//! ## Why this is sound without growing the TCB
//! Like [`crate::recognize`], this runs in the untrusted backend strictly downstream of checking, on
//! the fully-inlined `Cir`. The kernel and the independent re-checker only ever see the un-fused
//! `foldr`/`map` definitions. The rewrite is the standard `foldr/map` fusion law — for *pure* `f`/`g`
//! it is an equality (`foldr f z (map g xs) = foldr (f ∘₁ g) z xs`), proven bit-identical over the
//! corpus by the `BL_NO_FUSION` differential A/B switch. A bug here can only ever produce a wrong
//! *value*, never a false *proof*.
//!
//! ## Why it is conservative
//! Recognition is by exact structural fingerprint of the elaborator's lowered `foldr`/`map`
//! eliminator cores (captured from `BL_DUMP_CIR` over std/list.bl). If a user *redefines* `foldr`/
//! `map`, or the elaborator changes its encoding, the fingerprint simply fails to match and we fall
//! back to the un-fused lowering — never a miscompile, only a missed optimization. Two further guards
//! keep it observationally invisible:
//!   * **purity** — we fuse only when `f` and `g` are effect-free, because fusion interleaves the
//!     `g` applications with `f` (vs `map` running every `g` first), so a visible effect would
//!     reorder. Pure/total `deftotal` combinators (the only things that typecheck as `foldr`/`map`
//!     arguments in practice) are unaffected.
//!   * **single consumer** — we match `map g xs` only when it sits *directly* in `foldr`'s list
//!     argument. A `let m = map g xs in … m … m` binds the result to a variable (foldr's list arg is
//!     then a `Var`, not a `map` application), so a shared/multi-consumer pipeline never matches and
//!     is left intact (fusing it would duplicate the producer).

use crate::ir::{Arm, Cir};
use crate::lower::shift_free;
use blight_kernel::ConName;

/// Fuse every canonical single-consumer `foldr f z (map g xs)` redex in `c` to
/// `foldr (λx acc. f (g x) acc) z xs`. Runs bottom-up so a fused result can itself feed an enclosing
/// fusion (and so children are normalized before the parent fingerprint is tested).
pub fn fuse(c: &Cir) -> Cir {
    let rebuilt = map_children(c, fuse);
    try_fuse(&rebuilt).unwrap_or(rebuilt)
}

/// If `c` is a `foldr f z (map g xs)` application (both eliminators matching the captured prelude
/// fingerprints, with `f`/`g` pure), return its fused `foldr (λx acc. f (g x) acc) z xs`.
fn try_fuse(c: &Cir) -> Option<Cir> {
    let (foldr_head, f, z, list) = match_foldr_app(c)?;
    let (g, xs) = match_map_app(list)?;
    // SOUNDNESS: fusion interleaves `g` with `f` (vs `map` forcing every `g` first), so a visible
    // effect in either would reorder. Only fuse provably-pure combinators.
    if !is_pure(f) || !is_pure(g) {
        return None;
    }
    // The fused combiner `λx. λacc. f (g x) acc`. `f`/`g` live in the enclosing scope; under the two
    // new binders (`x` = Var1, `acc` = Var0) their free indices shift up by 2.
    let f2 = shift_free(f, 2);
    let g2 = shift_free(g, 2);
    let combiner = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::App(
        Box::new(Cir::App(
            Box::new(f2),
            Box::new(Cir::App(Box::new(g2), Box::new(Cir::Var(1)))),
        )),
        Box::new(Cir::Var(0)),
    )))));
    // Reuse the original `foldr` wrapper verbatim; only its `f` argument (now the combiner) and its
    // list argument (now the un-mapped `xs`) change. `z` rides through unchanged.
    Some(Cir::apply(
        foldr_head.clone(),
        [combiner, z.clone(), xs.clone()],
    ))
}

/// If `c` is a fully-applied `foldr` (`App(App(App(W, f), z), list)` with `W` the captured `foldr`
/// wrapper), return `(W, f, z, list)`.
fn match_foldr_app(c: &Cir) -> Option<(&Cir, &Cir, &Cir, &Cir)> {
    let (head, args) = c.unapply();
    if args.len() != 3 || !is_foldr_wrapper(head) {
        return None;
    }
    Some((head, args[0], args[1], args[2]))
}

/// If `c` is a fully-applied `map` (`App(App(W, g), xs)` with `W` the captured `map` wrapper), return
/// `(g, xs)`.
fn match_map_app(c: &Cir) -> Option<(&Cir, &Cir)> {
    let (head, args) = c.unapply();
    if args.len() != 2 || !is_map_wrapper(head) {
        return None;
    }
    Some((args[0], args[1]))
}

// ---- structural fingerprints (captured from BL_DUMP_CIR over std/list.bl) ----
//
// After erasure both wrappers drop their two `(Type 0)` parameters, so the lowered shapes are:
//
// `foldr f z xs` wrapper:  Lam(Lam(Lam( App(Fix(FOLDR_REC), Var0) )))     -- binds f,z,xs
//   FOLDR_REC = Lam(Case(Var0, [                                          -- binds the list `l`
//     nil{0}:  Var3,                                                      -- => z
//     cons{2}: App(App(App(Lam(Lam(Lam( App(App(Var9,Var2),Var0) ))), Var1), Var0), App(Var3,Var0)),
//   ]))                                                                   -- => f x (self rest)
//
// `map g xs` wrapper:      Lam(Lam( App(Fix(MAP_REC), Var0) ))            -- binds g,xs
//   MAP_REC = Lam(Case(Var0, [                                           -- binds the list `l`
//     nil{0}:  Con("nil",[]),
//     cons{2}: App(App(App(Lam(Lam(Lam( Con("cons",[App(Var8,Var2),Var0]) ))), Var1), Var0), App(Var3,Var0)),
//   ]))                                                                   -- => cons (g x) (self rest)

/// Is `w` the captured `foldr` wrapper `Lam(Lam(Lam(App(Fix(FOLDR_REC), Var0))))`?
fn is_foldr_wrapper(w: &Cir) -> bool {
    let Some(inner) = peel_lams(w, 3) else {
        return false;
    };
    let Cir::App(fix, arg) = inner else {
        return false;
    };
    if !is_var(arg, 0) {
        return false;
    }
    let Cir::Fix(rec) = fix.as_ref() else {
        return false;
    };
    *rec.as_ref() == foldr_rec()
}

/// Is `w` the captured `map` wrapper `Lam(Lam(App(Fix(MAP_REC), Var0)))`?
fn is_map_wrapper(w: &Cir) -> bool {
    let Some(inner) = peel_lams(w, 2) else {
        return false;
    };
    let Cir::App(fix, arg) = inner else {
        return false;
    };
    if !is_var(arg, 0) {
        return false;
    }
    let Cir::Fix(rec) = fix.as_ref() else {
        return false;
    };
    *rec.as_ref() == map_rec()
}

/// The `foldr` recurrence body `Lam(Case(Var0, [nil => z, cons => f x (self rest)]))` — a fixed,
/// closed `Cir` (every variable is a de Bruijn index), so equality against it is the fingerprint.
fn foldr_rec() -> Cir {
    Cir::Lam(Box::new(Cir::Case(
        Box::new(Cir::Var(0)),
        vec![
            Arm {
                con: ConName("nil".into()),
                binders: 0,
                body: Cir::Var(3),
            },
            Arm {
                con: ConName("cons".into()),
                binders: 2,
                body: method_app(Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(
                    Cir::App(
                        Box::new(Cir::App(Box::new(Cir::Var(9)), Box::new(Cir::Var(2)))),
                        Box::new(Cir::Var(0)),
                    ),
                ))))))),
            },
        ],
    )))
}

/// The `map` recurrence body `Lam(Case(Var0, [nil => nil, cons => cons (g x) (self rest)]))`.
fn map_rec() -> Cir {
    Cir::Lam(Box::new(Cir::Case(
        Box::new(Cir::Var(0)),
        vec![
            Arm {
                con: ConName("nil".into()),
                binders: 0,
                body: Cir::con(ConName("nil".into()), vec![]),
            },
            Arm {
                con: ConName("cons".into()),
                binders: 2,
                body: method_app(Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(
                    Cir::con(
                        ConName("cons".into()),
                        vec![
                            Cir::App(Box::new(Cir::Var(8)), Box::new(Cir::Var(2))),
                            Cir::Var(0),
                        ],
                    ),
                ))))))),
            },
        ],
    )))
}

/// Wrap a 3-binder `method` body into the lowered cons-arm application
/// `App(App(App(method, Var1), Var0), App(Var3, Var0))` — the elaborator's shape for applying the
/// arm method to the kept fields `x` (Var1) and `rest` (Var0) plus the induction hypothesis
/// `self rest` (`App(Var3, Var0)`).
fn method_app(method: Cir) -> Cir {
    Cir::App(
        Box::new(Cir::App(
            Box::new(Cir::App(Box::new(method), Box::new(Cir::Var(1)))),
            Box::new(Cir::Var(0)),
        )),
        Box::new(Cir::App(Box::new(Cir::Var(3)), Box::new(Cir::Var(0)))),
    )
}

/// Peel exactly `n` leading `Lam`s off `c`, returning the body beneath them (or `None` if there are
/// fewer than `n`).
fn peel_lams(c: &Cir, n: usize) -> Option<&Cir> {
    let mut cur = c;
    for _ in 0..n {
        let Cir::Lam(b) = cur else { return None };
        cur = b.as_ref();
    }
    Some(cur)
}

fn is_var(c: &Cir, i: usize) -> bool {
    matches!(c, Cir::Var(j) if *j == i)
}

/// Is `c` provably effect-free (safe to reorder under fusion)? Conservative: any effect/handler,
/// foreign call, force, delay cell, or region marks `c` impure (we then decline to fuse). The pure
/// arithmetic/data combinators that are the realistic `foldr`/`map` arguments contain none of these.
fn is_pure(c: &Cir) -> bool {
    match c {
        Cir::Op { .. }
        | Cir::Handle { .. }
        | Cir::Foreign(..)
        | Cir::Force(_)
        | Cir::Now(..)
        | Cir::Later(..)
        | Cir::Region(_) => false,
        _ => {
            let mut pure = true;
            for_each_child(c, &mut |child| pure &= is_pure(child));
            pure
        }
    }
}

/// Apply `f` to each immediate child of `c`. Mirrors the full `Cir` shape (pre-closure-conversion;
/// `Flat`/`FlatProj` cannot appear since fusion runs before `flatten`).
fn for_each_child(c: &Cir, f: &mut dyn FnMut(&Cir)) {
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
        Cir::Lam(b) | Cir::Fix(b) | Cir::Proj(_, b) | Cir::Force(b) | Cir::Region(b) => f(b),
        Cir::App(g, a) | Cir::Let(g, a) | Cir::CallClosure(g, a) => {
            f(g);
            f(a);
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().for_each(f)
        }
        Cir::Case(s, arms) => {
            f(s);
            arms.iter().for_each(|a| f(&a.body));
        }
        Cir::Now(e, _) | Cir::Later(e, _) => f(e),
        Cir::Op { arg, .. } => f(arg),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            f(body);
            f(return_clause);
            op_clauses.iter().for_each(|(_, e)| f(e));
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
        Cir::Flat { .. } | Cir::FlatProj { .. } => unreachable!("flatten runs after fusion"),
    }
}

/// Rebuild `c` by applying `f` to each immediate child (descending into binders unchanged — the
/// transform is de Bruijn-preserving). Mirrors the full `Cir` shape.
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
        Cir::Flat { .. } | Cir::FlatProj { .. } => unreachable!("flatten runs after fusion"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::IntPrimOp;

    /// `int-add` lowered: `λa.λb. a + b`.
    fn int_add() -> Cir {
        Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::IntPrim {
            op: IntPrimOp::Add,
            lhs: Box::new(Cir::Var(1)),
            rhs: Box::new(Cir::Var(0)),
        }))))
    }

    /// `int-double` lowered: `λa. a + a`.
    fn int_double() -> Cir {
        Cir::Lam(Box::new(Cir::IntPrim {
            op: IntPrimOp::Add,
            lhs: Box::new(Cir::Var(0)),
            rhs: Box::new(Cir::Var(0)),
        }))
    }

    /// The captured `foldr` wrapper `Lam(Lam(Lam(App(Fix(FOLDR_REC), Var0))))`.
    fn foldr_wrapper() -> Cir {
        Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::App(
            Box::new(Cir::Fix(Box::new(foldr_rec()))),
            Box::new(Cir::Var(0)),
        )))))))
    }

    /// The captured `map` wrapper `Lam(Lam(App(Fix(MAP_REC), Var0)))`.
    fn map_wrapper() -> Cir {
        Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::App(
            Box::new(Cir::Fix(Box::new(map_rec()))),
            Box::new(Cir::Var(0)),
        )))))
    }

    fn cons(h: Cir, t: Cir) -> Cir {
        Cir::con(ConName("cons".into()), vec![h, t])
    }
    fn nil() -> Cir {
        Cir::con(ConName("nil".into()), vec![])
    }

    /// `foldr int-add 0 (map int-double [1,2])` — the canonical listfold pipeline.
    fn foldr_of_map() -> Cir {
        let xs = cons(Cir::IntLit(1), cons(Cir::IntLit(2), nil()));
        let mapped = Cir::apply(map_wrapper(), [int_double(), xs]);
        Cir::apply(foldr_wrapper(), [int_add(), Cir::IntLit(0), mapped])
    }

    /// P7 RED: the canonical `foldr f z (map g xs)` fuses — the `map` wrapper disappears and the
    /// `foldr`'s list argument becomes the *raw* `xs`, with a synthesized combiner `λx.λacc. f (g x) acc`.
    #[test]
    fn foldr_of_map_fuses() {
        let fused = fuse(&foldr_of_map());

        // The result is still a 3-arg `foldr` application over the SAME wrapper.
        let (head, args) = fused.unapply();
        assert_eq!(args.len(), 3, "fused term is a 3-arg foldr application");
        assert!(is_foldr_wrapper(head), "fused head is the foldr wrapper");

        // Its list argument is now the raw input list (no `map` wrapper anywhere in the result).
        assert!(
            match_map_app(args[2]).is_none(),
            "fused foldr's list arg must not be a `map` application: {:?}",
            args[2]
        );
        assert!(
            !contains_map_wrapper(&fused),
            "the `map` wrapper must be gone from the fused term"
        );

        // The combiner is `λx.λacc. int-add (int-double x) acc`.
        let combiner = args[0];
        let expected = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::App(
            Box::new(Cir::App(
                Box::new(int_add()),
                Box::new(Cir::App(Box::new(int_double()), Box::new(Cir::Var(1)))),
            )),
            Box::new(Cir::Var(0)),
        )))));
        assert_eq!(
            combiner, &expected,
            "fused combiner is λx.λacc. f (g x) acc"
        );
    }

    /// A `map` whose result is bound to a `let` and consumed twice is NOT a direct argument of
    /// `foldr`, so it must be left un-fused (fusing would duplicate the producer). Here we model the
    /// multi-consumer site by feeding `foldr` a *variable* list (the let-bound map result): the
    /// fingerprint declines, and the term is returned unchanged.
    #[test]
    fn shared_map_is_not_fused() {
        // `foldr int-add 0 m` where `m` is a bound variable (Var0), not a `map` application.
        let term = Cir::apply(foldr_wrapper(), [int_add(), Cir::IntLit(0), Cir::Var(0)]);
        assert_eq!(
            fuse(&term),
            term,
            "a foldr over a non-map list is unchanged"
        );
    }

    /// A bare `map g xs` with no enclosing `foldr` is left untouched (no consumer to fuse into).
    #[test]
    fn bare_map_is_untouched() {
        let xs = cons(Cir::IntLit(1), nil());
        let m = Cir::apply(map_wrapper(), [int_double(), xs]);
        assert_eq!(fuse(&m), m, "a standalone map is unchanged");
    }

    /// Does any sub-term of `c` match the `map` wrapper fingerprint?
    fn contains_map_wrapper(c: &Cir) -> bool {
        if is_map_wrapper(c) {
            return true;
        }
        let mut found = false;
        for_each_child(c, &mut |child| found |= contains_map_wrapper(child));
        found
    }
}
