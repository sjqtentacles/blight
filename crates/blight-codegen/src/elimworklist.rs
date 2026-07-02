//! `elimworklist.rs` — the P3 (3b) non-tail linear fold → reverse-then-fold transform.
//!
//! [`crate::elimloop`] first tries the (3a) [`crate::lower::build_elim_loop`] tail-accumulator loop.
//! When that declines a *non-tail* linear fold — the induction hypothesis is consumed by a combining
//! operation rather than passed on in tail position, e.g. `length`/`sum-list`/`count-up`, so the
//! recovered method has **no** accumulator lambda (`kk == 0`) — the eager `Fix(Lam(Case))` still
//! descends the whole spine on the C stack and SIGSEGVs at depth.
//!
//! ## The reverse-then-fold decomposition
//! A non-tail linear catamorphism
//! ```text
//!   f (C_rec flds r) = g flds (f r)          -- IH `f r` consumed non-tail by the combiner `g`
//!   f  C_base        = z
//! ```
//! computes `g flds_1 (g flds_2 (… (g flds_n z)))`. Because the data type is **single-recursive-field**
//! the spine *is itself* a stack: we first `rev` it into a same-typed copy (its own constructors,
//! deepest node outermost) threading an accumulator, then `fold` that reversed copy left-to-right
//! seeding `z` and applying the original combiner `g` at each node. Both `rev` and `fold` are
//! *tail-accumulator* catamorphisms — exactly the (3a) shape — so handing them to
//! [`crate::lower::build_elim_loop`] makes each an O(1)-native-stack `Tail::Jump` loop. The composite
//! `λx. fold_loop (rev_loop x C_base) z` therefore runs in bounded stack while computing the identical
//! value (the combiner is applied to the same fields in the same order).
//!
//! ## Why this is sound
//! `rev` rebuilds each node with the data's *own* constructor (preserving its tag and non-recursive
//! fields, replacing only the recursive child with the reversed-so-far accumulator), so no new runtime
//! type is introduced and the precise GC tracer is unaffected. The decomposition reorders nothing
//! observable for **pure** combiners, so we refuse any method containing an effect. We also require the
//! original combiner to consume the recursion **only through the IH** (never touching the recursive
//! sub-structure directly), since the reversed-and-folded form no longer has that sub-structure in
//! hand. Unsupported shapes (trees, field-carrying or multiple base constructors, effectful or
//! structure-touching combiners) decline to `None`, leaving the eager form as the bit-identical
//! reference.
//!
//! Zero TCB: a pure `Cir → Cir` rewrite downstream of kernel checking, gated by `BL_NO_ELIMLOOP` and
//! proven observationally invisible by the differential matrix.

use crate::ir::{Alloc, Cir};
use crate::lower::{
    build_elim_loop, cir_has_effect, cir_uses, count_leading_lams, shift_free, CtorShape,
};

/// Per-constructor layout of a synthetic `k`-accumulator (`build_elim_loop`-shaped) method's leading
/// binders, in outer→inner declaration order: `Field(j) [, Ih(j)]` for each field, then `k` `Acc`s.
/// Returns the binder count `nb` and helpers to read field / IH / accumulator binders by their
/// body-relative de Bruijn index (`nb - 1 - position`).
struct Layout {
    nb: usize,
    /// `nb - 1 - position_of(Field(j))` for each field `j`.
    field_idx: Vec<usize>,
    /// `nb - 1 - position_of(Ih(rec_field))`, if there is a recursive field.
    ih_idx: Option<usize>,
}

impl Layout {
    fn new(is_rec: &[bool], k: usize) -> Self {
        let nfields = is_rec.len();
        let nrec = is_rec.iter().filter(|&&r| r).count();
        let nb = nfields + nrec + k;
        let mut field_pos = vec![0usize; nfields];
        let mut ih_pos: Option<usize> = None;
        let mut p = 0usize;
        for (j, &rec) in is_rec.iter().enumerate() {
            field_pos[j] = p;
            p += 1;
            if rec {
                ih_pos = Some(p);
                p += 1;
            }
        }
        let field_idx = field_pos.iter().map(|&fp| nb - 1 - fp).collect();
        let ih_idx = ih_pos.map(|ip| nb - 1 - ip);
        Layout {
            nb,
            field_idx,
            ih_idx,
        }
    }
}

/// Wrap `body` in `nb` leading `Cir::Lam` binders, yielding a `build_elim_loop`-shaped bare method.
fn lams(nb: usize, body: Cir) -> Cir {
    let mut c = body;
    for _ in 0..nb {
        c = Cir::Lam(Box::new(c));
    }
    c
}

/// Try to rebuild a non-tail **linear** catamorphism as a bounded-stack reverse-then-fold composite.
/// Returns `None` (fall back to the eager `lower_elim_fn` form, the bit-identical reference) whenever
/// the shape is unsupported or contains an effect / direct sub-structure use that the decomposition
/// cannot preserve.
pub(crate) fn build_elim_worklist(ctors: &[CtorShape], methods: &[Cir]) -> Option<Cir> {
    if ctors.is_empty() || ctors.len() != methods.len() {
        return None;
    }

    // Classify constructors. We support exactly one **nullary** base constructor (`nrec == 0`,
    // no fields) and any number of **single-recursive-field** constructors (`nrec == 1`); trees
    // (`nrec >= 2`), field-carrying or multiple base constructors are out of scope here.
    let mut base_idx: Option<usize> = None;
    for ctor in ctors {
        let nrec = ctor.is_rec.iter().filter(|&&r| r).count();
        match nrec {
            0 => {
                if !ctor.is_rec.is_empty() {
                    return None; // field-carrying base: rev would drop its fields
                }
                if base_idx.is_some() {
                    return None; // more than one base constructor
                }
            }
            1 => {}
            _ => return None, // tree
        }
    }
    for (idx, ctor) in ctors.iter().enumerate() {
        if ctor.is_rec.iter().all(|&r| !r) {
            base_idx = Some(idx);
        }
    }
    let base_idx = base_idx?;

    // No method may perform an effect: the reverse-then-fold reorders evaluation, observationally
    // invisible only for pure combiners.
    if methods.iter().any(cir_has_effect) {
        return None;
    }

    // Validate every recursive arm and synthesize the `rev` and `fold` methods.
    let mut rev_methods: Vec<Cir> = Vec::with_capacity(ctors.len());
    let mut fold_methods: Vec<Cir> = Vec::with_capacity(ctors.len());
    for (idx, ctor) in ctors.iter().enumerate() {
        let nrec = ctor.is_rec.iter().filter(|&&r| r).count();
        if nrec == 0 {
            // Base arm of `rev`/`fold`: `λacc. acc` (return the threaded accumulator).
            rev_methods.push(Cir::Lam(Box::new(Cir::Var(0))));
            fold_methods.push(Cir::Lam(Box::new(Cir::Var(0))));
            continue;
        }

        let is_rec = &ctor.is_rec;
        let nfields = is_rec.len();
        let rec_field = is_rec.iter().position(|&r| r).unwrap();

        // The original combiner is a plain (`k == 0`) method `λ(fields, ih). body`. If it has extra
        // leading lambdas it was the (3a) accumulator shape `build_elim_loop` should have taken; if
        // it has fewer it is malformed. Either way, decline.
        let nb_orig = nfields + nrec; // == nfields + 1
        if count_leading_lams(&methods[idx]) != nb_orig {
            return None;
        }
        // The combiner must consume the recursion only through its IH, never the recursive
        // sub-structure directly (the reversed-and-folded form no longer holds that sub-structure).
        let orig = Layout::new(is_rec, 0);
        let body_o = peel(&methods[idx], nb_orig);
        if cir_uses(body_o, orig.field_idx[rec_field]) {
            return None;
        }

        // Synthetic `rev`/`fold` methods are the (3a) tail-accumulator shape with `k == 1`.
        let lay = Layout::new(is_rec, 1);
        let acc = || Cir::Var(0); // the single accumulator (innermost binder)
        let ih = || Cir::Var(lay.ih_idx.unwrap());
        let field = |j: usize| Cir::Var(lay.field_idx[j]);

        // rev: `λ(fields, ih, acc). ih (C_rec fields[rec := acc])` — rebuild this node with the
        // recursive child replaced by the reversed-so-far accumulator, then recurse (tail) on the
        // real recursive child threading that rebuilt node.
        let rebuilt: Vec<Cir> = (0..nfields)
            .map(|j| if j == rec_field { acc() } else { field(j) })
            .collect();
        let rev_body = Cir::App(
            Box::new(ih()),
            Box::new(Cir::Con(ctor.name.clone(), rebuilt, Alloc::Gc)),
        );
        rev_methods.push(lams(lay.nb, rev_body));

        // fold: `λ(fields, ih, acc). ih (g fields[rec := _] acc)` — apply the original combiner `g`
        // to the non-recursive fields and the accumulator (in the IH slot), then recurse (tail) on
        // the rest threading that combined value. `g`'s captured free variables are slid out past
        // `fold`'s own `nb` binders.
        let g = shift_free(&methods[idx], lay.nb);
        let mut applied = g;
        for (j, &rec) in is_rec.iter().enumerate() {
            let arg = if j == rec_field {
                Cir::Erased // the recursive sub-structure: verified unused by `g`
            } else {
                field(j)
            };
            applied = Cir::App(Box::new(applied), Box::new(arg));
            if rec {
                // The IH slot of `g` receives the accumulated result.
                applied = Cir::App(Box::new(applied), Box::new(acc()));
            }
        }
        let fold_body = Cir::App(Box::new(ih()), Box::new(applied));
        fold_methods.push(lams(lay.nb, fold_body));
    }

    // Loop-ify both phases via the proven (3a) transform. Both are tail-accumulator catamorphisms,
    // so this must succeed; if it somehow declines, fall back to the eager form.
    let rev_loop = build_elim_loop(ctors, &rev_methods)?;
    let fold_loop = build_elim_loop(ctors, &fold_methods)?;

    // Compose: `λx. fold_loop (rev_loop x C_base) z`. The replacement presents the same `T -> R`
    // arity as the eager `Fix(Lam(Case))` it stands in for. `rev_loop`/`fold_loop`/`z` are placed
    // under the fresh `λx`, so their free variables (the original captured combiner/base captures)
    // slide up by one.
    let base_ctor = Cir::Con(ctors[base_idx].name.clone(), Vec::new(), Alloc::Gc);
    let z = shift_free(&methods[base_idx], 1);
    let reversed = Cir::App(
        Box::new(Cir::App(
            Box::new(shift_free(&rev_loop, 1)),
            Box::new(Cir::Var(0)),
        )),
        Box::new(base_ctor),
    );
    let folded = Cir::App(
        Box::new(Cir::App(
            Box::new(shift_free(&fold_loop, 1)),
            Box::new(reversed),
        )),
        Box::new(z),
    );
    Some(Cir::Lam(Box::new(folded)))
}

/// Peel exactly `n` leading `Cir::Lam` binders off `c` (callers have already verified the count).
fn peel(c: &Cir, n: usize) -> &Cir {
    let mut cur = c;
    for _ in 0..n {
        match cur {
            Cir::Lam(b) => cur = b,
            _ => return cur,
        }
    }
    cur
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::ConName;

    /// `count-up`'s recovered shape: a `Nat` with a nullary `Zero` base and a single-recursive-field
    /// `Succ` whose combiner `λk.λih. Succ ih` consumes the recursion only through the IH.
    fn count_up_methods() -> (Vec<CtorShape>, Vec<Cir>) {
        let ctors = vec![
            CtorShape {
                name: ConName("Zero".into()),
                is_rec: vec![],
            },
            CtorShape {
                name: ConName("Succ".into()),
                is_rec: vec![true],
            },
        ];
        // Zero -> Zero ; Succ k -> Succ (count-up k), i.e. method `λk.λih. Succ ih`.
        let zero_method = Cir::Con(ConName("Zero".into()), vec![], Alloc::Gc);
        let succ_method = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Con(
            ConName("Succ".into()),
            vec![Cir::Var(0)],
            Alloc::Gc,
        )))));
        (ctors, vec![zero_method, succ_method])
    }

    /// (3b) the non-tail linear `count-up` fold rebuilds as `λx. fold_loop (rev_loop x Zero) Zero`,
    /// where each of `rev_loop`/`fold_loop` is a (3a) `build_elim_loop` wrapper (`λscrut.λacc. fix …`).
    #[test]
    fn build_elim_worklist_decomposes_linear_fold() {
        let (ctors, methods) = count_up_methods();
        // 3a must decline this (no accumulator): the IH is consumed non-tail under `Succ`.
        assert!(
            build_elim_loop(&ctors, &methods).is_none(),
            "count-up is a non-tail fold, not a tail-accumulator loop"
        );

        let composite =
            build_elim_worklist(&ctors, &methods).expect("count-up matches the 3b linear shape");

        // `λx. (fold_loop (rev_loop x Zero) Zero)`
        let Cir::Lam(body) = &composite else {
            panic!("expected `λx. …`, got {composite:?}");
        };
        let Cir::App(fold_app, z) = body.as_ref() else {
            panic!("expected `fold_loop reversed z`, got {body:?}");
        };
        assert_eq!(
            **z,
            Cir::Con(ConName("Zero".into()), vec![], Alloc::Gc),
            "fold is seeded with the base value `Zero`"
        );
        let Cir::App(fold_loop, reversed) = fold_app.as_ref() else {
            panic!("expected `fold_loop reversed`, got {fold_app:?}");
        };
        // reversed = `rev_loop x Zero`
        let Cir::App(rev_app, base_ctor) = reversed.as_ref() else {
            panic!("expected `rev_loop x Zero`, got {reversed:?}");
        };
        assert_eq!(
            **base_ctor,
            Cir::Con(ConName("Zero".into()), vec![], Alloc::Gc),
            "rev is seeded with the empty base constructor `Zero`"
        );
        let Cir::App(rev_loop, x) = rev_app.as_ref() else {
            panic!("expected `rev_loop x`, got {rev_app:?}");
        };
        assert_eq!(**x, Cir::Var(0), "rev folds the function's argument `x`");

        // Both phases are (3a) loop wrappers: `λscrut.λacc. (fix loop. λstate. case …) init`.
        for (label, loopw) in [("rev", rev_loop.as_ref()), ("fold", fold_loop.as_ref())] {
            assert_eq!(
                count_leading_lams(loopw),
                2,
                "{label}_loop is a `λscrut.λacc.` (k=1) wrapper"
            );
            let mut inner = loopw;
            for _ in 0..2 {
                let Cir::Lam(b) = inner else { unreachable!() };
                inner = b;
            }
            let Cir::App(fixfn, _init) = inner else {
                panic!("{label}_loop body is `LOOP init`, got {inner:?}");
            };
            assert!(
                matches!(fixfn.as_ref(), Cir::Fix(_)),
                "{label}_loop drives a `fix` self-jump loop"
            );
        }
    }

    /// (3b) guards: trees, field-carrying or multiple base constructors, and effectful or
    /// structure-touching combiners decline (leaving the eager bit-identical form).
    #[test]
    fn build_elim_worklist_declines_unsupported_shapes() {
        // Binary tree (two recursive fields) — the worklist's linear decomposition does not apply.
        let tree = vec![CtorShape {
            name: ConName("Node".into()),
            is_rec: vec![true, true],
        }];
        assert!(build_elim_worklist(&tree, &[Cir::Lam(Box::new(Cir::Var(0)))]).is_none());

        // A combiner that touches the recursive sub-structure directly (`λk.λih. Succ k`, using the
        // field `k` not the IH) cannot be reversed-and-folded.
        let ctors = vec![
            CtorShape {
                name: ConName("Zero".into()),
                is_rec: vec![],
            },
            CtorShape {
                name: ConName("Succ".into()),
                is_rec: vec![true],
            },
        ];
        let uses_field = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Con(
            ConName("Succ".into()),
            vec![Cir::Var(1)], // the field `k`, not the IH (Var 0)
            Alloc::Gc,
        )))));
        let zero = Cir::Con(ConName("Zero".into()), vec![], Alloc::Gc);
        assert!(
            build_elim_worklist(&ctors, &[zero, uses_field]).is_none(),
            "a combiner reading the recursive sub-structure directly must decline"
        );
    }
}
