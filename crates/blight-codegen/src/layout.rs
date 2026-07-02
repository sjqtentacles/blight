//! A1' — whole-program, post-monomorphization layout flattening.
//!
//! [`crate::flatten`] (A1) lands the *proven* escaping-product flattening substrate (`Cir::Flat` /
//! `Cir::FlatProj` + the drill-to-leaf soundness contract) but runs **once, pre-monomorphization**,
//! on the single entry term. As the A1 disposition (`docs/roadmap-post-m6.md`) documents, that local
//! cut is *strictly subsumed by M27 [`crate::unbox`]* on the corpus: the only shape it can prove
//! safe locally — a `let`-bound literal product all of whose uses drill to a leaf — is exactly the
//! shape `unbox` already deletes outright, and the genuine win (a nested product that **escapes** a
//! function / is exposed only after specialization + inlining) is invisible to a single pre-mono
//! pass.
//!
//! This pass is the documented **A1′ follow-up**: it re-applies the *same proven* drill-to-leaf
//! transform across **every function body** of the **post-monomorphization, post-inline** program,
//! so a `let`-bound nested product that mono/inline has just *co-located* with its drill-to-leaf
//! readers (the producer function having been specialized/β-inlined into the consumer) is flattened
//! into one wider all-pointer object — even though no single pre-mono view ever saw the redex.
//!
//! ## Why this is bit-identical (zero new trust)
//! It calls [`crate::flatten::flatten`] verbatim — the identical, differentially-gated transform
//! whose soundness contract (flatten only a pure literal product whose binder is *never* read whole
//! and *never* `case`-matched, rewriting each projection chain to one `FlatProj` at the resolved
//! physical offset) is unchanged. The precise GC traces the wider all-pointer object by `nfields`
//! with **no collector change** (A1d). Running the proven, idempotent transform a second time at a
//! later pipeline stage cannot change a program's meaning; it can only flatten *more* of the redexes
//! the contract already admits. The whole pass is gated by the same `BL_NO_FLATTEN` switch and is in
//! the B1 differential matrix, so a miscompile would surface as a wrong *number*, never a false
//! *proof*. No kernel / elaborator change (`git diff crates/blight-kernel` empty).
//!
//! Set `BL_LAYOUT_STATS=1` to print, to stderr, how many function bodies the pass rewrote.

use crate::ir::{Func, Program};

/// Run whole-program layout flattening over a post-monomorphization program. Pure and total: maps
/// the proven [`crate::flatten::flatten`] over `entry` and every `Func.body`, leaving names and
/// recursion flags intact.
pub fn layout(prog: &Program) -> Program {
    let stats = std::env::var_os("BL_LAYOUT_STATS").is_some();
    if std::env::var_os("BL_LAYOUT_DUMP").is_some() {
        eprintln!("[layout-in] entry={:#?}", prog.entry);
        for f in &prog.funcs {
            eprintln!(
                "[layout-in] fn {} recursive={} = {:#?}",
                f.name, f.recursive, f.body
            );
        }
    }
    // Each post-mono transform is gated by the *same* off-switch as its pre-mono sibling, so the B1
    // differential matrix proves the whole pipeline (pre- + post-mono) bit-identical under that flag.
    //   - `BL_NO_UNBOX`  : post-mono SRA (delete the `Proj`-of-`Con`/`Case`-of-`Con` chains that
    //                      monomorphization + inlining expose but pre-mono `unbox` never saw).
    //   - `BL_NO_FLATTEN`: post-mono escaping-product flattening (the A1′ widening).
    // `unbox` runs first (it *deletes*; strictly better than flattening) and leaves no `Flat` nodes
    // for the subsequent `flatten` pass; both are proven, total, idempotent `Cir→Cir` transforms.
    let do_unbox = std::env::var_os("BL_NO_UNBOX").is_none();
    let do_flatten = std::env::var_os("BL_NO_FLATTEN").is_none();
    let mut unboxed = 0usize;
    let mut flattened = 0usize;

    let rewrite = |c: &crate::ir::Cir, ub: &mut usize, fl: &mut usize| -> crate::ir::Cir {
        let mut out = c.clone();
        if do_unbox {
            let u = crate::unbox::unbox(&out);
            if u != out {
                *ub += 1;
            }
            out = u;
        }
        if do_flatten {
            let f = crate::flatten::flatten(&out);
            if f != out {
                *fl += 1;
            }
            out = f;
        }
        out
    };

    let entry = rewrite(&prog.entry, &mut unboxed, &mut flattened);
    let funcs = prog
        .funcs
        .iter()
        .map(|f| Func {
            name: f.name.clone(),
            recursive: f.recursive,
            body: rewrite(&f.body, &mut unboxed, &mut flattened),
        })
        .collect();

    if stats {
        eprintln!("BL_LAYOUT_STATS unboxed_bodies={unboxed} flattened_bodies={flattened}");
    }
    Program { funcs, entry }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Alloc, Cir, FlatField, Func, Program};
    use blight_kernel::ConName;

    /// A `let`-bound nested tuple whose binder is read only by drill-to-leaf projections is flattened
    /// to one `Flat` + `FlatProj`s — the same proven shape `flatten` fires on, now reached through the
    /// whole-program `Program` driver (so it fires inside lifted function bodies post-mono).
    fn nested_drill_body() -> Cir {
        // let p = ((a, b), c) in fst (fst p)  -- de Bruijn: p = Var 0 in body
        let inner = Cir::Tuple(vec![Cir::Var(10), Cir::Var(11)], Alloc::Gc);
        let parent = Cir::Tuple(vec![inner, Cir::Var(12)], Alloc::Gc);
        let body = Cir::Proj(0, Box::new(Cir::Proj(0, Box::new(Cir::Var(0)))));
        Cir::Let(Box::new(parent), Box::new(body))
    }

    #[test]
    fn deletes_local_drill_inside_a_function_body() {
        // With the default flags the post-mono pass runs `unbox` first, which *deletes* a local
        // `let p = ((a,b),c) in fst (fst p)` outright (product β: it folds to the leaf `a`) — strictly
        // better than flattening. So the function body's allocation is gone, leaving just the leaf.
        let prog = Program {
            funcs: vec![Func {
                name: "f".into(),
                recursive: false,
                body: nested_drill_body(),
            }],
            entry: Cir::Var(0),
        };
        let out = layout(&prog);
        assert!(
            matches!(out.funcs[0].body, Cir::Var(_)),
            "expected the nested product to be deleted to its leaf var, got {:?}",
            out.funcs[0].body
        );
    }

    #[test]
    fn deletes_local_drill_in_entry_term_too() {
        let prog = Program {
            funcs: vec![],
            entry: nested_drill_body(),
        };
        let out = layout(&prog);
        assert!(matches!(out.entry, Cir::Var(_)));
    }

    /// A parent that escapes whole (returned bare) is left alone — the proven contract declines, so
    /// the whole-program driver declines too (no layout disagreement can arise).
    #[test]
    fn declines_when_binder_escapes_whole() {
        let parent = Cir::Tuple(
            vec![
                Cir::Tuple(vec![Cir::Var(10), Cir::Var(11)], Alloc::Gc),
                Cir::Var(12),
            ],
            Alloc::Gc,
        );
        let prog = Program {
            funcs: vec![],
            entry: Cir::Let(Box::new(parent), Box::new(Cir::Var(0))),
        };
        let out = layout(&prog);
        assert!(matches!(out.entry, Cir::Let(v, _) if matches!(v.as_ref(), Cir::Tuple(..))));
    }

    /// Idempotent: a program already containing `Flat`/`FlatProj` is unchanged by a second run.
    #[test]
    fn idempotent_on_already_flat() {
        let prog = Program {
            funcs: vec![],
            entry: nested_drill_body(),
        };
        let once = layout(&prog);
        let twice = layout(&once);
        assert_eq!(once, twice);
    }

    // Keep the unused imports honest for the test module.
    #[allow(unused_imports)]
    use {ConName as _ConName, FlatField as _FlatField};
}
