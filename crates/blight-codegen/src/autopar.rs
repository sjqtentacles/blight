//! Wave 10 / P4 — auto-parallelism candidate recognizer. **UNTRUSTED, analysis-only.**
//!
//! The roadmap's ask is to *auto-parallelize divide-and-conquer computations* using the shared-
//! nothing worker pool (`runtime/worker.c`, M17) and the P5 code-mobility substrate
//! (`crate::driver::code_table_source_for`, `bl_pool_submit_code`) that lets a worker be handed a
//! Blight closure (not just a native C callback). This module ships the **sound, checkable half** of
//! that ask — *finding* the candidates — as a pure `Cir → Vec<AutoparCandidate>` query. It is
//! deliberately **not** a rewrite pass: see "Why analysis-only" below for exactly what is missing to
//! turn a candidate into a safe parallel rewrite, and why shipping that rewrite today would be either
//! unsound or a large, unproven new codegen surface.
//!
//! ## What a candidate looks like
//! A **divide-and-conquer** site is a structural eliminator (`Cir::Fix(Lam(Case(Var(0), arms)))`,
//! exactly the shape [`crate::lower::lower_elim_fn`] emits and [`crate::elimloop`] already knows how
//! to recover) with a constructor arm whose induction hypothesis is used **two or more times** — i.e.
//! the arm recurses into 2+ independent, mutually-unreachable sub-structures and *combines* their
//! results, the way `tree-sum`'s `node l x r -> plus (tree-sum l) (plus x (tree-sum r))` combines the
//! left and right subtree sums. This is exactly the shape neither existing `Fix(Lam(Case))` consumer
//! can loop-ify:
//!   - [`crate::lower::build_elim_loop`] (P3/3a) requires **at most one** recursive field (a linear
//!     accumulator chain) so it can thread a single tail self-`Jump`; a second independent recursive
//!     call has nowhere tail-position to go.
//!   - [`crate::elimworklist::build_elim_worklist`] (P3/3b) likewise requires a single recursive field
//!     (it reverses the recursive spine onto a heap worklist, then folds it back); a second branch
//!     would need to fork the worklist itself, which it does not attempt.
//!
//! Because both declines, a genuine tree-shaped fold like `tree-sum` survives `elimloop` completely
//! unrewritten — its `Fix(Lam(Case))` reaches this pass's scan bit-for-bit as `lower_elim_fn` built
//! it, which is exactly what makes [`crate::elimloop::recover_canonical_eliminator`] (shared with
//! `elimloop`, not re-derived here) the right tool to recover its `(CtorShape, method)` pairs.
//!
//! ## Why analysis-only (the P4 go-bar's documented scope)
//! Turning a recognized candidate into an actual parallel rewrite — submit the left recursion to
//! [`crate::runtime`]'s worker pool via `bl_pool_submit_code` while the right recursion runs inline,
//! then join — needs three more things, none of which exist yet:
//!
//!   1. **A granularity cutoff.** Submitting a task at *every* recursive call (all the way to the
//!      leaves) is a guaranteed net loss: `runtime/worker.c`'s own design comment on
//!      `bl_pool_submit`/`bl_pool_join` notes each task pays a `malloc` + structural-copy serialize +
//!      mutex lock/condvar signal round trip, which swamps a tree-fold's many, tiny, near-leaf calls.
//!      A real rewrite needs a decrementing "fan-out budget" threaded as an extra parameter through
//!      every recursive call site of the recognized function, so parallel submission only happens
//!      near the root and falls back to an ordinary sequential call once the budget is exhausted —
//!      a genuine arity-changing codegen rewrite that has to compose correctly with `mono`/
//!      `closure`/`inline`, and does not exist in this codebase today.
//!   2. **A pool that cannot deadlock under recursive fan-out.** `worker.c`'s pool is fixed-size and
//!      purely blocking: `bl_pool_join` just sleeps on a condvar until the task's slot is filled. If
//!      a worker thread that is itself running a submitted task turns around and submits+joins its
//!      *own* sub-tasks to the *same* pool, every worker can end up blocked in `bl_pool_join`
//!      simultaneously with no thread ever free to actually drain the queue — a classic thread-pool
//!      deadlock. This is fine for the *single-level* fan-out `worker_code_test.c`/
//!      `share_nothing_worker_pool_parallel_map_reduce` exercise (the submitter is the main thread,
//!      never a worker), but unsound the moment a recognized site recurses more than one level deep
//!      while running *inside* a worker — exactly what a tree-shaped divide-and-conquer rewrite would
//!      do. Fixing this needs a work-stealing or "help while waiting" pool (a worker blocked in
//!      `bl_pool_join` should steal and run a queued task itself instead of sleeping) — a nontrivial
//!      `worker.c` rewrite that is itself unimplemented and unproven TSan-clean.
//!   3. **Proof the rewrite is bit-identical to the sequential fold.** The combiner (`plus` in
//!      `tree-sum`) must be associative/order-independent for a parallel evaluation to be
//!      observationally identical to the left-to-right sequential one on any effect it might
//!      perform (allocation order, non-associative float rounding, …). This pass's purity check
//!      (`cir_has_effect`) is a necessary but not sufficient proxy for that; a real rewrite would
//!      need the differential harness (`BL_NO_AUTOPAR`) to actually vary the two evaluation orders,
//!      which only makes sense once there is a second order to compare against.
//!
//! Items 1 and 2 are the genuine wall, not a matter of more code: shipping the naive unbounded-fan-out
//! rewrite today would be an unsound deadlock risk (task 2), and shipping a bounded one (task 1) is a
//! new, unproven codegen surface with no safety net. Per the roadmap's honest-scope convention (see
//! `docs/roadmap-post-m6.md`), P4 therefore ships the sound half — detection — as a pure analysis
//! (never touching the `Cir` it scans, so `BL_NO_AUTOPAR` is trivially bit-identical: nothing is ever
//! rewritten either way) and documents the rewrite as a **sharpened negative**, deferred behind the
//! `worker.c` work-stealing rewrite (item 2) it structurally depends on.
//!
//! ## Zero TCB
//! This pass never runs before kernel checking and never feeds anything back into it: it is a pure
//! read-only query over the untrusted backend `Cir`, called for its `BL_AUTOPAR_STATS` diagnostic
//! value only. A bug here can at worst mis-report or omit a candidate; it can never change what any
//! program computes.

use crate::elimloop::recover_canonical_eliminator;
use crate::ir::Cir;
use crate::lower::{cir_has_effect, visit_children};
use blight_kernel::ConName;

/// One recognized divide-and-conquer site: a constructor arm of a canonical structural eliminator
/// whose induction hypothesis is used `fanout` (>= 2) times — i.e. it recurses into `fanout`
/// independent sub-structures and combines their results. `pure` records whether the bare combining
/// method is free of [`Cir::Op`]/[`Cir::Handle`] (see module docs, deferral item 3): only a pure
/// combiner is even a *candidate* for a future order-changing rewrite, so an impure site is reported
/// (for `BL_AUTOPAR_STATS` visibility) but should never be acted on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AutoparCandidate {
    /// The constructor whose arm recurses `fanout` ways (e.g. `node` for a binary tree).
    pub ctor: ConName,
    /// How many independent recursive sub-results this arm's method combines (>= 2; a `fanout` of 1
    /// or 0 is exactly what `elimloop`'s 3a/3b transforms already handle, so it is never reported
    /// here — see module docs).
    pub fanout: usize,
    /// Whether the bare combining method is effect-free (a prerequisite — not a proof — for a
    /// future reordering to be sound; see module docs item 3).
    pub pure: bool,
}

/// Scan `c` for [`AutoparCandidate`]s. Intended to run once, over the whole lowered program, right
/// after [`crate::elimloop::elim_loop`] (so any linear/single-recursive-field site has already been
/// looped away, leaving only genuine tree-shaped folds for this scan to find) and before `unbox`/
/// `region`/`closure` (so the de Bruijn `Fix(Lam(Case(Var0, …)))` shape
/// [`recover_canonical_eliminator`] reads is still intact).
///
/// Never mutates or replaces `c` — see module docs "Why analysis-only". `enabled` is the
/// `BL_NO_AUTOPAR`-negated gate ([`crate::driver`]); when `false` this returns an empty list without
/// walking `c` at all (skipping the scan is always safe: it feeds nothing but a diagnostic).
pub fn analyze_gated(c: &Cir, enabled: bool) -> Vec<AutoparCandidate> {
    if !enabled {
        return Vec::new();
    }
    let mut found = Vec::new();
    walk(c, &mut found);
    found
}

/// Depth-first scan of every `Cir` node: at each node, try to recover a canonical eliminator (see
/// [`recover_canonical_eliminator`]) and record any `fanout >= 2` arm; then always recurse into every
/// child too (an eliminator's methods, or any other subterm, may itself contain a nested candidate —
/// e.g. a tree-of-trees fold, or a helper called from one arm that itself folds a tree).
fn walk(c: &Cir, found: &mut Vec<AutoparCandidate>) {
    if let Some((ctors, methods)) = recover_canonical_eliminator(c) {
        for (shape, method) in ctors.iter().zip(methods.iter()) {
            let fanout = shape.is_rec.iter().filter(|&&r| r).count();
            if fanout >= 2 {
                found.push(AutoparCandidate {
                    ctor: shape.name.clone(),
                    fanout,
                    pure: !cir_has_effect(method),
                });
            }
        }
    }
    visit_children(c, &mut |child| walk(child, found));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Alloc, Arm};
    use blight_kernel::ConName;

    /// Build the canonical `lower_elim_fn` output for a binary-tree `tree-sum`-shaped eliminator:
    /// `fix self. λscrut. case scrut of { leaf -> 0 ; node l x r -> plus (self l) (plus x (self r)) }`
    /// (a `NatPrim`-free stand-in combiner is irrelevant here — this test only exercises the
    /// structural recovery, not arithmetic). Field order for `node` is `[l: Rec, x: NonRec, r: Rec]`.
    fn tree_sum_fix() -> Cir {
        // `leaf` arm: 0 fields, body = `0` (an opaque placeholder value; content doesn't matter).
        let leaf_arm = Arm {
            con: ConName("leaf".to_string()),
            binders: 0,
            body: Cir::NatLit(0),
        };
        // `node` arm: 3 fields (l, x, r); self_idx = nfields + 1 = 4.
        // body = App(App(App(App(App(method, l=Var(2)), ih_l=App(Var(4),Var(2))), x=Var(1)), r=Var(0)), ih_r=App(Var(4),Var(0)))
        // `method` must itself be a closed `nfields + nrec`-ary (= 5) `Lam` chain (`recover_arm`
        // requires `count_leading_lams(head) >= nfields + nrec`, and, since it has no free
        // variables at all, embedding it directly (in place of the `2 + nfields`-shift
        // `lower_elim_fn` would apply to a *captured* method) is a no-op — a closed term's shift is
        // itself). Its body just references `ihl` (the innermost-but-one bound var) — content is
        // irrelevant, this test only exercises the structural recovery, not evaluation.
        let mut method_head = Cir::Var(3); // references `ihl`, the 2nd of the 5 method params
        for _ in 0..5 {
            method_head = Cir::Lam(Box::new(method_head));
        }
        let l = Cir::Var(2);
        let x = Cir::Var(1);
        let r = Cir::Var(0);
        let self_idx = 4;
        let ih_l = Cir::App(Box::new(Cir::Var(self_idx)), Box::new(l.clone()));
        let ih_r = Cir::App(Box::new(Cir::Var(self_idx)), Box::new(r.clone()));
        let body = Cir::App(
            Box::new(Cir::App(
                Box::new(Cir::App(
                    Box::new(Cir::App(
                        Box::new(Cir::App(Box::new(method_head), Box::new(l))),
                        Box::new(ih_l),
                    )),
                    Box::new(x),
                )),
                Box::new(r),
            )),
            Box::new(ih_r),
        );
        let node_arm = Arm {
            con: ConName("node".to_string()),
            binders: 3,
            body,
        };
        Cir::Fix(Box::new(Cir::Lam(Box::new(Cir::Case(
            Box::new(Cir::Var(0)),
            vec![leaf_arm, node_arm],
        )))))
    }

    #[test]
    fn recognizes_tree_shaped_fanout_two() {
        let c = tree_sum_fix();
        let found = analyze_gated(&c, true);
        assert_eq!(
            found.len(),
            1,
            "expected exactly one fanout>=2 candidate, got {found:?}"
        );
        assert_eq!(found[0].ctor, ConName("node".to_string()));
        assert_eq!(found[0].fanout, 2);
        assert!(found[0].pure, "the stand-in combiner has no Op/Handle node");
    }

    #[test]
    fn disabled_flag_short_circuits_to_empty() {
        let c = tree_sum_fix();
        assert_eq!(analyze_gated(&c, false), Vec::new());
    }

    #[test]
    fn linear_single_recursive_field_is_not_a_candidate() {
        // A `cons`-shaped arm with exactly one recursive field (a list fold) must NOT be reported:
        // that's exactly the P3/3a-or-3b territory, not P4's.
        let nil_arm = Arm {
            con: ConName("nil".to_string()),
            binders: 0,
            body: Cir::NatLit(0),
        };
        // `cons x xs -> f x (self xs)`; nfields=2, self_idx=3. `method` must be a closed
        // `nfields + nrec`-ary (= 2) `Lam` chain, per `recover_arm`'s arity check (see
        // `tree_sum_fix` above for why embedding a closed chain directly is valid).
        let mut method_head = Cir::Var(0);
        for _ in 0..2 {
            method_head = Cir::Lam(Box::new(method_head));
        }
        let x = Cir::Var(1);
        let xs = Cir::Var(0);
        let ih_xs = Cir::App(Box::new(Cir::Var(3)), Box::new(xs.clone()));
        let body = Cir::App(
            Box::new(Cir::App(
                Box::new(Cir::App(Box::new(method_head), Box::new(x))),
                Box::new(xs),
            )),
            Box::new(ih_xs),
        );
        let cons_arm = Arm {
            con: ConName("cons".to_string()),
            binders: 2,
            body,
        };
        let c = Cir::Fix(Box::new(Cir::Lam(Box::new(Cir::Case(
            Box::new(Cir::Var(0)),
            vec![nil_arm, cons_arm],
        )))));
        assert_eq!(analyze_gated(&c, true), Vec::new());
    }

    #[test]
    fn finds_nested_candidate_inside_a_let() {
        let inner = tree_sum_fix();
        let c = Cir::Let(Box::new(Cir::NatLit(0)), Box::new(inner));
        let found = analyze_gated(&c, true);
        assert_eq!(found.len(), 1);
    }

    #[test]
    fn flags_impure_combiner_as_not_pure() {
        // Same shape as `tree_sum_fix` but the `node` method performs an effect: `perform "IO" "print" ...`
        // wrapped around the combine — recovery must still succeed (the effect sits inside the
        // *applied* method reference position via Var, not reachable structurally since `method_head`
        // is just a Var placeholder) — so instead we inline an actual method body with an Op node
        // directly in the arm (bypassing the `head` abstraction) to exercise `cir_has_effect`.
        //
        // Simplest reliable way: build node arm whose `method` (the un-applied head, i.e. what
        // `recover_arm` unshifts) is itself a `Lam` chain ending in an `Op`, applied in place instead
        // of referencing an outside `Var`. Since `recover_arm` requires `head` to reference no
        // eliminator binder, embed the full lambda literally as the head expression.
        let self_idx = 4usize;
        let l = Cir::Var(2);
        let x = Cir::Var(1);
        let r = Cir::Var(0);
        let ih_l = Cir::App(Box::new(Cir::Var(self_idx)), Box::new(l.clone()));
        let ih_r = Cir::App(Box::new(Cir::Var(self_idx)), Box::new(r.clone()));
        // `method` = λl. λihl. λx. λr. λihr. perform "IO" "print" ihl  -- an effectful "combiner".
        let mut method = Cir::Op {
            effect: "IO".to_string(),
            op: "print".to_string(),
            arg: Box::new(Cir::Var(3)),
        };
        for _ in 0..5 {
            method = Cir::Lam(Box::new(method));
        }
        // Shift the method up by `2 + nfields` (=5) as `lower_elim_fn` would, so `recover_arm`'s
        // un-shift round-trips back to a closed-enough term. Since `method` here has no free `Var`s
        // referencing indices < 5 that would collide, a manual re-index isn't needed for correctness
        // of the *shape* check; we only need `head` (after peeling the spine) to be exactly this
        // `Lam` chain untouched by field/self/scrut indices, which it already is (all its `Var`s are
        // bound by its own five `Lam`s).
        let body = Cir::App(
            Box::new(Cir::App(
                Box::new(Cir::App(
                    Box::new(Cir::App(
                        Box::new(Cir::App(Box::new(method), Box::new(l))),
                        Box::new(ih_l),
                    )),
                    Box::new(x),
                )),
                Box::new(r),
            )),
            Box::new(ih_r),
        );
        let node_arm = Arm {
            con: ConName("node".to_string()),
            binders: 3,
            body,
        };
        let leaf_arm = Arm {
            con: ConName("leaf".to_string()),
            binders: 0,
            body: Cir::NatLit(0),
        };
        let c = Cir::Fix(Box::new(Cir::Lam(Box::new(Cir::Case(
            Box::new(Cir::Var(0)),
            vec![leaf_arm, node_arm],
        )))));
        let found = analyze_gated(&c, true);
        assert_eq!(found.len(), 1);
        assert!(!found[0].pure, "the combiner performs an IO effect");
    }

    // Silence an unused-import warning if `Alloc` ever stops being needed by a future edit here.
    #[allow(dead_code)]
    fn _uses_alloc(_: Alloc) {}
}
