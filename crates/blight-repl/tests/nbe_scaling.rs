//! Arc N / N5 rung-0 scaling harness (docs/roadmap-v0.1.md §N5): pins the *growth law* of
//! `do_elim`'s induction-hypothesis count on the canonical micro-reproducer — a match-forced
//! `nat-eq k k` — in both engines, via deterministic counters rather than wall-clock (slopes,
//! not timeouts: a fixed-size run under a kill budget is a censored observation that cannot
//! distinguish exponential from polynomial).
//!
//! Post-N5 law (the dead-IH fix landed: `do_elim` skips IHs whose receiving method provably
//! discards its binder): the IH count is LINEAR in k — the eager-exponential pre-N5 law
//! (measured here as ×~2.0 per +1: kernel [361, 618, 1131, 2156, 4205]) collapsed to +1 per
//! codepoint (kernel [7..11] over baseline, recheck [8..12]). These pins hold the fix in place:
//! any regression toward eager IHs turns the growth factor back toward 2.0 and fails loudly.

use blight_elab::{ElabEnv, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Elaborate a program that forces the kernel to *evaluate* `nat-eq k k` definitionally: the
/// refl proof `(the (Path Bool (nat-eq k k) true) (plam (i) true))` type-checks only by running
/// `nat-eq k k` to `true` inside the kernel's conversion check. Returns the kernel IH count for
/// exactly that check (counter reset before, read after).
fn kernel_ih_count(k: u64) -> u64 {
    let src = format!(
        "(load \"std/order.bl\")\n(the (Path Bool (nat-eq {k} {k}) true) (plam (i) true))"
    );
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut env = ElabEnv::new();
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            let _ = blight_kernel::normalize::take_ih_computed();
            prog.run(&src).expect("nat-eq refl program type-checks");
            blight_kernel::normalize::take_ih_computed()
        })
        .expect("spawn scaling thread")
        .join()
        .expect("scaling thread panicked")
}

/// Re-check the same judgement through the independent engine and return ITS IH count.
fn recheck_ih_count(k: u64) -> u64 {
    let src = format!(
        "(load \"std/order.bl\")\n(define n5probe (Path Bool (nat-eq {k} {k}) true) (plam (i) true))"
    );
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut env = ElabEnv::new();
            {
                let mut prog = Program::with_resolver(&mut env, prelude_resolver);
                prog.run(&src).expect("nat-eq refl program type-checks");
            }
            let (term, ty) = {
                let t = env.global_term("n5probe").expect("probe defined").clone();
                let ty = env.global_type("n5probe").expect("probe typed").clone();
                (t, ty)
            };
            let j = blight_kernel::Judgement::HasType { term, ty };
            let _ = blight_recheck::take_ih_computed();
            let _ = blight_recheck::recheck_judgement(env.signature(), &j);
            blight_recheck::take_ih_computed()
        })
        .expect("spawn scaling thread")
        .join()
        .expect("scaling thread panicked")
}

/// The growth law across one +1 step of the codepoint-sized input, as a rational factor.
fn growth(a: u64, b: u64) -> f64 {
    b as f64 / a.max(1) as f64
}

/// Post-N5 pin (kernel): the IH count grows LINEARLY on match-forced `nat-eq k k` (the dead-IH
/// skip removes the discarded inner-match IHs that made it exponential).
///
/// The kernel counter brackets the whole `Program::run` (the `(load "std/order.bl")` elaboration
/// contributes a k-independent constant), so the k=1 count is subtracted as baseline before
/// fitting the growth law.
#[test]
fn kernel_ih_count_linear_per_codepoint_post_n5() {
    let baseline = kernel_ih_count(1);
    let counts: Vec<u64> = (8..=12).map(|k| kernel_ih_count(k) - baseline).collect();
    for w in counts.windows(2) {
        let g = growth(w[0], w[1]);
        assert!(
            (0.9..=1.3).contains(&g),
            "post-N5 law: kernel IH count (load-baseline-subtracted) must stay linear per +1 \
             codepoint (eager-IH regression doubles it), got factor {g:.3} across {counts:?} \
             (baseline {baseline})"
        );
    }
}

/// Post-N5 pin (independent re-checker): same linear law, independently counted — the two
/// engines shared the defect at parity and now share the fix's law (each via its own
/// implementation).
#[test]
fn recheck_ih_count_linear_per_codepoint_post_n5() {
    let counts: Vec<u64> = (8..=12).map(recheck_ih_count).collect();
    for w in counts.windows(2) {
        let g = growth(w[0], w[1]);
        assert!(
            (0.9..=1.3).contains(&g),
            "post-N5 law: recheck IH count must stay linear per +1 codepoint (eager-IH \
             regression doubles it), got factor {g:.3} across {counts:?}"
        );
    }
}
