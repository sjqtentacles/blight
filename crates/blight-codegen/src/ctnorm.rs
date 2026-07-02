//! P6.2 compile-time normalization (verified constant folding / partial evaluation).
//!
//! For a **closed, effect-free** sub-`Term` we fold it to its normal form *by calling the kernel's
//! own trusted evaluator* ([`blight_kernel::normalize::eval`] + [`quote`]) at compile time, then
//! splice the result back before lowering. This is the most elegant item in the perf plan: the
//! optimizer's correctness for constant folding **is the kernel's own reduction rule**. We do not
//! add a second evaluator, so the trusted computing base does not grow; if the optimizer wires it
//! up wrong, the B1 differential A/B matrix catches it (gated by `BL_NO_CTNORM`).
//!
//! **Soundness.** Replacing a *closed* term `t` with `quote(eval(t))` is sound because a closed term
//! denotes the same value in every context (referential transparency over a total, pure fragment).
//! We only ever normalize a subterm that (a) has no free de Bruijn variable (so `eval` under the
//! empty environment is well-defined and the value is context-independent) and (b) is *pure*: it
//! contains no effect/partiality/foreign/cubical node — no `Op`/`Handle`/`Force`/`Now`/`Later`/
//! `Delay`/`Foreign` and none of the Kan/path formers. Excluding `Force`/`Later` also excludes the
//! one divergence surface (the Capretta delay monad, spec §4.5), so `eval` on a candidate always
//! terminates (the rest of the fragment is total).
//!
//! **Bounded cost (the step cap) — and why we exclude `Elim`.** `eval` is the *kernel's*, and it has
//! no fuel knob; we cannot add one without growing the TCB. A step cap on a fuel-less evaluator is
//! impossible to impose *deterministically* from outside (a wall-clock timeout would make builds
//! non-reproducible). The cost of normalizing a term is dominated by **recursion**, and in the total
//! core the *only* source of unbounded recursion is the inductive eliminator `Elim` (general
//! recursion arrives via the delay monad `Later`/`Force`, which we already exclude as impure). A
//! syntactically tiny `Elim` can drive an astronomically large reduction — e.g. `foldr (+) 0
//! (build-int-ones n800)` evaluates an 800-element list at compile time, and `factorial 20` an
//! exponential one — with no *static* bound on the work. We therefore make CTNORM provably cheap by
//! refusing any candidate that contains an `Elim`: what remains (β, projection, `IntPrim` literal
//! arithmetic, constructor/pair building) is strongly normalizing with cost bounded by the candidate
//! size. Combined with the AST-node `INPUT_CAP`, the size-non-increasing output rule, and the
//! `OUTPUT_CAP`, every fold is O(size) and the resulting term never grows (the "fewer ops" win, and
//! the unary-`Nat`-blowup guard the plan calls out). Folding recursive computations to a literal
//! (`factorial 4 → 24`) is the natural next step but needs a genuine *step-metered* evaluator (a
//! fuel-bounded reducer); since the kernel exposes none and we will not grow the TCB, that is left
//! out. On any miss we fall back to the original term. The traversal is top-down: a too-big or
//! `Elim`-bearing closed term is not folded whole, but its smaller eligible sub-pieces still are.

use blight_kernel::value::Env;
use blight_kernel::{Signature, Term};
use std::rc::Rc;

/// Max AST node count of a candidate we will hand to `eval` (bounds attempted work).
const INPUT_CAP: usize = 512;
/// Absolute ceiling on the spliced normal form's node count (a hard anti-bloat backstop on top of
/// the size-non-increasing rule).
const OUTPUT_CAP: usize = 512;

/// Fold every closed, effect-free subterm of `term` to its kernel normal form, subject to the cost
/// caps. Pure, total, and idempotent; the entry point the backend pipeline calls before `lower`.
/// `sig` is threaded into the evaluation environment because the kernel's eliminator reduction
/// (`do_elim`) reads the constructor declarations from the signature in scope.
pub fn ctnorm(term: &Term, sig: &Signature) -> Term {
    // The signature is `Rc`-shared into the eval environment once (closures capture it).
    let env = Env::with_sig(Rc::new(sig.clone()));
    go(term, &env)
}

/// Top-down: a closed, pure, within-budget subterm folds whole; otherwise we descend so its smaller
/// closed sub-pieces still fold. Folding the largest eligible region first is both fewer `eval`
/// calls and the maximal collapse.
fn go(term: &Term, env: &Env) -> Term {
    if is_pure(term) && !contains_elim(term) && is_closed(term) && size(term) <= INPUT_CAP {
        if let Some(nf) = try_normalize(term, env) {
            // Keep only a *non-growing* normal form (the "fewer ops" win and the unary-`Nat` blowup
            // guard) that is itself closed + pure (so re-lowering it is sound and effect-free).
            if size(&nf) <= size(term).min(OUTPUT_CAP) && is_pure(&nf) && is_closed(&nf) {
                return nf;
            }
        }
    }
    map_children(term, |c| go(c, env))
}

/// Normalize a closed term by the kernel's own evaluator, guarded so any panic (e.g. a term shape
/// `eval` does not expect) is a *fall back to the original*, never a build abort. Deterministic: a
/// panic on a given input is reproducible, so this preserves bit-identity across builds.
fn try_normalize(t: &Term, env: &Env) -> Option<Term> {
    let t = t.clone();
    let env = env.clone();
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let v = blight_kernel::normalize::eval(&env, &t);
        blight_kernel::normalize::quote(0, &v)
    }))
    .ok()
}

/// `true` iff `t` has no free de Bruijn variable (it is closed: every `Var` is bound by a binder
/// inside `t`). Binders that introduce a variable: `Lam`/`PLam` (1), `Pi`/`Sigma` (cod under 1),
/// `Elim` motive (1) and each method (its constructor arity — but we conservatively treat any `Var`
/// reaching the method root as bound by descending with the local cutoff), `Handle` clauses.
fn is_closed(t: &Term) -> bool {
    fn go(t: &Term, depth: usize) -> bool {
        match t {
            Term::Var(i) => *i < depth,
            Term::Univ(_) | Term::IntTy | Term::IntLit(_) | Term::Interval(_) | Term::Erased => {
                true
            }
            Term::Foreign { .. } => true, // opaque, no free var of ours; but `is_pure` rejects it anyway
            Term::Lam(b) | Term::PLam(b) => go(b, depth + 1),
            Term::Pi(_, a, b) | Term::Sigma(a, b) => go(a, depth) && go(b, depth + 1),
            Term::App(f, a) => go(f, depth) && go(a, depth),
            Term::Pair(a, b) => go(a, depth) && go(b, depth),
            Term::Fst(p) | Term::Snd(p) | Term::Unglue(p) => go(p, depth),
            Term::Ann(x, y) => go(x, depth) && go(y, depth),
            Term::Data(_, ps, is) => {
                ps.iter().all(|x| go(x, depth)) && is.iter().all(|x| go(x, depth))
            }
            Term::Con(_, args) => args.iter().all(|x| go(x, depth)),
            // A path constructor's `dim` is a pretype interval term (no de Bruijn *term* var of
            // ours to bind), mirroring `PApp`'s `_` above; only its (nullary, in this fragment)
            // `args` matter for term-closedness.
            Term::PCon { args, .. } => args.iter().all(|x| go(x, depth)),
            Term::Elim {
                motive,
                methods,
                scrutinee,
                ..
            } => {
                // The motive binds the scrutinee (1). Each method binds its constructor's
                // arguments; we don't know the arity here, so be conservative: a method is "closed"
                // only if it has no var free above a generous binder budget. Since we only *use*
                // closedness to gate normalization of the whole `Elim` (which we attempt only when
                // every part is closed), require motive/methods closed under +1 / their own roots.
                go(motive, depth + 1)
                    && methods.iter().all(|m| go(m, depth))
                    && go(scrutinee, depth)
            }
            Term::PathP { family, lhs, rhs } => {
                go(family, depth + 1) && go(lhs, depth) && go(rhs, depth)
            }
            Term::PApp(p, _) => go(p, depth),
            Term::Partial(_, a) => go(a, depth),
            Term::Transp { family, base, .. } => go(family, depth + 1) && go(base, depth),
            Term::HComp { ty, tube, base, .. } => {
                go(ty, depth) && go(tube, depth + 1) && go(base, depth)
            }
            Term::Comp {
                family, tube, base, ..
            } => go(family, depth + 1) && go(tube, depth + 1) && go(base, depth),
            Term::Glue {
                base, ty, equiv, ..
            } => go(base, depth) && go(ty, depth) && go(equiv, depth),
            Term::GlueTerm { partial, base, .. } => go(partial, depth) && go(base, depth),
            Term::System(_) => false, // conservatively not closed (avoid Cofib var bookkeeping)
            Term::Op { arg, .. } => go(arg, depth),
            Term::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                go(body, depth)
                    && go(return_clause, depth + 1)
                    && op_clauses.iter().all(|(_, e)| go(e, depth + 2))
            }
            Term::EffTy(_, a) => go(a, depth),
            Term::Delay(a) | Term::Now(a) | Term::Later(a) | Term::Force(a) => go(a, depth),
            Term::IntPrim { lhs, rhs, .. } => go(lhs, depth) && go(rhs, depth),
        }
    }
    go(t, 0)
}

/// `true` iff `t` contains no effect / partiality / foreign / cubical node anywhere — the fragment
/// the kernel's `eval` reduces totally with no divergence surface. Conservative: any node that can
/// get stuck on a neutral, diverge, or reference the trusted hatch disqualifies the whole subterm.
fn is_pure(t: &Term) -> bool {
    match t {
        // The disqualifying nodes (effects §4, partiality §4.5, foreign §7.6, cubical §2.6).
        Term::Op { .. }
        | Term::Handle { .. }
        | Term::EffTy(..)
        | Term::Delay(_)
        | Term::Now(_)
        | Term::Later(_)
        | Term::Force(_)
        | Term::Foreign { .. }
        | Term::Interval(_)
        | Term::PathP { .. }
        | Term::PLam(_)
        | Term::PApp(..)
        | Term::Partial(..)
        | Term::System(_)
        | Term::Transp { .. }
        | Term::HComp { .. }
        | Term::Comp { .. }
        | Term::Glue { .. }
        | Term::GlueTerm { .. }
        | Term::Unglue(_)
        // A path constructor (Wave 7/E4 HITs) is itself a cubical §2.6 node, disqualified for the
        // same reason `PathP`/`PLam`/`PApp` are above.
        | Term::PCon { .. }
        | Term::Erased => false,
        // Leaves.
        Term::Var(_) | Term::Univ(_) | Term::IntTy | Term::IntLit(_) => true,
        // Structural: pure iff every child is.
        Term::Lam(b) => is_pure(b),
        Term::Pi(_, a, b) | Term::Sigma(a, b) => is_pure(a) && is_pure(b),
        Term::App(f, a) | Term::Pair(f, a) | Term::Ann(f, a) => is_pure(f) && is_pure(a),
        Term::Fst(p) | Term::Snd(p) => is_pure(p),
        Term::Data(_, ps, is) => ps.iter().all(is_pure) && is.iter().all(is_pure),
        Term::Con(_, args) => args.iter().all(is_pure),
        Term::Elim {
            motive,
            methods,
            scrutinee,
            ..
        } => is_pure(motive) && methods.iter().all(is_pure) && is_pure(scrutinee),
        Term::IntPrim { lhs, rhs, .. } => is_pure(lhs) && is_pure(rhs),
    }
}

/// `true` iff `t` contains an inductive eliminator anywhere — the one unbounded-recursion source we
/// refuse to evaluate (see the module header: a tiny `Elim` can drive an arbitrarily large
/// reduction, and we have no deterministic step cap). Cheap structural scan.
fn contains_elim(t: &Term) -> bool {
    match t {
        Term::Elim { .. } => true,
        Term::Var(_)
        | Term::Univ(_)
        | Term::IntTy
        | Term::IntLit(_)
        | Term::Interval(_)
        | Term::Foreign { .. }
        | Term::System(_)
        | Term::Erased => false,
        Term::Lam(b)
        | Term::PLam(b)
        | Term::Fst(b)
        | Term::Snd(b)
        | Term::Unglue(b)
        | Term::Partial(_, b)
        | Term::EffTy(_, b)
        | Term::Delay(b)
        | Term::Now(b)
        | Term::Later(b)
        | Term::Force(b)
        | Term::Op { arg: b, .. }
        | Term::PApp(b, _) => contains_elim(b),
        Term::Pi(_, a, b)
        | Term::Sigma(a, b)
        | Term::App(a, b)
        | Term::Pair(a, b)
        | Term::Ann(a, b) => contains_elim(a) || contains_elim(b),
        Term::IntPrim { lhs, rhs, .. } => contains_elim(lhs) || contains_elim(rhs),
        Term::Data(_, ps, is) => ps.iter().any(contains_elim) || is.iter().any(contains_elim),
        Term::Con(_, args) => args.iter().any(contains_elim),
        Term::PCon { args, .. } => args.iter().any(contains_elim),
        Term::PathP { family, lhs, rhs } => {
            contains_elim(family) || contains_elim(lhs) || contains_elim(rhs)
        }
        Term::Transp { family, base, .. } => contains_elim(family) || contains_elim(base),
        Term::HComp { ty, tube, base, .. } => {
            contains_elim(ty) || contains_elim(tube) || contains_elim(base)
        }
        Term::Comp {
            family, tube, base, ..
        } => contains_elim(family) || contains_elim(tube) || contains_elim(base),
        Term::Glue {
            base, ty, equiv, ..
        } => contains_elim(base) || contains_elim(ty) || contains_elim(equiv),
        Term::GlueTerm { partial, base, .. } => contains_elim(partial) || contains_elim(base),
        Term::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            contains_elim(body)
                || contains_elim(return_clause)
                || op_clauses.iter().any(|(_, e)| contains_elim(e))
        }
    }
}

/// AST node count (the structural budget the caps compare against).
fn size(t: &Term) -> usize {
    1 + match t {
        Term::Var(_)
        | Term::Univ(_)
        | Term::IntTy
        | Term::IntLit(_)
        | Term::Interval(_)
        | Term::Foreign { .. }
        | Term::System(_)
        | Term::Erased => 0,
        Term::Lam(b)
        | Term::PLam(b)
        | Term::Fst(b)
        | Term::Snd(b)
        | Term::Unglue(b)
        | Term::Partial(_, b)
        | Term::EffTy(_, b)
        | Term::Delay(b)
        | Term::Now(b)
        | Term::Later(b)
        | Term::Force(b)
        | Term::Op { arg: b, .. }
        | Term::PApp(b, _) => size(b),
        Term::Pi(_, a, b)
        | Term::Sigma(a, b)
        | Term::App(a, b)
        | Term::Pair(a, b)
        | Term::Ann(a, b) => size(a) + size(b),
        Term::IntPrim { lhs, rhs, .. } => size(lhs) + size(rhs),
        Term::Data(_, ps, is) => {
            ps.iter().map(size).sum::<usize>() + is.iter().map(size).sum::<usize>()
        }
        Term::Con(_, args) => args.iter().map(size).sum(),
        Term::PCon { args, .. } => args.iter().map(size).sum(),
        Term::Elim {
            motive,
            methods,
            scrutinee,
            ..
        } => size(motive) + methods.iter().map(size).sum::<usize>() + size(scrutinee),
        Term::PathP { family, lhs, rhs } => size(family) + size(lhs) + size(rhs),
        Term::Transp { family, base, .. } => size(family) + size(base),
        Term::HComp { ty, tube, base, .. } => size(ty) + size(tube) + size(base),
        Term::Comp {
            family, tube, base, ..
        } => size(family) + size(tube) + size(base),
        Term::Glue {
            base, ty, equiv, ..
        } => size(base) + size(ty) + size(equiv),
        Term::GlueTerm { partial, base, .. } => size(partial) + size(base),
        Term::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            size(body)
                + size(return_clause)
                + op_clauses.iter().map(|(_, e)| size(e)).sum::<usize>()
        }
    }
}

/// Rebuild `t` with `f` applied to each immediate child `Term`. Used to descend when the whole node
/// is not an eligible fold target. Non-`Term` payloads (`Grade`, `Cofib`, `Interval`, names) are
/// preserved verbatim. Exotic cubical/`System` shapes are traversed structurally where they carry
/// boxed `Term` children and cloned otherwise.
fn map_children(t: &Term, f: impl Fn(&Term) -> Term) -> Term {
    let b = |x: &Term| Box::new(f(x));
    match t {
        Term::Var(_)
        | Term::Univ(_)
        | Term::IntTy
        | Term::IntLit(_)
        | Term::Interval(_)
        | Term::System(_)
        | Term::Foreign { .. }
        | Term::Erased => t.clone(),
        Term::Lam(x) => Term::Lam(b(x)),
        Term::PLam(x) => Term::PLam(b(x)),
        Term::Pi(g, a, c) => Term::Pi(*g, b(a), b(c)),
        Term::Sigma(a, c) => Term::Sigma(b(a), b(c)),
        Term::App(x, y) => Term::App(b(x), b(y)),
        Term::Pair(x, y) => Term::Pair(b(x), b(y)),
        Term::Fst(x) => Term::Fst(b(x)),
        Term::Snd(x) => Term::Snd(b(x)),
        Term::Ann(x, y) => Term::Ann(b(x), b(y)),
        Term::Data(n, ps, is) => Term::Data(
            n.clone(),
            ps.iter().map(&f).collect(),
            is.iter().map(&f).collect(),
        ),
        Term::Con(n, args) => Term::Con(n.clone(), args.iter().map(&f).collect()),
        Term::PCon {
            data,
            name,
            args,
            dim,
        } => Term::PCon {
            data: data.clone(),
            name: name.clone(),
            args: args.iter().map(&f).collect(),
            dim: dim.clone(),
        },
        Term::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => Term::Elim {
            data: data.clone(),
            motive: b(motive),
            methods: methods.iter().map(&f).collect(),
            scrutinee: b(scrutinee),
        },
        Term::PathP { family, lhs, rhs } => Term::PathP {
            family: b(family),
            lhs: b(lhs),
            rhs: b(rhs),
        },
        Term::PApp(p, r) => Term::PApp(b(p), r.clone()),
        Term::Partial(c, a) => Term::Partial(c.clone(), b(a)),
        Term::Transp {
            family,
            cofib,
            base,
        } => Term::Transp {
            family: b(family),
            cofib: cofib.clone(),
            base: b(base),
        },
        Term::HComp {
            ty,
            cofib,
            tube,
            base,
        } => Term::HComp {
            ty: b(ty),
            cofib: cofib.clone(),
            tube: b(tube),
            base: b(base),
        },
        Term::Comp {
            family,
            cofib,
            tube,
            base,
        } => Term::Comp {
            family: b(family),
            cofib: cofib.clone(),
            tube: b(tube),
            base: b(base),
        },
        Term::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => Term::Glue {
            base: b(base),
            cofib: cofib.clone(),
            ty: b(ty),
            equiv: b(equiv),
        },
        Term::GlueTerm {
            cofib,
            partial,
            base,
        } => Term::GlueTerm {
            cofib: cofib.clone(),
            partial: b(partial),
            base: b(base),
        },
        Term::Unglue(x) => Term::Unglue(b(x)),
        Term::Op {
            effect,
            op,
            type_args,
            arg,
        } => Term::Op {
            effect: effect.clone(),
            op: op.clone(),
            type_args: type_args.iter().map(&f).collect(),
            arg: b(arg),
        },
        Term::Handle {
            body,
            return_clause,
            op_clauses,
        } => Term::Handle {
            body: b(body),
            return_clause: b(return_clause),
            op_clauses: op_clauses.iter().map(|(n, e)| (n.clone(), b(e))).collect(),
        },
        Term::EffTy(r, a) => Term::EffTy(r.clone(), b(a)),
        Term::Delay(x) => Term::Delay(b(x)),
        Term::Now(x) => Term::Now(b(x)),
        Term::Later(x) => Term::Later(b(x)),
        Term::Force(x) => Term::Force(b(x)),
        Term::IntPrim { op, lhs, rhs } => Term::IntPrim {
            op: *op,
            lhs: b(lhs),
            rhs: b(rhs),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::term::ConName;
    use blight_kernel::{IntPrimOp, Signature, Term};

    /// CTNORM with an empty signature: enough for the `Int`/constructor tests (no `Elim` reduction,
    /// which is the only thing that consults the signature).
    fn fold(t: &Term) -> Term {
        ctnorm(t, &Signature::default())
    }

    fn nat(n: usize) -> Term {
        let mut t = Term::Con(ConName("Zero".into()), vec![]);
        for _ in 0..n {
            t = Term::Con(ConName("Succ".into()), vec![t]);
        }
        t
    }

    fn count(t: &Term) -> usize {
        // crude node count for the test's expectations
        match t {
            Term::Con(_, args) => 1 + args.iter().map(count).sum::<usize>(),
            Term::IntPrim { lhs, rhs, .. } => 1 + count(lhs) + count(rhs),
            _ => 1,
        }
    }

    /// A closed primitive `Int` arithmetic subterm folds to a single literal at compile time
    /// (`2 + 3 → 5`) — fewer runtime ops, by the kernel's own definitional reduction.
    #[test]
    fn folds_closed_int_arithmetic() {
        let t = Term::IntPrim {
            op: IntPrimOp::Add,
            lhs: Box::new(Term::IntLit(2)),
            rhs: Box::new(Term::IntLit(3)),
        };
        assert_eq!(fold(&t), Term::IntLit(5));
    }

    /// Folding happens for closed sub-pieces even when the enclosing term is left alone: the second
    /// operand `(10 * 4)` collapses to `40` under an outer (non-foldable, variable-bearing) op.
    #[test]
    fn folds_nested_closed_subterm() {
        // (x * (10 * 4))  with x = Var(0) free → outer is not closed, inner (10*4) is.
        let t = Term::IntPrim {
            op: IntPrimOp::Mul,
            lhs: Box::new(Term::Var(0)),
            rhs: Box::new(Term::IntPrim {
                op: IntPrimOp::Mul,
                lhs: Box::new(Term::IntLit(10)),
                rhs: Box::new(Term::IntLit(4)),
            }),
        };
        let got = fold(&t);
        let want = Term::IntPrim {
            op: IntPrimOp::Mul,
            lhs: Box::new(Term::Var(0)),
            rhs: Box::new(Term::IntLit(40)),
        };
        assert_eq!(got, want);
    }

    /// A closed term that is already a normal form is returned unchanged (idempotent, no growth).
    #[test]
    fn leaves_normal_form_unchanged() {
        let t = nat(40);
        let got = fold(&t);
        assert_eq!(got, t);
        assert_eq!(count(&got), count(&t));
    }

    /// The recursion guard (the deterministic step cap): a closed term that contains an inductive
    /// `Elim` is **never** evaluated away — there is no static bound on an eliminator's reduction
    /// cost (a tiny `Elim` can drive an astronomically large fold), so CTNORM refuses it and leaves
    /// the `Elim` in place for the runtime. (Folding it would require a step-metered evaluator the
    /// kernel does not expose; growing the TCB to add one is off the table.)
    #[test]
    fn never_folds_eliminator() {
        use blight_kernel::term::DataName;
        // Elim Nat (λ_. Nat) [ Zero ; λk.λih. Succ ih ] (Succ (Succ Zero))  — a "double"-ish fold.
        let t = Term::Elim {
            data: DataName("Nat".into()),
            motive: Box::new(Term::Lam(Box::new(Term::Con(
                ConName("Nat".into()),
                vec![],
            )))),
            methods: vec![
                Term::Con(ConName("Zero".into()), vec![]),
                Term::Lam(Box::new(Term::Lam(Box::new(Term::Con(
                    ConName("Succ".into()),
                    vec![Term::Var(0)],
                ))))),
            ],
            scrutinee: Box::new(nat(2)),
        };
        // `contains_elim` short-circuits the fold; the term is returned structurally intact (children
        // may be touched, but the eliminator itself must survive).
        assert!(matches!(fold(&t), Term::Elim { .. }));
    }

    /// An effectful subterm is never normalized away (it is not pure): an `Op` node is left intact.
    #[test]
    fn never_folds_effectful() {
        let t = Term::Op {
            effect: blight_kernel::EffName("IO".into()),
            op: "print".to_string(),
            type_args: vec![],
            arg: Box::new(Term::IntLit(1)),
        };
        assert_eq!(fold(&t), t);
    }
}
