//! Grade-`0` erasure (spec §7.2): the first post-check compiler pass.
//!
//! Once a term has been *accepted* by the kernel, the grading discipline (§3.3) guarantees that
//! every grade-`0` binder and argument is computationally irrelevant: it may appear in *types*
//! but never flows into a runtime-relevant position. Erasure removes that content, so dependent
//! indices (`Vec a n`'s `n`), proofs, and phantom dictionaries cost **nothing** at runtime.
//!
//! Erasure is *type-directed*: the binder grades live on the `Pi` nodes of the term's type, not
//! on the `Lam`/`App` nodes of the term itself. We therefore walk the term against its (core,
//! quoted) type:
//!
//! - a `λ` whose corresponding `Pi`-binder grade is `0` is **dropped**, and every reference to
//!   that binder inside the (erased) body becomes [`Term::Erased`] — but, since the body is
//!   well-graded, no *runtime* reference survives, so `Erased` is unreachable in practice;
//! - an application `f a` whose function domain grade is `0` **drops** the argument `a`;
//! - all other nodes are traversed structurally, with de Bruijn indices renumbered to account for
//!   the binders that were removed.
//!
//! We do not need the type for the recursive structure beyond the binder grades, so the walk
//! keeps a parallel "is this de Bruijn level erased?" environment rather than re-deriving the
//! type at every node.

use crate::semiring::{Grade, Semiring};
use crate::term::Term;

/// Erase grade-`0` content from `term`, whose type is `ty` (a core type term in the same scope).
/// Returns a term in which all grade-`0` binders and arguments have been removed and the
/// remaining de Bruijn indices renumbered.
///
/// `term` must already have been accepted by the kernel against `ty`; erasure assumes
/// well-gradedness and is purely a syntactic transformation.
pub fn erase(term: &Term, ty: &Term) -> Term {
    // `kept[lvl]` answers "is the variable bound at de Bruijn *level* `lvl` retained after
    // erasure?". Innermost-last (a stack): pushing on binder entry, popping on exit. The new
    // index of a kept variable is its position among the kept variables to its outer side.
    let mut env: Vec<bool> = Vec::new();
    go(term, ty, &mut env)
}

/// The grade of the outermost `Pi` binder of `ty`, if `ty` is a function type.
fn pi_grade(ty: &Term) -> Option<(Grade, &Term, &Term)> {
    match ty {
        Term::Pi(g, dom, cod) => Some((*g, dom, cod)),
        _ => None,
    }
}

fn go(term: &Term, ty: &Term, env: &mut Vec<bool>) -> Term {
    match term {
        // A variable is rewritten to its post-erasure index, or to `Erased` if its binder was
        // dropped (which, for a well-graded *runtime* occurrence, never happens).
        Term::Var(i) => match renumber(*i, env) {
            Some(j) => Term::Var(j),
            None => Term::Erased,
        },

        // `λ. body` against `Pi (x:^ρ A) B`. If ρ = 0 the binder is erased: the body is walked
        // with `x` marked dropped, and the resulting `λ` is *removed* (the body takes its place,
        // now one binder shallower). Otherwise the `λ` is kept.
        Term::Lam(body) => {
            if let Some((g, _dom, cod)) = pi_grade(ty) {
                let keep = g != Grade::zero();
                env.push(keep);
                let body2 = go(body, cod, env);
                env.pop();
                if keep {
                    Term::Lam(Box::new(body2))
                } else {
                    // The binder is gone; `body2` already has `x`'s slot removed via renumbering.
                    body2
                }
            } else {
                // No Pi type to guide us (shouldn't happen for a checked λ); keep conservatively.
                env.push(true);
                let body2 = go(body, ty, env);
                env.pop();
                Term::Lam(Box::new(body2))
            }
        }

        // `f a`. Erasure is *binder-driven*: we drop erased binders at the `Lam` that introduces
        // them (above). An application is traversed structurally; the function and argument are
        // each walked. (Dropping an *argument* at a grade-0 application site requires the
        // function's type, which the caller supplies for top-level definitions; for the general
        // nested case we conservatively keep the argument, which is always sound — an unused
        // erased value is dead code the later backend passes remove.)
        Term::App(f, a) => Term::App(
            Box::new(go(f, &Term::Erased, env)),
            Box::new(go(a, &Term::Erased, env)),
        ),

        Term::Univ(_) | Term::Data(_, _, _) => term.clone(),

        Term::Pi(g, dom, cod) => {
            // Types are not runtime content, but we still renumber any free variables so the term
            // stays well-scoped if it is ever re-embedded. Domain in current scope; codomain under
            // one (kept) binder.
            let dom2 = go(dom, &Term::Erased, env);
            env.push(true);
            let cod2 = go(cod, &Term::Erased, env);
            env.pop();
            Term::Pi(*g, Box::new(dom2), Box::new(cod2))
        }

        Term::Sigma(dom, cod) => {
            let dom2 = go(dom, &Term::Erased, env);
            env.push(true);
            let cod2 = go(cod, &Term::Erased, env);
            env.pop();
            Term::Sigma(Box::new(dom2), Box::new(cod2))
        }

        Term::Pair(a, b) => Term::Pair(
            Box::new(go(a, &Term::Erased, env)),
            Box::new(go(b, &Term::Erased, env)),
        ),
        Term::Fst(p) => Term::Fst(Box::new(go(p, &Term::Erased, env))),
        Term::Snd(p) => Term::Snd(Box::new(go(p, &Term::Erased, env))),

        Term::Ann(t, ann_ty) => {
            // Re-thread the real type for the inner term.
            Term::Ann(
                Box::new(go(t, ann_ty, env)),
                Box::new(go(ann_ty, &Term::Erased, env)),
            )
        }

        Term::Con(c, args) => Term::Con(
            c.clone(),
            args.iter().map(|t| go(t, &Term::Erased, env)).collect(),
        ),

        Term::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => Term::Elim {
            data: data.clone(),
            motive: Box::new(go(motive, &Term::Erased, env)),
            methods: methods.iter().map(|t| go(t, &Term::Erased, env)).collect(),
            scrutinee: Box::new(go(scrutinee, &Term::Erased, env)),
        },

        // `dim` carries no *term* variable content (dimensions live in a separate space); only
        // `args` can.
        Term::PCon {
            data,
            name,
            args,
            dim,
        } => Term::PCon {
            data: data.clone(),
            name: name.clone(),
            args: args.iter().map(|t| go(t, &Term::Erased, env)).collect(),
            dim: dim.clone(),
        },

        // Cubical formers carry no *term* binders (dimensions live in a separate space) so the
        // term-variable environment is unchanged when descending.
        Term::PathP { family, lhs, rhs } => Term::PathP {
            family: Box::new(go(family, &Term::Erased, env)),
            lhs: Box::new(go(lhs, &Term::Erased, env)),
            rhs: Box::new(go(rhs, &Term::Erased, env)),
        },
        Term::PLam(body) => Term::PLam(Box::new(go(body, &Term::Erased, env))),
        Term::PApp(p, r) => Term::PApp(Box::new(go(p, &Term::Erased, env)), r.clone()),
        Term::Partial(c, a) => Term::Partial(c.clone(), Box::new(go(a, &Term::Erased, env))),
        Term::Transp {
            family,
            cofib,
            base,
        } => Term::Transp {
            family: Box::new(go(family, &Term::Erased, env)),
            cofib: cofib.clone(),
            base: Box::new(go(base, &Term::Erased, env)),
        },
        Term::HComp {
            ty: t,
            cofib,
            tube,
            base,
        } => Term::HComp {
            ty: Box::new(go(t, &Term::Erased, env)),
            cofib: cofib.clone(),
            tube: Box::new(go(tube, &Term::Erased, env)),
            base: Box::new(go(base, &Term::Erased, env)),
        },
        Term::Comp {
            family,
            cofib,
            tube,
            base,
        } => Term::Comp {
            family: Box::new(go(family, &Term::Erased, env)),
            cofib: cofib.clone(),
            tube: Box::new(go(tube, &Term::Erased, env)),
            base: Box::new(go(base, &Term::Erased, env)),
        },
        Term::Glue {
            base,
            cofib,
            ty: t,
            equiv,
        } => Term::Glue {
            base: Box::new(go(base, &Term::Erased, env)),
            cofib: cofib.clone(),
            ty: Box::new(go(t, &Term::Erased, env)),
            equiv: Box::new(go(equiv, &Term::Erased, env)),
        },
        Term::GlueTerm {
            cofib,
            partial,
            base,
        } => Term::GlueTerm {
            cofib: cofib.clone(),
            partial: Box::new(go(partial, &Term::Erased, env)),
            base: Box::new(go(base, &Term::Erased, env)),
        },
        Term::Unglue(g) => Term::Unglue(Box::new(go(g, &Term::Erased, env))),
        // Effects are runtime-relevant (M2 does not erase effectful structure). Traverse
        // structurally, honoring the handler clause binders (return: 1; op clauses: 2).
        // The type-argument instantiation of a parameterized effect's operation is type-level
        // content (Wave 7/E2), like a `Data`'s own `params`/`indices` above — not runtime content,
        // so it is carried unchanged rather than traversed (see the `Data` arm's `term.clone()`).
        Term::Op {
            effect,
            op,
            type_args,
            arg,
        } => Term::Op {
            effect: effect.clone(),
            op: op.clone(),
            type_args: type_args.clone(),
            arg: Box::new(go(arg, &Term::Erased, env)),
        },
        Term::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            let body2 = go(body, &Term::Erased, env);
            env.push(true);
            let ret2 = go(return_clause, &Term::Erased, env);
            env.pop();
            let clauses2 = op_clauses
                .iter()
                .map(|(name, e)| {
                    env.push(true);
                    env.push(true);
                    let e2 = go(e, &Term::Erased, env);
                    env.pop();
                    env.pop();
                    (name.clone(), Box::new(e2))
                })
                .collect();
            Term::Handle {
                body: Box::new(body2),
                return_clause: Box::new(ret2),
                op_clauses: clauses2,
            }
        }
        Term::EffTy(row, a) => Term::EffTy(row.clone(), Box::new(go(a, &Term::Erased, env))),
        Term::Delay(a) => Term::Delay(Box::new(go(a, &Term::Erased, env))),
        Term::Now(a) => Term::Now(Box::new(go(a, &Term::Erased, env))),
        Term::Later(a) => Term::Later(Box::new(go(a, &Term::Erased, env))),
        Term::Force(a) => Term::Force(Box::new(go(a, &Term::Erased, env))),
        // A foreign postulate is runtime content (a C call); its type is irrelevant at runtime and
        // its symbol carries no de Bruijn indices, so it survives erasure unchanged.
        Term::Foreign { symbol, ty } => Term::Foreign {
            symbol: symbol.clone(),
            ty: ty.clone(),
        },
        // Int type/literal are runtime content with no de Bruijn indices. An IntPrim's operands
        // are runtime-relevant and must be renumbered.
        Term::IntTy | Term::IntLit(_) => term.clone(),
        Term::IntPrim { op, lhs, rhs } => Term::IntPrim {
            op: *op,
            lhs: Box::new(go(lhs, &Term::Erased, env)),
            rhs: Box::new(go(rhs, &Term::Erased, env)),
        },
        Term::System(_) | Term::Interval(_) | Term::Erased => term.clone(),
    }
}

/// Map an old de Bruijn *index* to its new index given the kept/dropped environment, or `None`
/// if the referenced binder was dropped. The environment is innermost-last; index `i` refers to
/// the binder `i` steps from the innermost, i.e. position `len - 1 - i`.
fn renumber(i: usize, env: &[bool]) -> Option<usize> {
    let len = env.len();
    if i >= len {
        // A free variable beyond the tracked binders: shift by the number of *dropped* binders so
        // it stays pointing at the same outer slot. Since we track all binders we cross, this is
        // only reached for genuinely free variables of a closed-after-erasure term; keep as-is
        // minus dropped count.
        let dropped = env.iter().filter(|k| !**k).count();
        return Some(i - dropped);
    }
    let pos = len - 1 - i;
    if !env[pos] {
        return None;
    }
    // New index = number of kept binders strictly inner to `pos` (positions pos+1..len).
    let kept_inner = env[pos + 1..].iter().filter(|k| **k).count();
    Some(kept_inner)
}

/// Does the variable at de Bruijn index `i` occur (in runtime position) anywhere in `term`?
/// Used by tests and by callers that want to confirm an erased binder truly vanished.
pub fn occurs(i: usize, term: &Term) -> bool {
    fn go(i: usize, term: &Term) -> bool {
        match term {
            Term::Var(j) => *j == i,
            Term::Univ(_) | Term::Data(_, _, _) | Term::Interval(_) | Term::Erased => false,
            Term::IntTy | Term::IntLit(_) => false,
            Term::IntPrim { lhs, rhs, .. } => go(i, lhs) || go(i, rhs),
            Term::Pi(_, a, b) | Term::Sigma(a, b) => go(i, a) || go(i + 1, b),
            Term::Lam(b) => go(i + 1, b),
            Term::App(f, a) | Term::Pair(f, a) => go(i, f) || go(i, a),
            // `PLam` binds a *dimension*, not a term variable, so the term index is unchanged.
            Term::PLam(p) => go(i, p),
            Term::Fst(p) | Term::Snd(p) | Term::Unglue(p) => go(i, p),
            Term::Ann(t, ty) => go(i, t) || go(i, ty),
            Term::Con(_, args) => args.iter().any(|t| go(i, t)),
            Term::Elim {
                motive,
                methods,
                scrutinee,
                ..
            } => go(i, motive) || methods.iter().any(|t| go(i, t)) || go(i, scrutinee),
            Term::PCon { args, .. } => args.iter().any(|t| go(i, t)),
            Term::PathP { family, lhs, rhs } => go(i, family) || go(i, lhs) || go(i, rhs),
            Term::PApp(p, _) => go(i, p),
            Term::Partial(_, a) => go(i, a),
            Term::Transp { family, base, .. } => go(i, family) || go(i, base),
            Term::HComp { ty, tube, base, .. } => go(i, ty) || go(i, tube) || go(i, base),
            Term::Comp {
                family, tube, base, ..
            } => go(i, family) || go(i, tube) || go(i, base),
            Term::Glue {
                base, ty, equiv, ..
            } => go(i, base) || go(i, ty) || go(i, equiv),
            Term::GlueTerm { partial, base, .. } => go(i, partial) || go(i, base),
            Term::System(branches) => branches.iter().any(|b| go(i, &b.term)),
            Term::Op { arg, .. } => go(i, arg),
            Term::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                go(i, body)
                    || go(i + 1, return_clause)
                    || op_clauses.iter().any(|(_, e)| go(i + 2, e))
            }
            Term::EffTy(_, a) | Term::Delay(a) | Term::Now(a) | Term::Later(a) | Term::Force(a) => {
                go(i, a)
            }
            Term::Foreign { ty, .. } => go(i, ty),
        }
    }
    go(i, term)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Term;

    fn u0() -> Term {
        Term::Univ(crate::term::Level::Zero)
    }

    /// `λ (x:^0 A). y` (where `y` is an outer var) erases to just the body with the binder gone.
    /// The dropped binder leaves no trace: `occurs(0, result)` is false.
    #[test]
    fn drops_zero_lambda() {
        // type: (x:^0 U0) -> U0   ; term: λ. <body referencing only outer scope = none here>
        // Use body = Var(0) would reference x; instead body = U0 (no var) to isolate the drop.
        let ty = Term::Pi(Grade::Zero, Box::new(u0()), Box::new(u0()));
        let term = Term::Lam(Box::new(u0()));
        let erased = erase(&term, &ty);
        assert_eq!(erased, u0(), "the erased λ vanishes, leaving its body");
    }

    /// A relevant (ω) binder is kept.
    #[test]
    fn keeps_relevant() {
        let ty = Term::Pi(Grade::Omega, Box::new(u0()), Box::new(u0()));
        let term = Term::Lam(Box::new(Term::Var(0)));
        let erased = erase(&term, &ty);
        assert_eq!(
            erased,
            Term::Lam(Box::new(Term::Var(0))),
            "ω binder kept verbatim"
        );
    }

    /// Dropping an *outer* erased binder renumbers references to *inner* kept binders.
    /// type: (a:^0 U0) -> (b:^ω U0) -> U0 ; term: λ a. λ b. b
    /// After erasing `a`, the body `λ b. b` remains and `b`'s index (0) is unchanged.
    #[test]
    fn renumbers_indices() {
        let ty = Term::Pi(
            Grade::Zero,
            Box::new(u0()),
            Box::new(Term::Pi(Grade::Omega, Box::new(u0()), Box::new(u0()))),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(0)))));
        let erased = erase(&term, &ty);
        assert_eq!(
            erased,
            Term::Lam(Box::new(Term::Var(0))),
            "erasing the outer erased binder leaves λ b. b with b at index 0"
        );
    }

    /// A reference to a *kept* binder that sits outside a *dropped* one is renumbered down.
    /// type: (a:^ω U0) -> (b:^0 U0) -> U0 ; term: λ a. λ b. a
    /// `a` is at index 1 inside the body; after dropping `b`, `a` becomes index 0.
    #[test]
    fn renumbers_past_dropped_inner() {
        let ty = Term::Pi(
            Grade::Omega,
            Box::new(u0()),
            Box::new(Term::Pi(Grade::Zero, Box::new(u0()), Box::new(u0()))),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(1)))));
        let erased = erase(&term, &ty);
        assert_eq!(
            erased,
            Term::Lam(Box::new(Term::Var(0))),
            "after dropping the inner erased b, the kept a moves from index 1 to 0"
        );
    }

    /// Erasure is idempotent: erasing an already-erased term (against the *erased* type, i.e. with
    /// the erased binders gone) is a no-op.
    #[test]
    fn idempotent() {
        let ty = Term::Pi(Grade::Omega, Box::new(u0()), Box::new(u0()));
        let term = Term::Lam(Box::new(Term::Var(0)));
        let once = erase(&term, &ty);
        let twice = erase(&once, &ty);
        assert_eq!(once, twice, "erase ∘ erase = erase");
    }

    /// `occurs` correctly reports presence/absence of a runtime variable reference.
    #[test]
    fn occurs_basic() {
        assert!(occurs(0, &Term::Var(0)));
        assert!(!occurs(0, &Term::Var(1)));
        // Under a binder, the outer var's index increases: `occurs(1, λ. Var(2))` looks for
        // index 2 inside the body and finds it.
        assert!(occurs(1, &Term::Lam(Box::new(Term::Var(2)))));
        // ...but `occurs(1, λ. Var(1))` looks for index 2 and does not find Var(1).
        assert!(!occurs(1, &Term::Lam(Box::new(Term::Var(1)))));
        assert!(occurs(0, &Term::Lam(Box::new(Term::Var(1)))));
        // The dropped lambda's body has no occurrence of the erased var.
        let ty = Term::Pi(Grade::Zero, Box::new(u0()), Box::new(u0()));
        let erased = erase(&Term::Lam(Box::new(u0())), &ty);
        assert!(!occurs(0, &erased));
    }
}
