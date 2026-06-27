//! Lowering kernel core `Term` to backend `Cir` (spec section 7).
//!
//! Runs `blight_kernel::erase::erase` first, then translates the checked, erased core term into
//! the untyped `Cir`. The type and cubical layers are dropped: `Univ`/`Pi`/`Sigma`-as-types are
//! never reached at runtime, path abstractions become ordinary functions over an erased dimension
//! argument, and `PApp` becomes application. The two recursion shapes are handled distinctly:
//!
//! - `Elim` (structural recursion) lowers to a recursive eliminator function:
//!   `(fix self. lam scrut. case scrut of arms) scrutinee`, where each arm applies the
//!   constructor's method to its kept fields and, after each recursive field, the induction
//!   hypothesis `self field` -- mirroring `do_elim` in `normalize.rs`.
//! - `Later (App (Var self) ...)` (partial recursion) is recognized at the enclosing `Lam`: a
//!   `Lam` whose body refers to its own binder under a `Later` is lowered to a `Cir::Fix` so the
//!   runtime delay trampoline can drive it.
//!
//! After translation, a `dead_bindings` pass closes the documented argument-position erasure gap
//! (`erase.rs`): an application whose argument is `Erased` (or a `let` binding an `Erased` value
//! whose bound variable is unused) is removed.

use crate::ir::{Arm, Cir};
use blight_kernel::signature::Arg;
use blight_kernel::{DataName, Grade, Signature, Term};

/// The region capability token constructor (declared in the untrusted prelude `regions.bl`). The
/// elaborator threads exactly this token into a `(region …)` desugaring.
const REGION_TOKEN: &str = "rgn-tok";

/// Whether `App(f, a)` is the desugared region redex `App(Ann(λ body, Π(1, _, _)), Con("rgn-tok"))`
/// the elaborator produces for `(region r body)`. Recognizing the grade-1 binder and the token
/// constructor keeps this from misfiring on ordinary applications.
fn is_region_redex(f: &Term, a: &Term) -> bool {
    let arg_is_token = matches!(a, Term::Con(c, args) if c.0 == REGION_TOKEN && args.is_empty());
    if !arg_is_token {
        return false;
    }
    matches!(
        f,
        Term::Ann(lam, pi)
            if matches!(lam.as_ref(), Term::Lam(_))
                && matches!(pi.as_ref(), Term::Pi(Grade::One, _, _))
    )
}

/// Lower a checked global `term` of type `ty` to `Cir`, erasing grade-0 content first.
pub fn lower(term: &Term, ty: &Term, sig: &Signature) -> Cir {
    let erased = blight_kernel::erase::erase(term, ty);
    let cir = lower_term(&erased, sig);
    dead_bindings(&cir)
}

/// Lower an already-erased term (used by tests that build erased terms directly).
pub fn lower_erased(term: &Term, sig: &Signature) -> Cir {
    dead_bindings(&lower_term(term, sig))
}

fn lower_term(term: &Term, sig: &Signature) -> Cir {
    match term {
        Term::Var(i) => Cir::Var(*i),

        // A `Lam` for partial recursion refers to its own binder under a `Later`. Detect that and
        // lower to `Fix`; otherwise an ordinary function.
        Term::Lam(body) => {
            if body_is_later_recursive(body) {
                Cir::Fix(Box::new(lower_term(body, sig)))
            } else {
                Cir::Lam(Box::new(lower_term(body, sig)))
            }
        }
        Term::App(f, a) => {
            // Region scope recognition (spec §3.5): the elaborator desugars `(region r body)` to
            //   App(Ann(Lam body, Pi(1, Rgn, cod)), Con("rgn-tok"))
            // — a grade-1 λ over the capability, applied to the fresh token. We recognize that exact
            // shape and wrap the lowered application in a `Cir::Region` scope so the backend brackets
            // it with arena enter/leave. The token itself lowers normally (it is a harmless nullary
            // value bound as the λ's argument); only the *scope* matters downstream.
            if is_region_redex(f, a) {
                let inner = Cir::App(Box::new(lower_term(f, sig)), Box::new(lower_term(a, sig)));
                return Cir::Region(Box::new(inner));
            }
            Cir::App(Box::new(lower_term(f, sig)), Box::new(lower_term(a, sig)))
        }

        // Pairs / projections become tuples / projections.
        Term::Pair(a, b) => Cir::tuple(vec![lower_term(a, sig), lower_term(b, sig)]),
        Term::Fst(p) => Cir::Proj(0, Box::new(lower_term(p, sig))),
        Term::Snd(p) => Cir::Proj(1, Box::new(lower_term(p, sig))),

        // An ascription is transparent at runtime.
        Term::Ann(t, _) => lower_term(t, sig),

        // Constructors become tagged records.
        Term::Con(c, args) => {
            Cir::con(c.clone(), args.iter().map(|a| lower_term(a, sig)).collect())
        }

        // The dependent eliminator becomes a recursive eliminator function applied to the
        // scrutinee (structural recursion).
        Term::Elim {
            data,
            methods,
            scrutinee,
            ..
        } => {
            let elim_fn = lower_elim_fn(data, methods, sig);
            Cir::App(Box::new(elim_fn), Box::new(lower_term(scrutinee, sig)))
        }

        // The delay monad: the partial-recursion runtime substrate.
        Term::Now(a) => Cir::now(lower_term(a, sig)),
        Term::Later(a) => Cir::later(lower_term(a, sig)),
        // `force d` drives the delay trampoline to a value (anf.rs lowers a tail `Force` to the
        // `bl_force` trampoline; bounded stack).
        Term::Force(a) => Cir::Force(Box::new(lower_term(a, sig))),
        // A foreign postulate lowers to a call to its external C symbol (spec §7.6, the FFI hatch).
        Term::Foreign { symbol, .. } => Cir::Foreign(symbol.clone()),
        // ---- primitive machine integers (M11) ----
        // `Int` is a *type*: no runtime content. A literal becomes a boxed `BL_INT`; an `IntPrim`
        // lowers to a runtime helper call on its (lowered) operands.
        Term::IntTy => Cir::Erased,
        Term::IntLit(n) => Cir::IntLit(*n),
        Term::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(lower_term(lhs, sig)),
            rhs: Box::new(lower_term(rhs, sig)),
        },
        // `Delay A` is a *type*; it has no runtime content of its own.
        Term::Delay(_) => Cir::Erased,

        // Effects (if not fully handled before codegen).
        Term::Op { effect, op, arg } => Cir::Op {
            effect: effect.0.clone(),
            op: op.clone(),
            arg: Box::new(lower_term(arg, sig)),
        },
        // A deep handler. Each clause is lowered into an ordinary closure so the existing closure
        // conversion lifts it and captures its free variables; the backend then installs them via
        // `bl_handle_clo` (which applies the clause closures through the normal calling convention):
        //   - body          → a thunk `λ_. body` (run once to start the computation);
        //   - return_clause → `λx. r`  (the kernel clause already binds `x` as de Bruijn 0);
        //   - op clause      → curried `λx. λk. e` (the kernel clause binds `x`=1, `k`=0, so wrapping
        //     in two λs that re-introduce those binders preserves the indices: outer λ binds `x`,
        //     inner λ binds `k`).
        // The body has no binder of its own, so we shift it under the thunk's ignored parameter.
        Term::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(Cir::Lam(Box::new(shift_cir_up(&lower_term(body, sig), 1)))),
            return_clause: Box::new(Cir::Lam(Box::new(lower_term(return_clause, sig)))),
            op_clauses: op_clauses
                .iter()
                .map(|(name, e)| {
                    (
                        name.clone(),
                        Cir::Lam(Box::new(Cir::Lam(Box::new(lower_term(e, sig))))),
                    )
                })
                .collect(),
        },

        // Path abstraction/application: a path is a function over an (erased) dimension; lower the
        // body as a function and applications as `force`/apply. The dimension argument carries no
        // runtime content, so `PApp` simply forwards the function.
        Term::PLam(body) => Cir::Lam(Box::new(lower_term(body, sig))),
        Term::PApp(p, _) => lower_term(p, sig),

        // Everything else is type-level / cubical Kan machinery with no runtime content. After
        // erasure these only appear in erased positions; map them to the poison placeholder.
        Term::Univ(_)
        | Term::Pi(_, _, _)
        | Term::Sigma(_, _)
        | Term::Data(_, _, _)
        | Term::Interval(_)
        | Term::PathP { .. }
        | Term::Partial(_, _)
        | Term::System(_)
        | Term::Transp { .. }
        | Term::HComp { .. }
        | Term::Comp { .. }
        | Term::Glue { .. }
        | Term::GlueTerm { .. }
        | Term::Unglue(_)
        | Term::EffTy(_, _)
        | Term::Erased => Cir::Erased,
    }
}

/// Build the recursive eliminator function for `Elim D _ methods _`:
/// `fix self. lam scrut. case scrut of [arm per constructor]`. Each arm binds the constructor's
/// fields and applies `methods[idx]` to them, inserting `self field` after each recursive field
/// (the induction hypothesis), mirroring `do_elim` (`normalize.rs`).
///
/// Inside the `Fix`, de Bruijn 0 is `self`; inside the `lam scrut`, 0 is `scrut` and 1 is `self`.
/// Within an arm body, the constructor's fields are the innermost binders (last = innermost), and
/// outer indices are shifted by the number of arm binders. The captured `methods` therefore must
/// be shifted by `2 + binders` (past `self`, `scrut`, and the field binders) at each use.
fn lower_elim_fn(data: &DataName, methods: &[Term], sig: &Signature) -> Cir {
    let decl = sig
        .get(data)
        .unwrap_or_else(|| panic!("lower: unknown data type {data:?}"));
    let methods_cir: Vec<Cir> = methods.iter().map(|m| lower_term(m, sig)).collect();

    let arms: Vec<Arm> = decl
        .constructors
        .iter()
        .enumerate()
        .map(|(idx, ctor)| {
            let nfields = ctor.args.len();
            // Field binders are introduced innermost; field `j` (0-based from the first arg) sits
            // at de Bruijn index `nfields - 1 - j` inside the arm body. `self` lives outside the
            // `lam scrut` and the field binders: it is at index `nfields + 1` from within the arm.
            let self_idx = nfields + 1;
            // The method, captured from outside the eliminator, must be shifted past `self`,
            // `scrut`, and the `nfields` field binders.
            let method = shift_cir(&methods_cir[idx], 2 + nfields);
            let mut body = method;
            for (j, arg) in ctor.args.iter().enumerate() {
                let field_idx = nfields - 1 - j;
                body = Cir::App(Box::new(body), Box::new(Cir::Var(field_idx)));
                if matches!(arg, Arg::Rec(_)) {
                    // Induction hypothesis: `self field`.
                    let ih = Cir::App(Box::new(Cir::Var(self_idx)), Box::new(Cir::Var(field_idx)));
                    body = Cir::App(Box::new(body), Box::new(ih));
                }
            }
            Arm {
                con: ctor.name.clone(),
                binders: nfields,
                body,
            }
        })
        .collect();

    // `lam scrut. case scrut of arms`; scrut is de Bruijn 0.
    let lam = Cir::Lam(Box::new(Cir::Case(Box::new(Cir::Var(0)), arms)));
    Cir::Fix(Box::new(lam))
}

/// Does this `Lam` body refer to the lambda's own binder *as the head of a `Later`-guarded
/// application*? That is the signature of the elaborator's partial-recursion compilation
/// (`elaborate_rec`): the whole function is `λself. …` and every recursive step is `Later (self a₁
/// … aₙ)`, i.e. an application **spine whose head is `self`**.
///
/// The head check matters: an `Elim` method lambda (e.g. a `match` arm of a partial-recursive
/// function) can legitimately *contain* a `Later (self … xs …)` in which the method's own field
/// binders appear as *arguments*. Such a method binder must stay an ordinary `Lam`; only the
/// genuine self-binder — the one in head position — turns into a `Fix`. Matching on mere mention
/// (rather than head position) misfired here and lowered method lambdas to `Fix`, dropping their
/// remaining parameters and corrupting the eliminator's calling convention.
fn body_is_later_recursive(body: &Term) -> bool {
    /// The applicative head of `t`, peeling `App` spines (and transparent ascriptions).
    fn app_head(t: &Term) -> &Term {
        match t {
            Term::App(f, _) => app_head(f),
            Term::Ann(inner, _) => app_head(inner),
            other => other,
        }
    }
    fn under_later(t: &Term, self_idx: usize) -> bool {
        match t {
            Term::Later(inner) => matches!(app_head(inner), Term::Var(i) if *i == self_idx),
            Term::Lam(b) => under_later(b, self_idx + 1),
            Term::App(f, a) => under_later(f, self_idx) || under_later(a, self_idx),
            Term::Pair(a, b) | Term::Ann(a, b) => {
                under_later(a, self_idx) || under_later(b, self_idx)
            }
            Term::Fst(p) | Term::Snd(p) | Term::Now(p) => under_later(p, self_idx),
            Term::Elim {
                methods, scrutinee, ..
            } => {
                methods.iter().any(|m| under_later(m, self_idx)) || under_later(scrutinee, self_idx)
            }
            Term::Con(_, args) => args.iter().any(|a| under_later(a, self_idx)),
            Term::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                under_later(body, self_idx)
                    || under_later(return_clause, self_idx + 1)
                    || op_clauses.iter().any(|(_, e)| under_later(e, self_idx + 2))
            }
            Term::Op { arg, .. } => under_later(arg, self_idx),
            _ => false,
        }
    }
    under_later(body, 0)
}

/// Shift all free de Bruijn variables in a `Cir` by `by`, accounting for binders crossed.
fn shift_cir(c: &Cir, by: usize) -> Cir {
    fn go(c: &Cir, by: usize, depth: usize) -> Cir {
        match c {
            Cir::Var(i) => {
                if *i >= depth {
                    Cir::Var(i + by)
                } else {
                    Cir::Var(*i)
                }
            }
            Cir::Global(_) | Cir::Erased | Cir::Foreign(_) => c.clone(),
            Cir::Lam(b) => Cir::Lam(Box::new(go(b, by, depth + 1))),
            Cir::Fix(b) => Cir::Fix(Box::new(go(b, by, depth + 1))),
            Cir::App(f, a) => Cir::App(Box::new(go(f, by, depth)), Box::new(go(a, by, depth))),
            Cir::Let(v, b) => Cir::Let(Box::new(go(v, by, depth)), Box::new(go(b, by, depth + 1))),
            Cir::Con(c2, args, al) => Cir::Con(
                c2.clone(),
                args.iter().map(|a| go(a, by, depth)).collect(),
                *al,
            ),
            Cir::Case(s, arms) => Cir::Case(
                Box::new(go(s, by, depth)),
                arms.iter()
                    .map(|arm| Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: go(&arm.body, by, depth + arm.binders),
                    })
                    .collect(),
            ),
            Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(|e| go(e, by, depth)).collect(), *al),
            Cir::Proj(i, e) => Cir::Proj(*i, Box::new(go(e, by, depth))),
            Cir::Now(e, al) => Cir::Now(Box::new(go(e, by, depth)), *al),
            Cir::Later(e, al) => Cir::Later(Box::new(go(e, by, depth)), *al),
            Cir::Force(e) => Cir::Force(Box::new(go(e, by, depth))),
            Cir::Region(b) => Cir::Region(Box::new(go(b, by, depth))),
            Cir::Op { effect, op, arg } => Cir::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(arg, by, depth)),
            },
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => Cir::Handle {
                body: Box::new(go(body, by, depth)),
                return_clause: Box::new(go(return_clause, by, depth + 1)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(n, e)| (n.clone(), go(e, by, depth + 2)))
                    .collect(),
            },
            Cir::MkClosure(f, env, al) => Cir::MkClosure(
                f.clone(),
                env.iter().map(|e| go(e, by, depth)).collect(),
                *al,
            ),
            Cir::EnvRef(_) => c.clone(),
            Cir::CallClosure(f, a) => {
                Cir::CallClosure(Box::new(go(f, by, depth)), Box::new(go(a, by, depth)))
            }
            Cir::IntLit(_) => c.clone(),
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, depth)),
                rhs: Box::new(go(rhs, by, depth)),
            },
        }
    }
    go(c, by, 0)
}

/// Close the argument-position erasure gap (`erase.rs`): erasure drops grade-0 *binders* at their
/// `Lam`, but conservatively keeps grade-0 *arguments* at nested application sites (it lacks the
/// callee's type there). After lowering, such an argument is `Cir::Erased`. This untrusted pass
/// removes those dead arguments. Because it runs over `Cir` (post-check, untrusted), it adds no
/// kernel trust; a mistake is at worst a behavior bug.
///
/// It also drops `let x = Erased in body` bindings whose `x` is unused, and rewrites an
/// application `f Erased` by dropping the erased argument when `f` is a lambda whose binder is
/// unused (a curried grade-0 argument).
pub fn dead_bindings(c: &Cir) -> Cir {
    match c {
        Cir::Var(_) | Cir::Global(_) | Cir::Erased | Cir::Foreign(_) | Cir::IntLit(_) => c.clone(),
        Cir::Lam(b) => Cir::Lam(Box::new(dead_bindings(b))),
        Cir::Fix(b) => Cir::Fix(Box::new(dead_bindings(b))),
        Cir::App(f, a) => {
            let f2 = dead_bindings(f);
            let a2 = dead_bindings(a);
            // `(lam. body) Erased` with the binder unused: beta-drop the erased argument.
            if matches!(a2, Cir::Erased) {
                if let Cir::Lam(body) = &f2 {
                    if !cir_uses(body, 0) {
                        return strip_binder(body);
                    }
                }
            }
            Cir::App(Box::new(f2), Box::new(a2))
        }
        Cir::Let(v, b) => {
            let v2 = dead_bindings(v);
            let b2 = dead_bindings(b);
            if matches!(v2, Cir::Erased) && !cir_uses(&b2, 0) {
                return strip_binder(&b2);
            }
            Cir::Let(Box::new(v2), Box::new(b2))
        }
        Cir::Con(c2, args, al) => {
            Cir::Con(c2.clone(), args.iter().map(dead_bindings).collect(), *al)
        }
        Cir::Case(s, arms) => Cir::Case(
            Box::new(dead_bindings(s)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: dead_bindings(&arm.body),
                })
                .collect(),
        ),
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(dead_bindings).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(dead_bindings(e))),
        Cir::Now(e, al) => Cir::Now(Box::new(dead_bindings(e)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(dead_bindings(e)), *al),
        Cir::Force(e) => Cir::Force(Box::new(dead_bindings(e))),
        Cir::Region(b) => Cir::Region(Box::new(dead_bindings(b))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(dead_bindings(arg)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(dead_bindings(body)),
            return_clause: Box::new(dead_bindings(return_clause)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), dead_bindings(e)))
                .collect(),
        },
        Cir::MkClosure(f, env, al) => {
            Cir::MkClosure(f.clone(), env.iter().map(dead_bindings).collect(), *al)
        }
        Cir::EnvRef(_) => c.clone(),
        Cir::CallClosure(f, a) => {
            Cir::CallClosure(Box::new(dead_bindings(f)), Box::new(dead_bindings(a)))
        }
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(dead_bindings(lhs)),
            rhs: Box::new(dead_bindings(rhs)),
        },
    }
}

/// Does `c` reference the variable at de Bruijn index `i` (under the binders crossed)?
pub(crate) fn cir_uses(c: &Cir, i: usize) -> bool {
    match c {
        Cir::Var(j) => *j == i,
        Cir::Global(_) | Cir::Erased | Cir::Foreign(_) => false,
        Cir::Lam(b) | Cir::Fix(b) => cir_uses(b, i + 1),
        Cir::App(f, a) => cir_uses(f, i) || cir_uses(a, i),
        Cir::Let(v, b) => cir_uses(v, i) || cir_uses(b, i + 1),
        Cir::Con(_, args, _) | Cir::Tuple(args, _) => args.iter().any(|a| cir_uses(a, i)),
        Cir::Case(s, arms) => {
            cir_uses(s, i) || arms.iter().any(|arm| cir_uses(&arm.body, i + arm.binders))
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            cir_uses(e, i)
        }
        Cir::Op { arg, .. } => cir_uses(arg, i),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            cir_uses(body, i)
                || cir_uses(return_clause, i + 1)
                || op_clauses.iter().any(|(_, e)| cir_uses(e, i + 2))
        }
        Cir::MkClosure(_, env, _) => env.iter().any(|e| cir_uses(e, i)),
        Cir::EnvRef(_) => false,
        Cir::CallClosure(f, a) => cir_uses(f, i) || cir_uses(a, i),
        Cir::IntLit(_) => false,
        Cir::IntPrim { lhs, rhs, .. } => cir_uses(lhs, i) || cir_uses(rhs, i),
    }
}

/// Remove the innermost binder from `body` (which does not use it), lowering every free index by
/// one. Used when a dead binding/argument is dropped.
fn strip_binder(body: &Cir) -> Cir {
    // The binder at index 0 is unused; shift everything above it down by one.
    shift_cir_down(body, 0)
}

fn shift_cir_down(c: &Cir, depth: usize) -> Cir {
    match c {
        Cir::Var(i) => {
            if *i > depth {
                Cir::Var(i - 1)
            } else {
                Cir::Var(*i)
            }
        }
        Cir::Global(_) | Cir::Erased | Cir::Foreign(_) | Cir::IntLit(_) => c.clone(),
        Cir::Lam(b) => Cir::Lam(Box::new(shift_cir_down(b, depth + 1))),
        Cir::Fix(b) => Cir::Fix(Box::new(shift_cir_down(b, depth + 1))),
        Cir::App(f, a) => Cir::App(
            Box::new(shift_cir_down(f, depth)),
            Box::new(shift_cir_down(a, depth)),
        ),
        Cir::Let(v, b) => Cir::Let(
            Box::new(shift_cir_down(v, depth)),
            Box::new(shift_cir_down(b, depth + 1)),
        ),
        Cir::Con(c2, args, al) => Cir::Con(
            c2.clone(),
            args.iter().map(|a| shift_cir_down(a, depth)).collect(),
            *al,
        ),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(shift_cir_down(s, depth)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: shift_cir_down(&arm.body, depth + arm.binders),
                })
                .collect(),
        ),
        Cir::Tuple(es, al) => {
            Cir::Tuple(es.iter().map(|e| shift_cir_down(e, depth)).collect(), *al)
        }
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(shift_cir_down(e, depth))),
        Cir::Now(e, al) => Cir::Now(Box::new(shift_cir_down(e, depth)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(shift_cir_down(e, depth)), *al),
        Cir::Force(e) => Cir::Force(Box::new(shift_cir_down(e, depth))),
        Cir::Region(b) => Cir::Region(Box::new(shift_cir_down(b, depth))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(shift_cir_down(arg, depth)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(shift_cir_down(body, depth)),
            return_clause: Box::new(shift_cir_down(return_clause, depth)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), shift_cir_down(e, depth)))
                .collect(),
        },
        Cir::MkClosure(f, env, al) => Cir::MkClosure(
            f.clone(),
            env.iter().map(|e| shift_cir_down(e, depth)).collect(),
            *al,
        ),
        Cir::EnvRef(_) => c.clone(),
        Cir::CallClosure(f, a) => Cir::CallClosure(
            Box::new(shift_cir_down(f, depth)),
            Box::new(shift_cir_down(a, depth)),
        ),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(shift_cir_down(lhs, depth)),
            rhs: Box::new(shift_cir_down(rhs, depth)),
        },
    }
}

/// Raise every free de Bruijn index `>= depth` in `c` by one (the dual of [`shift_cir_down`]). Used
/// to slide a term under one freshly-introduced binder — e.g. wrapping a handler body computation in
/// a thunk `λ_. body` for closure-based handler installation.
fn shift_cir_up(c: &Cir, depth: usize) -> Cir {
    match c {
        Cir::Var(i) => {
            if *i >= depth {
                Cir::Var(i + 1)
            } else {
                Cir::Var(*i)
            }
        }
        Cir::Global(_) | Cir::Erased | Cir::EnvRef(_) | Cir::Foreign(_) | Cir::IntLit(_) => {
            c.clone()
        }
        Cir::Lam(b) => Cir::Lam(Box::new(shift_cir_up(b, depth + 1))),
        Cir::Fix(b) => Cir::Fix(Box::new(shift_cir_up(b, depth + 1))),
        Cir::App(f, a) => Cir::App(
            Box::new(shift_cir_up(f, depth)),
            Box::new(shift_cir_up(a, depth)),
        ),
        Cir::Let(v, b) => Cir::Let(
            Box::new(shift_cir_up(v, depth)),
            Box::new(shift_cir_up(b, depth + 1)),
        ),
        Cir::Con(c2, args, al) => Cir::Con(
            c2.clone(),
            args.iter().map(|a| shift_cir_up(a, depth)).collect(),
            *al,
        ),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(shift_cir_up(s, depth)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: shift_cir_up(&arm.body, depth + arm.binders),
                })
                .collect(),
        ),
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(|e| shift_cir_up(e, depth)).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(shift_cir_up(e, depth))),
        Cir::Now(e, al) => Cir::Now(Box::new(shift_cir_up(e, depth)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(shift_cir_up(e, depth)), *al),
        Cir::Force(e) => Cir::Force(Box::new(shift_cir_up(e, depth))),
        Cir::Region(b) => Cir::Region(Box::new(shift_cir_up(b, depth))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(shift_cir_up(arg, depth)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(shift_cir_up(body, depth)),
            return_clause: Box::new(shift_cir_up(return_clause, depth)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), shift_cir_up(e, depth)))
                .collect(),
        },
        Cir::MkClosure(f, env, al) => Cir::MkClosure(
            f.clone(),
            env.iter().map(|e| shift_cir_up(e, depth)).collect(),
            *al,
        ),
        Cir::CallClosure(f, a) => Cir::CallClosure(
            Box::new(shift_cir_up(f, depth)),
            Box::new(shift_cir_up(a, depth)),
        ),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(shift_cir_up(lhs, depth)),
            rhs: Box::new(shift_cir_up(rhs, depth)),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::signature::{Constructor, DataDecl};
    use blight_kernel::term::Interval;
    use blight_kernel::term::Level;
    use blight_kernel::ConName;

    fn nat_name() -> DataName {
        DataName("Nat".into())
    }

    /// A `Nat` signature: `Zero | Succ (n : Nat)`.
    fn nat_sig() -> Signature {
        let mut sig = Signature::new();
        sig.declare(DataDecl {
            name: nat_name(),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![
                Constructor {
                    name: ConName("Zero".into()),
                    args: vec![],
                    result_indices: vec![],
                },
                Constructor {
                    name: ConName("Succ".into()),
                    args: vec![Arg::Rec(vec![])],
                    result_indices: vec![],
                },
            ],
            path_constructors: vec![],
        });
        sig
    }

    fn u0() -> Term {
        Term::Univ(Level::Zero)
    }

    /// An `Elim` over `Nat` lowers to a `Fix (lam scrut. case scrut of [Zero arm, Succ arm])`,
    /// with the `Succ` arm binding the predecessor field and an induction hypothesis `self pred`.
    #[test]
    fn lower_elim_to_case() {
        let sig = nat_sig();
        // Elim Nat motive [m_zero, m_succ] (Zero) — scrutinee is a constructor.
        let term = Term::Elim {
            data: nat_name(),
            motive: Box::new(u0()),
            methods: vec![Term::Var(0), Term::Var(1)],
            scrutinee: Box::new(Term::Con(ConName("Zero".into()), vec![])),
        };
        let cir = lower_erased(&term, &sig);
        // App(Fix(Lam(Case(Var0, arms))), Con Zero)
        let Cir::App(elim_fn, scrut) = &cir else {
            panic!("expected an application, got {cir:?}");
        };
        assert_eq!(**scrut, Cir::con(ConName("Zero".into()), vec![]));
        let Cir::Fix(lam) = &**elim_fn else {
            panic!("expected a Fix, got {elim_fn:?}");
        };
        let Cir::Lam(case) = &**lam else {
            panic!("expected a Lam, got {lam:?}");
        };
        let Cir::Case(_scrut, arms) = &**case else {
            panic!("expected a Case, got {case:?}");
        };
        assert_eq!(arms.len(), 2);
        assert_eq!(arms[0].con, ConName("Zero".into()));
        assert_eq!(arms[0].binders, 0);
        assert_eq!(arms[1].con, ConName("Succ".into()));
        assert_eq!(arms[1].binders, 1);
        // The Succ arm body applies the method to the field (Var 0) and the IH (self field).
        // self is at index nfields+1 = 2 inside the arm.
        if let Cir::App(inner, ih) = &arms[1].body {
            assert_eq!(
                **ih,
                Cir::App(Box::new(Cir::Var(2)), Box::new(Cir::Var(0))),
                "the IH is `self pred`"
            );
            if let Cir::App(_method, field) = &**inner {
                assert_eq!(**field, Cir::Var(0), "the method is applied to the field");
            } else {
                panic!("expected method applied to field, got {inner:?}");
            }
        } else {
            panic!(
                "expected Succ arm to be an application, got {:?}",
                arms[1].body
            );
        }
    }

    /// A `Lam` whose body has `Later (self ...)` lowers to a `Cir::Fix`.
    #[test]
    fn lower_later_to_fix_thunk() {
        let sig = Signature::new();
        // λ self. later (self <something>) — the partial-recursion shape.
        let body = Term::Later(Box::new(Term::App(
            Box::new(Term::Var(0)),
            Box::new(Term::Con(ConName("Zero".into()), vec![])),
        )));
        let term = Term::Lam(Box::new(body));
        let cir = lower_erased(&term, &sig);
        match cir {
            Cir::Fix(inner) => match *inner {
                Cir::Later(_, _) => {}
                other => panic!("expected Fix(Later ...), got Fix({other:?})"),
            },
            other => panic!("expected a Fix, got {other:?}"),
        }
    }

    /// A `PLam`/`PApp` (path) lowers to a function/application — paths become functions.
    #[test]
    fn paths_lowered_as_functions() {
        let sig = Signature::new();
        let plam = Term::PLam(Box::new(Term::Var(0)));
        assert_eq!(lower_erased(&plam, &sig), Cir::Lam(Box::new(Cir::Var(0))));
        let papp = Term::PApp(Box::new(Term::Var(0)), Interval::I0);
        assert_eq!(lower_erased(&papp, &sig), Cir::Var(0));
    }

    /// The dead-argument pass removes `(lam. body) Erased` when the binder is unused.
    #[test]
    fn dead_arg_eliminated() {
        // (λ x. y) Erased, where the body ignores x (refers to an outer var, index 1).
        let inner = Cir::App(
            Box::new(Cir::Lam(Box::new(Cir::Var(1)))),
            Box::new(Cir::Erased),
        );
        let cleaned = dead_bindings(&inner);
        // The erased argument and its binder vanish; `Var(1)` becomes `Var(0)`.
        assert_eq!(cleaned, Cir::Var(0));
        assert!(!contains_erased(&cleaned), "no Erased remains");
    }

    /// `lower` runs `erase` before translating: a grade-0 lambda binder is gone in the output.
    #[test]
    fn erase_runs_first() {
        let sig = Signature::new();
        // type: (x :^0 U0) -> U0 ; term: λ. Con Zero  (the body ignores x).
        let ty = Term::Pi(blight_kernel::Grade::Zero, Box::new(u0()), Box::new(u0()));
        let term = Term::Lam(Box::new(Term::Con(ConName("Zero".into()), vec![])));
        let cir = lower(&term, &ty, &sig);
        // The grade-0 λ is erased, leaving just the constructor (no Lam wrapper).
        assert_eq!(cir, Cir::con(ConName("Zero".into()), vec![]));
    }

    /// The desugared region redex `App(Ann(λ body, Π(1, Rgn, cod)), Con "rgn-tok")` lowers to a
    /// `Cir::Region` scope wrapping the body's allocation (spec §3.5). An ordinary application with
    /// a non-token argument must NOT be wrapped.
    #[test]
    fn region_scope_lowered() {
        let sig = nat_sig();
        // body = Con "Zero" []  (the region's result; the λ binder `r : Rgn` is unused here).
        let body = Term::Con(ConName("Zero".into()), vec![]);
        let lam = Term::Lam(Box::new(body));
        // Π(1, Rgn, Nat) — grade-1 binder over the opaque region handle.
        let pi = Term::Pi(
            Grade::One,
            Box::new(Term::Con(ConName("Rgn".into()), vec![])),
            Box::new(Term::Con(ConName("Nat".into()), vec![])),
        );
        let redex = Term::App(
            Box::new(Term::Ann(Box::new(lam), Box::new(pi))),
            Box::new(Term::Con(ConName("rgn-tok".into()), vec![])),
        );
        let cir = lower_erased(&redex, &sig);
        assert!(
            matches!(cir, Cir::Region(_)),
            "region redex lowers to a Cir::Region scope, got {cir:?}"
        );

        // An ordinary application (grade-many, non-token arg) stays a bare App.
        let plain = Term::App(
            Box::new(Term::Lam(Box::new(Term::Var(0)))),
            Box::new(Term::Con(ConName("Zero".into()), vec![])),
        );
        let cir2 = lower_erased(&plain, &sig);
        assert!(
            !matches!(cir2, Cir::Region(_)),
            "a plain application must not become a region scope, got {cir2:?}"
        );
    }

    fn contains_erased(c: &Cir) -> bool {
        match c {
            Cir::Erased => true,
            Cir::Var(_) | Cir::Global(_) | Cir::Foreign(_) | Cir::IntLit(_) => false,
            Cir::Lam(b) | Cir::Fix(b) => contains_erased(b),
            Cir::App(f, a) => contains_erased(f) || contains_erased(a),
            Cir::Let(v, b) => contains_erased(v) || contains_erased(b),
            Cir::Con(_, args, _) | Cir::Tuple(args, _) => args.iter().any(contains_erased),
            Cir::Case(s, arms) => {
                contains_erased(s) || arms.iter().any(|a| contains_erased(&a.body))
            }
            Cir::Proj(_, e)
            | Cir::Now(e, _)
            | Cir::Later(e, _)
            | Cir::Force(e)
            | Cir::Region(e) => contains_erased(e),
            Cir::Op { arg, .. } => contains_erased(arg),
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                contains_erased(body)
                    || contains_erased(return_clause)
                    || op_clauses.iter().any(|(_, e)| contains_erased(e))
            }
            Cir::MkClosure(_, env, _) => env.iter().any(contains_erased),
            Cir::EnvRef(_) => false,
            Cir::CallClosure(f, a) => contains_erased(f) || contains_erased(a),
            Cir::IntPrim { lhs, rhs, .. } => contains_erased(lhs) || contains_erased(rhs),
        }
    }
}
