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

use crate::ir::{Alloc, Arm, Cir};
use blight_kernel::signature::Arg;
use blight_kernel::{ConName, DataName, Grade, Signature, Term};

/// The region capability token constructor (declared in the untrusted prelude `regions.bl`). The
/// elaborator threads exactly this token into a `(region …)` desugaring.
const REGION_TOKEN: &str = "rgn-tok";

/// Whether `App(f, a)` is the desugared region redex `App(Ann(λ body, Π(1, _, _)), Con("rgn-tok"))`
/// the elaborator produces for `(region r body)`. Recognizing the grade-1 binder and the token
/// constructor keeps this from misfiring on ordinary applications.
/// Is `ty` (transparently through `Ann`) a `Pi` — i.e. would a bare reference to a `foreign`
/// postulate of this type be a function that must be called saturated, never used point-free?
fn is_pi_type(ty: &Term) -> bool {
    match ty {
        Term::Pi(..) => true,
        Term::Ann(t, _) => is_pi_type(t),
        _ => false,
    }
}

/// If `f` is (transparently through `Ann`) a `Term::Foreign`, return its C symbol — the head
/// recognized by `lower_term`'s `Term::App` case to flatten a saturated foreign call (spec §7.6,
/// Wave 2 / L2). Elaborated global references are inlined at their use site (this whole-program
/// compiler substitutes a global's definition wherever it is referenced — see `mono.rs`), so a call
/// to a `foreign`-declared name reaches `lower_term` as a literal `Term::Foreign` head, not an
/// indirection to resolve.
fn foreign_head(f: &Term) -> Option<&str> {
    match f {
        Term::Foreign { symbol, .. } => Some(symbol.as_str()),
        Term::Ann(t, _) => foreign_head(t),
        _ => None,
    }
}

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
            // A saturated (single-application) foreign call (spec §7.6, Wave 2 / L2's `F64` hatch):
            // `App(Foreign{symbol,..}, a)` lowers directly to the flat `Cir::Foreign(symbol, Some(a))`
            // rather than the generic curried `Cir::App`, which would (wrongly) try to treat the
            // 0-arg foreign *call's result* as a closure to further apply. Multi-operand foreign ops
            // (e.g. `f64+`) are declared with a SINGLE `Pi` argument that is itself a packed `Pair` —
            // exactly the `std/bytes.bl`/`std/array.bl` multi-arg-effect-op convention — so this one
            // case covers every arity the hatch supports; see `ir.rs`'s `Cir::Foreign` doc comment.
            if let Some(symbol) = foreign_head(f) {
                return Cir::Foreign(symbol.to_string(), Some(Box::new(lower_term(a, sig))));
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
        //
        // `now a` is eager: its payload is an already-available value, stored directly in the
        // `BL_NOW` node. `later a` is the *guarded* step of a (possibly diverging) `define-rec`
        // self-call; it must stay **lazy**, so we defer `a` behind a *thunk closure* `λ_. a`
        // (an ignored unit parameter) rather than evaluating it now. The runtime trampoline
        // `bl_force` drives a `BL_LATER` by *applying* that thunk through the ordinary closure
        // calling convention (`fn(clo, _)`), one step per back-edge, in bounded C stack — the M4
        // "million-deep recursion does not overflow" property. Eagerly lowering `later a` (the
        // previous behavior) both defeated that bound and stored a *value* where the trampoline
        // expects a thunk closure, so any program that actually reached the partial path
        // (`bl_force` on a real `later`) read a bogus function pointer and crashed. Wrapping in a
        // `Lam` here lets closure conversion lift the thunk and capture `self`/the step arguments
        // exactly like any other lambda.
        Term::Now(a) => Cir::now(lower_term(a, sig)),
        Term::Later(a) => {
            let inner = lower_term(a, sig);
            Cir::later(Cir::Lam(Box::new(shift_cir(&inner, 1))))
        }
        // `force d` drives the delay trampoline to a value (anf.rs lowers a tail `Force` to the
        // `bl_force` trampoline; bounded stack).
        Term::Force(a) => Cir::Force(Box::new(lower_term(a, sig))),
        // A BARE (unapplied) foreign postulate lowers to a 0-arg call to its external C symbol
        // (spec §7.6, the FFI hatch). `lower_term`'s `Term::App` case (`foreign_head`) intercepts
        // every SATURATED call of a function-typed foreign before it reaches here; a function-typed
        // `Term::Foreign` arriving here unapplied (e.g. a point-free reference passed as a value,
        // never called) would silently 0-arg-call a C function expecting a real argument — a
        // miscompile, not a runtime hazard, but one worth failing loudly on rather than emitting
        // silently wrong code (spec's "a claim that cannot close must fail, never be faked").
        Term::Foreign { symbol, ty } => {
            if is_pi_type(ty) {
                panic!(
                    "internal: function-typed `foreign` postulate `{symbol}` used unapplied \
                     (point-free) — every `foreign` of Pi type must be called fully saturated at \
                     each use site; see `lower.rs`'s `foreign_head`"
                );
            }
            Cir::Foreign(symbol.clone(), None)
        }
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
        // `if-zero s t e` (T1a): a native `i64` branch on the scrutinee. All three subterms are at
        // the same binder depth (no binder introduced), so they lower directly.
        Term::IfZero { scrut, then_, else_ } => Cir::IfZero {
            scrut: Box::new(lower_term(scrut, sig)),
            then_: Box::new(lower_term(then_, sig)),
            else_: Box::new(lower_term(else_, sig)),
        },
        // `Delay A` is a *type*; it has no runtime content of its own.
        Term::Delay(_) => Cir::Erased,

        // Effects (if not fully handled before codegen). A parameterized effect's `type_args`
        // (Wave 7/E2) are erased type-level content, like a `Data`'s params — they carry no
        // runtime representation, so codegen only lowers the value argument.
        Term::Op {
            effect,
            op,
            arg,
            type_args: _,
        } => Cir::Op {
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
        //
        // `PCon` (Wave 7/E4 HITs) belongs in this bucket too: unlike `PLam`/`PApp` (an ordinary
        // function over an erased dimension, so the *function* has real runtime content even
        // though its argument does not), a path constructor's dimension argument would have to be
        // *observed* to pick which boundary/interior point it denotes — but a dimension carries no
        // runtime data at all (module doc, spec §2.6). A well-typed program can only route a `PCon`
        // through positions the grading discipline already marks irrelevant (the classic circle
        // recursor's codomain is a Kan-filled type precisely so eliminating it never needs to
        // *inspect* the dimension at runtime), so this placeholder is unreachable in practice, same
        // as its cubical siblings below.
        Term::Univ(_)
        | Term::Pi(_, _, _)
        | Term::Sigma(_, _)
        | Term::Data(_, _, _)
        | Term::Interval(_)
        | Term::PathP { .. }
        | Term::PCon { .. }
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
            Cir::Global(_) | Cir::Erased => c.clone(),
            Cir::Foreign(sym, arg) => Cir::Foreign(
                sym.clone(),
                arg.as_ref().map(|a| Box::new(go(a, by, depth))),
            ),
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
            Cir::IntLit(_) | Cir::NatLit(_) | Cir::StrLit(_) => c.clone(),
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, depth)),
                rhs: Box::new(go(rhs, by, depth)),
            },
            // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
            Cir::IfZero { scrut, then_, else_ } => Cir::IfZero {
                scrut: Box::new(go(scrut, by, depth)),
                then_: Box::new(go(then_, by, depth)),
                else_: Box::new(go(else_, by, depth)),
            },
            Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, depth)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, by, depth))),
            },
            Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, depth)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, by, depth))),
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
                    .map(|fl| fl.map_cir(|x| go(x, by, depth)))
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
                    .map(|fl| fl.map_cir(|x| go(x, by, depth)))
                    .collect(),
                scrut: Box::new(go(scrut, by, depth)),
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
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(
            sym.clone(),
            arg.as_ref().map(|a| Box::new(dead_bindings(a))),
        ),
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
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero { scrut, then_, else_ } => Cir::IfZero {
            scrut: Box::new(dead_bindings(scrut)),
            then_: Box::new(dead_bindings(then_)),
            else_: Box::new(dead_bindings(else_)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(dead_bindings(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(dead_bindings(r))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(dead_bindings(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(dead_bindings(r))),
        },
        Cir::Flat {
            tag,
            fields,
            total_slots,
            alloc,
        } => Cir::Flat {
            tag: tag.clone(),
            fields: fields.iter().map(|fl| fl.map_cir(dead_bindings)).collect(),
            total_slots: *total_slots,
            alloc: *alloc,
        },
        Cir::FlatProj {
            index,
            layout,
            scrut,
        } => Cir::FlatProj {
            index: *index,
            layout: layout.iter().map(|fl| fl.map_cir(dead_bindings)).collect(),
            scrut: Box::new(dead_bindings(scrut)),
        },
    }
}

/// Does `c` reference the variable at de Bruijn index `i` (under the binders crossed)?
pub(crate) fn cir_uses(c: &Cir, i: usize) -> bool {
    match c {
        Cir::Var(j) => *j == i,
        Cir::Global(_) | Cir::Erased => false,
        Cir::Foreign(_, arg) => arg.as_ref().is_some_and(|a| cir_uses(a, i)),
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
        Cir::IntLit(_) | Cir::NatLit(_) | Cir::StrLit(_) => false,
        Cir::IntPrim { lhs, rhs, .. } => cir_uses(lhs, i) || cir_uses(rhs, i),
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero { scrut, then_, else_ } => {
            cir_uses(scrut, i) || cir_uses(then_, i) || cir_uses(else_, i)
        }
        Cir::NatPrim { lhs, rhs, .. } => {
            cir_uses(lhs, i) || rhs.as_ref().map(|r| cir_uses(r, i)).unwrap_or(false)
        }
        Cir::FloatPrim { lhs, rhs, .. } => {
            cir_uses(lhs, i) || rhs.as_ref().map(|r| cir_uses(r, i)).unwrap_or(false)
        }
        Cir::Flat { fields, .. } => fields.iter().any(|fl| fl.any_cir(|x| cir_uses(x, i))),
        Cir::FlatProj { layout, scrut, .. } => {
            cir_uses(scrut, i) || layout.iter().any(|fl| fl.any_cir(|x| cir_uses(x, i)))
        }
    }
}

/// Remove the innermost binder from `body` (which does not use it), lowering every free index by
/// one. Used when a dead binding/argument is dropped.
fn strip_binder(body: &Cir) -> Cir {
    // The binder at index 0 is unused; shift everything above it down by one.
    shift_cir_down(body, 0)
}

pub(crate) fn shift_cir_down(c: &Cir, depth: usize) -> Cir {
    match c {
        Cir::Var(i) => {
            if *i > depth {
                Cir::Var(i - 1)
            } else {
                Cir::Var(*i)
            }
        }
        Cir::Global(_) | Cir::Erased | Cir::IntLit(_) | Cir::NatLit(_) | Cir::StrLit(_) => {
            c.clone()
        }
        Cir::Foreign(sym, arg) => Cir::Foreign(
            sym.clone(),
            arg.as_ref().map(|a| Box::new(shift_cir_down(a, depth))),
        ),
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
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero { scrut, then_, else_ } => Cir::IfZero {
            scrut: Box::new(shift_cir_down(scrut, depth)),
            then_: Box::new(shift_cir_down(then_, depth)),
            else_: Box::new(shift_cir_down(else_, depth)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(shift_cir_down(lhs, depth)),
            rhs: rhs.as_ref().map(|r| Box::new(shift_cir_down(r, depth))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(shift_cir_down(lhs, depth)),
            rhs: rhs.as_ref().map(|r| Box::new(shift_cir_down(r, depth))),
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
                .map(|fl| fl.map_cir(|x| shift_cir_down(x, depth)))
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
                .map(|fl| fl.map_cir(|x| shift_cir_down(x, depth)))
                .collect(),
            scrut: Box::new(shift_cir_down(scrut, depth)),
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
        Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(
            sym.clone(),
            arg.as_ref().map(|a| Box::new(shift_cir_up(a, depth))),
        ),
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
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero { scrut, then_, else_ } => Cir::IfZero {
            scrut: Box::new(shift_cir_up(scrut, depth)),
            then_: Box::new(shift_cir_up(then_, depth)),
            else_: Box::new(shift_cir_up(else_, depth)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(shift_cir_up(lhs, depth)),
            rhs: rhs.as_ref().map(|r| Box::new(shift_cir_up(r, depth))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(shift_cir_up(lhs, depth)),
            rhs: rhs.as_ref().map(|r| Box::new(shift_cir_up(r, depth))),
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
                .map(|fl| fl.map_cir(|x| shift_cir_up(x, depth)))
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
                .map(|fl| fl.map_cir(|x| shift_cir_up(x, depth)))
                .collect(),
            scrut: Box::new(shift_cir_up(scrut, depth)),
        },
    }
}

// ============================================================================================
// P3 (3a) — the linear tail-accumulator elim-loop transform support.
//
// [`crate::elimloop`] recovers, from the eager catamorphism `Fix(Lam(Case(Var0, arms)))` that
// [`lower_elim_fn`] produced, a per-constructor [`CtorShape`] plus the bare (un-shifted) method for
// each arm, then calls [`build_elim_loop`] to (when the pattern matches) rebuild the eliminator as a
// **bounded-stack accumulator loop** — a `Fix(Lam(Case(Proj(0, state), …)))` whose recursive arm is a
// *tail* self-application over a packed `(scrut, a1…ak)` state tuple. After closure conversion that
// tail self-call becomes a [`crate::anf::Tail::Jump`] (a loop back-edge), so a `fuel`-deep input runs
// in O(1) C stack instead of descending the spine with an eager non-tail self-call.
//
// Zero TCB: this is a pure `Cir → Cir` rewrite downstream of kernel checking; a bug is a wrong
// *number* (caught by the `BL_NO_ELIMLOOP` differential), never a false *proof*.
// ============================================================================================

/// The per-constructor structural shape [`crate::elimloop`] recovers from an eager eliminator arm:
/// the constructor name and, per kept field (in declaration order), whether that field is recursive
/// (carries an induction hypothesis).
pub(crate) struct CtorShape {
    pub name: ConName,
    pub is_rec: Vec<bool>,
}

/// Count the leading `Cir::Lam` binders of `c` (its syntactic arity before the first non-lambda).
pub(crate) fn count_leading_lams(c: &Cir) -> usize {
    let mut n = 0;
    let mut cur = c;
    while let Cir::Lam(b) = cur {
        n += 1;
        cur = b;
    }
    n
}

/// Peel exactly `n` leading `Cir::Lam` binders off `c`, returning the body, or `None` if `c` has
/// fewer than `n` leading lambdas.
fn peel_lams(c: &Cir, n: usize) -> Option<&Cir> {
    let mut cur = c;
    for _ in 0..n {
        match cur {
            Cir::Lam(b) => cur = b,
            _ => return None,
        }
    }
    Some(cur)
}

/// Apply `f(var_index, binder_depth)` at every [`Cir::Var`] leaf of `c`, where `binder_depth` counts
/// the binders entered between the root of `c` and that leaf. A single structural walker used to
/// build the de Bruijn shift and the method-body substitution the elim-loop transform needs, without
/// duplicating per-variant recursion.
fn map_vars(c: &Cir, depth: usize, f: &dyn Fn(usize, usize) -> Cir) -> Cir {
    match c {
        Cir::Var(i) => f(*i, depth),
        Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(
            sym.clone(),
            arg.as_ref().map(|a| Box::new(map_vars(a, depth, f))),
        ),
        Cir::Lam(b) => Cir::Lam(Box::new(map_vars(b, depth + 1, f))),
        Cir::Fix(b) => Cir::Fix(Box::new(map_vars(b, depth + 1, f))),
        Cir::App(g, a) => Cir::App(
            Box::new(map_vars(g, depth, f)),
            Box::new(map_vars(a, depth, f)),
        ),
        Cir::Let(v, b) => Cir::Let(
            Box::new(map_vars(v, depth, f)),
            Box::new(map_vars(b, depth + 1, f)),
        ),
        Cir::Con(n, args, al) => Cir::Con(
            n.clone(),
            args.iter().map(|a| map_vars(a, depth, f)).collect(),
            *al,
        ),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(map_vars(s, depth, f)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: map_vars(&arm.body, depth + arm.binders, f),
                })
                .collect(),
        ),
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(|e| map_vars(e, depth, f)).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(map_vars(e, depth, f))),
        Cir::Now(e, al) => Cir::Now(Box::new(map_vars(e, depth, f)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(map_vars(e, depth, f)), *al),
        Cir::Force(e) => Cir::Force(Box::new(map_vars(e, depth, f))),
        Cir::Region(b) => Cir::Region(Box::new(map_vars(b, depth, f))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(map_vars(arg, depth, f)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(map_vars(body, depth, f)),
            return_clause: Box::new(map_vars(return_clause, depth + 1, f)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), map_vars(e, depth + 2, f)))
                .collect(),
        },
        Cir::MkClosure(n, env, al) => Cir::MkClosure(
            n.clone(),
            env.iter().map(|e| map_vars(e, depth, f)).collect(),
            *al,
        ),
        Cir::CallClosure(g, a) => Cir::CallClosure(
            Box::new(map_vars(g, depth, f)),
            Box::new(map_vars(a, depth, f)),
        ),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(map_vars(lhs, depth, f)),
            rhs: Box::new(map_vars(rhs, depth, f)),
        },
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero { scrut, then_, else_ } => Cir::IfZero {
            scrut: Box::new(map_vars(scrut, depth, f)),
            then_: Box::new(map_vars(then_, depth, f)),
            else_: Box::new(map_vars(else_, depth, f)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(map_vars(lhs, depth, f)),
            rhs: rhs.as_ref().map(|r| Box::new(map_vars(r, depth, f))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(map_vars(lhs, depth, f)),
            rhs: rhs.as_ref().map(|r| Box::new(map_vars(r, depth, f))),
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
                .map(|fl| fl.map_cir(|x| map_vars(x, depth, f)))
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
                .map(|fl| fl.map_cir(|x| map_vars(x, depth, f)))
                .collect(),
            scrut: Box::new(map_vars(scrut, depth, f)),
        },
    }
}

/// Raise every free de Bruijn index of `c` (those `>= 0` at its root, accounting for inner binders)
/// by `by`. Used to slide an arm-scope replacement expression under the binders crossed inside a
/// substituted accumulator-update expression.
pub(crate) fn shift_free(c: &Cir, by: usize) -> Cir {
    if by == 0 {
        return c.clone();
    }
    map_vars(c, 0, &|i, d| {
        if i >= d {
            Cir::Var(i + by)
        } else {
            Cir::Var(i)
        }
    })
}

/// Substitute, in a recovered method body whose own scope has `nb` leading binders, each local
/// binder index by its loop-scope replacement from `local_map` (length `nb`, given in the loop arm's
/// scope at depth 0), and shift every free variable (index `>= nb`, captured from outside the
/// original eliminator) up by `free_shift`. Replacements are shifted under whatever binders the
/// substitution descends through, so this is capture-avoiding.
fn subst_method_body(body: &Cir, nb: usize, local_map: &[Cir], free_shift: usize) -> Cir {
    map_vars(body, 0, &|i, d| {
        if i < d {
            // A binder introduced *inside* the body itself.
            Cir::Var(i)
        } else {
            let j = i - d; // index into the method's own (nb-binder + free) scope
            if j < nb {
                shift_free(&local_map[j], d)
            } else {
                Cir::Var((j - nb) + free_shift + d)
            }
        }
    })
}

/// Does `c` contain an effect node ([`Cir::Op`]/[`Cir::Handle`])? The elim-loop transform reorders an
/// accumulator update relative to the (now tail) recursive call, so it must refuse any update that
/// performs an effect — purity is what makes the reordering observationally invisible.
pub(crate) fn cir_has_effect(c: &Cir) -> bool {
    match c {
        Cir::Op { .. } | Cir::Handle { .. } => true,
        _ => {
            let mut found = false;
            visit_children(c, &mut |child| {
                if !found {
                    found = cir_has_effect(child);
                }
            });
            found
        }
    }
}

/// Visit each immediate `Cir` child of `c` (no de Bruijn tracking — used for structural predicates).
/// Exposed to [`crate::autopar`] (P4) so its whole-program candidate scan doesn't need a fourth copy
/// of this traversal (`elimloop`/`cse`/`fusion` each already keep their own transform-shaped one).
pub(crate) fn visit_children(c: &Cir, f: &mut impl FnMut(&Cir)) {
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
        Cir::Lam(b) | Cir::Fix(b) => f(b),
        Cir::App(a, b) | Cir::Let(a, b) | Cir::CallClosure(a, b) => {
            f(a);
            f(b);
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            for a in args {
                f(a);
            }
        }
        Cir::Case(s, arms) => {
            f(s);
            for arm in arms {
                f(&arm.body);
            }
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            f(e)
        }
        Cir::Op { arg, .. } => f(arg),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            f(body);
            f(return_clause);
            for (_, e) in op_clauses {
                f(e);
            }
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero { scrut, then_, else_ } => {
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
        Cir::Flat { fields, .. } => {
            for fl in fields {
                fl.any_cir(|x| {
                    f(x);
                    false
                });
            }
        }
        Cir::FlatProj { layout, scrut, .. } => {
            f(scrut);
            for fl in layout {
                fl.any_cir(|x| {
                    f(x);
                    false
                });
            }
        }
    }
}

/// One leading binder of a recovered eliminator method, in outer-to-inner declaration order.
enum BinderKind {
    /// The `j`-th kept constructor field.
    Field(usize),
    /// The induction hypothesis for the `j`-th (recursive) field.
    Ih(usize),
    /// A motive accumulator parameter (the function-typed motive's arguments).
    Acc,
}

/// Try to rebuild a linear tail-accumulator catamorphism as a bounded-stack accumulator loop.
///
/// `ctors`/`methods` are the per-arm shapes and bare (un-shifted, own-scope) methods [`crate::elimloop`]
/// recovered from the eager `Fix(Lam(Case(Var0, arms)))`. Returns `Some(loop)` — a curried
/// `λscrut.λa1…λak. (fix loop. λstate. case state.0 …) (scrut, a1…ak)` of the **same type** as the
/// original eliminator (so it is a drop-in, eta-long replacement even under partial application) —
/// when every recursive constructor:
///   * has exactly **one** recursive field (linear recursion; trees fall through to the 3b worklist);
///   * abstracts `nfields + nrec + k` leading lambdas with the same `k >= 1` (a function-typed motive
///     with `k` accumulators); and
///   * uses its induction hypothesis **exactly once, in tail position, saturated to all `k`
///     accumulators**, with no effect in any accumulator-update expression.
///
/// Otherwise returns `None` (the caller falls back to the worklist or the eager form).
pub(crate) fn build_elim_loop(ctors: &[CtorShape], methods: &[Cir]) -> Option<Cir> {
    if ctors.len() != methods.len() || ctors.is_empty() {
        return None;
    }

    enum ArmInfo {
        Base,
        Rec { rec_field: usize, bs: Vec<Cir> },
    }

    let mut k: Option<usize> = None;
    let mut infos: Vec<ArmInfo> = Vec::with_capacity(ctors.len());

    for (idx, ctor) in ctors.iter().enumerate() {
        let nfields = ctor.is_rec.len();
        let nrec = ctor.is_rec.iter().filter(|&&r| r).count();
        if nrec == 0 {
            infos.push(ArmInfo::Base);
            continue;
        }
        // Linear only: a multi-recursive-field constructor (e.g. a binary tree) is the 3b worklist's
        // job, not this tail-accumulator loop.
        if nrec != 1 {
            return None;
        }
        let rec_field = ctor.is_rec.iter().position(|&r| r).unwrap();

        // Accumulator arity for this arm = leading lambdas beyond the (fields + IHs) binders.
        let total_lams = count_leading_lams(&methods[idx]);
        if total_lams < nfields + nrec {
            return None;
        }
        let kk = total_lams - (nfields + nrec);
        if kk == 0 {
            // No accumulator: the IH is consumed non-tail (a fold like `length`/`sum`); 3b's job.
            return None;
        }
        match k {
            None => k = Some(kk),
            Some(prev) if prev != kk => return None,
            _ => {}
        }
        let nb = nfields + nrec + kk;

        // The body lives under all `nb` binders. Build the binder list (outer→inner) so we can find
        // the IH's body-relative de Bruijn index.
        let mut outer: Vec<BinderKind> = Vec::with_capacity(nb);
        for j in 0..nfields {
            outer.push(BinderKind::Field(j));
            if ctor.is_rec[j] {
                outer.push(BinderKind::Ih(j));
            }
        }
        for _ in 0..kk {
            outer.push(BinderKind::Acc);
        }
        debug_assert_eq!(outer.len(), nb);

        let body = peel_lams(&methods[idx], nb)?;

        // Body-index of the IH binder: outer position p sits at index nb-1-p inside the body.
        let ih_outer_pos = outer
            .iter()
            .position(|b| matches!(b, BinderKind::Ih(j) if *j == rec_field))
            .unwrap();
        let ih_index = nb - 1 - ih_outer_pos;

        // Require the body to be `ih B1 … Bk` (IH in head position, saturated to exactly k args).
        let (head, args) = body.unapply();
        if args.len() != kk {
            return None;
        }
        if !matches!(head, Cir::Var(i) if *i == ih_index) {
            return None;
        }
        // The IH must be used *exactly once* (only as the head): it must not appear in any update,
        // and no update may perform an effect (the loop reorders updates before the recursive call).
        for a in &args {
            if cir_uses(a, ih_index) || cir_has_effect(a) {
                return None;
            }
        }
        let bs: Vec<Cir> = args.iter().map(|a| (*a).clone()).collect();
        infos.push(ArmInfo::Rec { rec_field, bs });
    }

    let k = k?; // at least one recursive constructor, else nothing to make stack-safe

    // Build the loop arms. Inside the loop's `Lam` (state = Var 0, self = Var 1), each arm binds the
    // constructor's `nfields` real fields (no IH binder). The first thing every arm body does is
    // *alias the state tuple to a fresh local* `s` (`let s = state in …`). This is deliberate and
    // load-bearing for de Bruijn correctness: the ANF normalizer threads outer-variable shifts
    // through case-arm scrutinee slots and operand sequencing, and reading a *deep* outer variable
    // (the `state` tuple, which sits above the field binders) repeatedly across several sequenced
    // operands is exactly the shape its deferred-shift composition mishandles. By binding `s` once
    // (a zero-`Comp` atom alias that introduces no shift frame) we make every subsequent
    // `Proj(1+i, s)` read a *recently bound, low-index* local — the same shape as an ordinary deep
    // `let` chain — so all the operand sequencing stays within the well-exercised path.
    //
    // After `let s = state`, the arm's innermost scope is:
    //   s         = Var(0)
    //   field j   = Var(nfields - j)        (the field binders, shifted up by the `s` alias)
    //   state     = Var(nfields + 1)        (no longer read directly)
    //   self      = Var(nfields + 2)        (the `Fix` binder)
    // A captured method free var (index >= `nb` in the eager method body — bound outside the
    // eliminator) sits `free_shift = k + nfields + 4` binders out: `k+1` wrapper lambdas + `Fix`
    // self + `Lam` state + `nfields` field binders + the `s` alias.
    let loop_arms: Vec<Arm> = ctors
        .iter()
        .zip(infos.iter())
        .enumerate()
        .map(|(idx, (ctor, info))| {
            let nfields = ctor.is_rec.len();
            let self_idx = nfields + 2;
            let free_shift = k + nfields + 4;
            let field_var = |fj: usize| Cir::Var(nfields - fj);
            // Accumulator `i` is the (1+i)'th slot of the state tuple, read through the local alias
            // `s` = Var(0).
            let acc_proj = |i: usize| Cir::Proj(1 + i, Box::new(Cir::Var(0)));

            let core = match info {
                ArmInfo::Base => {
                    // Apply the bare base method (shifted into the arm scope) to its fields then the
                    // `k` accumulators — exactly the value the eager arm yields once saturated.
                    let mut applied = shift_free(&methods[idx], free_shift);
                    for j in 0..nfields {
                        applied = Cir::App(Box::new(applied), Box::new(field_var(j)));
                    }
                    for i in 0..k {
                        applied = Cir::App(Box::new(applied), Box::new(acc_proj(i)));
                    }
                    applied
                }
                ArmInfo::Rec { rec_field, bs } => {
                    let nrec = 1usize;
                    let nb = nfields + nrec + k;
                    let mut outer: Vec<BinderKind> = Vec::with_capacity(nb);
                    for j in 0..nfields {
                        outer.push(BinderKind::Field(j));
                        if ctor.is_rec[j] {
                            outer.push(BinderKind::Ih(j));
                        }
                    }
                    for _ in 0..k {
                        outer.push(BinderKind::Acc);
                    }
                    // Map the method body's `nb` local binders to arm-scope replacements.
                    let mut local_map = vec![Cir::Erased; nb];
                    let mut acc_i = 0usize;
                    for (p, kind) in outer.iter().enumerate() {
                        let bidx = nb - 1 - p;
                        local_map[bidx] = match kind {
                            BinderKind::Field(fj) => field_var(*fj),
                            BinderKind::Ih(_) => Cir::Erased, // verified unused in any update
                            BinderKind::Acc => {
                                let e = acc_proj(acc_i);
                                acc_i += 1;
                                e
                            }
                        };
                    }
                    // New state = (recursive field, B1', …, Bk'); tail self-call → Jump.
                    let mut state_elems = Vec::with_capacity(k + 1);
                    state_elems.push(field_var(*rec_field));
                    for b in bs {
                        state_elems.push(subst_method_body(b, nb, &local_map, free_shift));
                    }
                    Cir::App(
                        Box::new(Cir::Var(self_idx)),
                        Box::new(Cir::Tuple(state_elems, Alloc::Gc)),
                    )
                }
            };

            // `let s = state in <core>` — `state` is Var(nfields) *before* this alias binder.
            Arm {
                con: ctor.name.clone(),
                binders: nfields,
                body: Cir::Let(Box::new(Cir::Var(nfields)), Box::new(core)),
            }
        })
        .collect();

    // LOOP = fix self. λ state. case state.0 of <loop_arms>
    let loop_fix = Cir::Fix(Box::new(Cir::Lam(Box::new(Cir::Case(
        Box::new(Cir::Proj(0, Box::new(Cir::Var(0)))),
        loop_arms,
    )))));

    // Wrapper: λ scrut. λ a1. … λ ak. LOOP (scrut, a1, …, ak)  (scrut = Var k, ai = Var (k-i)).
    let init_state: Vec<Cir> = (0..=k).map(|i| Cir::Var(k - i)).collect();
    let mut wrapper = Cir::App(
        Box::new(loop_fix),
        Box::new(Cir::Tuple(init_state, Alloc::Gc)),
    );
    for _ in 0..=k {
        wrapper = Cir::Lam(Box::new(wrapper));
    }
    Some(wrapper)
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
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
            motive: Rc::new(u0()),
            methods: vec![Term::Var(0), Term::Var(1)],
            scrutinee: Rc::new(Term::Con(ConName("Zero".into()), vec![])),
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
        let body = Term::Later(Rc::new(Term::App(
            Rc::new(Term::Var(0)),
            Rc::new(Term::Con(ConName("Zero".into()), vec![])),
        )));
        let term = Term::Lam(Rc::new(body));
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
        let plam = Term::PLam(Rc::new(Term::Var(0)));
        assert_eq!(lower_erased(&plam, &sig), Cir::Lam(Box::new(Cir::Var(0))));
        let papp = Term::PApp(Rc::new(Term::Var(0)), Interval::I0);
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
        let ty = Term::Pi(blight_kernel::Grade::Zero, Rc::new(u0()), Rc::new(u0()));
        let term = Term::Lam(Rc::new(Term::Con(ConName("Zero".into()), vec![])));
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
        let lam = Term::Lam(Rc::new(body));
        // Π(1, Rgn, Nat) — grade-1 binder over the opaque region handle.
        let pi = Term::Pi(
            Grade::One,
            Rc::new(Term::Con(ConName("Rgn".into()), vec![])),
            Rc::new(Term::Con(ConName("Nat".into()), vec![])),
        );
        let redex = Term::App(
            Rc::new(Term::Ann(Rc::new(lam), Rc::new(pi))),
            Rc::new(Term::Con(ConName("rgn-tok".into()), vec![])),
        );
        let cir = lower_erased(&redex, &sig);
        assert!(
            matches!(cir, Cir::Region(_)),
            "region redex lowers to a Cir::Region scope, got {cir:?}"
        );

        // An ordinary application (grade-many, non-token arg) stays a bare App.
        let plain = Term::App(
            Rc::new(Term::Lam(Rc::new(Term::Var(0)))),
            Rc::new(Term::Con(ConName("Zero".into()), vec![])),
        );
        let cir2 = lower_erased(&plain, &sig);
        assert!(
            !matches!(cir2, Cir::Region(_)),
            "a plain application must not become a region scope, got {cir2:?}"
        );
    }

    /// The `sum-go` method shapes: `Zero ↦ λidx.λacc. acc`, and
    /// `Succ ↦ λf.λih.λidx.λacc. ih (Succ idx) (acc + idx)` (the IH used once, in tail position,
    /// saturated to the two accumulators — exactly what `recognize` leaves after folding `plus`).
    fn sum_go_methods() -> (Vec<CtorShape>, Vec<Cir>) {
        use crate::ir::NatPrimOp;
        // body indices in Succ method scope: f=3, ih=2, idx=1, acc=0.
        let succ_body = Cir::App(
            Box::new(Cir::App(
                Box::new(Cir::Var(2)),                                         // ih
                Box::new(Cir::con(ConName("Succ".into()), vec![Cir::Var(1)])), // Succ idx
            )),
            Box::new(Cir::NatPrim {
                op: NatPrimOp::Add,
                lhs: Box::new(Cir::Var(0)),       // acc
                rhs: Some(Box::new(Cir::Var(1))), // idx
            }),
        );
        let succ_method = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Lam(
            Box::new(succ_body),
        )))))));
        let zero_method = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Var(0))))); // λidx.λacc. acc
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
        (ctors, vec![zero_method, succ_method])
    }

    /// 3a: the tail-accumulator `sum-go` catamorphism rebuilds as a `λscrut.λidx.λacc.` wrapper around
    /// a `fix loop. λstate. case state.0 …` whose `Succ` arm is a **tail self-application** over the
    /// updated `(pred, Succ idx, acc+idx)` state — i.e. a loop back-edge, no eager non-tail IH.
    #[test]
    fn build_elim_loop_rewrites_tail_accumulator() {
        use crate::ir::NatPrimOp;
        let (ctors, methods) = sum_go_methods();
        let looped = build_elim_loop(&ctors, &methods).expect("sum-go matches the 3a pattern");

        // Wrapper: k+1 = 3 leading lambdas, then `App(Fix, Tuple[scrut, idx, acc])`.
        assert_eq!(count_leading_lams(&looped), 3, "λscrut.λidx.λacc. …");
        let inner = peel_lams(&looped, 3).unwrap();
        let Cir::App(fixfn, init) = inner else {
            panic!("expected `LOOP init_state`, got {inner:?}");
        };
        assert_eq!(
            **init,
            Cir::Tuple(vec![Cir::Var(2), Cir::Var(1), Cir::Var(0)], Alloc::Gc),
            "initial state is (scrut, a1, a2) from the wrapper binders"
        );
        let Cir::Fix(lam) = fixfn.as_ref() else {
            panic!("expected a Fix loop, got {fixfn:?}");
        };
        let Cir::Lam(case) = lam.as_ref() else {
            panic!("expected the loop's λstate, got {lam:?}");
        };
        let Cir::Case(scrut, arms) = case.as_ref() else {
            panic!("expected `case state.0`, got {case:?}");
        };
        assert_eq!(
            **scrut,
            Cir::Proj(0, Box::new(Cir::Var(0))),
            "scrutinee is the state's first slot"
        );
        assert_eq!(arms.len(), 2);

        // Succ arm: binds the one field; the body aliases the state tuple to a local `s` (= Var 0)
        // then is the *tail* self-application over the new state tuple, reading each accumulator as
        // `Proj(1+i, s)`. With k=2, nfields=1 and the `s` alias on top: self = Var 3,
        // field(pred) = Var 1, s = Var 0.
        let succ = &arms[1];
        assert_eq!(succ.con, ConName("Succ".into()));
        assert_eq!(succ.binders, 1);
        let s = || Cir::Var(0);
        let core = Cir::App(
            Box::new(Cir::Var(3)), // self
            Box::new(Cir::Tuple(
                vec![
                    Cir::Var(1), // pred field (recursive field), shifted past the `s` alias
                    // Succ idx, where idx = s slot 1
                    Cir::con(ConName("Succ".into()), vec![Cir::Proj(1, Box::new(s()))]),
                    // acc + idx = s slot 2 + s slot 1
                    Cir::NatPrim {
                        op: NatPrimOp::Add,
                        lhs: Box::new(Cir::Proj(2, Box::new(s()))),
                        rhs: Some(Box::new(Cir::Proj(1, Box::new(s())))),
                    },
                ],
                Alloc::Gc,
            )),
        );
        // The whole arm body is `let s = state in <core>`; with nfields = 1, state = Var 1 here.
        let expected_succ = Cir::Let(Box::new(Cir::Var(1)), Box::new(core));
        assert_eq!(succ.body, expected_succ, "Succ arm is a tail self-jump");

        // Zero arm: `let s = state in <base method applied to the accumulators>` (no recursion).
        let zero = &arms[0];
        assert_eq!(zero.con, ConName("Zero".into()));
        assert_eq!(zero.binders, 0);
        assert!(
            matches!(&zero.body, Cir::Let(v, b) if matches!(**v, Cir::Var(0)) && matches!(**b, Cir::App(_, _))),
            "Zero arm aliases state then applies the base method to the accumulators: {:?}",
            zero.body
        );
    }

    /// 3a guard: when the induction hypothesis is **not** in tail position (it is consumed by another
    /// operation, e.g. `(plus (ih …) acc)`), the pattern does not match and `build_elim_loop` declines
    /// (the caller falls back to the worklist / eager form).
    #[test]
    fn build_elim_loop_declines_non_tail_ih() {
        use crate::ir::NatPrimOp;
        let (ctors, mut methods) = sum_go_methods();
        // Succ method: `λf.λih.λidx.λacc. (ih idx acc) + acc` — IH no longer the spine head.
        let mut non_tail = Cir::NatPrim {
            op: NatPrimOp::Add,
            lhs: Box::new(Cir::App(
                Box::new(Cir::App(Box::new(Cir::Var(2)), Box::new(Cir::Var(1)))),
                Box::new(Cir::Var(0)),
            )),
            rhs: Some(Box::new(Cir::Var(0))),
        };
        for _ in 0..4 {
            non_tail = Cir::Lam(Box::new(non_tail));
        }
        methods[1] = non_tail;
        assert!(
            build_elim_loop(&ctors, &methods).is_none(),
            "a non-tail IH must not be looped (falls back)"
        );
    }

    /// 3a guard: a multi-recursive-field constructor (a binary tree) is the worklist's job, so the
    /// tail-accumulator loop declines it.
    #[test]
    fn build_elim_loop_declines_multi_recursive_field() {
        // A `Node l r` style constructor with two recursive fields.
        let ctors = vec![CtorShape {
            name: ConName("Node".into()),
            is_rec: vec![true, true],
        }];
        let methods = vec![Cir::Lam(Box::new(Cir::Var(0)))];
        assert!(
            build_elim_loop(&ctors, &methods).is_none(),
            "two recursive fields fall through to 3b"
        );
    }

    fn contains_erased(c: &Cir) -> bool {
        match c {
            Cir::Erased => true,
            Cir::Var(_) | Cir::Global(_) | Cir::IntLit(_) | Cir::NatLit(_) | Cir::StrLit(_) => {
                false
            }
            Cir::Foreign(_, arg) => arg.as_ref().is_some_and(|a| contains_erased(a)),
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
            Cir::IfZero { scrut, then_, else_ } => {
                contains_erased(scrut) || contains_erased(then_) || contains_erased(else_)
            }
            Cir::NatPrim { lhs, rhs, .. } => {
                contains_erased(lhs) || rhs.as_ref().map(|r| contains_erased(r)).unwrap_or(false)
            }
            Cir::FloatPrim { lhs, rhs, .. } => {
                contains_erased(lhs) || rhs.as_ref().map(|r| contains_erased(r)).unwrap_or(false)
            }
            Cir::Flat { fields, .. } => fields.iter().any(|fl| fl.any_cir(contains_erased)),
            Cir::FlatProj { layout, scrut, .. } => {
                contains_erased(scrut) || layout.iter().any(|fl| fl.any_cir(contains_erased))
            }
        }
    }
}
