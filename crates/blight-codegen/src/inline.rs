//! A4 — conservative cross-function inliner (an untrusted backend representation optimization).
//!
//! Closure conversion ([`crate::closure`]) lifts every lambda to a top-level [`Func`] taking one
//! value parameter (de Bruijn 0) plus an environment record. A function that captures **nothing** is
//! special: its body is *closed except for its single parameter* — it contains no [`Cir::EnvRef`]
//! and no free de Bruijn index `>= 1` (closure conversion proved both, see
//! [`crate::closure::Converter::lift`]). For such a function a call site is exactly
//! `CallClosure(MkClosure(name, []), arg)`, and inlining it is the textbook β-as-`let`:
//!
//! ```text
//!   CallClosure(MkClosure(f, []), arg)        ⇝   Let(arg, body_of_f)
//!   let c = MkClosure(f, []) in … (c arg) …   ⇝   let c = … in … Let(arg, body_of_f) …
//! ```
//!
//! Because the callee body's only free variable is its parameter (index 0) and a [`Cir::Let`] binds
//! its value as index 0 in the body, the de Bruijn indices line up **with no shifting at all**: the
//! body drops in verbatim, and `arg` (which lives in the caller's scope) is left untouched. Wrapping
//! the argument in a `let` (rather than substituting it into every parameter occurrence) is what makes
//! this **call-by-value-preserving**: `arg` is evaluated exactly once regardless of how many times the
//! parameter is used, so the transform preserves effects, work, *and* termination. The result is
//! observationally identical to the call — only the indirect call is gone.
//!
//! ## Direct vs. indirect call sites (why this complements `mono`)
//! [`crate::mono`]'s known-closure specialization already inlines the *direct* shape
//! `CallClosure(MkClosure(f, env), arg)` (head is a literal closure). What it leaves behind — and
//! what this pass adds — is the *indirect* shape: a captureless closure `let`-bound to a variable and
//! then called through that variable (`let c = MkClosure(f, []) in … (c x) …`), which arises whenever
//! a small helper is shared across several uses. We β-as-`let` each such call; the closure binding `c`
//! is kept untouched (it stays correct for any other / escaping uses, and is dropped by the linker if
//! it becomes dead), so no escape analysis is needed — every β-as-`let` is unconditionally valid.
//!
//! ## Why this is zero-TCB and bit-identical
//! Like every other backend fast path (recognize/unbox/flatten/spine-fusion) the inliner only
//! rewrites the **untrusted** `Cir`: the kernel and the independent re-checker never see ANF, so a
//! bug here can only ever produce a wrong *number*, never a false *proof*. It is gated by
//! `BL_NO_INLINE` and wired into the B1 differential corpus (`DIFF_FLAGS`), which builds the whole
//! example set with the pass on and off and asserts bit-identical stdout.
//!
//! ## The conservative guard (what we refuse to inline)
//! A callee is inlined only when it is **non-recursive**, **captureless**, **small** (its `Cir` node
//! count is at most [`INLINE_SIZE_BUDGET`]), and its body is free of:
//!   - effect operations / handlers ([`Cir::Op`], [`Cir::Handle`]) — the *effect-safety guard*;
//!   - region scopes / arena allocations ([`Cir::Region`], any [`Alloc::Arena`]) — splicing an
//!     arena allocation is sound only inside its originating region's dynamic extent, so we sidestep
//!     the whole question by never inlining a body that mentions one;
//!   - the FFI escape hatch ([`Cir::Foreign`]) and any stray [`Cir::EnvRef`] (belt-and-suspenders:
//!     a captureless body has none, but we never want to relocate one if it somehow appears).
//!
//! Direct self-recursion can never form a cycle (we only inline non-recursive functions, and the
//! lifted non-recursive functions form a DAG — a cycle would require a `Fix`, i.e. a *recursive*
//! function), but we additionally carry an expansion-path set so the pass is robustly terminating.
//!
//! ## Relationship to `mono`, and current firing status
//! [`crate::mono`] inlines a known closure call by **direct substitution** `body[arg/x]`, and
//! *deliberately declines* when the argument may perform an effect and the parameter is used a number
//! of times other than once (dropping or duplicating the effect would be unsound — see
//! `mono::reduce`). This pass is the **call-by-value-safe complement**: because it β-as-`let`s, it can
//! inline exactly those mono-declined captureless calls (the `let` runs the argument once regardless
//! of parameter-use count), plus the indirect `let`-bound captureless-closure calls mono's
//! literal-head matcher never inspects.
//!
//! **Status (like [`crate::flatten`]): proven, gated, differential-clean — currently subsumed by
//! `mono` on the example corpus, so it fires zero times today.** mono's substitution-based specializer
//! already reduces every direct non-recursive call the corpus contains; what it leaves is either
//! genuinely recursive, or an *interprocedural* closure flow (a small helper passed as an argument
//! into a recursive combinator and reached inside it via a parameter/`EnvRef`) — devirtualizing that
//! is the documented whole-program / higher-order-specialization follow-up, not a local rewrite. This
//! file lands the proven, bit-identical, `BL_NO_INLINE`-gated substrate and its B1 differential wiring
//! so the standing safety net (and the additive CBV-safe capability) is in place ahead of that work.

use crate::ir::{Alloc, Arm, Cir, FlatField, Func, Program};
use std::collections::{HashMap, HashSet};

/// Maximum callee `Cir` node count eligible for inlining. Small enough that inlining a leaf helper
/// (a projection, a constructor wrapper, a one-line arithmetic combinator) is a clear win and code
/// growth stays bounded; large bodies are left as out-of-line calls.
pub const INLINE_SIZE_BUDGET: usize = 24;

/// Inline every small, non-recursive, captureless, effect-free top-level function into its call
/// sites. Returns a new [`Program`] with the same `funcs` (now with inlined bodies; an inlined
/// function may become dead, which the linker drops) and an inlined `entry`.
pub fn inline(prog: &Program) -> Program {
    // The set of functions we are willing to inline, keyed by name → body. Built once up front so a
    // call site can look its callee up in O(1) and we never re-scan.
    let inlinable: HashMap<String, Cir> = prog
        .funcs
        .iter()
        .filter(|f| is_inlinable(f))
        .map(|f| (f.name.clone(), f.body.clone()))
        .collect();

    if inlinable.is_empty() {
        return prog.clone();
    }

    let mut sites = 0usize;
    let funcs = prog
        .funcs
        .iter()
        .map(|f| Func {
            name: f.name.clone(),
            recursive: f.recursive,
            // A function body opens under one binder: its parameter (de Bruijn 0), whose static
            // closure identity we do not know — so the scope starts with one unknown (`None`) slot.
            body: rewrite(
                &f.body,
                &inlinable,
                &mut vec![None],
                &mut HashSet::new(),
                &mut sites,
            ),
        })
        .collect();
    let entry = rewrite(
        &prog.entry,
        &inlinable,
        &mut Vec::new(),
        &mut HashSet::new(),
        &mut sites,
    );
    // Opt-in diagnostic (mirrors BL_GC_STATS): how many call sites were inlined and from how many
    // candidate functions. Written to stderr so it never contaminates a program's stdout golden.
    if std::env::var_os("BL_INLINE_STATS").is_some() {
        eprintln!(
            "BL_INLINE_STATS candidates={} sites_inlined={}",
            inlinable.len(),
            sites
        );
    }
    Program { funcs, entry }
}

/// Is `f` a legal inline target? See the module-level conservative guard.
fn is_inlinable(f: &Func) -> bool {
    !f.recursive && size_within(&f.body, INLINE_SIZE_BUDGET) && body_is_safe(&f.body)
}

/// Rewrite `c`, replacing each inlinable captureless call (direct or via a `let`-bound closure
/// variable) with a `let`-bound copy of the callee body.
///
/// `scope` is the de Bruijn binder stack: `scope[scope.len()-1]` is index 0, and each entry is
/// `Some(name)` when that binder is bound to `MkClosure(name, [])` for an inlinable `name` (so a call
/// through the variable can be devirtualized), else `None`. `active` is the set of callee names being
/// expanded along this path (a cycle guard); `sites` tallies inlined call sites for `BL_INLINE_STATS`.
fn rewrite(
    c: &Cir,
    inlinable: &HashMap<String, Cir>,
    scope: &mut Vec<Option<String>>,
    active: &mut HashSet<String>,
    sites: &mut usize,
) -> Cir {
    match c {
        // A call: try to resolve its head to an inlinable function (literal closure, or a scope
        // variable known to hold a captureless closure of one).
        Cir::CallClosure(f, a) | Cir::App(f, a) => {
            let target = call_target(f, scope, inlinable);
            if let Some(name) = target {
                if !active.contains(&name) {
                    if let Some(body) = inlinable.get(&name) {
                        // The argument is spliced unchanged into the caller's scope.
                        let arg = rewrite(a, inlinable, scope, active, sites);
                        // Expand the callee body in its *own* scope (param = index 0, otherwise
                        // closed), guarding against re-entering `name` along this path.
                        active.insert(name.clone());
                        let mut body_scope = vec![None];
                        let body = rewrite(body, inlinable, &mut body_scope, active, sites);
                        active.remove(&name);
                        *sites += 1;
                        // β-as-let: the body's parameter (de Bruijn 0) becomes this let binder; the
                        // body is otherwise closed, so no shifting is needed (see the module comment).
                        return Cir::Let(Box::new(arg), Box::new(body));
                    }
                }
            }
            // Not inlined: rewrite head and argument structurally (same scope).
            let nf = rewrite(f, inlinable, scope, active, sites);
            let na = rewrite(a, inlinable, scope, active, sites);
            match c {
                Cir::App(_, _) => Cir::App(Box::new(nf), Box::new(na)),
                _ => Cir::CallClosure(Box::new(nf), Box::new(na)),
            }
        }
        // A `let` binds one new innermost variable; record whether it names an inlinable closure so a
        // later call through it can be devirtualized.
        Cir::Let(v, b) => {
            let nv = rewrite(v, inlinable, scope, active, sites);
            let entry = closure_name(&nv, inlinable);
            scope.push(entry);
            let nb = rewrite(b, inlinable, scope, active, sites);
            scope.pop();
            Cir::Let(Box::new(nv), Box::new(nb))
        }
        // Other binder-introducing nodes: push the right number of unknown slots before recursing.
        Cir::Lam(b) => {
            scope.push(None);
            let nb = rewrite(b, inlinable, scope, active, sites);
            scope.pop();
            Cir::Lam(Box::new(nb))
        }
        Cir::Fix(b) => {
            scope.push(None);
            let nb = rewrite(b, inlinable, scope, active, sites);
            scope.pop();
            Cir::Fix(Box::new(nb))
        }
        Cir::Case(s, arms) => {
            let ns = rewrite(s, inlinable, scope, active, sites);
            let narms = arms
                .iter()
                .map(|arm| {
                    for _ in 0..arm.binders {
                        scope.push(None);
                    }
                    let body = rewrite(&arm.body, inlinable, scope, active, sites);
                    for _ in 0..arm.binders {
                        scope.pop();
                    }
                    Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body,
                    }
                })
                .collect();
            Cir::Case(Box::new(ns), narms)
        }
        // Everything else introduces no binders: rewrite each child in the same scope.
        _ => map_children(c, &mut |child| {
            rewrite(child, inlinable, scope, active, sites)
        }),
    }
}

/// Resolve a call head to the name of the inlinable function it calls, if any: a literal captureless
/// `MkClosure(name, [])`, or a scope variable bound to one.
fn call_target(
    head: &Cir,
    scope: &[Option<String>],
    inlinable: &HashMap<String, Cir>,
) -> Option<String> {
    match head {
        Cir::MkClosure(name, caps, _) if caps.is_empty() && inlinable.contains_key(name) => {
            Some(name.clone())
        }
        Cir::Var(k) => scope
            .len()
            .checked_sub(1 + *k)
            .and_then(|i| scope[i].clone()),
        _ => None,
    }
}

/// If `c` is a captureless closure of an inlinable function, its name (for the scope map), else None.
fn closure_name(c: &Cir, inlinable: &HashMap<String, Cir>) -> Option<String> {
    match c {
        Cir::MkClosure(name, caps, _) if caps.is_empty() && inlinable.contains_key(name) => {
            Some(name.clone())
        }
        _ => None,
    }
}

/// Structurally apply `f` to each immediate `Cir` child of `c`, rebuilding the node. (A small
/// hand-rolled functor so the rewrite stays a one-liner and never forgets a variant.)
fn map_children(c: &Cir, f: &mut impl FnMut(&Cir) -> Cir) -> Cir {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(sym.clone(), arg.as_ref().map(|a| Box::new(f(a)))),
        Cir::Lam(b) => Cir::Lam(Box::new(f(b))),
        Cir::Fix(b) => Cir::Fix(Box::new(f(b))),
        Cir::App(g, a) => Cir::App(Box::new(f(g)), Box::new(f(a))),
        Cir::CallClosure(g, a) => Cir::CallClosure(Box::new(f(g)), Box::new(f(a))),
        Cir::Let(v, b) => Cir::Let(Box::new(f(v)), Box::new(f(b))),
        Cir::Con(n, args, al) => Cir::Con(n.clone(), args.iter().map(f).collect(), *al),
        Cir::Tuple(args, al) => Cir::Tuple(args.iter().map(f).collect(), *al),
        Cir::MkClosure(n, args, al) => Cir::MkClosure(n.clone(), args.iter().map(f).collect(), *al),
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
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(f(e))),
        Cir::Now(e, al) => Cir::Now(Box::new(f(e)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(f(e)), *al),
        Cir::Force(e) => Cir::Force(Box::new(f(e))),
        Cir::Region(b) => Cir::Region(Box::new(f(b))),
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
            fields: fields.iter().map(|fl| fl.map_cir(|cc| f(cc))).collect(),
            total_slots: *total_slots,
            alloc: *alloc,
        },
        Cir::FlatProj {
            index,
            layout,
            scrut,
        } => Cir::FlatProj {
            index: *index,
            layout: layout.clone(),
            scrut: Box::new(f(scrut)),
        },
    }
}

/// Is the `Cir` node count of `c` at most `budget`? Short-circuits as soon as the budget is blown so
/// a huge body costs O(budget), not O(body).
fn size_within(c: &Cir, budget: usize) -> bool {
    fn go(c: &Cir, remaining: &mut isize) -> bool {
        if *remaining < 0 {
            return false;
        }
        *remaining -= 1;
        let mut ok = *remaining >= 0;
        if ok {
            visit_children(c, &mut |child| {
                if ok {
                    ok = go(child, remaining);
                }
            });
        }
        ok
    }
    let mut remaining = budget as isize;
    go(c, &mut remaining)
}

/// Does `c` avoid every construct the conservative guard forbids (effects, handlers, regions, arena
/// allocations, FFI, and stray env references)? See the module comment.
fn body_is_safe(c: &Cir) -> bool {
    match c {
        Cir::Op { .. }
        | Cir::Handle { .. }
        | Cir::Region(_)
        | Cir::Foreign(..)
        | Cir::EnvRef(_) => false,
        Cir::Con(_, _, Alloc::Arena)
        | Cir::Tuple(_, Alloc::Arena)
        | Cir::MkClosure(_, _, Alloc::Arena)
        | Cir::Now(_, Alloc::Arena)
        | Cir::Later(_, Alloc::Arena) => false,
        Cir::Flat {
            alloc: Alloc::Arena,
            ..
        } => false,
        _ => {
            let mut ok = true;
            visit_children(c, &mut |child| {
                if ok {
                    ok = body_is_safe(child);
                }
            });
            ok
        }
    }
}

/// Visit each immediate `Cir` child of `c` (read-only). Mirrors [`map_children`]'s structure.
fn visit_children(c: &Cir, f: &mut impl FnMut(&Cir)) {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => {}
        Cir::Foreign(_, arg) => {
            if let Some(a) = arg {
                f(a);
            }
        }
        Cir::Lam(b)
        | Cir::Fix(b)
        | Cir::Proj(_, b)
        | Cir::Now(b, _)
        | Cir::Later(b, _)
        | Cir::Force(b)
        | Cir::Region(b) => f(b),
        Cir::App(g, a) | Cir::CallClosure(g, a) | Cir::Let(g, a) => {
            f(g);
            f(a);
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().for_each(f)
        }
        Cir::Case(s, arms) => {
            f(s);
            arms.iter().for_each(|arm| f(&arm.body));
        }
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
        Cir::Flat { fields, .. } => {
            for fl in fields {
                visit_flatfield(fl, f);
            }
        }
        Cir::FlatProj { scrut, .. } => f(scrut),
    }
}

/// Visit every embedded `Cir` of a flattened field (a leaf value, or every slot of a nested
/// sub-product), in slot order.
fn visit_flatfield(fl: &FlatField, f: &mut impl FnMut(&Cir)) {
    match fl {
        FlatField::Leaf(c) => f(c),
        FlatField::Nested { slots, .. } => {
            for s in slots {
                visit_flatfield(s, f);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::ConName;

    /// A small, non-recursive, captureless function is inlined at its call site as a `let`-bound copy
    /// of its body, with the de Bruijn parameter becoming the let binder — and no leftover call.
    #[test]
    fn captureless_small_call_is_inlined() {
        // `id_f`: λx. x  (body = Var 0).  entry = id_f applied to a constructor value.
        let id_f = Func {
            name: "id_f".into(),
            recursive: false,
            body: Cir::Var(0),
        };
        let entry = Cir::CallClosure(
            Box::new(Cir::mkclosure("id_f".into(), vec![])),
            Box::new(Cir::con(ConName("Zero".into()), vec![])),
        );
        let prog = Program {
            funcs: vec![id_f],
            entry,
        };
        let out = inline(&prog);
        // entry becomes `let x = Zero in x` — no CallClosure remains.
        match &out.entry {
            Cir::Let(v, b) => {
                assert!(matches!(v.as_ref(), Cir::Con(_, _, _)));
                assert_eq!(**b, Cir::Var(0), "parameter ref became the let binder");
            }
            other => panic!("expected an inlined let, got {other:?}"),
        }
    }

    /// The indirect case: a captureless closure `let`-bound to a variable and then called through
    /// that variable is devirtualized and inlined (the binding is kept for any other uses). This is
    /// the shape `mono` leaves behind that the cross-function inliner is here to catch.
    #[test]
    fn let_bound_closure_call_is_inlined() {
        // id_f: λx. x
        let id_f = Func {
            name: "id_f".into(),
            recursive: false,
            body: Cir::Var(0),
        };
        // entry = let c = MkClosure(id_f, []) in (c Zero)   (c is de Bruijn 0 in the body)
        let entry = Cir::Let(
            Box::new(Cir::mkclosure("id_f".into(), vec![])),
            Box::new(Cir::CallClosure(
                Box::new(Cir::Var(0)),
                Box::new(Cir::con(ConName("Zero".into()), vec![])),
            )),
        );
        let prog = Program {
            funcs: vec![id_f],
            entry,
        };
        let out = inline(&prog);
        // entry = let c = MkClosure(id_f, []) in (let x = Zero in x) — the inner call is gone.
        let Cir::Let(_, inner) = &out.entry else {
            panic!("outer let preserved: {:?}", out.entry);
        };
        match inner.as_ref() {
            Cir::Let(v, b) => {
                assert!(matches!(v.as_ref(), Cir::Con(_, _, _)));
                assert_eq!(**b, Cir::Var(0));
            }
            other => panic!("indirect call should inline to a let: {other:?}"),
        }
    }

    /// A *recursive* function is never inlined (it would not terminate / it is not a DAG node).
    #[test]
    fn recursive_callee_not_inlined() {
        let rec = Func {
            name: "rec".into(),
            recursive: true,
            body: Cir::Var(0),
        };
        let entry = Cir::CallClosure(
            Box::new(Cir::mkclosure("rec".into(), vec![])),
            Box::new(Cir::Erased),
        );
        let prog = Program {
            funcs: vec![rec],
            entry,
        };
        let out = inline(&prog);
        assert!(
            matches!(out.entry, Cir::CallClosure(_, _)),
            "a recursive callee must not be inlined: {:?}",
            out.entry
        );
    }

    /// A *capturing* call site (non-empty `MkClosure` env) is never inlined — its environment is
    /// load-bearing and the body would reference it via `EnvRef`.
    #[test]
    fn capturing_call_not_inlined() {
        let f = Func {
            name: "g".into(),
            recursive: false,
            body: Cir::EnvRef(0),
        };
        let entry = Cir::CallClosure(
            Box::new(Cir::mkclosure("g".into(), vec![Cir::Var(0)])),
            Box::new(Cir::Erased),
        );
        let prog = Program {
            funcs: vec![f],
            entry,
        };
        let out = inline(&prog);
        assert!(
            matches!(out.entry, Cir::CallClosure(_, _)),
            "a capturing call must not be inlined: {:?}",
            out.entry
        );
    }

    /// The effect-safety guard: a function whose body performs an effect is not inlined.
    #[test]
    fn effectful_callee_not_inlined() {
        let f = Func {
            name: "do_op".into(),
            recursive: false,
            body: Cir::Op {
                effect: "Console".into(),
                op: "print".into(),
                arg: Box::new(Cir::Var(0)),
            },
        };
        let entry = Cir::CallClosure(
            Box::new(Cir::mkclosure("do_op".into(), vec![])),
            Box::new(Cir::Erased),
        );
        let prog = Program {
            funcs: vec![f],
            entry,
        };
        let out = inline(&prog);
        assert!(
            matches!(out.entry, Cir::CallClosure(_, _)),
            "an effectful callee must not be inlined: {:?}",
            out.entry
        );
    }

    /// A body larger than the budget is left as an out-of-line call.
    #[test]
    fn oversized_callee_not_inlined() {
        // Build a body well over the budget: a deep right-nested tuple chain.
        let mut body = Cir::Var(0);
        for _ in 0..(INLINE_SIZE_BUDGET + 5) {
            body = Cir::Tuple(vec![body], Alloc::Gc);
        }
        let f = Func {
            name: "big".into(),
            recursive: false,
            body,
        };
        let entry = Cir::CallClosure(
            Box::new(Cir::mkclosure("big".into(), vec![])),
            Box::new(Cir::Erased),
        );
        let prog = Program {
            funcs: vec![f],
            entry,
        };
        let out = inline(&prog);
        assert!(
            matches!(out.entry, Cir::CallClosure(_, _)),
            "an oversized callee must not be inlined: {:?}",
            out.entry
        );
    }

    /// Nested inlining: a chain `h → g → (leaf)` fully collapses, and the cycle guard makes the pass
    /// terminate even though we expand callee bodies recursively.
    #[test]
    fn nested_inlining_collapses_chain() {
        // leaf: λx. Succ x
        let leaf = Func {
            name: "leaf".into(),
            recursive: false,
            body: Cir::con(ConName("Succ".into()), vec![Cir::Var(0)]),
        };
        // g: λx. leaf x   (calls leaf)
        let g = Func {
            name: "g".into(),
            recursive: false,
            body: Cir::CallClosure(
                Box::new(Cir::mkclosure("leaf".into(), vec![])),
                Box::new(Cir::Var(0)),
            ),
        };
        // entry: g Zero
        let entry = Cir::CallClosure(
            Box::new(Cir::mkclosure("g".into(), vec![])),
            Box::new(Cir::con(ConName("Zero".into()), vec![])),
        );
        let prog = Program {
            funcs: vec![leaf, g],
            entry,
        };
        let out = inline(&prog);
        // No call closures remain anywhere in the inlined entry.
        fn has_call(c: &Cir) -> bool {
            let mut found = false;
            if matches!(c, Cir::CallClosure(_, _)) {
                return true;
            }
            super::visit_children(c, &mut |child| found = found || has_call(child));
            found
        }
        assert!(
            !has_call(&out.entry),
            "the whole call chain should inline away: {:?}",
            out.entry
        );
    }
}
