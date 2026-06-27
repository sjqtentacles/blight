//! Whole-program monomorphization over the closure-converted [`crate::ir::Program`] (spec 7.5).
//!
//! Because globals are fully **inlined at elaboration**, each entry point is one closed,
//! self-contained term: there is no global call graph to specialize across. Monomorphization is
//! therefore an **intra-program** specialization (MLton-style) that removes the indirection left
//! by generics and trait dictionaries:
//!
//! - **Dictionary selection.** A trait dictionary is a tuple of methods; selecting a method is
//!   `Proj(i, Tuple[m0, m1, …])`, which reduces to `m_i`. After conversion the dictionary is
//!   often built and projected in the same term, so this statically resolves the method.
//! - **Known-closure specialization.** `CallClosure(MkClosure(f, env), arg)` calls a *statically
//!   known* function `f`. When `f` is non-recursive we inline its body, substituting the
//!   environment captures and the argument, which specializes a polymorphic function to its
//!   concrete instantiation and turns an indirect call into straight-line code.
//!
//! The pass iterates to a fixpoint (bounded), and is **untrusted**: it preserves behavior but a
//! mistake is a miscompilation, never an unsoundness.

use crate::ir::{Arm, Cir, Func, Program};
use std::collections::HashMap;

/// Monomorphize a closure-converted program: resolve dictionary selections and specialize known,
/// non-recursive closure calls. Returns a program in which residual generic indirection has been
/// removed where statically determinable.
pub fn monomorphize(prog: &Program) -> Program {
    let func_map: HashMap<String, Func> = prog
        .funcs
        .iter()
        .map(|f| (f.name.clone(), f.clone()))
        .collect();

    let mut entry = prog.entry.clone();
    // Iterate to a (bounded) fixpoint: each pass may expose new redexes.
    for _ in 0..MAX_ROUNDS {
        let next = reduce(&entry, &func_map);
        if next == entry {
            break;
        }
        entry = next;
    }

    // Reduce the bodies of any funcs that survive (those still referenced indirectly, e.g.
    // recursive functions or escaping closures).
    let funcs = prog
        .funcs
        .iter()
        .map(|f| {
            let mut body = f.body.clone();
            for _ in 0..MAX_ROUNDS {
                let next = reduce(&body, &func_map);
                if next == body {
                    break;
                }
                body = next;
            }
            Func {
                name: f.name.clone(),
                recursive: f.recursive,
                body,
            }
        })
        .collect();

    prune_unreachable(Program { funcs, entry })
}

const MAX_ROUNDS: usize = 64;

/// Drop functions that are never named by a reachable `MkClosure`. After specialization, the
/// inlined `λ`-shells left behind by closure conversion become unreferenced; removing them keeps
/// the emitted module free of dead code (so e.g. an erased grade-0 index leaves *no* residual
/// function shell). Reachability starts at the program `entry` and follows `MkClosure` name edges
/// to a fixpoint. This is a pure shrink and cannot change behavior of the running program.
pub fn prune_unreachable(prog: Program) -> Program {
    let by_name: HashMap<&str, &Func> = prog.funcs.iter().map(|f| (f.name.as_str(), f)).collect();

    let mut reachable: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut work: Vec<String> = Vec::new();
    collect_closure_names(&prog.entry, &mut work);
    while let Some(name) = work.pop() {
        if reachable.insert(name.clone()) {
            if let Some(f) = by_name.get(name.as_str()) {
                collect_closure_names(&f.body, &mut work);
            }
        }
    }

    let funcs = prog
        .funcs
        .iter()
        .filter(|f| reachable.contains(&f.name))
        .cloned()
        .collect();
    Program {
        funcs,
        entry: prog.entry,
    }
}

/// Push the name of every `MkClosure` appearing in `c` onto `out`.
fn collect_closure_names(c: &Cir, out: &mut Vec<String>) {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::Foreign(_)
        | Cir::IntLit(_) => {}
        Cir::Lam(b) | Cir::Fix(b) => collect_closure_names(b, out),
        Cir::App(f, a) | Cir::CallClosure(f, a) | Cir::Let(f, a) => {
            collect_closure_names(f, out);
            collect_closure_names(a, out);
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            collect_closure_names(lhs, out);
            collect_closure_names(rhs, out);
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) => {
            args.iter().for_each(|a| collect_closure_names(a, out))
        }
        Cir::MkClosure(n, caps, _) => {
            out.push(n.clone());
            caps.iter().for_each(|a| collect_closure_names(a, out));
        }
        Cir::Case(s, arms) => {
            collect_closure_names(s, out);
            arms.iter()
                .for_each(|a| collect_closure_names(&a.body, out));
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            collect_closure_names(e, out)
        }
        Cir::Op { arg, .. } => collect_closure_names(arg, out),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            collect_closure_names(body, out);
            collect_closure_names(return_clause, out);
            op_clauses
                .iter()
                .for_each(|(_, e)| collect_closure_names(e, out));
        }
    }
}

/// One reduction pass: dictionary selection + known-closure-call specialization, applied
/// bottom-up.
fn reduce(c: &Cir, funcs: &HashMap<String, Func>) -> Cir {
    // First reduce children, then attempt a redex at the root.
    let c = reduce_children(c, funcs);
    match &c {
        // Dictionary selection: project a statically-built tuple.
        Cir::Proj(i, e) => {
            if let Cir::Tuple(elems, _) = &**e {
                if let Some(elem) = elems.get(*i) {
                    return elem.clone();
                }
            }
            c
        }
        // Known-closure call: `CallClosure(MkClosure(f, env), arg)` with `f` non-recursive.
        Cir::CallClosure(callee, arg) => {
            if let Cir::MkClosure(name, env, _) = &**callee {
                if let Some(func) = funcs.get(name) {
                    // Beta-reducing `(λx. body) arg` to `body[arg/x]` is only sound when it does not
                    // *discard* an effect: if `arg` performs an effect (e.g. `perform print "A"`) and
                    // the parameter is unused (a discarded `let _ = …`), substitution would drop the
                    // operation entirely. In that case keep the call so the native OpNode-aware
                    // `bl_app` sequences the effect (its continuation is `λx. body`). Pure args, or a
                    // used parameter, inline freely.
                    let would_drop_effect = top_effectful(arg) && !body_uses_param(&func.body);
                    if !func.recursive && should_inline(&func.body) && !would_drop_effect {
                        // Substitute: de Bruijn 0 = arg; EnvRef(k) = env[k].
                        return instantiate(&func.body, arg, env);
                    }
                }
            }
            c
        }
        _ => c,
    }
}

/// Inline only when it will not blow up: the body must not itself contain another (different)
/// recursive self-call pattern, and we keep it simple by allowing any body (the bound rounds
/// prevent runaway). A more refined size heuristic can be layered later (spec 7.5 trade-off).
fn should_inline(_body: &Cir) -> bool {
    true
}

/// Does `c` perform an observable effect when evaluated *to a value at this position* — i.e. without
/// first crossing a binder that suspends evaluation? `perform`/`handle`/`force` are the effectful
/// eliminators; `Lam`/`Later` thunk their bodies, so an effect underneath them is not performed by
/// merely evaluating `c`. Used to decide whether dropping an unused beta-redex argument would lose
/// an effect (in which case we must keep the call so the runtime sequences it).
fn top_effectful(c: &Cir) -> bool {
    match c {
        Cir::Op { .. } | Cir::Handle { .. } | Cir::Force(_) => true,
        // Suspended: their bodies do not run when this node is evaluated.
        Cir::Lam(_) | Cir::Fix(_) | Cir::Later(_, _) => false,
        // A foreign C call may have arbitrary side effects, so never let beta-reduction discard one.
        Cir::Foreign(_) => true,
        Cir::Var(_) | Cir::Global(_) | Cir::Erased | Cir::EnvRef(_) | Cir::IntLit(_) => false,
        Cir::App(f, a) | Cir::CallClosure(f, a) => top_effectful(f) || top_effectful(a),
        Cir::IntPrim { lhs, rhs, .. } => top_effectful(lhs) || top_effectful(rhs),
        Cir::Let(v, b) => top_effectful(v) || top_effectful(b),
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().any(top_effectful)
        }
        Cir::Case(s, arms) => top_effectful(s) || arms.iter().any(|a| top_effectful(&a.body)),
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Region(e) => top_effectful(e),
    }
}

/// Does a closure body reference its parameter (de Bruijn 0)? After closure conversion the parameter
/// is `Var(0)` directly in the body (captures are `EnvRef`), so this is `cir_uses(body, 0)`.
fn body_uses_param(body: &Cir) -> bool {
    crate::lower::cir_uses(body, 0)
}

/// Substitute the closure's argument for de Bruijn 0 and the environment captures for `EnvRef(k)`
/// throughout `body`. Free de Bruijn variables above 0 are shifted down by one (the parameter is
/// consumed). The substituted `arg`/`env` are expressions in the *caller's* scope and must be
/// shifted as we descend under binders.
fn instantiate(body: &Cir, arg: &Cir, env: &[Cir]) -> Cir {
    fn go(c: &Cir, depth: usize, arg: &Cir, env: &[Cir]) -> Cir {
        match c {
            Cir::Var(i) => {
                if *i == depth {
                    shift(arg, depth)
                } else if *i > depth {
                    Cir::Var(i - 1)
                } else {
                    Cir::Var(*i)
                }
            }
            Cir::EnvRef(k) => {
                // Captures belong to the caller's scope; shift past the binders we crossed.
                shift(&env[*k], depth)
            }
            Cir::Global(_) | Cir::Erased | Cir::Foreign(_) | Cir::IntLit(_) => c.clone(),
            Cir::Lam(b) => Cir::Lam(Box::new(go(b, depth + 1, arg, env))),
            Cir::Fix(b) => Cir::Fix(Box::new(go(b, depth + 1, arg, env))),
            Cir::App(f, a) => Cir::App(
                Box::new(go(f, depth, arg, env)),
                Box::new(go(a, depth, arg, env)),
            ),
            Cir::CallClosure(f, a) => Cir::CallClosure(
                Box::new(go(f, depth, arg, env)),
                Box::new(go(a, depth, arg, env)),
            ),
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, depth, arg, env)),
                rhs: Box::new(go(rhs, depth, arg, env)),
            },
            Cir::Let(v, b) => Cir::Let(
                Box::new(go(v, depth, arg, env)),
                Box::new(go(b, depth + 1, arg, env)),
            ),
            Cir::Con(n, args, al) => Cir::Con(
                n.clone(),
                args.iter().map(|a| go(a, depth, arg, env)).collect(),
                *al,
            ),
            Cir::Tuple(args, al) => {
                Cir::Tuple(args.iter().map(|a| go(a, depth, arg, env)).collect(), *al)
            }
            Cir::MkClosure(n, caps, al) => Cir::MkClosure(
                n.clone(),
                caps.iter().map(|a| go(a, depth, arg, env)).collect(),
                *al,
            ),
            Cir::Case(s, arms) => Cir::Case(
                Box::new(go(s, depth, arg, env)),
                arms.iter()
                    .map(|a| Arm {
                        con: a.con.clone(),
                        binders: a.binders,
                        body: go(&a.body, depth + a.binders, arg, env),
                    })
                    .collect(),
            ),
            Cir::Proj(i, e) => Cir::Proj(*i, Box::new(go(e, depth, arg, env))),
            Cir::Now(e, al) => Cir::Now(Box::new(go(e, depth, arg, env)), *al),
            Cir::Later(e, al) => Cir::Later(Box::new(go(e, depth, arg, env)), *al),
            Cir::Force(e) => Cir::Force(Box::new(go(e, depth, arg, env))),
            Cir::Region(b) => Cir::Region(Box::new(go(b, depth, arg, env))),
            Cir::Op { effect, op, arg: a } => Cir::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(a, depth, arg, env)),
            },
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => Cir::Handle {
                body: Box::new(go(body, depth, arg, env)),
                return_clause: Box::new(go(return_clause, depth, arg, env)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(n, e)| (n.clone(), go(e, depth, arg, env)))
                    .collect(),
            },
        }
    }
    go(body, 0, arg, env)
}

/// Shift all free de Bruijn variables in `c` up by `by` (used when moving a caller-scope
/// expression under `by` binders introduced by the inlined body).
fn shift(c: &Cir, by: usize) -> Cir {
    fn go(c: &Cir, by: usize, depth: usize) -> Cir {
        match c {
            Cir::Var(i) => {
                if *i >= depth {
                    Cir::Var(i + by)
                } else {
                    Cir::Var(*i)
                }
            }
            Cir::Global(_) | Cir::EnvRef(_) | Cir::Erased | Cir::Foreign(_) | Cir::IntLit(_) => {
                c.clone()
            }
            Cir::Lam(b) => Cir::Lam(Box::new(go(b, by, depth + 1))),
            Cir::Fix(b) => Cir::Fix(Box::new(go(b, by, depth + 1))),
            Cir::App(f, a) => Cir::App(Box::new(go(f, by, depth)), Box::new(go(a, by, depth))),
            Cir::CallClosure(f, a) => {
                Cir::CallClosure(Box::new(go(f, by, depth)), Box::new(go(a, by, depth)))
            }
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, depth)),
                rhs: Box::new(go(rhs, by, depth)),
            },
            Cir::Let(v, b) => Cir::Let(Box::new(go(v, by, depth)), Box::new(go(b, by, depth + 1))),
            Cir::Con(n, args, al) => Cir::Con(
                n.clone(),
                args.iter().map(|a| go(a, by, depth)).collect(),
                *al,
            ),
            Cir::Tuple(args, al) => {
                Cir::Tuple(args.iter().map(|a| go(a, by, depth)).collect(), *al)
            }
            Cir::MkClosure(n, caps, al) => Cir::MkClosure(
                n.clone(),
                caps.iter().map(|a| go(a, by, depth)).collect(),
                *al,
            ),
            Cir::Case(s, arms) => Cir::Case(
                Box::new(go(s, by, depth)),
                arms.iter()
                    .map(|a| Arm {
                        con: a.con.clone(),
                        binders: a.binders,
                        body: go(&a.body, by, depth + a.binders),
                    })
                    .collect(),
            ),
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
                return_clause: Box::new(go(return_clause, by, depth)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(n, e)| (n.clone(), go(e, by, depth)))
                    .collect(),
            },
        }
    }
    if by == 0 {
        c.clone()
    } else {
        go(c, by, 0)
    }
}

/// Recurse into `c`'s children with `reduce`.
fn reduce_children(c: &Cir, funcs: &HashMap<String, Func>) -> Cir {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::Foreign(_)
        | Cir::IntLit(_) => c.clone(),
        Cir::Lam(b) => Cir::Lam(Box::new(reduce(b, funcs))),
        Cir::Fix(b) => Cir::Fix(Box::new(reduce(b, funcs))),
        Cir::App(f, a) => Cir::App(Box::new(reduce(f, funcs)), Box::new(reduce(a, funcs))),
        Cir::CallClosure(f, a) => {
            Cir::CallClosure(Box::new(reduce(f, funcs)), Box::new(reduce(a, funcs)))
        }
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(reduce(lhs, funcs)),
            rhs: Box::new(reduce(rhs, funcs)),
        },
        Cir::Let(v, b) => Cir::Let(Box::new(reduce(v, funcs)), Box::new(reduce(b, funcs))),
        Cir::Con(n, args, al) => Cir::Con(
            n.clone(),
            args.iter().map(|a| reduce(a, funcs)).collect(),
            *al,
        ),
        Cir::Tuple(args, al) => Cir::Tuple(args.iter().map(|a| reduce(a, funcs)).collect(), *al),
        Cir::MkClosure(n, caps, al) => Cir::MkClosure(
            n.clone(),
            caps.iter().map(|a| reduce(a, funcs)).collect(),
            *al,
        ),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(reduce(s, funcs)),
            arms.iter()
                .map(|a| Arm {
                    con: a.con.clone(),
                    binders: a.binders,
                    body: reduce(&a.body, funcs),
                })
                .collect(),
        ),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(reduce(e, funcs))),
        Cir::Now(e, al) => Cir::Now(Box::new(reduce(e, funcs)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(reduce(e, funcs)), *al),
        Cir::Force(e) => Cir::Force(Box::new(reduce(e, funcs))),
        Cir::Region(b) => Cir::Region(Box::new(reduce(b, funcs))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(reduce(arg, funcs)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(reduce(body, funcs)),
            return_clause: Box::new(reduce(return_clause, funcs)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), reduce(e, funcs)))
                .collect(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::closure;
    use blight_kernel::ConName;

    /// A dictionary selection `Proj(1, Tuple[Zero, Succ])` resolves to the second method.
    #[test]
    fn dict_application_specialized() {
        // (Proj 1 (Tuple [Con Zero, Con (Succ ...)]))
        let dict = Cir::tuple(vec![
            Cir::con(ConName("Zero".into()), vec![]),
            Cir::con(ConName("One".into()), vec![]),
        ]);
        let prog = Program {
            funcs: vec![],
            entry: Cir::Proj(1, Box::new(dict)),
        };
        let mono = monomorphize(&prog);
        assert_eq!(mono.entry, Cir::con(ConName("One".into()), vec![]));
    }

    /// The polymorphic identity, applied to a value, specializes to that value.
    #[test]
    fn polymorphic_id_specialized() {
        // id = λx. x ; entry = id (Con Zero)
        let id = Cir::Lam(Box::new(Cir::Var(0)));
        let term = Cir::App(
            Box::new(id),
            Box::new(Cir::con(ConName("Zero".into()), vec![])),
        );
        let prog = closure::convert(&term);
        let mono = monomorphize(&prog);
        // After specialization the application is gone, leaving the argument value.
        assert_eq!(mono.entry, Cir::con(ConName("Zero".into()), vec![]));
    }

    /// `show` for `Nat` (a dictionary method selected then applied) specializes to a direct call.
    /// Model: `show = λdict. λx. (Proj 0 dict) x`; applied to a concrete dict whose method is
    /// `λn. Con "S" [n]`. Specialization should collapse to `Con "S" [arg]`.
    #[test]
    fn mono_specializes_show_nat() {
        // method = λn. Con "S" [n]
        let method = Cir::Lam(Box::new(Cir::con(ConName("S".into()), vec![Cir::Var(0)])));
        // dict = Tuple [method]
        let dict = Cir::tuple(vec![method]);
        // show = λdict. λx. (Proj 0 dict) x   -> dict is Var 1, x is Var 0 inside
        let show = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::App(
            Box::new(Cir::Proj(0, Box::new(Cir::Var(1)))),
            Box::new(Cir::Var(0)),
        )))));
        // entry = show dict (Con Zero)
        let term = Cir::App(
            Box::new(Cir::App(Box::new(show), Box::new(dict))),
            Box::new(Cir::con(ConName("Zero".into()), vec![])),
        );
        let prog = closure::convert(&term);
        let mono = monomorphize(&prog);
        // Fully specialized: Con "S" [Con Zero].
        assert_eq!(
            mono.entry,
            Cir::con(
                ConName("S".into()),
                vec![Cir::con(ConName("Zero".into()), vec![])]
            ),
            "show Nat specializes to a direct constructor application: {:?}",
            mono.entry
        );
    }

    /// After specializing away an applied lambda, the lifted shell is unreferenced and pruned, so
    /// no dead `Func` survives into codegen.
    #[test]
    fn prune_drops_specialized_shells() {
        let id = Cir::Lam(Box::new(Cir::Var(0)));
        let term = Cir::App(
            Box::new(id),
            Box::new(Cir::con(ConName("Zero".into()), vec![])),
        );
        let prog = closure::convert(&term);
        assert!(
            !prog.funcs.is_empty(),
            "closure conversion lifts the id shell"
        );
        let mono = monomorphize(&prog);
        assert!(
            mono.funcs.is_empty(),
            "the inlined-away id shell must be pruned, leaving no dead funcs: {:?}",
            mono.funcs
        );
        assert_eq!(mono.entry, Cir::con(ConName("Zero".into()), vec![]));
    }
}
