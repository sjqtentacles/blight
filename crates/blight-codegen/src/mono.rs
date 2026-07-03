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
    if std::env::var_os("BL_NO_MONO").is_some() {
        return prog.clone();
    }
    let func_map: HashMap<String, Func> = prog
        .funcs
        .iter()
        .map(|f| (f.name.clone(), f.clone()))
        .collect();
    // Whole-program effect analysis (computed once): which functions, fully applied, may perform an
    // effect. Used to decide whether dropping/duplicating a beta-redex argument is sound.
    let eff = effectful_funcs(&func_map);

    let mut entry = prog.entry.clone();
    // Iterate to a (bounded) fixpoint: each pass may expose new redexes.
    for _ in 0..MAX_ROUNDS {
        let next = reduce(&entry, &func_map, &eff);
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
                let next = reduce(&body, &func_map, &eff);
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
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => {}
        Cir::Foreign(_, arg) => {
            if let Some(a) = arg {
                collect_closure_names(a, out);
            }
        }
        Cir::Lam(b) | Cir::Fix(b) => collect_closure_names(b, out),
        Cir::App(f, a) | Cir::CallClosure(f, a) | Cir::Let(f, a) => {
            collect_closure_names(f, out);
            collect_closure_names(a, out);
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            collect_closure_names(lhs, out);
            collect_closure_names(rhs, out);
        }
        Cir::NatPrim { lhs, rhs, .. } => {
            collect_closure_names(lhs, out);
            if let Some(r) = rhs {
                collect_closure_names(r, out);
            }
        }
        Cir::FloatPrim { lhs, rhs, .. } => {
            collect_closure_names(lhs, out);
            if let Some(r) = rhs {
                collect_closure_names(r, out);
            }
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
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after monomorphization")
        }
    }
}

/// One reduction pass: dictionary selection + known-closure-call specialization, applied
/// bottom-up. `eff` is the whole-program set of effectful function names (see `effectful_funcs`).
fn reduce(c: &Cir, funcs: &HashMap<String, Func>, eff: &std::collections::HashSet<String>) -> Cir {
    // First reduce children, then attempt a redex at the root.
    let c = reduce_children(c, funcs, eff);
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
                    // Beta-reducing `(λx. body) arg` to `body[arg/x]` substitutes `arg` at *every* use
                    // of `x`. With an effectful `arg` (a `perform`/`force`/foreign call, or a *call*
                    // whose callee performs effects — the lexer's curried `wr …`/`fill-from …`) this
                    // is only sound when the effect runs exactly as often as before:
                    //   * unused param (0 uses) → substitution would *drop* the effect;
                    //   * 2+ uses               → substitution would *duplicate* it.
                    // So we inline an effectful `arg` only when the parameter is used *exactly once*
                    // (the effect still runs once); otherwise keep the call and let the native
                    // OpNode-aware `bl_app` sequence it (continuation = `λx. body`). Pure args inline
                    // freely regardless of use count. `arg_may_effect` uses the precomputed
                    // whole-program `eff` set, so it correctly sees a curried call to an effectful
                    // `define-rec` worker (whose `perform` sits under its parameter binders) while a
                    // genuinely pure recursor (`string-reverse`, palindrome) stays inlinable.
                    let uses = count_param_uses(&func.body);
                    let inhibits_effect_inline = uses != 1 && arg_may_effect(arg, eff);
                    if !func.recursive && should_inline(&func.body) && !inhibits_effect_inline {
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

/// Whole-program effect analysis (computed once, fixpoint): the set of function names whose body —
/// when **fully applied** — may perform an observable effect (`perform`/`force`/foreign), directly or
/// by calling another effectful function. Unlike a position-sensitive top-level effect check, this
/// scans
/// *through* `Lam`/`Fix`/`Later` binders: a curried recursive worker (the lexer's `wr`/`fill-from`)
/// carries its `perform set-byte` under the `λh.λi.…` parameter binders, and fully applying it runs
/// that body. A function calling such a worker (the 3-arg wrapper, or `main`) is transitively
/// effectful. Call heads are resolved through `MkClosure`/`Global` names (currying chains included).
/// This is used only to decide whether *dropping/duplicating* a beta-redex argument is sound, so an
/// over-approximation (treating a never-fully-applied partial as effectful) only costs a missed
/// inline, never correctness.
fn effectful_funcs(funcs: &HashMap<String, Func>) -> std::collections::HashSet<String> {
    use std::collections::HashSet;
    // direct[f] = f's body syntactically contains an Op/Force/Foreign (scanning through binders).
    // calls[f]  = set of function names f's body calls (resolved heads).
    fn scan(c: &Cir, direct: &mut bool, calls: &mut HashSet<String>) {
        match c {
            Cir::Op { arg, .. } => {
                *direct = true;
                scan(arg, direct, calls);
            }
            Cir::Force(e) => {
                *direct = true;
                scan(e, direct, calls);
            }
            Cir::Foreign(_, arg) => {
                *direct = true;
                if let Some(a) = arg {
                    scan(a, direct, calls);
                }
            }
            Cir::App(f, a) | Cir::CallClosure(f, a) => {
                // Resolve the (possibly curried) head to a function name and record the call edge.
                let mut head = &**f;
                loop {
                    match head {
                        Cir::App(g, _) | Cir::CallClosure(g, _) => head = g,
                        Cir::MkClosure(name, _, _) | Cir::Global(name) => {
                            calls.insert(name.clone());
                            break;
                        }
                        _ => break,
                    }
                }
                scan(f, direct, calls);
                scan(a, direct, calls);
            }
            Cir::Lam(b) | Cir::Fix(b) | Cir::Later(b, _) => scan(b, direct, calls),
            Cir::Let(v, b) => {
                scan(v, direct, calls);
                scan(b, direct, calls);
            }
            Cir::Con(_, args, _) | Cir::Tuple(args, _) => {
                for a in args {
                    scan(a, direct, calls);
                }
            }
            // A `MkClosure(name, caps)` is a *value* that exists to be applied (often indirectly, by
            // being returned and then called at another site — e.g. the lexer's continuation chain
            // `rec_1` → `lam_8` returns `MkClosure(lam_7)` which is then applied to the recursion, and
            // the `perform set-byte` lives in `lam_7`). A purely syntactic "head resolves to a name"
            // call graph misses these indirect applications, so we conservatively record *every*
            // referenced closure name as a potential call edge. This over-approximates effectfulness
            // (a closure that is built but never applied is treated as if called), which for the
            // drop/duplicate decision only costs a missed inline, never a dropped/duplicated effect.
            Cir::MkClosure(name, caps, _) => {
                calls.insert(name.clone());
                for a in caps {
                    scan(a, direct, calls);
                }
            }
            Cir::Case(s, arms) => {
                scan(s, direct, calls);
                for a in arms {
                    scan(&a.body, direct, calls);
                }
            }
            Cir::IntPrim { lhs, rhs, .. } => {
                scan(lhs, direct, calls);
                scan(rhs, direct, calls);
            }
            Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
                scan(lhs, direct, calls);
                if let Some(r) = rhs {
                    scan(r, direct, calls);
                }
            }
            Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Region(e) => scan(e, direct, calls),
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                // A `handle` installs a handler and runs its body (which may perform). Treat it as a
                // direct effect site and scan its sub-terms for call edges.
                *direct = true;
                scan(body, direct, calls);
                scan(return_clause, direct, calls);
                for (_, e) in op_clauses {
                    scan(e, direct, calls);
                }
            }
            Cir::Var(_)
            | Cir::EnvRef(_)
            | Cir::Global(_)
            | Cir::Erased
            | Cir::IntLit(_)
            | Cir::NatLit(_)
            | Cir::StrLit(_) => {}
            Cir::Flat { .. } | Cir::FlatProj { .. } => {
                unreachable!("flatten runs after monomorphization")
            }
        }
    }
    let mut direct: HashSet<String> = HashSet::new();
    let mut edges: HashMap<String, HashSet<String>> = HashMap::new();
    for (name, f) in funcs {
        let mut d = false;
        let mut calls = HashSet::new();
        scan(&f.body, &mut d, &mut calls);
        if d {
            direct.insert(name.clone());
        }
        edges.insert(name.clone(), calls);
    }
    // Fixpoint: propagate effectfulness backwards along call edges (f effectful if it calls any
    // effectful g). Iterate to saturation.
    let mut eff = direct;
    loop {
        let mut changed = false;
        for (name, callees) in &edges {
            if eff.contains(name) {
                continue;
            }
            if callees.iter().any(|c| eff.contains(c)) {
                eff.insert(name.clone());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    eff
}

/// Could *evaluating `arg` to a value at this position* perform an observable effect? Used to gate
/// dropping/duplicating a beta-redex argument. `arg` is effectful if, without first crossing a
/// suspending binder (`Lam`/`Fix`/`Later` — whose body is not run by evaluating `arg`), it reaches a
/// `perform`/`handle`/`force`/foreign node, **or** an application whose (possibly curried) head
/// resolves to a function in the whole-program effectful set `eff`. A `Var`/`EnvRef`-headed
/// application (a self-recursive or `let`-bound-closure call) is treated as maybe-effectful only when
/// it actually reaches `eff`; an unresolvable head is conservatively effectful (a missed inline, never
/// a dropped effect). This is the precise complement of `effectful_funcs`: the set sees through
/// parameter binders to find a worker's `perform`, and here we resolve the call edge to that worker.
fn arg_may_effect(c: &Cir, eff: &std::collections::HashSet<String>) -> bool {
    match c {
        Cir::Op { .. } | Cir::Handle { .. } | Cir::Force(_) | Cir::Foreign(..) => true,
        // Suspended: evaluating this node does not run the body.
        Cir::Lam(_) | Cir::Fix(_) | Cir::Later(_, _) => false,
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => false,
        Cir::App(f, a) | Cir::CallClosure(f, a) => {
            if arg_may_effect(f, eff) || arg_may_effect(a, eff) {
                return true;
            }
            // Resolve the (possibly curried) head to a function name; the call runs that body.
            let mut head = &**f;
            loop {
                match head {
                    Cir::App(g, _) | Cir::CallClosure(g, _) => head = g,
                    Cir::MkClosure(name, _, _) | Cir::Global(name) => {
                        return eff.contains(name);
                    }
                    // Self-recursive / let-bound-closure head we cannot name: conservatively keep.
                    Cir::Var(_) | Cir::EnvRef(_) => return true,
                    _ => return false,
                }
            }
        }
        Cir::IntPrim { lhs, rhs, .. } => arg_may_effect(lhs, eff) || arg_may_effect(rhs, eff),
        Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
            arg_may_effect(lhs, eff)
                || rhs
                    .as_ref()
                    .map(|r| arg_may_effect(r, eff))
                    .unwrap_or(false)
        }
        Cir::Let(v, b) => arg_may_effect(v, eff) || arg_may_effect(b, eff),
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().any(|a| arg_may_effect(a, eff))
        }
        Cir::Case(s, arms) => {
            arg_may_effect(s, eff) || arms.iter().any(|a| arg_may_effect(&a.body, eff))
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Region(e) => arg_may_effect(e, eff),
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after monomorphization")
        }
    }
}

/// Count how many times a closure body uses its parameter (de Bruijn 0), saturating at 2 (we only
/// ever distinguish 0 / exactly-1 / many). After closure conversion the parameter is `Var(0)` in the
/// body (captures are `EnvRef`); we descend tracking the binder depth so a nested `Var(depth)` is the
/// same parameter. Crucially, *any* use under a suspending binder (`Lam`/`Fix`/`Later` body) counts
/// as "many": that body may run more than once, so substituting an effectful argument there would
/// re-perform the effect per invocation. This is what makes effectful-argument inlining sound — it
/// fires only when the effect would run exactly once.
fn count_param_uses(body: &Cir) -> usize {
    fn go(c: &Cir, depth: usize, suspended: bool) -> usize {
        let cap = |n: usize| n.min(2);
        match c {
            Cir::Var(i) => {
                if *i == depth {
                    if suspended {
                        2
                    } else {
                        1
                    }
                } else {
                    0
                }
            }
            Cir::Global(_)
            | Cir::Erased
            | Cir::EnvRef(_)
            | Cir::IntLit(_)
            | Cir::NatLit(_)
            | Cir::StrLit(_) => 0,
            Cir::Foreign(_, arg) => arg.as_ref().map(|a| go(a, depth, suspended)).unwrap_or(0),
            // Suspending binders: a use inside runs an unknown number of times.
            Cir::Lam(b) | Cir::Fix(b) => cap(go(b, depth + 1, true)),
            Cir::Later(e, _) => cap(go(e, depth, true)),
            Cir::Let(v, b) => cap(go(v, depth, suspended) + go(b, depth + 1, suspended)),
            Cir::App(f, a) | Cir::CallClosure(f, a) => {
                cap(go(f, depth, suspended) + go(a, depth, suspended))
            }
            Cir::IntPrim { lhs, rhs, .. } => {
                cap(go(lhs, depth, suspended) + go(rhs, depth, suspended))
            }
            Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
                cap(go(lhs, depth, suspended)
                    + rhs.as_ref().map(|r| go(r, depth, suspended)).unwrap_or(0))
            }
            Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
                cap(args.iter().map(|a| go(a, depth, suspended)).sum())
            }
            // Each arm binds `arm.binders` fields, so the parameter is at `depth + binders` inside it.
            // Arms are alternatives (only one runs), but to stay conservative we sum: an effectful arg
            // used in two arms still must not be duplicated into both.
            Cir::Case(s, arms) => cap(go(s, depth, suspended)
                + arms
                    .iter()
                    .map(|a| go(&a.body, depth + a.binders, suspended))
                    .sum::<usize>()),
            Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Force(e) | Cir::Region(e) => {
                cap(go(e, depth, suspended))
            }
            Cir::Op { arg, .. } => cap(go(arg, depth, suspended)),
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => cap(go(body, depth, true)
                + go(return_clause, depth + 1, true)
                + op_clauses
                    .iter()
                    .map(|(_, e)| go(e, depth + 2, true))
                    .sum::<usize>()),
            Cir::Flat { .. } | Cir::FlatProj { .. } => {
                unreachable!("flatten runs after monomorphization")
            }
        }
    }
    go(body, 0, false)
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
            Cir::Global(_) | Cir::Erased | Cir::IntLit(_) | Cir::NatLit(_) | Cir::StrLit(_) => {
                c.clone()
            }
            Cir::Foreign(sym, a) => Cir::Foreign(
                sym.clone(),
                a.as_ref().map(|x| Box::new(go(x, depth, arg, env))),
            ),
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
            Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
                op: *op,
                lhs: Box::new(go(lhs, depth, arg, env)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, depth, arg, env))),
            },
            Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
                op: *op,
                lhs: Box::new(go(lhs, depth, arg, env)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, depth, arg, env))),
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
            Cir::Flat { .. } | Cir::FlatProj { .. } => {
                unreachable!("flatten runs after monomorphization")
            }
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
            Cir::Global(_)
            | Cir::EnvRef(_)
            | Cir::Erased
            | Cir::IntLit(_)
            | Cir::NatLit(_)
            | Cir::StrLit(_) => c.clone(),
            Cir::Foreign(sym, a) => {
                Cir::Foreign(sym.clone(), a.as_ref().map(|x| Box::new(go(x, by, depth))))
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
            Cir::Flat { .. } | Cir::FlatProj { .. } => {
                unreachable!("flatten runs after monomorphization")
            }
        }
    }
    if by == 0 {
        c.clone()
    } else {
        go(c, by, 0)
    }
}

/// Recurse into `c`'s children with `reduce`.
fn reduce_children(
    c: &Cir,
    funcs: &HashMap<String, Func>,
    eff: &std::collections::HashSet<String>,
) -> Cir {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(
            sym.clone(),
            arg.as_ref().map(|a| Box::new(reduce(a, funcs, eff))),
        ),
        Cir::Lam(b) => Cir::Lam(Box::new(reduce(b, funcs, eff))),
        Cir::Fix(b) => Cir::Fix(Box::new(reduce(b, funcs, eff))),
        Cir::App(f, a) => Cir::App(
            Box::new(reduce(f, funcs, eff)),
            Box::new(reduce(a, funcs, eff)),
        ),
        Cir::CallClosure(f, a) => Cir::CallClosure(
            Box::new(reduce(f, funcs, eff)),
            Box::new(reduce(a, funcs, eff)),
        ),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(reduce(lhs, funcs, eff)),
            rhs: Box::new(reduce(rhs, funcs, eff)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(reduce(lhs, funcs, eff)),
            rhs: rhs.as_ref().map(|r| Box::new(reduce(r, funcs, eff))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(reduce(lhs, funcs, eff)),
            rhs: rhs.as_ref().map(|r| Box::new(reduce(r, funcs, eff))),
        },
        Cir::Let(v, b) => Cir::Let(
            Box::new(reduce(v, funcs, eff)),
            Box::new(reduce(b, funcs, eff)),
        ),
        Cir::Con(n, args, al) => Cir::Con(
            n.clone(),
            args.iter().map(|a| reduce(a, funcs, eff)).collect(),
            *al,
        ),
        Cir::Tuple(args, al) => {
            Cir::Tuple(args.iter().map(|a| reduce(a, funcs, eff)).collect(), *al)
        }
        Cir::MkClosure(n, caps, al) => Cir::MkClosure(
            n.clone(),
            caps.iter().map(|a| reduce(a, funcs, eff)).collect(),
            *al,
        ),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(reduce(s, funcs, eff)),
            arms.iter()
                .map(|a| Arm {
                    con: a.con.clone(),
                    binders: a.binders,
                    body: reduce(&a.body, funcs, eff),
                })
                .collect(),
        ),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(reduce(e, funcs, eff))),
        Cir::Now(e, al) => Cir::Now(Box::new(reduce(e, funcs, eff)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(reduce(e, funcs, eff)), *al),
        Cir::Force(e) => Cir::Force(Box::new(reduce(e, funcs, eff))),
        Cir::Region(b) => Cir::Region(Box::new(reduce(b, funcs, eff))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(reduce(arg, funcs, eff)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(reduce(body, funcs, eff)),
            return_clause: Box::new(reduce(return_clause, funcs, eff)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), reduce(e, funcs, eff)))
                .collect(),
        },
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after monomorphization")
        }
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

    /// A small effectful `Op` (a `perform` with no continuation argument that matters here).
    fn perform_op() -> Cir {
        Cir::Op {
            effect: "Bytes".into(),
            op: "new-bytes".into(),
            arg: Box::new(Cir::con(ConName("Zero".into()), vec![])),
        }
    }

    /// Like `perform_op` but for the A3a `Arrays` effect's `new-array` — used by
    /// `effectful_new_array_used_twice_is_not_inlined` below to pin the same no-duplication property
    /// by name for the new effect, not just its `Bytes` sibling.
    fn perform_new_array_op() -> Cir {
        Cir::Op {
            effect: "Arrays".into(),
            op: "new-array".into(),
            arg: Box::new(Cir::con(ConName("Zero".into()), vec![])),
        }
    }

    /// Like `perform_op` but for the Wave 10 / P2 `Graphics` effect's `init-window` — used by
    /// `effectful_init_window_used_twice_is_not_inlined` below to pin the same no-duplication
    /// property by name for the graphics FFI go-bar's own effectful op (docs/design-wave4-gobars.md
    /// §5 item 4's required "double-`init-window` safety" regression).
    fn perform_init_window_op() -> Cir {
        Cir::Op {
            effect: "Graphics".into(),
            op: "init-window".into(),
            arg: Box::new(Cir::con(ConName("Zero".into()), vec![])),
        }
    }

    /// Build `entry = (λx. body) (perform …)` as a closure call over a non-recursive, non-capturing
    /// lifted function `f` whose body is `body`. This mirrors how a `let x = perform … in body`
    /// reaches the monomorphizer after closure conversion.
    fn call_with_effectful_arg(body: Cir) -> Program {
        Program {
            funcs: vec![Func {
                name: "f".into(),
                recursive: false,
                body,
            }],
            entry: Cir::CallClosure(
                Box::new(Cir::MkClosure("f".into(), vec![], crate::ir::Alloc::Gc)),
                Box::new(perform_op()),
            ),
        }
    }

    /// REGRESSION (C2 byte-buffer miscompile): an effectful argument whose parameter is used *more
    /// than once* must NOT be inlined — substituting it at every use duplicates the effect (e.g.
    /// `let h = perform new-bytes … in (… get h …) (… set h …)` would allocate two buffers and the
    /// `get` would read a different, empty one). The `CallClosure` must survive so the runtime
    /// performs the single effect once and shares its result.
    #[test]
    fn effectful_arg_used_twice_is_not_inlined() {
        // body = Tuple [Var0, Var0] — the parameter used twice.
        let body = Cir::tuple(vec![Cir::Var(0), Cir::Var(0)]);
        let prog = call_with_effectful_arg(body);
        let mono = monomorphize(&prog);
        assert!(
            matches!(mono.entry, Cir::CallClosure(_, _)),
            "an effectful arg used twice must keep its call (no effect duplication); got {:?}",
            mono.entry
        );
    }

    /// REGRESSION guard (A3a `Arrays`, mirrors the C2 `Bytes` regression above by name): an effectful
    /// `new-array` handle used *more than once* — e.g. `let h = perform new-array … in (set-elem h …)
    /// (get-elem h …)` — must NOT be inlined either, for exactly the same reason as `new-bytes`:
    /// substituting `h` at every use would allocate two arrays and `get-elem` would read a different,
    /// freshly zeroed one instead of the one `set-elem` wrote to. The monomorphizer's inlining
    /// decision is driven purely by `Cir::Op`'s effectfulness, not by which effect/op it names, so
    /// this exercises the identical code path as `effectful_arg_used_twice_is_not_inlined` under the
    /// concrete op the A3a feature actually introduces.
    #[test]
    fn effectful_new_array_used_twice_is_not_inlined() {
        let body = Cir::tuple(vec![Cir::Var(0), Cir::Var(0)]);
        let prog = Program {
            funcs: vec![Func {
                name: "f".into(),
                recursive: false,
                body,
            }],
            entry: Cir::CallClosure(
                Box::new(Cir::MkClosure("f".into(), vec![], crate::ir::Alloc::Gc)),
                Box::new(perform_new_array_op()),
            ),
        };
        let mono = monomorphize(&prog);
        assert!(
            matches!(mono.entry, Cir::CallClosure(_, _)),
            "an effectful `new-array` used twice must keep its call (no double allocation); got {:?}",
            mono.entry
        );
    }

    /// REGRESSION guard (Wave 10 / P2 `Graphics`, mirrors the A3a `Arrays` guard above by name): an
    /// effectful `init-window` handle used *more than once* must NOT be inlined either — a second
    /// window/renderer would be materialized if the `perform` were duplicated at every use site,
    /// exactly the same hazard `new-bytes`/`new-array` guard against. This is the
    /// docs/design-wave4-gobars.md §5 go-bar's explicitly required "double-`init-window` safety" test.
    #[test]
    fn effectful_init_window_used_twice_is_not_inlined() {
        let body = Cir::tuple(vec![Cir::Var(0), Cir::Var(0)]);
        let prog = Program {
            funcs: vec![Func {
                name: "f".into(),
                recursive: false,
                body,
            }],
            entry: Cir::CallClosure(
                Box::new(Cir::MkClosure("f".into(), vec![], crate::ir::Alloc::Gc)),
                Box::new(perform_init_window_op()),
            ),
        };
        let mono = monomorphize(&prog);
        assert!(
            matches!(mono.entry, Cir::CallClosure(_, _)),
            "an effectful `init-window` used twice must keep its call (no double window); got {:?}",
            mono.entry
        );
    }

    /// CONTROL: the same shape but the parameter is used *exactly once* inlines freely — the single
    /// effect still runs exactly once, now in argument position of the substituted expression.
    #[test]
    fn effectful_arg_used_once_inlines() {
        // body = Con "S" [Var0] — the parameter used once.
        let body = Cir::con(ConName("S".into()), vec![Cir::Var(0)]);
        let prog = call_with_effectful_arg(body);
        let mono = monomorphize(&prog);
        assert_eq!(
            mono.entry,
            Cir::con(ConName("S".into()), vec![perform_op()]),
            "an effectful arg used once inlines into its single use site: {:?}",
            mono.entry
        );
    }

    /// An effectful argument whose parameter is *unused* must NOT be inlined either — substitution
    /// would drop the effect entirely (a discarded `let _ = perform print …`).
    #[test]
    fn effectful_arg_unused_is_not_inlined() {
        // body = Con "Zero" [] — the parameter unused.
        let body = Cir::con(ConName("Zero".into()), vec![]);
        let prog = call_with_effectful_arg(body);
        let mono = monomorphize(&prog);
        assert!(
            matches!(mono.entry, Cir::CallClosure(_, _)),
            "an effectful arg with an unused param must keep its call (no effect dropped); got {:?}",
            mono.entry
        );
    }

    /// `count_param_uses` saturates at 2, treats uses under a suspending `Lam` as "many", and ignores
    /// non-parameter variables.
    #[test]
    fn count_param_uses_basics() {
        assert_eq!(count_param_uses(&Cir::con(ConName("Z".into()), vec![])), 0);
        assert_eq!(count_param_uses(&Cir::Var(0)), 1);
        assert_eq!(
            count_param_uses(&Cir::tuple(vec![Cir::Var(0), Cir::Var(0)])),
            2
        );
        // A use under a `Lam` body counts as many (the body may run repeatedly).
        assert_eq!(count_param_uses(&Cir::Lam(Box::new(Cir::Var(1)))), 2);
        // A free variable that is not the parameter (index past the binder) does not count.
        assert_eq!(count_param_uses(&Cir::Lam(Box::new(Cir::Var(2)))), 0);
    }
}
