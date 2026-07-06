//! Closure conversion and lambda lifting over [`crate::ir::Cir`] (spec section 7).
//!
//! After lowering, the IR still has nested `Lam`/`Fix` nodes that capture free variables from
//! their enclosing scope. Closure conversion makes that capture explicit: every function becomes a
//! top-level [`crate::ir::Func`] taking an *environment record* as its (implicit) zeroth context
//! and a single value argument, and each former free-variable reference becomes an
//! [`Cir::EnvRef`]. At the original site, the function value is built with [`Cir::MkClosure`],
//! packaging the captured values; applications become [`Cir::CallClosure`].
//!
//! De Bruijn discipline: inside a lifted function body, de Bruijn index 0 is the value parameter,
//! and captured variables are reached via `EnvRef(k)` (not by index). The captured-value
//! expressions inside `MkClosure` are evaluated in the *enclosing* scope, so they keep ordinary
//! indices.

use crate::ir::{Arm, Cir, Func, Program};

/// Closure-convert an entire entry expression into a [`Program`] of lifted functions plus a
/// residual entry term.
pub fn convert(entry: &Cir) -> Program {
    let mut cc = Converter {
        funcs: Vec::new(),
        counter: 0,
    };
    let entry = cc.go(entry);
    Program {
        funcs: cc.funcs,
        entry,
    }
}

struct Converter {
    funcs: Vec<Func>,
    counter: usize,
}

impl Converter {
    fn fresh(&mut self, hint: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("{hint}_{n}")
    }

    /// Convert `c`, lifting any `Lam`/`Fix` it directly contains. Returns a term with no remaining
    /// `Lam`/`Fix` nodes (they are replaced by `MkClosure`).
    fn go(&mut self, c: &Cir) -> Cir {
        match c {
            Cir::Var(_)
            | Cir::Global(_)
            | Cir::EnvRef(_)
            | Cir::Erased
            | Cir::IntLit(_)
            | Cir::NatLit(_)
            | Cir::StrLit(_) => c.clone(),
            Cir::Foreign(sym, arg) => {
                Cir::Foreign(sym.clone(), arg.as_ref().map(|a| Box::new(self.go(a))))
            }

            Cir::Lam(body) => self.lift(body, false, "lam"),
            // `Fix(Lam(inner))` is a *recursive function*: the `Fix` binder is the function's own
            // self-reference and the inner `Lam` binds its value parameter. Applying it (e.g. the
            // eliminator `App(Fix(Lam …), scrutinee)`) must bind the *parameter*, not the self, so
            // we lift the two binders into one recursive function (param = index 0, self = index 1)
            // rather than two nested functions.
            Cir::Fix(body) => {
                if let Cir::Lam(inner) = &**body {
                    self.lift_recursive_fn(inner)
                } else {
                    self.lift(body, true, "fix")
                }
            }

            Cir::App(f, a) => Cir::CallClosure(Box::new(self.go(f)), Box::new(self.go(a))),
            Cir::CallClosure(f, a) => Cir::CallClosure(Box::new(self.go(f)), Box::new(self.go(a))),
            Cir::Let(v, b) => {
                // `Let` binds one variable; convert the body in the extended scope. The body's
                // de Bruijn 0 is the let-bound value; converting it does not lift the `Let` itself.
                Cir::Let(Box::new(self.go(v)), Box::new(self.go(b)))
            }
            Cir::Con(name, args, al) => {
                Cir::Con(name.clone(), args.iter().map(|a| self.go(a)).collect(), *al)
            }
            Cir::Case(s, arms) => Cir::Case(
                Box::new(self.go(s)),
                arms.iter()
                    .map(|arm| Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: self.go(&arm.body),
                    })
                    .collect(),
            ),
            Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(|e| self.go(e)).collect(), *al),
            Cir::Proj(i, e) => Cir::Proj(*i, Box::new(self.go(e))),
            Cir::Now(e, al) => Cir::Now(Box::new(self.go(e)), *al),
            Cir::Later(e, al) => Cir::Later(Box::new(self.go(e)), *al),
            Cir::Force(e) => Cir::Force(Box::new(self.go(e))),
            Cir::Region(b) => Cir::Region(Box::new(self.go(b))),
            Cir::Op { effect, op, arg } => Cir::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(self.go(arg)),
            },
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => Cir::Handle {
                body: Box::new(self.go(body)),
                return_clause: Box::new(self.go(return_clause)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(n, e)| (n.clone(), self.go(e)))
                    .collect(),
            },
            Cir::MkClosure(f, env, al) => {
                Cir::MkClosure(f.clone(), env.iter().map(|e| self.go(e)).collect(), *al)
            }
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(self.go(lhs)),
                rhs: Box::new(self.go(rhs)),
            },
            // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
            Cir::IfZero {
                scrut,
                then_,
                else_,
            } => Cir::IfZero {
                scrut: Box::new(self.go(scrut)),
                then_: Box::new(self.go(then_)),
                else_: Box::new(self.go(else_)),
            },
            Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
                op: *op,
                lhs: Box::new(self.go(lhs)),
                rhs: rhs.as_ref().map(|r| Box::new(self.go(r))),
            },
            Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
                op: *op,
                lhs: Box::new(self.go(lhs)),
                rhs: rhs.as_ref().map(|r| Box::new(self.go(r))),
            },
            Cir::Flat { .. } | Cir::FlatProj { .. } => {
                unreachable!("flatten runs after closure conversion")
            }
        }
    }

    /// Lift a function body (under one binder: the parameter, or `self` for a `Fix`). Computes the
    /// free variables, builds the lifted [`Func`], and returns the `MkClosure` site.
    ///
    /// For a `Fix`, de Bruijn 0 in `body` is the recursive self-reference; the runtime binds the
    /// closure to itself, so we do *not* capture it — we mark the func `recursive` and leave `self`
    /// reachable as the closure's own value (an `EnvRef`-free self call lowers to a direct call).
    fn lift(&mut self, body: &Cir, recursive: bool, hint: &str) -> Cir {
        // Free variables of `body` are indices >= 1 (index 0 is the bound parameter/self).
        let mut fvs: Vec<usize> = Vec::new();
        collect_free(body, 1, &mut fvs);
        fvs.sort_unstable();
        fvs.dedup();

        // Build the capture expressions (in the enclosing scope): variable `idx` (its de Bruijn
        // value seen from outside this binder is `idx - 1`).
        let captures: Vec<Cir> = fvs.iter().map(|&idx| Cir::Var(idx - 1)).collect();

        // Rewrite the body: the parameter (index 0) stays index 0; each captured free variable
        // `fvs[k]` becomes `EnvRef(k)`. First recursively convert nested functions.
        let converted = self.go(body);
        let rebound = rebind(&converted, &fvs);

        let name = self.fresh(hint);
        self.funcs.push(Func {
            name: name.clone(),
            recursive,
            body: rebound,
        });
        Cir::mkclosure(name, captures)
    }

    /// Lift `Fix(Lam(inner))` into a single recursive function. Inside `inner` the de Bruijn scope
    /// is: index 0 = the value parameter, index 1 = the recursive *self*, indices `>= 2` = free
    /// variables captured from the enclosing scope. The lifted function takes the parameter as its
    /// argument (so applying the fixpoint binds the parameter, not the self); references to `self`
    /// become the function's own closure value (`MkClosure(name, captures)`); free variables become
    /// `EnvRef`s.
    fn lift_recursive_fn(&mut self, inner: &Cir) -> Cir {
        // Free variables are those reaching outside both binders: normalized to the body's entry
        // scope (depth 2), they are indices `>= 2`. We record `entry_idx` (>= 2) for each.
        let mut fvs: Vec<usize> = Vec::new();
        collect_free_at(inner, 2, &mut fvs);
        fvs.sort_unstable();
        fvs.dedup();

        // Capture expressions, evaluated in the enclosing scope (outside both binders): an
        // entry-scope index `e` denotes enclosing-scope index `e - 2`.
        let captures: Vec<Cir> = fvs.iter().map(|&e| Cir::Var(e - 2)).collect();

        let name = self.fresh("rec");
        // First convert nested functions, then rebind self/free-vars.
        let converted = self.go(inner);
        let rebound = rebind_recursive(&converted, &fvs, &name, &captures);

        self.funcs.push(Func {
            name: name.clone(),
            recursive: true,
            body: rebound,
        });
        Cir::mkclosure(name, captures)
    }
}

/// Collect the free de Bruijn indices of `c`, each **normalized to the function's entry scope**
/// (the scope just inside the function's single binder, i.e. `depth == 1`). A variable occurring
/// `extra` binders deep with raw index `i` denotes entry-scope index `i - (depth - 1)`; recording
/// that normalized value means the *same* captured variable always maps to the *same* entry index
/// regardless of how deep its occurrences are (e.g. under `Case` arm binders). `captures` and
/// [`rebind`] both speak this entry-scope language, so they agree.
fn collect_free(c: &Cir, depth: usize, out: &mut Vec<usize>) {
    collect_free_norm(c, depth, depth, out)
}

/// Collect free de Bruijn indices of `c`, normalized to entry scope `entry_depth` (the depth just
/// inside the function's binders). Variables with normalized index `>= entry_depth` are free.
fn collect_free_at(c: &Cir, entry_depth: usize, out: &mut Vec<usize>) {
    collect_free_norm(c, entry_depth, entry_depth, out)
}

/// Core free-variable collector. `start` is the entry depth (the binder count of the function being
/// lifted); `depth` is the current depth as we descend. A variable at raw index `i` is free iff
/// `i >= depth`; we record its entry-scope index `i - (depth - start)`.
fn collect_free_norm(c: &Cir, start: usize, depth: usize, out: &mut Vec<usize>) {
    macro_rules! rec {
        ($e:expr, $d:expr) => {
            collect_free_norm($e, start, $d, out)
        };
    }
    match c {
        Cir::Var(i) => {
            if *i >= depth {
                out.push(*i - (depth - start));
            }
        }
        Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => {}
        Cir::Foreign(_, arg) => {
            if let Some(a) = arg {
                rec!(a, depth)
            }
        }
        Cir::Lam(b) | Cir::Fix(b) => rec!(b, depth + 1),
        Cir::App(f, a) | Cir::CallClosure(f, a) => {
            rec!(f, depth);
            rec!(a, depth);
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            rec!(lhs, depth);
            rec!(rhs, depth);
        }
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => {
            rec!(scrut, depth);
            rec!(then_, depth);
            rec!(else_, depth);
        }
        Cir::NatPrim { lhs, rhs, .. } => {
            rec!(lhs, depth);
            if let Some(r) = rhs {
                rec!(r, depth);
            }
        }
        Cir::FloatPrim { lhs, rhs, .. } => {
            rec!(lhs, depth);
            if let Some(r) = rhs {
                rec!(r, depth);
            }
        }
        Cir::Let(v, b) => {
            rec!(v, depth);
            rec!(b, depth + 1);
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().for_each(|a| rec!(a, depth))
        }
        Cir::Case(s, arms) => {
            rec!(s, depth);
            arms.iter()
                .for_each(|arm| rec!(&arm.body, depth + arm.binders));
        }
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            rec!(e, depth)
        }
        Cir::Op { arg, .. } => rec!(arg, depth),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            rec!(body, depth);
            rec!(return_clause, depth);
            op_clauses.iter().for_each(|(_, e)| rec!(e, depth));
        }
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after closure conversion")
        }
    }
}

/// Rewrite a (already nested-function-converted) body so that each free variable listed in `fvs`
/// (at the function's entry depth) becomes an `EnvRef(k)` where `k` is its position in `fvs`. The
/// parameter (index 0) and any locally-introduced binders are left intact.
fn rebind(c: &Cir, fvs: &[usize]) -> Cir {
    fn go(c: &Cir, fvs: &[usize], depth: usize) -> Cir {
        match c {
            Cir::Var(i) => {
                if *i >= depth {
                    // A free variable of the function: map via fvs (the raw index is `i - depth`
                    // measured from entry, i.e. `i` minus the extra binders we crossed).
                    let entry_idx = i - depth + 1; // +1: entry depth was 1 (the parameter)
                    if let Some(k) = fvs.iter().position(|&f| f == entry_idx) {
                        Cir::EnvRef(k)
                    } else {
                        Cir::Var(*i)
                    }
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
            Cir::Foreign(sym, arg) => Cir::Foreign(
                sym.clone(),
                arg.as_ref().map(|a| Box::new(go(a, fvs, depth))),
            ),
            Cir::Lam(b) => Cir::Lam(Box::new(go(b, fvs, depth + 1))),
            Cir::Fix(b) => Cir::Fix(Box::new(go(b, fvs, depth + 1))),
            Cir::App(f, a) => Cir::App(Box::new(go(f, fvs, depth)), Box::new(go(a, fvs, depth))),
            Cir::CallClosure(f, a) => {
                Cir::CallClosure(Box::new(go(f, fvs, depth)), Box::new(go(a, fvs, depth)))
            }
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, fvs, depth)),
                rhs: Box::new(go(rhs, fvs, depth)),
            },
            // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
            Cir::IfZero {
                scrut,
                then_,
                else_,
            } => Cir::IfZero {
                scrut: Box::new(go(scrut, fvs, depth)),
                then_: Box::new(go(then_, fvs, depth)),
                else_: Box::new(go(else_, fvs, depth)),
            },
            Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
                op: *op,
                lhs: Box::new(go(lhs, fvs, depth)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, fvs, depth))),
            },
            Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
                op: *op,
                lhs: Box::new(go(lhs, fvs, depth)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, fvs, depth))),
            },
            Cir::Let(v, b) => {
                Cir::Let(Box::new(go(v, fvs, depth)), Box::new(go(b, fvs, depth + 1)))
            }
            Cir::Con(n, args, al) => Cir::Con(
                n.clone(),
                args.iter().map(|a| go(a, fvs, depth)).collect(),
                *al,
            ),
            Cir::Tuple(args, al) => {
                Cir::Tuple(args.iter().map(|a| go(a, fvs, depth)).collect(), *al)
            }
            Cir::MkClosure(n, args, al) => Cir::MkClosure(
                n.clone(),
                args.iter().map(|a| go(a, fvs, depth)).collect(),
                *al,
            ),
            Cir::Case(s, arms) => Cir::Case(
                Box::new(go(s, fvs, depth)),
                arms.iter()
                    .map(|arm| Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: go(&arm.body, fvs, depth + arm.binders),
                    })
                    .collect(),
            ),
            Cir::Proj(i, e) => Cir::Proj(*i, Box::new(go(e, fvs, depth))),
            Cir::Now(e, al) => Cir::Now(Box::new(go(e, fvs, depth)), *al),
            Cir::Later(e, al) => Cir::Later(Box::new(go(e, fvs, depth)), *al),
            Cir::Force(e) => Cir::Force(Box::new(go(e, fvs, depth))),
            Cir::Region(b) => Cir::Region(Box::new(go(b, fvs, depth))),
            Cir::Op { effect, op, arg } => Cir::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(arg, fvs, depth)),
            },
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => Cir::Handle {
                body: Box::new(go(body, fvs, depth)),
                return_clause: Box::new(go(return_clause, fvs, depth)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(n, e)| (n.clone(), go(e, fvs, depth)))
                    .collect(),
            },
            Cir::Flat { .. } | Cir::FlatProj { .. } => {
                unreachable!("flatten runs after closure conversion")
            }
        }
    }
    // Entry depth is 1: index 0 is the parameter/self.
    go(c, fvs, 1)
}

/// Rewrite the body of a lifted recursive function (see [`Converter::lift_recursive_fn`]). The
/// original body lives in entry scope of depth 2 (index 0 = parameter, index 1 = self). The emitted
/// function keeps only the parameter as a real binder; `self` becomes the function's own closure
/// value and free variables become `EnvRef`s. So, for an occurrence at raw index `i` under `b`
/// locally-introduced binders, the entry index is `e = i - b` and we map:
///   * `e == 0` → the parameter, left as `Var(i)`;
///   * `e == 1` → `self`, rewritten to `MkClosure(name, [EnvRef(0)…EnvRef(n-1)])` (the function
///     rebuilds its own closure from its captures);
///   * `e >= 2` → a captured free variable, rewritten to `EnvRef(k)` for its position `k` in `fvs`.
fn rebind_recursive(c: &Cir, fvs: &[usize], name: &str, captures: &[Cir]) -> Cir {
    // The self-closure rebuilt from the function's own environment.
    let self_closure = Cir::mkclosure(
        name.to_string(),
        (0..captures.len()).map(Cir::EnvRef).collect(),
    );
    fn go(c: &Cir, fvs: &[usize], depth: usize, selfc: &Cir) -> Cir {
        match c {
            Cir::Var(i) => {
                let e = i.checked_sub(depth);
                match e {
                    None => Cir::Var(*i),     // below a local binder: bound here
                    Some(0) => Cir::Var(*i),  // the parameter
                    Some(1) => selfc.clone(), // self-reference
                    Some(entry) => {
                        // entry >= 2: a captured free variable.
                        match fvs.iter().position(|&f| f == entry) {
                            Some(k) => Cir::EnvRef(k),
                            None => Cir::Var(*i),
                        }
                    }
                }
            }
            Cir::Global(_)
            | Cir::EnvRef(_)
            | Cir::Erased
            | Cir::IntLit(_)
            | Cir::NatLit(_)
            | Cir::StrLit(_) => c.clone(),
            Cir::Foreign(sym, arg) => Cir::Foreign(
                sym.clone(),
                arg.as_ref().map(|a| Box::new(go(a, fvs, depth, selfc))),
            ),
            Cir::Lam(b) => Cir::Lam(Box::new(go(b, fvs, depth + 1, selfc))),
            Cir::Fix(b) => Cir::Fix(Box::new(go(b, fvs, depth + 1, selfc))),
            Cir::App(f, a) => Cir::App(
                Box::new(go(f, fvs, depth, selfc)),
                Box::new(go(a, fvs, depth, selfc)),
            ),
            Cir::CallClosure(f, a) => Cir::CallClosure(
                Box::new(go(f, fvs, depth, selfc)),
                Box::new(go(a, fvs, depth, selfc)),
            ),
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, fvs, depth, selfc)),
                rhs: Box::new(go(rhs, fvs, depth, selfc)),
            },
            // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
            Cir::IfZero {
                scrut,
                then_,
                else_,
            } => Cir::IfZero {
                scrut: Box::new(go(scrut, fvs, depth, selfc)),
                then_: Box::new(go(then_, fvs, depth, selfc)),
                else_: Box::new(go(else_, fvs, depth, selfc)),
            },
            Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
                op: *op,
                lhs: Box::new(go(lhs, fvs, depth, selfc)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, fvs, depth, selfc))),
            },
            Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
                op: *op,
                lhs: Box::new(go(lhs, fvs, depth, selfc)),
                rhs: rhs.as_ref().map(|r| Box::new(go(r, fvs, depth, selfc))),
            },
            Cir::Let(v, b) => Cir::Let(
                Box::new(go(v, fvs, depth, selfc)),
                Box::new(go(b, fvs, depth + 1, selfc)),
            ),
            Cir::Con(n, args, al) => Cir::Con(
                n.clone(),
                args.iter().map(|a| go(a, fvs, depth, selfc)).collect(),
                *al,
            ),
            Cir::Tuple(args, al) => {
                Cir::Tuple(args.iter().map(|a| go(a, fvs, depth, selfc)).collect(), *al)
            }
            Cir::MkClosure(n, args, al) => Cir::MkClosure(
                n.clone(),
                args.iter().map(|a| go(a, fvs, depth, selfc)).collect(),
                *al,
            ),
            Cir::Case(s, arms) => Cir::Case(
                Box::new(go(s, fvs, depth, selfc)),
                arms.iter()
                    .map(|arm| Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: go(&arm.body, fvs, depth + arm.binders, selfc),
                    })
                    .collect(),
            ),
            Cir::Proj(i, e) => Cir::Proj(*i, Box::new(go(e, fvs, depth, selfc))),
            Cir::Now(e, al) => Cir::Now(Box::new(go(e, fvs, depth, selfc)), *al),
            Cir::Later(e, al) => Cir::Later(Box::new(go(e, fvs, depth, selfc)), *al),
            Cir::Force(e) => Cir::Force(Box::new(go(e, fvs, depth, selfc))),
            Cir::Region(b) => Cir::Region(Box::new(go(b, fvs, depth, selfc))),
            Cir::Op { effect, op, arg } => Cir::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(arg, fvs, depth, selfc)),
            },
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => Cir::Handle {
                body: Box::new(go(body, fvs, depth, selfc)),
                return_clause: Box::new(go(return_clause, fvs, depth, selfc)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(n, e)| (n.clone(), go(e, fvs, depth, selfc)))
                    .collect(),
            },
            Cir::Flat { .. } | Cir::FlatProj { .. } => {
                unreachable!("flatten runs after closure conversion")
            }
        }
    }
    // Entry depth: at the top of the body no extra local binders have been crossed yet, so the raw
    // index *is* the entry index (0 = parameter, 1 = self, >= 2 = captured free variable).
    go(c, fvs, 0, &self_closure)
}

/// Are there any residual `Lam`/`Fix` nodes left in `c`? After conversion there must be none.
pub fn has_free_lambdas(c: &Cir) -> bool {
    match c {
        Cir::Lam(_) | Cir::Fix(_) => true,
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::Erased
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => false,
        Cir::Foreign(_, arg) => arg.as_ref().is_some_and(|a| has_free_lambdas(a)),
        Cir::App(f, a) | Cir::CallClosure(f, a) | Cir::Let(f, a) => {
            has_free_lambdas(f) || has_free_lambdas(a)
        }
        Cir::IntPrim { lhs, rhs, .. } => has_free_lambdas(lhs) || has_free_lambdas(rhs),
        // if-zero: a non-binding branch — recurse into all three subterms like IntPrim.
        Cir::IfZero {
            scrut,
            then_,
            else_,
        } => has_free_lambdas(scrut) || has_free_lambdas(then_) || has_free_lambdas(else_),
        Cir::NatPrim { lhs, rhs, .. } => {
            has_free_lambdas(lhs) || rhs.as_ref().map(|r| has_free_lambdas(r)).unwrap_or(false)
        }
        Cir::FloatPrim { lhs, rhs, .. } => {
            has_free_lambdas(lhs) || rhs.as_ref().map(|r| has_free_lambdas(r)).unwrap_or(false)
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().any(has_free_lambdas)
        }
        Cir::Case(s, arms) => has_free_lambdas(s) || arms.iter().any(|a| has_free_lambdas(&a.body)),
        Cir::Proj(_, e) | Cir::Now(e, _) | Cir::Later(e, _) | Cir::Force(e) | Cir::Region(e) => {
            has_free_lambdas(e)
        }
        Cir::Op { arg, .. } => has_free_lambdas(arg),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            has_free_lambdas(body)
                || has_free_lambdas(return_clause)
                || op_clauses.iter().any(|(_, e)| has_free_lambdas(e))
        }
        Cir::Flat { fields, .. } => fields.iter().any(flatfield_has_free_lambdas),
        Cir::FlatProj { scrut, .. } => has_free_lambdas(scrut),
    }
}

/// `has_free_lambdas` lifted to a flattened field (A1): recurse into a leaf's value or every slot
/// of an inlined sub-product.
fn flatfield_has_free_lambdas(f: &crate::ir::FlatField) -> bool {
    match f {
        crate::ir::FlatField::Leaf(c) => has_free_lambdas(c),
        crate::ir::FlatField::Nested { slots, .. } => slots.iter().any(flatfield_has_free_lambdas),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::ConName;

    /// An `Alloc::Arena` tag (and the enclosing `Cir::Region` scope) rides through closure
    /// conversion unchanged (pass-through threading, spec §3.5).
    #[test]
    fn tags_survive_closure_conv() {
        use crate::ir::Alloc;
        // entry = region { Con "Zero" [] @Arena }  (no lambdas to lift; CC is a structural pass)
        let term = Cir::Region(Box::new(Cir::Con(
            ConName("Zero".into()),
            vec![],
            Alloc::Arena,
        )));
        let prog = convert(&term);
        let Cir::Region(inner) = &prog.entry else {
            panic!("region scope must survive CC: {:?}", prog.entry);
        };
        assert!(
            matches!(inner.as_ref(), Cir::Con(_, _, Alloc::Arena)),
            "the Arena tag must survive closure conversion: {inner:?}"
        );
    }

    /// capture via `EnvRef(0)`, and the program has two lifted functions.
    #[test]
    fn closure_conv_captures_free_vars() {
        // Outer: Lam( Lam( Var(1) ) )   (Var(1) = x, the outer parameter)
        let term = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Var(1)))));
        let prog = convert(&term);
        assert_eq!(prog.funcs.len(), 2, "two lambdas lifted");
        // The inner function's body should reference its captured `x` as EnvRef(0).
        let inner = prog
            .funcs
            .iter()
            .find(|f| matches!(f.body, Cir::EnvRef(0)))
            .expect("inner function references EnvRef(0)");
        assert!(!inner.recursive);
        // The outer function builds the inner closure capturing its parameter (Var 0).
        let outer = prog
            .funcs
            .iter()
            .find(|f| matches!(&f.body, Cir::MkClosure(_, caps, _) if caps == &vec![Cir::Var(0)]))
            .expect("outer function builds inner closure capturing its parameter");
        assert!(!outer.recursive);
        // The entry is the outer closure (no captures).
        assert!(matches!(prog.entry, Cir::MkClosure(_, ref caps, _) if caps.is_empty()));
    }

    /// Nested lambdas all lift to top level; nothing nested remains.
    #[test]
    fn nested_lambda_lifts() {
        let term = Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Var(
            0,
        )))))));
        let prog = convert(&term);
        assert_eq!(prog.funcs.len(), 3);
        for f in &prog.funcs {
            assert!(
                !has_free_lambdas(&f.body),
                "lifted body has no nested lambdas"
            );
        }
    }

    /// After conversion the whole program (entry + all funcs) has no residual `Lam`/`Fix`.
    #[test]
    fn no_free_vars_after_cc() {
        // A realistic term: Con Succ (App (Lam x. x) (Con Zero))
        let term = Cir::con(
            ConName("Succ".into()),
            vec![Cir::App(
                Box::new(Cir::Lam(Box::new(Cir::Var(0)))),
                Box::new(Cir::con(ConName("Zero".into()), vec![])),
            )],
        );
        let prog = convert(&term);
        assert!(!has_free_lambdas(&prog.entry));
        for f in &prog.funcs {
            assert!(!has_free_lambdas(&f.body));
        }
        // The application became a CallClosure.
        if let Cir::Con(_, args, _) = &prog.entry {
            assert!(matches!(args[0], Cir::CallClosure(_, _)));
        } else {
            panic!("expected Con entry");
        }
    }

    /// A `Fix` whose body is *not* a `Lam` (a bare guarded recursive value) still lifts to a single
    /// `recursive` function via the general path.
    #[test]
    fn fix_lifts_recursive() {
        let term = Cir::Fix(Box::new(Cir::later(Cir::Var(0))));
        let prog = convert(&term);
        assert_eq!(prog.funcs.len(), 1);
        assert!(prog.funcs[0].recursive);
    }

    /// A `Fix(Lam(body))` (a recursive *function*) lifts to a single recursive function whose
    /// binder is the lambda's value parameter — applying it binds the parameter, not the self.
    /// Self-references inside become the function's own rebuilt closure, not a value parameter.
    /// Regression: previously the two binders were lifted as two nested functions, so applying the
    /// fixpoint bound the argument to `self` and silently mis-ran every eliminator.
    #[test]
    fn recursive_fn_binds_parameter_not_self() {
        // Fix( Lam( App(Var 1 /* self */, Var 0 /* param */) ) ): `f = λx. f x`.
        let term = Cir::Fix(Box::new(Cir::Lam(Box::new(Cir::App(
            Box::new(Cir::Var(1)),
            Box::new(Cir::Var(0)),
        )))));
        let prog = convert(&term);
        assert_eq!(
            prog.funcs.len(),
            1,
            "one recursive function, not two nested ones"
        );
        let f = &prog.funcs[0];
        assert!(f.recursive, "the lifted function is recursive");
        // Body is `CallClosure(self_closure, Var 0)`: the parameter is de Bruijn 0, and `self` is
        // the function's own closure (no captures here, so an empty MkClosure of itself).
        let Cir::CallClosure(callee, arg) = &f.body else {
            panic!("expected a self-call on the parameter: {:?}", f.body);
        };
        assert!(
            matches!(&**callee, Cir::MkClosure(n, caps, _) if n == &f.name && caps.is_empty()),
            "self-reference rebuilds the function's own closure: {callee:?}"
        );
        assert_eq!(
            **arg,
            Cir::Var(0),
            "the call argument is the bound parameter"
        );
        // The entry is the fixpoint's closure (no captures).
        assert!(matches!(prog.entry, Cir::MkClosure(_, ref c, _) if c.is_empty()));
    }

    /// A free variable that occurs *under additional binders* (e.g. inside a `Case` arm) is captured
    /// at the right index. Regression: `collect_free` used to record the occurrence-relative index
    /// (inflated by the inner binders), so the capture pointed at the wrong slot.
    #[test]
    fn free_var_under_case_binder_captured_correctly() {
        use blight_kernel::ConName;
        // Lam( Case(Var 0, [ Succ k -> Var 2 /* the enclosing free var, under the field binder */ ]) )
        let body = Cir::Case(
            Box::new(Cir::Var(0)),
            vec![Arm {
                con: ConName("Succ".into()),
                binders: 1,
                // Under the field binder, the enclosing free var (entry index 1) is raw index 2.
                body: Cir::Var(2),
            }],
        );
        // Wrap in one extra enclosing binder so there is a free var to capture.
        let term = Cir::Lam(Box::new(Cir::Lam(Box::new(body))));
        let prog = convert(&term);
        // The inner function must capture exactly its one free var and reference it via EnvRef(0).
        let inner = prog
            .funcs
            .iter()
            .find(|f| matches!(&f.body, Cir::Case(_, arms) if matches!(&arms[0].body, Cir::EnvRef(0))))
            .expect("inner function references its capture as EnvRef(0)");
        assert!(!inner.recursive);
    }
}
