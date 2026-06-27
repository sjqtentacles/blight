//! ANF normalization, tail-call detection, and the delay-trampoline loop (spec 7.4 tier 1).
//!
//! A-Normal Form makes evaluation order explicit: every intermediate result is bound by a `let`,
//! operands of calls/constructors are **atoms** (variables or already-evaluated values), and the
//! **tail position** of a function is syntactically apparent. This is the representation LLVM
//! codegen consumes, and it is where we perform the spec 7.4 *tier-1* tail-call optimization:
//!
//! - **Self/mutual tail calls → jumps.** A call in tail position to the enclosing (recursive)
//!   function is rewritten to a [`Tail::Jump`], which codegen emits as a back-edge (a loop)
//!   instead of a call frame. This guarantees constant stack for self-recursive loops regardless
//!   of what the LLVM tail-call pass decides.
//! - **Delay trampoline.** A `Force(e)` over a `later`-guarded recursive computation is lowered to
//!   a [`Tail::Trampoline`] loop: repeatedly step the delay until a `now` is reached, with bounded
//!   stack. This is the realistic deep-recursion path (the core has no general fixpoint; unbounded
//!   recursion arrives as the Capretta delay monad, spec 4.5).

use crate::ir::{Arm, Cir, Program};

/// An ANF *atom*: a value that requires no further evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    /// A bound variable (de Bruijn index into the ANF let-scope).
    Var(usize),
    /// A reference to the environment record's `i`-th capture (inside a lifted function).
    EnvRef(usize),
    /// A top-level function name.
    Global(String),
    /// The erased poison value.
    Erased,
}

/// An ANF *computation*: the right-hand side of a `let`, evaluated for its value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Comp {
    /// An atom (already a value).
    Atom(Atom),
    /// Allocate a closure capturing the given atoms for top-level function `name`. The [`Alloc`]
    /// tag records whether the closure record goes on the GC heap or the enclosing region's arena.
    MkClosure(String, Vec<Atom>, crate::ir::Alloc),
    /// Call a closure atom with an argument atom (non-tail; the result is bound).
    Call(Atom, Atom),
    /// Build a constructor value. The [`Alloc`] tag records its allocation site.
    Con(blight_kernel::ConName, Vec<Atom>, crate::ir::Alloc),
    /// Build a tuple. The [`Alloc`] tag records its allocation site.
    Tuple(Vec<Atom>, crate::ir::Alloc),
    /// Project a tuple component.
    Proj(usize, Atom),
    /// `now a` — an immediately-available delayed value. The [`Alloc`] tag records its allocation.
    Now(Atom, crate::ir::Alloc),
    /// `later a` — a guarded delay step (a thunk atom). The [`Alloc`] tag records its allocation.
    Later(Atom, crate::ir::Alloc),
    /// Perform an effect operation.
    Op {
        effect: String,
        op: String,
        arg: Atom,
    },
    /// Call a foreign (FFI) C symbol with no arguments, yielding its `BlValue` result (spec §7.6).
    Foreign(String),
    /// A machine-integer literal (M11): allocates a `BL_INT` value carrying the i64 payload.
    IntLit(i64),
    /// A primitive `Int` operation over two atoms (M11): emitted as a call to the corresponding
    /// `prim.c` runtime helper (`bl_int_add`/`…`), which unboxes both `BL_INT` operands, computes,
    /// and boxes the `BL_INT` result.
    IntPrim {
        op: blight_kernel::IntPrimOp,
        lhs: Atom,
        rhs: Atom,
    },
}

/// An ANF *tail expression*: what a block evaluates to. Tail position is explicit here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tail {
    /// Return an atom.
    Ret(Atom),
    /// `let x = comp in rest` — bind a computation, continue (x = innermost de Bruijn 0 in rest).
    Let(Comp, Box<Tail>),
    /// A tail call to a closure atom with an argument atom (an ordinary tail call; codegen uses
    /// `tailcc`/`musttail`).
    TailCall(Atom, Atom),
    /// A tail self-call rewritten to a back-edge jump (tier-1 TCO): re-enter the current function
    /// with a new argument atom, as a loop, using **no** new stack frame.
    Jump(Atom),
    /// `case scrut of [arm…]` in tail position.
    Case(Atom, Vec<TailArm>),
    /// Force a delay value to its result, driving the trampoline loop (bounded stack).
    Trampoline(Atom),
    /// A region scope `region { body }` in tail position (spec §3.5): the codegen brackets `body`
    /// with arena enter/leave so `Alloc::Arena` allocations inside are bump-allocated and reclaimed
    /// in O(1) at scope exit. The arena leave is emitted at the lexical boundary, never after a tail
    /// call (preserving the `musttail` safepoint rule, spec §7.4).
    Region(Box<Tail>),
    /// A deep effect handler in tail position. After lowering wrapped each clause in a thunk/lambda
    /// and closure conversion lifted them, the three clauses arrive here as ordinary closure *atoms*:
    /// `body` is a thunk `λ_. <computation>` (run once to start the handled computation);
    /// `return_clause` is `λx. r`; and each op clause is a curried `λx. λk. e`. The backend installs
    /// them via `bl_handle_clo`, which drives the deep-handler semantics by applying these closures
    /// through the normal calling convention.
    Handle {
        body: Atom,
        return_clause: Atom,
        op_clauses: Vec<(String, Atom)>,
    },
}

/// One arm of an ANF tail [`Tail::Case`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TailArm {
    pub con: blight_kernel::ConName,
    pub binders: usize,
    pub body: Tail,
}

/// An ANF top-level function: a body in tail form, plus whether it is recursive (so self tail
/// calls become jumps).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnfFunc {
    pub name: String,
    pub recursive: bool,
    pub body: Tail,
}

/// A whole ANF program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnfProgram {
    pub funcs: Vec<AnfFunc>,
    pub entry: Tail,
    /// Per-constructor tag: the constructor's index within its `DataDecl.constructors`. This is the
    /// value stored in a `Con` object's aux word and switched on by `case` (which uses the
    /// constructor's *declaration order* as the arm index). Empty when normalized without a
    /// signature (tests fall back to a name-derived id).
    pub con_tags: std::collections::HashMap<blight_kernel::ConName, u64>,
}

/// Build the per-constructor tag map from a signature: each constructor maps to its 0-based index
/// within its data declaration's `constructors` list (matching the `case` arm order).
pub fn con_tags_from_sig(
    sig: &blight_kernel::Signature,
) -> std::collections::HashMap<blight_kernel::ConName, u64> {
    let mut tags = std::collections::HashMap::new();
    for decl in sig.data_decls() {
        for (idx, ctor) in decl.constructors.iter().enumerate() {
            tags.insert(ctor.name.clone(), idx as u64);
        }
    }
    tags
}

/// Normalize a closure-converted [`Program`] to ANF, performing tier-1 TCO and the delay
/// trampoline transform.
pub fn normalize(prog: &Program) -> AnfProgram {
    let funcs = prog
        .funcs
        .iter()
        .map(|f| AnfFunc {
            name: f.name.clone(),
            recursive: f.recursive,
            // Inside a function, `self` is the function itself; a tail call to `self` becomes a
            // jump. We mark the current function name so `to_tail` can recognize it.
            body: to_tail(&f.body, Some(&f.name), f.recursive),
        })
        .collect();
    let entry = to_tail(&prog.entry, None, false);
    AnfProgram {
        funcs,
        entry,
        con_tags: std::collections::HashMap::new(),
    }
}

/// A fresh-binder counter encoded purely through the de Bruijn discipline: when we `let`-bind a
/// computation, the continuation runs under one extra binder, so existing atoms must be shifted.
/// We avoid global gensym by building bottom-up.
///
/// Convert a `Cir` expression into a tail expression. `self_name` is the enclosing recursive
/// function's name (for self-tail-call→jump); `is_rec` says whether the function is recursive
/// (a `Fix`-derived function calling itself).
fn to_tail(c: &Cir, self_name: Option<&str>, is_rec: bool) -> Tail {
    // Build by ANF-ing into a sequence of lets ending in a tail.
    let mut binder = Anfer::new(self_name, is_rec);
    binder.tail(c)
}

struct Anfer<'a> {
    self_name: Option<&'a str>,
    is_rec: bool,
}

impl<'a> Anfer<'a> {
    fn new(self_name: Option<&'a str>, is_rec: bool) -> Self {
        Anfer { self_name, is_rec }
    }

    /// Emit `c` in tail position.
    fn tail(&mut self, c: &Cir) -> Tail {
        match c {
            // A tail force becomes the trampoline loop.
            Cir::Force(e) => {
                let (binds, atom) = self.atomize(e);
                wrap(binds, Tail::Trampoline(atom))
            }
            // A tail call: detect self-call → jump.
            Cir::CallClosure(f, a) => {
                // Sequence the callee then the argument, keeping the de Bruijn discipline straight
                // (each `let` introduced for `f` shifts the vars seen by `a`, and vice versa).
                let (binds, mut atoms) = self.seq(&[(**f).clone(), (**a).clone()]);
                let aa = atoms.pop().unwrap();
                let fa = atoms.pop().unwrap();
                // Is the callee a self-reference closure? After CC, a self call is `MkClosure(self
                // name)` or the recursive function's own closure. We recognize a direct global to
                // the current function.
                if let (Some(sn), true) = (self.self_name, self.is_rec) {
                    if is_self_closure(&fa, sn) {
                        return wrap(binds, Tail::Jump(aa));
                    }
                }
                wrap(binds, Tail::TailCall(fa, aa))
            }
            Cir::App(f, a) => {
                // App should have become CallClosure after CC; handle defensively as a call.
                self.tail(&Cir::CallClosure(f.clone(), a.clone()))
            }
            Cir::Case(scrut, arms) => {
                let (binds, satom) = self.atomize(scrut);
                let pushed = binds.len();
                let arms2 = arms
                    .iter()
                    .map(|arm| TailArm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        // Codegen evaluates the scrutinee (emitting `binds` as `pushed` slots), then
                        // pushes this arm's `arm.binders` field slots on top before running the
                        // body. So the body's references to the *outer* scope must skip those
                        // `pushed` scrutinee slots — shift them up. The arm's own field binders stay
                        // below the cutoff and are untouched.
                        body: {
                            let shifted = shift_cir_under(&arm.body, pushed, arm.binders);
                            let mut inner = Anfer::new(self.self_name, self.is_rec);
                            inner.tail(&shifted)
                        },
                    })
                    .collect();
                wrap(binds, Tail::Case(satom, arms2))
            }
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                // After lowering + closure conversion each clause is a closure value (MkClosure).
                // Sequence all of them through `seq` so the de Bruijn indices stay correct as each
                // closure-construction `let` shifts the ones bound before it, then install via
                // `bl_handle_clo`.
                let mut subs = Vec::with_capacity(2 + op_clauses.len());
                subs.push((**body).clone());
                subs.push((**return_clause).clone());
                for (_, e) in op_clauses {
                    subs.push(e.clone());
                }
                let (binds, atoms) = self.seq(&subs);
                let body_a = atoms[0].clone();
                let ret_a = atoms[1].clone();
                let ops = op_clauses
                    .iter()
                    .enumerate()
                    .map(|(i, (n, _))| (n.clone(), atoms[2 + i].clone()))
                    .collect();
                wrap(
                    binds,
                    Tail::Handle {
                        body: body_a,
                        return_clause: ret_a,
                        op_clauses: ops,
                    },
                )
            }
            // A region scope in tail position: bracket its body with arena enter/leave. The body
            // is re-ANFed in tail position so its own tail call / case lands inside the scope.
            Cir::Region(body) => {
                let mut inner = Anfer::new(self.self_name, self.is_rec);
                Tail::Region(Box::new(inner.tail(body)))
            }
            // Otherwise, atomize to a value and return it.
            _ => {
                let (binds, atom) = self.atomize(c);
                wrap(binds, Tail::Ret(atom))
            }
        }
    }

    /// ANF-normalize `c` into a list of `let`-bindings plus a final atom naming its value.
    ///
    /// **De Bruijn discipline.** The returned `(binds, atom)` is understood relative to a scope `S`
    /// (the scope in which `c` lives). Emitting `binds` as nested `let`s (`binds[0]` outermost,
    /// `binds[last]` innermost) extends `S` by `binds.len()` slots; `atom` and every `Atom::Var`
    /// occurring inside `binds` are indices into that *extended innermost* scope. This is the exact
    /// model codegen uses (`Tail::Let` pushes one slot; `Var(0)` is the innermost). Honoring it is
    /// essential: when we sequence several sub-expressions (constructor fields, call operands), each
    /// new `let` shifts every variable that was already in scope, so we shift as we go via
    /// [`Self::seq`].
    fn atomize(&mut self, c: &Cir) -> (Vec<Comp>, Atom) {
        match c {
            Cir::Var(i) => (vec![], Atom::Var(*i)),
            Cir::EnvRef(k) => (vec![], Atom::EnvRef(*k)),
            Cir::Global(g) => (vec![], Atom::Global(g.clone())),
            Cir::Erased => (vec![], Atom::Erased),

            Cir::MkClosure(name, caps, al) => {
                let (mut binds, atoms) = self.seq(caps);
                binds.push(Comp::MkClosure(name.clone(), atoms, *al));
                (binds, Atom::Var(0))
            }
            Cir::CallClosure(f, a) | Cir::App(f, a) => {
                let (mut binds, mut atoms) = self.seq(&[(**f).clone(), (**a).clone()]);
                let aa = atoms.pop().unwrap();
                let fa = atoms.pop().unwrap();
                binds.push(Comp::Call(fa, aa));
                (binds, Atom::Var(0))
            }
            Cir::Con(name, args, al) => {
                let (mut binds, atoms) = self.seq(args);
                binds.push(Comp::Con(name.clone(), atoms, *al));
                (binds, Atom::Var(0))
            }
            Cir::Tuple(args, al) => {
                let (mut binds, atoms) = self.seq(args);
                binds.push(Comp::Tuple(atoms, *al));
                (binds, Atom::Var(0))
            }
            Cir::Proj(i, e) => {
                let (mut binds, a) = self.atomize(e);
                binds.push(Comp::Proj(*i, a));
                (binds, Atom::Var(0))
            }
            Cir::Now(e, al) => {
                let (mut binds, a) = self.atomize(e);
                binds.push(Comp::Now(a, *al));
                (binds, Atom::Var(0))
            }
            Cir::Later(e, al) => {
                let (mut binds, a) = self.atomize(e);
                binds.push(Comp::Later(a, *al));
                (binds, Atom::Var(0))
            }
            Cir::Force(e) => {
                // A non-tail force still trampolines; bind its result.
                let (mut binds, a) = self.atomize(e);
                binds.push(Comp::Now(a, crate::ir::Alloc::Gc));
                (binds, Atom::Var(0))
            }
            Cir::Op { effect, op, arg } => {
                let (mut binds, a) = self.atomize(arg);
                binds.push(Comp::Op {
                    effect: effect.clone(),
                    op: op.clone(),
                    arg: a,
                });
                (binds, Atom::Var(0))
            }
            Cir::Foreign(sym) => (vec![Comp::Foreign(sym.clone())], Atom::Var(0)),
            Cir::IntLit(n) => (vec![Comp::IntLit(*n)], Atom::Var(0)),
            Cir::IntPrim { op, lhs, rhs } => {
                let (mut binds, mut atoms) = self.seq(&[(**lhs).clone(), (**rhs).clone()]);
                let ra = atoms.pop().unwrap();
                let la = atoms.pop().unwrap();
                binds.push(Comp::IntPrim {
                    op: *op,
                    lhs: la,
                    rhs: ra,
                });
                (binds, Atom::Var(0))
            }
            // A `Let` binds one variable that the body refers to as de Bruijn 0. We ANF the bound
            // value into `nv` slots, add one slot naming its result, then ANF the body. The body
            // already counts the let binder as index 0; its references to the *outer* scope (index
            // >= 1) must skip the `nv` value-slots we inserted between the binder and that scope.
            Cir::Let(v, b) => {
                let (mut binds, va) = self.atomize(v);
                let nv = binds.len();
                binds.push(Comp::Atom(va));
                let body = shift_cir_under(b, nv, 1);
                let (bb, ba) = self.atomize(&body);
                binds.extend(bb);
                (binds, ba)
            }
            Cir::Lam(_) | Cir::Fix(_) | Cir::Case(_, _) | Cir::Handle { .. } => {
                // These don't appear as sub-atoms post-CC for the programs we compile; emit a
                // poison atom rather than panicking so the pure-Rust pipeline is total.
                (vec![], Atom::Erased)
            }
            // A region scope in non-tail position: atomize the body for its value. Arena bracketing
            // only fires for tail-position regions (the common `(region r …)` shape, where the body
            // is the region's result); a non-tail region keeps its allocations on the GC heap, which
            // is always safe.
            Cir::Region(body) => self.atomize(body),
        }
    }

    /// ANF a left-to-right sequence of sub-expressions (constructor fields, call operands), keeping
    /// the de Bruijn discipline straight. Each sub-expression `cs[k]` is atomized in a scope already
    /// extended by all the `let`s emitted for `cs[0..k]`, so before atomizing it we shift its free
    /// `Cir::Var`s up by that running count. Symmetrically, every atom we have *already* produced
    /// (and every var inside earlier binds) is shifted up as later sub-expressions push more `let`s,
    /// so the whole returned `(binds, atoms)` is consistent in the final innermost scope.
    fn seq(&mut self, cs: &[Cir]) -> (Vec<Comp>, Vec<Atom>) {
        let mut binds: Vec<Comp> = Vec::new();
        let mut atoms: Vec<Atom> = Vec::new();
        for c in cs {
            let emitted = binds.len();
            // Shift this sub-expression's free vars past the `let`s already in scope.
            let shifted = shift_cir(c, emitted);
            let (b, a) = self.atomize(&shifted);
            let added = b.len();
            // Everything produced so far becomes `added` slots further from the innermost scope.
            for atom in atoms.iter_mut() {
                *atom = shift_atom(atom, 0, added);
            }
            binds.extend(b);
            atoms.push(a);
        }
        (binds, atoms)
    }
}

/// Shift every free `Cir::Var(i)` (with `i >= 0` at the top level) up by `by`. Binders encountered
/// (`Lam`/`Fix`/`Let` body / `Case` arm binders) raise the cutoff. Used by [`Anfer::seq`] to move a
/// sub-expression past `let`s introduced for its left siblings.
fn shift_cir(c: &Cir, by: usize) -> Cir {
    shift_cir_under(c, by, 0)
}

/// Like [`shift_cir`] but with an initial `cutoff`: free vars are those with index `>= cutoff`.
/// Used for `Case` arm bodies, whose first `arm.binders` indices are the freshly-bound constructor
/// fields (left untouched) and whose outer references must skip the scrutinee's emitted `let`s.
fn shift_cir_under(c: &Cir, by: usize, cutoff0: usize) -> Cir {
    fn go(c: &Cir, by: usize, cutoff: usize) -> Cir {
        match c {
            Cir::Var(i) => {
                if *i >= cutoff {
                    Cir::Var(i + by)
                } else {
                    Cir::Var(*i)
                }
            }
            Cir::EnvRef(_) | Cir::Global(_) | Cir::Erased | Cir::Foreign(_) | Cir::IntLit(_) => {
                c.clone()
            }
            Cir::Lam(b) => Cir::Lam(Box::new(go(b, by, cutoff + 1))),
            Cir::Fix(b) => Cir::Fix(Box::new(go(b, by, cutoff + 1))),
            Cir::App(f, a) => Cir::App(Box::new(go(f, by, cutoff)), Box::new(go(a, by, cutoff))),
            Cir::CallClosure(f, a) => {
                Cir::CallClosure(Box::new(go(f, by, cutoff)), Box::new(go(a, by, cutoff)))
            }
            Cir::Let(v, b) => {
                Cir::Let(Box::new(go(v, by, cutoff)), Box::new(go(b, by, cutoff + 1)))
            }
            Cir::Con(n, args, al) => Cir::Con(
                n.clone(),
                args.iter().map(|a| go(a, by, cutoff)).collect(),
                *al,
            ),
            Cir::Tuple(args, al) => {
                Cir::Tuple(args.iter().map(|a| go(a, by, cutoff)).collect(), *al)
            }
            Cir::MkClosure(n, args, al) => Cir::MkClosure(
                n.clone(),
                args.iter().map(|a| go(a, by, cutoff)).collect(),
                *al,
            ),
            Cir::Case(s, arms) => Cir::Case(
                Box::new(go(s, by, cutoff)),
                arms.iter()
                    .map(|arm| Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: go(&arm.body, by, cutoff + arm.binders),
                    })
                    .collect(),
            ),
            Cir::Proj(i, e) => Cir::Proj(*i, Box::new(go(e, by, cutoff))),
            Cir::Now(e, al) => Cir::Now(Box::new(go(e, by, cutoff)), *al),
            Cir::Later(e, al) => Cir::Later(Box::new(go(e, by, cutoff)), *al),
            Cir::Force(e) => Cir::Force(Box::new(go(e, by, cutoff))),
            Cir::Region(b) => Cir::Region(Box::new(go(b, by, cutoff))),
            Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
                op: *op,
                lhs: Box::new(go(lhs, by, cutoff)),
                rhs: Box::new(go(rhs, by, cutoff)),
            },
            Cir::Op { effect, op, arg } => Cir::Op {
                effect: effect.clone(),
                op: op.clone(),
                arg: Box::new(go(arg, by, cutoff)),
            },
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => Cir::Handle {
                body: Box::new(go(body, by, cutoff)),
                return_clause: Box::new(go(return_clause, by, cutoff)),
                op_clauses: op_clauses
                    .iter()
                    .map(|(n, e)| (n.clone(), go(e, by, cutoff)))
                    .collect(),
            },
        }
    }
    go(c, by, cutoff0)
}

/// Wrap a tail expression in a sequence of `let` bindings (innermost last).
fn wrap(binds: Vec<Comp>, tail: Tail) -> Tail {
    binds
        .into_iter()
        .rev()
        .fold(tail, |acc, comp| Tail::Let(comp, Box::new(acc)))
}

/// Is atom `a` a closure of the current self function `sn`? After CC, the recursive self-reference
/// is the function's own closure; we recognize a direct global to `sn`. (A `MkClosure(sn, …)` is
/// reduced to a global by the time it reaches here in the simple programs we target.)
fn is_self_closure(a: &Atom, sn: &str) -> bool {
    matches!(a, Atom::Global(g) if g == sn)
}

/// Shift a free atom var by `by` if at/above `depth` (used when an atom crosses introduced lets).
fn shift_atom(a: &Atom, depth: usize, by: usize) -> Atom {
    match a {
        Atom::Var(i) if *i >= depth => Atom::Var(i + by),
        _ => a.clone(),
    }
}

/// Does this tail expression name every call (i.e. is it in ANF)? A structural check used by tests:
/// every `Call`/`MkClosure`/`Con`/`Tuple`/`Proj`/`Op` appears as a `let`-bound [`Comp`], never
/// nested inside another computation's operand (operands are [`Atom`]s by construction).
pub fn is_anf(t: &Tail) -> bool {
    match t {
        Tail::Ret(_) | Tail::TailCall(_, _) | Tail::Jump(_) | Tail::Trampoline(_) => true,
        Tail::Let(_comp, rest) => is_anf(rest),
        Tail::Case(_, arms) => arms.iter().all(|a| is_anf(&a.body)),
        Tail::Region(body) => is_anf(body),
        Tail::Handle {
            body: _,
            return_clause: _,
            op_clauses: _,
        } => true,
    }
}

/// Does `t` contain a [`Tail::Jump`] (a self-tail-call turned into a loop)?
pub fn has_jump(t: &Tail) -> bool {
    match t {
        Tail::Jump(_) => true,
        Tail::Ret(_) | Tail::TailCall(_, _) | Tail::Trampoline(_) => false,
        Tail::Let(_, rest) => has_jump(rest),
        Tail::Case(_, arms) => arms.iter().any(|a| has_jump(&a.body)),
        Tail::Region(body) => has_jump(body),
        Tail::Handle {
            body: _,
            return_clause: _,
            op_clauses: _,
        } => false,
    }
}

/// Does `t` contain a [`Tail::Trampoline`]?
pub fn has_trampoline(t: &Tail) -> bool {
    match t {
        Tail::Trampoline(_) => true,
        Tail::Ret(_) | Tail::TailCall(_, _) | Tail::Jump(_) => false,
        Tail::Let(_, rest) => has_trampoline(rest),
        Tail::Case(_, arms) => arms.iter().any(|a| has_trampoline(&a.body)),
        Tail::Region(body) => has_trampoline(body),
        Tail::Handle {
            body: _,
            return_clause: _,
            op_clauses: _,
        } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Func;
    use blight_kernel::ConName;

    /// An `Alloc::Arena` tag on an allocation inside a `Cir::Region` survives ANF normalization: the
    /// region becomes a `Tail::Region` and the allocation's `Comp` carries the same tag (pass-through
    /// threading, spec §3.5).
    #[test]
    fn tags_survive_anf() {
        use crate::ir::Alloc;
        // entry = region { Con "Zero" [] @Arena }
        let entry = Cir::Region(Box::new(Cir::Con(
            ConName("Zero".into()),
            vec![],
            Alloc::Arena,
        )));
        let prog = Program {
            funcs: vec![],
            entry,
        };
        let anf = normalize(&prog);
        let Tail::Region(inner) = &anf.entry else {
            panic!("region scope must become a Tail::Region: {:?}", anf.entry);
        };
        // The body is `let x = Con Zero @Arena in Ret x`.
        let Tail::Let(Comp::Con(_, _, alloc), _) = inner.as_ref() else {
            panic!("region body must bind the constructor: {inner:?}");
        };
        assert_eq!(*alloc, Alloc::Arena, "the Arena tag must survive ANF");
    }

    /// Every call is named: ANF-ing a nested application produces only `let`-bound calls with atom
    /// operands.
    #[test]
    fn anf_names_all_calls() {
        // entry = f (g x)  -> after CC: CallClosure(f, CallClosure(g, x))
        let term = Cir::CallClosure(
            Box::new(Cir::Global("f".into())),
            Box::new(Cir::CallClosure(
                Box::new(Cir::Global("g".into())),
                Box::new(Cir::Var(0)),
            )),
        );
        let prog = Program {
            funcs: vec![],
            entry: term,
        };
        let anf = normalize(&prog);
        assert!(is_anf(&anf.entry), "entry is in ANF: {:?}", anf.entry);
        // The inner call (g x) is let-bound, and the outer is a tail call.
        match &anf.entry {
            Tail::Let(Comp::Call(g, _), rest) => {
                assert_eq!(*g, Atom::Global("g".into()));
                assert!(matches!(**rest, Tail::TailCall(Atom::Global(_), _)));
            }
            other => panic!("expected let-bound inner call, got {other:?}"),
        }
    }

    /// A self tail call in a recursive function becomes a `Jump` (a loop), not a call.
    #[test]
    fn self_tailcall_becomes_loop() {
        // function `loop`: body = CallClosure(Global "loop", Var 0)  (tail self-call)
        let func = Func {
            name: "loop".into(),
            recursive: true,
            body: Cir::CallClosure(Box::new(Cir::Global("loop".into())), Box::new(Cir::Var(0))),
        };
        let prog = Program {
            funcs: vec![func],
            entry: Cir::Erased,
        };
        let anf = normalize(&prog);
        let loopf = &anf.funcs[0];
        assert!(
            has_jump(&loopf.body),
            "self tail call became a jump: {:?}",
            loopf.body
        );
        assert!(!matches!(loopf.body, Tail::TailCall(_, _)));
    }

    /// Sequencing several non-trivial sub-expressions keeps the de Bruijn discipline straight: a
    /// constructor whose two fields each bind a computation must reference the *earlier* field's
    /// result at the correctly-shifted index (it sits one slot further from the innermost once the
    /// second field's `let` is introduced). Regression: the old `atomize` ignored shifting, so the
    /// first field pointed at the wrong slot.
    #[test]
    fn seq_shifts_earlier_atoms() {
        use crate::ir::Alloc;
        // entry = Pair( g x , h x )  → after CC: Tuple[ CallClosure(g,x), CallClosure(h,x) ]
        let term = Cir::Tuple(
            vec![
                Cir::CallClosure(Box::new(Cir::Global("g".into())), Box::new(Cir::Var(0))),
                Cir::CallClosure(Box::new(Cir::Global("h".into())), Box::new(Cir::Var(0))),
            ],
            Alloc::Gc,
        );
        let prog = Program {
            funcs: vec![],
            entry: term,
        };
        let anf = normalize(&prog);
        // entry = let a = g x ; let b = h x ; ret (Tuple [a, b]) — where the final Tuple names the
        // first call as Var(1) (now one slot deeper) and the second as Var(0).
        let Tail::Let(Comp::Call(_, _), rest1) = &anf.entry else {
            panic!("first call let: {:?}", anf.entry);
        };
        let Tail::Let(Comp::Call(_, _), rest2) = &**rest1 else {
            panic!("second call let: {rest1:?}");
        };
        let Tail::Let(Comp::Tuple(atoms, _), _) = &**rest2 else {
            panic!("tuple let: {rest2:?}");
        };
        assert_eq!(
            atoms,
            &vec![Atom::Var(1), Atom::Var(0)],
            "earlier field shifted past the later field's let"
        );
    }
}
