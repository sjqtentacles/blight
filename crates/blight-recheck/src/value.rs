//! This crate's own semantic values for NbE (independent of [`blight_kernel::value`]). A value is
//! either a canonical form, a *neutral* (a variable stuck under eliminations), or a *reflected*
//! form that carries enough type information to realize η and the path boundary rules on neutrals
//! (the same trick the kernel uses, re-implemented here so the two NbEs are independent).

use crate::term::{RGrade, RInterval, RTerm};
use std::rc::Rc;

/// A semantic value.
#[derive(Debug, Clone)]
pub enum RValue {
    Neutral(Neutral),
    Univ(u32),
    Pi(RGrade, Box<RValue>, Closure),
    Lam(Closure),
    Sigma(Box<RValue>, Closure),
    Pair(Box<RValue>, Box<RValue>),
    Data(blight_kernel::DataName, Vec<RValue>, Vec<RValue>),
    Con(blight_kernel::ConName, Vec<RValue>),
    PathP {
        family: DimClosure,
        lhs: Box<RValue>,
        rhs: Box<RValue>,
    },
    PLam(DimClosure),
    /// A reflected (η-expanded) path: a neutral known to have path type, carrying its endpoints so
    /// `p @ 0 = lhs`, `p @ 1 = rhs` fire even on a stuck path.
    ReflectedPath {
        neutral: Neutral,
        lhs: Box<RValue>,
        rhs: Box<RValue>,
    },
    /// A reflected function: a neutral known to have Π type, η-expanded on application.
    ReflectedFun {
        neutral: Neutral,
        cod: Closure,
    },
    /// An interval value (only in dimension argument position).
    Interval(RInterval),

    // ---- partiality (spec §4.5): the intensional Capretta delay (modeled independently) ----
    /// `Delay A` as a type value.
    Delay(Box<RValue>),
    /// `now a : Delay A`.
    Now(Box<RValue>),
    /// `later d : Delay A` — a guarded, non-reducing node (intensional).
    Later(Box<RValue>),
    /// `force d` stuck on a guarded `later` (`force (now a)` reduces; over a neutral it reflects to
    /// `Neutral::Force`; only the `later` case lands here).
    Force(Box<RValue>),

    // ---- effects and handlers (spec §4) ----
    // `! E A` has no value of its own: it is *definitionally its payload* `A` at the value level
    // (`normalize.rs` collapses `RTerm::EffTy(a)` to `eval a`, mirroring the kernel), with the effect
    // row tracked separately as the threaded `RRow` (B2). So there is no `EffTy` value variant.

    // ---- primitive machine integers (M11) ----
    /// `Int` as a type value.
    IntTy,
    /// An integer literal value.
    IntLit(i64),
}

/// A neutral: a free variable (as a de Bruijn *level*) under a spine of eliminations.
#[derive(Debug, Clone)]
pub enum Neutral {
    Var(usize),
    App(Box<Neutral>, Box<RValue>),
    Fst(Box<Neutral>),
    Snd(Box<Neutral>),
    PApp(Box<Neutral>, RInterval),
    Elim {
        data: blight_kernel::DataName,
        motive: Box<RValue>,
        methods: Vec<RValue>,
        scrutinee: Box<Neutral>,
    },
    /// `force _` — forcing a neutral of `Delay A`, kept stuck.
    Force(Box<Neutral>),
    /// A *stuck* `perform op a`: the re-checker does not run effect semantics, so a `perform`
    /// evaluates to this neutral (carrying the op name and the argument value). It only needs to
    /// round-trip through `quote`; it is never reduced.
    Op {
        effect: blight_kernel::row::EffName,
        op: blight_kernel::signature::OpName,
        /// Type-argument instantiation (Wave 7/E2), threaded so two stuck `perform`s of a
        /// differently-instantiated parameterized operation are never misjudged convertible.
        type_args: Vec<RValue>,
        arg: Box<RValue>,
    },
    /// A *stuck* `handle …`: the re-checker does not run handler semantics, so a `handle`
    /// evaluates to this neutral. The body value, return clause, and op clauses are captured (with
    /// their closure environment) so the node can round-trip through `quote`; it is never reduced.
    /// The binder structure (return clause: 1 binder; each op clause: 2 binders) is restored at
    /// quote time by opening with fresh variables.
    Handle {
        env: Env,
        body: Box<RValue>,
        return_clause: Rc<RTerm>,
        op_clauses: Vec<(blight_kernel::signature::OpName, Rc<RTerm>)>,
    },
    /// A *stuck* primitive `Int` operation: at least one operand is neutral.
    IntPrim {
        op: blight_kernel::IntPrimOp,
        lhs: Box<RValue>,
        rhs: Box<RValue>,
    },
}

/// A term closure capturing an environment and a body with one free term binder.
#[derive(Debug, Clone)]
pub struct Closure {
    pub env: Env,
    pub body: Rc<RTerm>,
}

/// A closure over a dimension binder (path families and path lambdas).
#[derive(Debug, Clone)]
pub struct DimClosure {
    pub env: Env,
    pub body: Rc<RTerm>,
}

/// A persistent, structurally-shared stack of bound values (head = most-recently-bound). Mirrors
/// `blight_kernel::value`'s `ValueChain` for the same reason: a `Vec`-backed environment makes
/// `Env::extend` — invoked on every β/ι step — an O(n) copy of every previously-bound value, so a
/// deeply-recursive term pays O(n²) in environment bookkeeping alone, compounding further whenever
/// a closure capturing such an environment is itself cloned (e.g. `do_elim`'s per-constructor-arg
/// `motive.clone()`/`methods.clone()`). Since the two checkers must independently agree on *every*
/// decision, this crate's `conv`/`eval` must independently finish on the same terms the kernel's
/// does (Wave 5/N1's re-checker-parity requirement) — hence the identical representation fix here.
#[derive(Debug, Clone, Default)]
struct TermChain(Option<Rc<TermNode>>);

#[derive(Debug)]
struct TermNode {
    head: RValue,
    tail: TermChain,
    len: usize,
}

impl TermChain {
    fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.len)
    }

    fn push(&self, head: RValue) -> TermChain {
        TermChain(Some(Rc::new(TermNode {
            head,
            tail: self.clone(),
            len: self.len() + 1,
        })))
    }

    fn get(&self, mut index: usize) -> Option<&RValue> {
        let mut cur = self;
        loop {
            let node = cur.0.as_ref()?;
            if index == 0 {
                return Some(&node.head);
            }
            index -= 1;
            cur = &node.tail;
        }
    }

    /// Rebuild the chain with the value at list-position `index` (0 = head) replaced, sharing
    /// every node below it; a no-op past the end, mirroring `Env::set_level`'s contract.
    fn set(&self, index: usize, v: RValue) -> TermChain {
        match &self.0 {
            None => self.clone(),
            Some(node) => {
                if index == 0 {
                    node.tail.push(v)
                } else {
                    node.tail.set(index - 1, v).push(node.head.clone())
                }
            }
        }
    }
}

/// An evaluation environment: term bindings and dimension bindings, innermost last.
#[derive(Debug, Clone, Default)]
pub struct Env {
    terms: TermChain,
    dims: Vec<RInterval>,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    /// O(1): a single `Rc` bump on the shared chain, not a copy of every previously-bound value.
    pub fn extend(&self, v: RValue) -> Env {
        Env {
            terms: self.terms.push(v),
            dims: self.dims.clone(),
        }
    }

    pub fn extend_dim(&self, r: RInterval) -> Env {
        let mut e = self.clone();
        e.dims.push(r);
        e
    }

    /// Look up term de Bruijn *index* `i` (0 = innermost).
    pub fn lookup(&self, i: usize) -> Option<&RValue> {
        self.terms.get(i)
    }

    /// Replace the term bound at de Bruijn *level* `lvl` (0 = outermost) with `v`, used to apply a
    /// per-branch index specialization during dependent pattern matching. Shares every chain node
    /// except the O(lvl) path rebuilt down to the replaced position.
    pub fn set_level(&self, lvl: usize, v: RValue) -> Env {
        let n = self.terms.len();
        if lvl < n {
            Env {
                terms: self.terms.set(n - 1 - lvl, v),
                dims: self.dims.clone(),
            }
        } else {
            self.clone()
        }
    }

    /// Look up dimension de Bruijn *index* `i` (0 = innermost).
    pub fn lookup_dim(&self, i: usize) -> Option<&RInterval> {
        let n = self.dims.len();
        if i < n {
            self.dims.get(n - 1 - i)
        } else {
            None
        }
    }
}
