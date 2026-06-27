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

    // ---- effects and handlers (spec §4): modeled at the TYPE LEVEL only ----
    /// `! E A` as a type value (the row `E` is dropped; only the payload type `A` is kept).
    EffTy(Box<RValue>),

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

/// An evaluation environment: term bindings and dimension bindings, innermost last.
#[derive(Debug, Clone, Default)]
pub struct Env {
    terms: Vec<RValue>,
    dims: Vec<RInterval>,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    pub fn extend(&self, v: RValue) -> Env {
        let mut e = self.clone();
        e.terms.push(v);
        e
    }

    pub fn extend_dim(&self, r: RInterval) -> Env {
        let mut e = self.clone();
        e.dims.push(r);
        e
    }

    /// Look up term de Bruijn *index* `i` (0 = innermost).
    pub fn lookup(&self, i: usize) -> Option<&RValue> {
        let n = self.terms.len();
        if i < n {
            self.terms.get(n - 1 - i)
        } else {
            None
        }
    }

    /// Replace the term bound at de Bruijn *level* `lvl` (0 = outermost) with `v`, used to apply a
    /// per-branch index specialization during dependent pattern matching.
    pub fn set_level(&self, lvl: usize, v: RValue) -> Env {
        let mut e = self.clone();
        if lvl < e.terms.len() {
            e.terms[lvl] = v;
        }
        e
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
