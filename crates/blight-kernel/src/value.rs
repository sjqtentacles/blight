//! The NbE semantic domain (spec §3 of the implementation strategy doc; spec §2.5/§2.8).
//!
//! `eval : Term -> Value` interprets a term in an environment; `quote : Value -> Term` reads
//! a value back to a normal-form term. Definitional equality (`Conv`) compares normal forms.

use crate::signature::Signature;
use crate::term::{ConName, DataName, Interval, Level, Term};
use std::rc::Rc;

/// A closure: an unevaluated body together with the environment it captured.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Closure {
    pub env: Env,
    pub body: Term,
}

/// The semantic domain. Canonical values plus *neutrals* (stuck computations on a variable).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    /// A neutral term (a variable with a spine of eliminations applied).
    Neutral(Neutral),
    Univ(Level),
    Pi(crate::semiring::Grade, Box<Value>, Closure),
    Lam(Closure),
    Sigma(Box<Value>, Closure),
    Pair(Box<Value>, Box<Value>),
    Data(DataName, Vec<Value>, Vec<Value>),
    Con(ConName, Vec<Value>),
    PathP {
        family: Closure,
        lhs: Box<Value>,
        rhs: Box<Value>,
    },
    PLam(Closure),
    /// A *reflected* neutral of `PathP` type (η for paths at neutrals). Carries the underlying
    /// neutral spine together with its endpoints, so applying it at `0`/`1` computes the boundary
    /// and applying it at a dimension variable stays neutral (`PApp neutral r`).
    ///
    /// This is produced by [`reflect`](crate::value::reflect): any neutral whose type is a `PathP`
    /// is reflected here, whether it is a bare variable (`p : Path A x y`) or an applied spine
    /// (`h x : Path B (f x) (g x)`).
    ReflectedPath {
        neutral: Neutral,
        lhs: Box<Value>,
        rhs: Box<Value>,
    },
    /// A *reflected* neutral of `Pi` type: a function value that, when applied, reflects the
    /// applied spine at the (instantiated) codomain. This is what carries path endpoints through a
    /// path-valued function `h : Pi (x:A) (Path B (f x) (g x))` so that `(h x) @ 0 ≡ f x`.
    ReflectedFun {
        neutral: Neutral,
        /// The function's domain (unused for reduction but kept for completeness/quoting).
        dom: Box<Value>,
        /// The codomain family `B`; applied to the argument value to get the result type that the
        /// applied spine is reflected against.
        cod: Closure,
    },
    Glue {
        base: Box<Value>,
        cofib: crate::term::Cofib,
        ty: Box<Value>,
        equiv: Box<Value>,
    },

    // ---- effects (spec §4): the effectful-neutral and runtime continuation ----
    /// An **effectful-neutral** (spec §4, M2): a `perform op arg` whose enclosing handler is not
    /// yet known, so the computation is *stuck on the operation* exactly like a [`Neutral`] is
    /// stuck on a variable. The `cont` spine records the eliminations applied *since* the operation
    /// was performed (in order, outermost-last): when a `Handle` interprets this operation it will
    /// resume by replaying `cont` onto the value the handler passes to the continuation `k`.
    ///
    /// This is the free-monad node realized for a direct-style evaluator: each eliminator
    /// (`apply`, `do_elim`, projections, `papp`, `unglue`) *bubbles* an `OpNode` by pushing itself
    /// onto `cont` rather than getting stuck.
    OpNode {
        effect: crate::row::EffName,
        op: crate::signature::OpName,
        arg: Box<Value>,
        /// Pending eliminations to replay on resume, in application order (index 0 first).
        cont: Vec<Frame>,
    },

    /// A **runtime delimited continuation** (spec §4.3, M2): produced *only* by the evaluator when
    /// a [`Value::OpNode`] is interpreted by an enclosing `Handle`. Invoking `k v` (via [`apply`])
    /// resumes the captured computation by replaying `cont` onto `v` and then re-installing the
    /// handler `handler` around the result (deep-handler semantics — the handler stays in force for
    /// the remainder of the resumed computation). There is no source/`Term` form for this; `k` in a
    /// handler clause is an ordinary bound variable of function type `Bᵢ → C ! E`.
    Cont {
        /// The captured continuation spine to replay on the resume value.
        cont: Vec<Frame>,
        /// The handler to re-install around the resumed result (deep handlers).
        handler: Rc<HandlerVal>,
    },

    // ---- partiality (spec §4.5): the intensional Capretta delay ----
    /// `Delay A` as a *type* value (the type former). Carries the underlying value type `A`.
    Delay(Box<Value>),
    /// `now a : Delay A` — an immediately-available value of `Delay A`.
    Now(Box<Value>),
    /// `later d : Delay A` — a single **guarded** delay step. NbE does *not* force the inner
    /// `Delay A` value: `Later` is a canonical, non-reducing node, so each normalization step
    /// unfolds at most one layer and stays finite even for divergent (`define-rec`) computations.
    Later(Box<Value>),
    /// `force d` stuck on a **guarded** `later` (spec §4.5): forcing a `later` does not unfold it
    /// (intensional partiality keeps the delay structure observable), so `force (later d)` is a
    /// canonical, non-reducing node. (`force` on a `now` reduces; `force` on a neutral reflects to
    /// `Neutral::Force`; `force` on an `OpNode` bubbles — only the `later` case lands here.)
    Force(Box<Value>),

    // ---- primitive machine integers (M11) ----
    /// `Int` as a type value (`IntTy : Univ 0`).
    IntTy,
    /// An integer literal value holding its `i64`.
    IntLit(i64),
}

/// A handler value (spec §4.3): the captured environment plus the `return` and operation clauses,
/// kept as un-evaluated bodies (with their binders) so they can be run against fresh `x`/`k`. This
/// is the data an enclosing `Handle` folds an [`Value::OpNode`] tree with, and what a resumed
/// [`Value::Cont`] re-installs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandlerVal {
    /// The environment captured at the `Handle` site (the clauses' free variables live here).
    pub env: Env,
    /// `return x. r` — the value clause, binding the result `x` (1 binder, de Bruijn 0 = `x`).
    pub return_clause: Term,
    /// `(op x k. e)...` — one clause per handled operation, each binding `x` then `k`
    /// (2 binders: `k` innermost = de Bruijn 0, `x` = de Bruijn 1).
    pub op_clauses: Vec<(crate::signature::OpName, Term)>,
}

/// One pending elimination in an [`Value::OpNode`] continuation spine (or a resumed continuation).
/// Mirrors the [`Neutral`] eliminator set: replaying a frame on a value `v` re-applies that
/// elimination to `v`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Frame {
    /// `_ a` — application of the (resumed) value to a fixed argument `a`.
    App(Value),
    /// `f _` — application of a fixed function value `f` to the (resumed) value. This is the
    /// *argument-position* frame: it bubbles when an operation is performed in an argument, so
    /// call-by-value sequencing `(λx. …) (perform op a)` records "apply the function to my result".
    AppFun(Value),
    /// `fst _`.
    Fst,
    /// `snd _`.
    Snd,
    /// `_ @ r` — path application at an interval.
    PApp(Interval),
    /// `unglue _`.
    Unglue,
    /// `Elim D motive methods _` — eliminating the (resumed) value as a scrutinee.
    Elim {
        data: DataName,
        motive: Box<Value>,
        methods: Vec<Value>,
    },
    /// `force _` — forcing the (resumed) delay value.
    Force,
}

/// A neutral: a free variable (de Bruijn *level*) under a stack of eliminations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Neutral {
    /// A variable, stored as a de Bruijn *level* (so it is stable under weakening).
    Var(usize),
    App(Box<Neutral>, Box<Value>),
    Fst(Box<Neutral>),
    Snd(Box<Neutral>),
    PApp(Box<Neutral>, Interval),
    Elim {
        data: DataName,
        motive: Box<Value>,
        methods: Vec<Value>,
        scrutinee: Box<Neutral>,
    },
    /// `force _` — forcing a neutral (a variable of `Delay A`), kept stuck.
    Force(Box<Neutral>),
    /// `foreign "sym" : A` — an opaque trusted constant (spec §7.6). It is *stuck by construction*:
    /// nothing reduces it, and two foreigns are convertible only when their symbols (and types)
    /// coincide. Carrying the type lets `quote` reconstruct the original `Term::Foreign`.
    Foreign {
        symbol: String,
        ty: Box<Value>,
    },
    /// A *stuck* primitive `Int` operation (M11): at least one operand is neutral (not a literal),
    /// so the operation cannot reduce. Carries both operand values so `quote` can reconstruct the
    /// `Term::IntPrim`. (When both operands are `IntLit`s, `eval` reduces to an `IntLit` instead.)
    IntPrim {
        op: crate::term::IntPrimOp,
        lhs: Box<Value>,
        rhs: Box<Value>,
    },
}

/// An evaluation environment: values for the de Bruijn variables in scope, plus a shared handle
/// to the inductive [`Signature`] so that `eval` can perform ι-reduction on `Elim` without an
/// extra threaded parameter. The signature is shared (`Rc`) and captured into closures.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Env {
    values: Vec<Value>,
    /// Interpretations of dimension (interval) variables, indexed like `values` (most-recent
    /// binding first). Dimension variables live in a separate de Bruijn space from term vars.
    dims: Vec<Interval>,
    sig: Option<Rc<Signature>>,
}

impl Env {
    pub fn empty() -> Self {
        Env {
            values: Vec::new(),
            dims: Vec::new(),
            sig: None,
        }
    }

    /// An empty environment carrying a signature (used by the checker/normalizer entry points).
    pub fn with_sig(sig: Rc<Signature>) -> Self {
        Env {
            values: Vec::new(),
            dims: Vec::new(),
            sig: Some(sig),
        }
    }

    /// The signature this environment carries, if any.
    pub fn sig(&self) -> Option<&Rc<Signature>> {
        self.sig.as_ref()
    }

    /// Extend the environment with a value for the newly bound variable, preserving the sig.
    pub fn extend(&self, value: Value) -> Self {
        let mut values = Vec::with_capacity(self.values.len() + 1);
        values.push(value);
        values.extend(self.values.iter().cloned());
        Env {
            values,
            dims: self.dims.clone(),
            sig: self.sig.clone(),
        }
    }

    /// Extend the environment with an interpretation for a freshly bound dimension variable.
    pub fn extend_dim(&self, dim: Interval) -> Self {
        let mut dims = Vec::with_capacity(self.dims.len() + 1);
        dims.push(dim);
        dims.extend(self.dims.iter().cloned());
        Env {
            values: self.values.clone(),
            dims,
            sig: self.sig.clone(),
        }
    }

    /// Look up the interval bound to dimension de Bruijn index `i`.
    pub fn lookup_dim(&self, index: usize) -> Option<&Interval> {
        self.dims.get(index)
    }

    pub fn dim_len(&self) -> usize {
        self.dims.len()
    }

    /// Look up the value bound to de Bruijn index `i`.
    pub fn lookup(&self, index: usize) -> Option<&Value> {
        self.values.get(index)
    }

    /// Replace the value bound at de Bruijn *level* `lvl` (0 = outermost) with `v`. The internal
    /// store is innermost-first (de Bruijn-index order), so level `lvl` lives at index
    /// `len - 1 - lvl`. Used to apply a per-branch index specialization during dependent
    /// pattern-match refinement (see the kernel's `infer_elim` refinement path). Out-of-range
    /// levels are a no-op.
    pub fn set_level(&self, lvl: usize, v: Value) -> Env {
        let mut e = self.clone();
        let n = e.values.len();
        if lvl < n {
            e.values[n - 1 - lvl] = v;
        }
        e
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}
