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

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}
