//! The NbE semantic domain (spec §3 of the implementation strategy doc; spec §2.5/§2.8).
//!
//! `eval : Term -> Value` interprets a term in an environment; `quote : Value -> Term` reads
//! a value back to a normal-form term. Definitional equality (`Conv`) compares normal forms.

use crate::signature::Signature;
use crate::term::{ConName, DataName, Interval, Level, Term};
use std::rc::Rc;

/// Take ownership of the `Value` inside an `Rc`, cloning only when shared — the audited
/// N6 replacement for what was a plain `*boxed` move before `Value`'s children moved to `Rc`
/// (same contract as `crate::term::unshare`: identical behavior, the fallback clone is shallow
/// because this node's own children are behind `Rc`).
/// Take ownership of a shared argument vector, cloning only when shared (N6 — the `Con`/`Data`
/// args moved behind `Rc<Vec<_>>` so a k-deep constructor chain clones in O(1)).
pub fn unshare_args(rc: Rc<Vec<Value>>) -> Vec<Value> {
    Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())
}

pub fn unshare_value(rc: Rc<Value>) -> Value {
    Rc::try_unwrap(rc).unwrap_or_else(|rc| (*rc).clone())
}

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
    Pi(crate::semiring::Grade, Rc<Value>, Closure),
    Lam(Closure),
    Sigma(Rc<Value>, Closure),
    Pair(Rc<Value>, Rc<Value>),
    Data(DataName, Rc<Vec<Value>>, Rc<Vec<Value>>),
    Con(ConName, Rc<Vec<Value>>),
    /// The value-level counterpart of [`crate::term::Term::PCon`] (spec §2.7, Wave 7/E4): a path
    /// constructor applied to its arguments, at a *non-endpoint* dimension. [`crate::normalize::eval`]
    /// collapses an endpoint `dim` (`I0`/`I1`) to the constructor's declared boundary value
    /// directly, so this variant's `dim` is never `I0`/`I1` — it is a genuine new canonical value
    /// (analogous to [`Value::Con`], but indexed by a dimension rather than only by term args).
    PCon {
        data: DataName,
        name: ConName,
        args: Rc<Vec<Value>>,
        dim: Interval,
    },
    PathP {
        family: Closure,
        lhs: Rc<Value>,
        rhs: Rc<Value>,
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
        lhs: Rc<Value>,
        rhs: Rc<Value>,
    },
    /// A *reflected* neutral of `Pi` type: a function value that, when applied, reflects the
    /// applied spine at the (instantiated) codomain. This is what carries path endpoints through a
    /// path-valued function `h : Pi (x:A) (Path B (f x) (g x))` so that `(h x) @ 0 ≡ f x`.
    ReflectedFun {
        neutral: Neutral,
        /// The function's domain (unused for reduction but kept for completeness/quoting).
        dom: Rc<Value>,
        /// The codomain family `B`; applied to the argument value to get the result type that the
        /// applied spine is reflected against.
        cod: Closure,
    },
    Glue {
        base: Rc<Value>,
        cofib: crate::term::Cofib,
        ty: Rc<Value>,
        equiv: Rc<Value>,
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
        /// The operation's type-argument instantiation (Wave 7/E2), carried through evaluation so
        /// two effectful-neutrals of a *differently-instantiated* parameterized operation are never
        /// misjudged convertible (see `conv_at`'s `OpNode` rule) — the value-level analogue of
        /// [`Value::Data`]'s `params`. Empty for a non-parameterized effect.
        type_args: Vec<Value>,
        arg: Rc<Value>,
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
    Delay(Rc<Value>),
    /// `now a : Delay A` — an immediately-available value of `Delay A`.
    Now(Rc<Value>),
    /// `later d : Delay A` — a single **guarded** delay step. NbE does *not* force the inner
    /// `Delay A` value: `Later` is a canonical, non-reducing node, so each normalization step
    /// unfolds at most one layer and stays finite even for divergent (`define-rec`) computations.
    Later(Rc<Value>),
    /// `force d` stuck on a **guarded** `later` (spec §4.5): forcing a `later` does not unfold it
    /// (intensional partiality keeps the delay structure observable), so `force (later d)` is a
    /// canonical, non-reducing node. (`force` on a `now` reduces; `force` on a neutral reflects to
    /// `Neutral::Force`; `force` on an `OpNode` bubbles — only the `later` case lands here.)
    Force(Rc<Value>),

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
        motive: Rc<Value>,
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
    App(Rc<Neutral>, Rc<Value>),
    Fst(Rc<Neutral>),
    Snd(Rc<Neutral>),
    PApp(Rc<Neutral>, Interval),
    Elim {
        data: DataName,
        motive: Rc<Value>,
        methods: Vec<Value>,
        scrutinee: Rc<Neutral>,
    },
    /// `force _` — forcing a neutral (a variable of `Delay A`), kept stuck.
    Force(Rc<Neutral>),
    /// `foreign "sym" : A` — an opaque trusted constant (spec §7.6). It is *stuck by construction*:
    /// nothing reduces it, and two foreigns are convertible only when their symbols (and types)
    /// coincide. Carrying the type lets `quote` reconstruct the original `Term::Foreign`.
    Foreign {
        symbol: String,
        ty: Rc<Value>,
    },
    /// A *stuck* primitive `Int` operation (M11): at least one operand is neutral (not a literal),
    /// so the operation cannot reduce. Carries both operand values so `quote` can reconstruct the
    /// `Term::IntPrim`. (When both operands are `IntLit`s, `eval` reduces to an `IntLit` instead.)
    IntPrim {
        op: crate::term::IntPrimOp,
        lhs: Rc<Value>,
        rhs: Rc<Value>,
    },
}

/// A persistent, structurally-shared stack of bound values (head = most-recently-bound, matching
/// de Bruijn index 0).
///
/// This exists purely for performance, and is the core of Wave 5/N1's "NbE-with-sharing": storing
/// bindings in a `Vec<Value>` (the previous representation) makes [`Env::extend`] — invoked on
/// every β/ι step — an O(n) copy of every previously-bound value, so a computation `n` binders
/// deep pays O(n²) in environment bookkeeping alone. That cost then multiplies *again* every time
/// a closure capturing such an environment is itself cloned, which `do_elim`'s recursive-argument
/// case does once per constructor argument (`motive.clone()`/`methods.clone()` in `normalize.rs`).
/// This compounding "no sharing across reduction steps" cost is exactly what
/// `crates/blight-prelude/spore_reader.bl` documents as the normalizer performance wall.
///
/// A persistent cons-list makes `extend`/`clone` an O(1) `Rc` bump instead: everything below the
/// new binding is shared, not copied, so an environment's cost is paid once when built, not once
/// per snapshot taken of it. Lookup by index walks the list — O(index) instead of the `Vec`'s
/// O(1) — but a de Bruijn index is bounded by *lexical* nesting depth at its use site, not by
/// total reduction depth, so this is the right trade for a normalizer that recurses far deeper
/// than any single term ever binds.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ValueChain(Option<Rc<ValueNode>>);

#[derive(Debug, PartialEq, Eq)]
struct ValueNode {
    head: Value,
    tail: ValueChain,
    /// Cached so `ValueChain::len` (hence `Env::len`) stays O(1) rather than walking the list.
    len: usize,
}

impl ValueChain {
    fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.len)
    }

    fn push(&self, head: Value) -> ValueChain {
        ValueChain(Some(Rc::new(ValueNode {
            head,
            tail: self.clone(),
            len: self.len() + 1,
        })))
    }

    fn get(&self, mut index: usize) -> Option<&Value> {
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
    /// every node below it (only the O(index) path from the head down is reallocated). A no-op
    /// (returns an unchanged clone) once the chain is exhausted before `index` is reached, mirroring
    /// [`Env::set_level`]'s existing "out-of-range level is a no-op" contract.
    fn set(&self, index: usize, v: Value) -> ValueChain {
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

/// An evaluation environment: values for the de Bruijn variables in scope, plus a shared handle
/// to the inductive [`Signature`] so that `eval` can perform ι-reduction on `Elim` without an
/// extra threaded parameter. The signature is shared (`Rc`) and captured into closures.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Env {
    values: ValueChain,
    /// Interpretations of dimension (interval) variables, indexed like `values` (most-recent
    /// binding first). Dimension variables live in a separate de Bruijn space from term vars.
    dims: Vec<Interval>,
    sig: Option<Rc<Signature>>,
}

impl Env {
    pub fn empty() -> Self {
        Env {
            values: ValueChain::default(),
            dims: Vec::new(),
            sig: None,
        }
    }

    /// An empty environment carrying a signature (used by the checker/normalizer entry points).
    pub fn with_sig(sig: Rc<Signature>) -> Self {
        Env {
            values: ValueChain::default(),
            dims: Vec::new(),
            sig: Some(sig),
        }
    }

    /// The signature this environment carries, if any.
    pub fn sig(&self) -> Option<&Rc<Signature>> {
        self.sig.as_ref()
    }

    /// Extend the environment with a value for the newly bound variable, preserving the sig.
    ///
    /// O(1): this is a single `Rc` bump on the shared [`ValueChain`], not a copy of every
    /// previously-bound value (see `ValueChain`'s doc-comment for why that matters).
    pub fn extend(&self, value: Value) -> Self {
        Env {
            values: self.values.push(value),
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

    /// Rebind an already-bound dimension variable to a specific interval (used to specialize a
    /// "generic point" environment to one face/vertex of a cofibration while leaving every other
    /// dimension's binding untouched). Panics if `index` is out of range.
    pub fn override_dim(&self, index: usize, dim: Interval) -> Self {
        let mut dims = self.dims.clone();
        dims[index] = dim;
        Env {
            values: self.values.clone(),
            dims,
            sig: self.sig.clone(),
        }
    }

    pub fn dim_len(&self) -> usize {
        self.dims.len()
    }

    /// Look up the value bound to de Bruijn index `i`.
    pub fn lookup(&self, index: usize) -> Option<&Value> {
        self.values.get(index)
    }

    /// Replace the value bound at de Bruijn *level* `lvl` (0 = outermost) with `v`. The logical
    /// store is innermost-first (de Bruijn-index order), so level `lvl` lives at chain position
    /// `len - 1 - lvl`. Used to apply a per-branch index specialization during dependent
    /// pattern-match refinement (see the kernel's `infer_elim` refinement path). Out-of-range
    /// levels are a no-op. Shares every chain node except the O(lvl) path rebuilt down to the
    /// replaced position.
    pub fn set_level(&self, lvl: usize, v: Value) -> Env {
        let n = self.values.len();
        if lvl < n {
            Env {
                values: self.values.set(n - 1 - lvl, v),
                dims: self.dims.clone(),
                sig: self.sig.clone(),
            }
        } else {
            self.clone()
        }
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.len() == 0
    }
}
