//! Core term grammar (spec §2.2), nameless (de Bruijn) representation.
//!
//! Terms and types are the same syntactic category ("types are terms"). Ordinary term
//! variables and *dimension* (interval) variables live in separate de Bruijn spaces, since
//! the interval `𝕀` is a pretype (spec §2.6): it has elements but is not in any universe and
//! is never stored at runtime.

use crate::semiring::Grade;

/// A universe level (spec §2.4): `0 | suc ℓ | ℓ ⊔ ℓ' | u` where `u` is a level variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Level {
    Zero,
    Suc(Box<Level>),
    Max(Box<Level>, Box<Level>),
    /// A level variable, as a de Bruijn index into the level context.
    Var(usize),
}

/// An interval term `r : 𝕀` (spec §2.6): endpoints, dimension variables, and the De Morgan
/// algebra. Interval terms are normalized to a canonical form for lattice-equation deciding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Interval {
    /// The endpoint 0.
    I0,
    /// The endpoint 1.
    I1,
    /// A dimension variable (de Bruijn index in the dimension context).
    Dim(usize),
    /// `r ∧ s` (De Morgan min).
    Min(Box<Interval>, Box<Interval>),
    /// `r ∨ s` (De Morgan max).
    Max(Box<Interval>, Box<Interval>),
    /// `¬ r` (De Morgan negation).
    Neg(Box<Interval>),
}

/// A cofibration `φ` (spec §2.6): the "where is this partial element defined" constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cofib {
    /// `⊤` — always satisfied.
    Top,
    /// `⊥` — never satisfied.
    Bot,
    /// `r = 0`.
    Eq0(Interval),
    /// `r = 1`.
    Eq1(Interval),
    /// `φ ∧ ψ`.
    And(Box<Cofib>, Box<Cofib>),
    /// `φ ∨ ψ`.
    Or(Box<Cofib>, Box<Cofib>),
}

/// One branch of a system `[ φᵢ ↦ tᵢ ]` (spec §2.6).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SystemBranch {
    pub face: Cofib,
    pub term: Term,
}

/// The core term grammar (spec §2.2). Nameless: binders introduce de Bruijn indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    // ---- core dependent layer ----
    /// A term variable (de Bruijn index).
    Var(usize),
    /// `Univ ℓ` — a universe at level ℓ (spec §2.4).
    Univ(Level),
    /// `Pi (x :^ρ A) B` — dependent function type; `ρ` is the binder grade (spec §3).
    Pi(Grade, Box<Term>, Box<Term>),
    /// `λ. t` — function (binder is nameless).
    Lam(Box<Term>),
    /// `f a` — application.
    App(Box<Term>, Box<Term>),
    /// `Sigma (x : A) B` — dependent pair type.
    Sigma(Box<Term>, Box<Term>),
    /// `(a , b)` — pair.
    Pair(Box<Term>, Box<Term>),
    /// First projection.
    Fst(Box<Term>),
    /// Second projection.
    Snd(Box<Term>),
    /// `(the A t)` — a type ascription (spec §5). Lets a checkable term (e.g. a `Lam`) appear in
    /// inference position; elaborated from the surface `the`/`define` ascriptions. The ascription
    /// is itself checked, so it adds no trust.
    Ann(Box<Term>, Box<Term>),

    // ---- data / recursion (spec §2.7) ----
    /// A (higher) inductive type former applied to params and indices: `Data D params indices`.
    Data(DataName, Vec<Term>, Vec<Term>),
    /// A constructor applied to its arguments: `Con c args`.
    Con(ConName, Vec<Term>),
    /// The dependent eliminator: `Elim D motive methods scrutinee`.
    Elim {
        data: DataName,
        motive: Box<Term>,
        methods: Vec<Term>,
        scrutinee: Box<Term>,
    },

    // ---- cubical layer (spec §2.6) ----
    /// An interval term lifted into the term grammar (only valid in dimension position).
    Interval(Interval),
    /// `PathP (i. A) x y` — dependent path over a line of types. `Path A x y` is the constant
    /// case (line `A` ignores `i`).
    PathP {
        family: Box<Term>,
        lhs: Box<Term>,
        rhs: Box<Term>,
    },
    /// `λ i. t` — path abstraction (binds a dimension variable).
    PLam(Box<Term>),
    /// `p @ r` — path application at interval `r`.
    PApp(Box<Term>, Interval),
    /// `Partial φ A` — partial element of `A` on cofibration `φ`.
    Partial(Cofib, Box<Term>),
    /// A system `[ φᵢ ↦ tᵢ ]`.
    System(Vec<SystemBranch>),
    /// `Transp (i. A) φ a0` — transport.
    Transp {
        family: Box<Term>,
        cofib: Cofib,
        base: Box<Term>,
    },
    /// `HComp A φ (i. u) a0` — homogeneous composition.
    HComp {
        ty: Box<Term>,
        cofib: Cofib,
        tube: Box<Term>,
        base: Box<Term>,
    },
    /// `Comp (i. A) φ (i. u) a0` — general Kan composition (derivable from HComp + Transp).
    Comp {
        family: Box<Term>,
        cofib: Cofib,
        tube: Box<Term>,
        base: Box<Term>,
    },
    /// `Glue A φ T e` — Glue type former.
    Glue {
        base: Box<Term>,
        cofib: Cofib,
        ty: Box<Term>,
        equiv: Box<Term>,
    },
    /// `glue` introduction.
    GlueTerm {
        cofib: Cofib,
        partial: Box<Term>,
        base: Box<Term>,
    },
    /// `unglue` elimination.
    Unglue(Box<Term>),
}

/// The name of an inductive (or higher inductive) type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataName(pub String);

/// The name of a constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConName(pub String);
