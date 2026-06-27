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

    // ---- effects and handlers (spec §4) ----
    /// `perform op a` — invoke effect operation `op` of `effect` with argument `a` (spec §4.2).
    /// Contributes the effect's label to the row at the operation's continuation-multiplicity
    /// grade. Reduces to an `OpNode` under NbE (an effectful-neutral awaiting an enclosing
    /// `Handle`).
    Op {
        effect: crate::row::EffName,
        op: crate::signature::OpName,
        arg: Box<Term>,
    },
    /// `handle body { return x. r ; (op x k. e)... }` (spec §4.3). The handler interprets each
    /// listed operation, discharging that label from `body`'s row. Binders:
    /// - `return_clause` binds the result value `x` (1 binder).
    /// - each op clause binds the operation argument `x` then the continuation `k` (2 binders,
    ///   `k` innermost = de Bruijn 0, `x` = de Bruijn 1), where `k : Bᵢ → C ! E`.
    Handle {
        body: Box<Term>,
        return_clause: Box<Term>,
        op_clauses: Vec<(crate::signature::OpName, Box<Term>)>,
    },
    /// `! E A` — the effectful computation type: an `A`-computation that may use the effects in
    /// row `E` (spec §4.1). Pure `A` is `! ⟨⟩ A`.
    EffTy(crate::row::Row, Box<Term>),

    // ---- partiality (spec §4.5) ----
    /// `Delay A` — the (intensional Capretta) delay type former: a possibly-non-terminating
    /// computation of `A`. Divergence surfaces in this type.
    Delay(Box<Term>),
    /// `now a : Delay A` — an immediately-available value.
    Now(Box<Term>),
    /// `later d : Delay A` — a guarded delay step. NbE treats `Later` as a non-forced node so each
    /// normalization step unfolds finitely.
    Later(Box<Term>),
    /// `force d : A` when `d : Delay A` — the delay eliminator (spec §4.5). `force (now a) ⇝ a`;
    /// `force` over a `later`/neutral stays stuck (NbE keeps `Later` guarded). Typing `force`
    /// contributes the built-in `Partial` label to the row, so a proof may not use it.
    Force(Box<Term>),

    // ---- foreign function interface (spec §7.6 — the explicit unsafe hatch) ----
    /// `foreign "sym" : A` — an *opaque postulate* standing for an external C symbol `sym` of the
    /// ascribed type `A`. This is the one deliberate hole in the otherwise-total core: the kernel
    /// takes it on faith (it type-checks as a stuck constant of type `A`, never reduces, and carries
    /// no body), so it GROWS the trusted computing base. The independent re-checker therefore
    /// *declines* to certify any judgement that mentions a `Foreign` — a `foreign` import is trusted
    /// code that cannot be re-verified. Codegen lowers it to a direct call to the C symbol.
    Foreign { symbol: String, ty: Box<Term> },

    // ---- primitive machine integers (M11 — int-codegen; TCB-growing, user-approved) ----
    /// `Int` — the type of 64-bit signed machine integers (`i64`). A primitive kernel type:
    /// `IntTy : Univ 0`. It is *not* an inductive `Data`; it is a built-in base type with native
    /// arithmetic, so the kernel grows its trusted base to include `i64` semantics.
    IntTy,
    /// An integer literal `n : Int`, holding its `i64` value directly (not a unary `Nat`).
    IntLit(i64),
    /// A primitive arithmetic/comparison operation on two `Int` operands. Arithmetic ops
    /// (`Add/Sub/Mul/Div`) have type `Int`; comparisons (`Eq/Lt`) also return `Int` (`1` = true,
    /// `0` = false) — we deliberately return `Int` rather than the inductive `Bool` so the kernel's
    /// Int fragment is self-contained (the typing rule needs no `Bool` signature in scope, which
    /// keeps the TCB growth minimal and the kernel's own unit tests signature-free). A friendly
    /// `Bool`-returning comparison can be built in untrusted stdlib on top of this.
    IntPrim {
        op: IntPrimOp,
        lhs: Box<Term>,
        rhs: Box<Term>,
    },

    // ---- erasure (spec §7.2) ----
    /// A sentinel marking a sub-term that has been removed by the grade-`0` erasure pass. It has
    /// no runtime content and must never appear in a term submitted to the kernel; it exists only
    /// in the *output* of [`crate::erase::erase`] so that an erased argument position can be
    /// represented before the surrounding binder/application is dropped. Reaching it at runtime is
    /// a compiler bug.
    Erased,
}

/// The name of an inductive (or higher inductive) type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DataName(pub String);

/// The name of a constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConName(pub String);

/// A primitive `Int` operation (M11). Arithmetic (`Add/Sub/Mul/Div`) returns `Int`; comparisons
/// (`Eq/Lt`) return `Int` (`1`/`0`). Division (and `Sub` producing a negative, etc.) are total on
/// `i64` with wrapping/`0`-on-div-by-zero semantics handled in `eval` (see [`crate::normalize`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntPrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Lt,
}
