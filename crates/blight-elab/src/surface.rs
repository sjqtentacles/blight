//! The surface AST (spec §5): named binders and tower sugar, before elaboration to core terms.
//! UNTRUSTED. Names here are real identifiers (not yet de Bruijn).

/// A surface-level binder `(x A)` or `(x A ρ)` with an optional grade. An *implicit* binder
/// `{x A}` is solved by the elaborator (metavariable + unification / instance search) rather than
/// supplied at the call site (spec §6.4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binder {
    pub name: String,
    pub ty: Surface,
    /// Surface grade; `None` means the default `ω`.
    pub grade: Option<Surface>,
    /// `true` for an implicit binder `{x A}` whose argument is inferred, not passed explicitly.
    pub implicit: bool,
}

/// A surface pattern (spec §6.2). The richer `match` compiler supports nested constructor
/// patterns, wildcards, and variable patterns; the old flat `(Con x y)` is the special case of
/// constructor patterns whose sub-patterns are all variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// `_` — matches anything, binds nothing.
    Wild,
    /// `x` — matches anything, binds it to `x`.
    Var(String),
    /// `(Con p …)` — matches `Con` applied to sub-patterns; `Con` with no args is the nullary case.
    Con(String, Vec<Pattern>),
}

/// A `match` clause `[pat … body]`: one pattern per scrutinee, then the body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    /// One pattern per scrutinee (length matches the number of scrutinees).
    pub patterns: Vec<Pattern>,
    pub body: Surface,
}

/// The surface term language (spec §5). Tower sugar (`match`, `Path`, etc.) is desugared by the
/// elaborator into core kernel terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Surface {
    Var(String),
    /// `(the T e)` — type ascription (the `check` entry point).
    The(Box<Surface>, Box<Surface>),
    /// `(lam (x ...) body)`.
    Lam(Vec<String>, Box<Surface>),
    /// `(f a ...)` — application (possibly multi-argument).
    App(Box<Surface>, Vec<Surface>),
    /// `(Pi ((x A) ...) B)`.
    Pi(Vec<Binder>, Box<Surface>),
    /// `(Path A x y)`.
    Path(Box<Surface>, Box<Surface>, Box<Surface>),
    /// `(plam (i) body)` — path abstraction.
    PLam(String, Box<Surface>),
    /// `(p @ r)` — path application.
    PApp(Box<Surface>, Box<Surface>),
    /// `(match scrut … clauses…)` — sugar; compiles to nested `Elim`. Supports multiple scrutinees,
    /// nested/wildcard patterns, and inference-mode (motive from the first clause / an ascription).
    Match(Vec<Surface>, Vec<Clause>),
    /// A universe `(Type ℓ)`.
    Univ(usize),
    /// `(Delay A)` — the partiality (Capretta delay) type former (spec §4.5).
    Delay(Box<Surface>),
    /// `(now a)` — an immediately-available delayed value.
    Now(Box<Surface>),
    /// `(later d)` — a guarded delay step (a possibly-diverging continuation).
    Later(Box<Surface>),
    /// `(force d)` — force a `Delay A` to its `A` value (spec §4.5). The forced computation may
    /// diverge, so it carries the built-in `Partial` effect (it cannot inhabit a proof).
    Force(Box<Surface>),
    /// `(perform op arg)` — perform an algebraic operation (spec §4.2); elaborates to `Term::Op`.
    Perform(String, Box<Surface>),
    /// `(handle body (return x r) (op x k e) ...)` — an effect handler (spec §4.3); elaborates to
    /// `Term::Handle`. The first clause is the `return` clause; the rest are operation clauses.
    Handle {
        body: Box<Surface>,
        /// `return x. r` — the value clause: the bound name and its body.
        return_clause: (String, Box<Surface>),
        /// `(op x k e)...` — one clause per handled operation: the op name, the argument binder,
        /// the continuation binder, and the clause body.
        op_clauses: Vec<(String, String, String, Surface)>,
    },
    /// `(! E A)` — an effectful computation type (spec §4.1): an `A`-computation in row `E`. `E` is
    /// a single effect name, or `()`/`pure` for the empty (pure) row.
    Bang(Box<Surface>, Box<Surface>),
    /// `(Sigma ((x A) ...) B)` — dependent pair / record type (spec §6.4/§6.5). Sugar over the
    /// kernel `Term::Sigma`; an n-ary telescope nests right.
    Sigma(Vec<Binder>, Box<Surface>),
    /// `(pair a b)` or `(a , b)` — a (possibly dependent) pair; elaborates to `Term::Pair`.
    Pair(Box<Surface>, Box<Surface>),
    /// `(fst p)` — first projection.
    Fst(Box<Surface>),
    /// `(snd p)` — second projection.
    Snd(Box<Surface>),
    /// `(let ((x e)) b)` — a non-recursive local binding; desugars to `((lam (x) b) e)`.
    Let(String, Box<Surface>, Box<Surface>),
    /// `(region r body)` — open a memory region (spec §3.5). The capability `r : Rgn` is bound at
    /// grade `1` (linear) so the existing kernel rule scopes its lifetime; the elaborator desugars
    /// this to a grade-1 λ over `r`, applied to a fresh `rgn-tok`. Carries no new core node — it is
    /// an ordinary linear binding the backend recognizes for arena allocation.
    Region(String, Box<Surface>),
    // ---- primitive machine integers (M11 — int-codegen) ----
    /// The `Int` type atom — primitive 64-bit signed machine integers. Distinct from `Nat`: bare
    /// numerals keep elaborating to unary `Nat`, so existing programs are unaffected.
    IntTy,
    /// `(int 42)` — a primitive `Int` literal carrying its `i64` value. We use the explicit `(int
    /// n)` form (rather than overloading bare numerals) precisely so `Nat` literals keep their
    /// meaning.
    IntLit(i64),
    /// A primitive `Int` operation: `(int+ a b)`, `(int- a b)`, `(int* a b)`, `(int/ a b)`,
    /// `(int= a b)`, `(int< a b)`. Comparisons conclude `Int` (1/0) like the kernel primitive.
    IntPrim(blight_kernel::IntPrimOp, Box<Surface>, Box<Surface>),
}

/// A constructor declaration within a `defdata`: its name, the field telescope, and (for indexed
/// families) the result indices it targets, in the scope `[fields…, params…]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorDecl {
    pub name: String,
    pub fields: Vec<Binder>,
    pub result_indices: Vec<Surface>,
}

/// A top-level surface declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    /// `(defdata D (params...) (Con (field ty)...)...)` or the indexed form
    /// `(defdata D (params...) (indices...) (Con (field ty)... (=> idx...))...)`.
    DefData {
        name: String,
        params: Vec<Binder>,
        indices: Vec<Binder>,
        constructors: Vec<ConstructorDecl>,
    },
    /// `(define-rec name body)` — a (possibly recursive) definition. If its recursion is
    /// structural it compiles to `Elim` (total, partiality grade `0`); otherwise it elaborates to a
    /// partial (`Delay`-typed, `Later`-guarded) definition carrying the built-in `Partial` effect at
    /// a nonzero grade (spec §4.5, §6.2).
    DefineRec { name: String, body: Surface },
    /// `(deftotal name body)` — like `define-rec`, but *requires* the structural/`Elim`
    /// compilation: a non-structural recursion is rejected (partiality grade must be `0`).
    DefTotal { name: String, body: Surface },
    /// `(effect E (op param-ty result-ty) ...)` — declare an algebraic effect and its operations
    /// (spec §4.2). Each operation is `(name A B)` with parameter type `A` and result type `B`.
    DefEffect {
        name: String,
        ops: Vec<(String, Surface, Surface)>,
    },
    /// `(define name body)` — a non-recursive definition.
    Define { name: String, body: Surface },
    /// `(foreign name <type> "c_symbol")` — an opaque trusted FFI postulate (spec §7.6). Binds
    /// `name` to a kernel `Foreign` constant of the ascribed `type`, lowered to a call of the C
    /// symbol `c_symbol`. This is the one deliberate hole in the total core: the kernel trusts it
    /// (growing the TCB), and the independent re-checker declines any term that mentions it.
    Foreign {
        name: String,
        ty: Surface,
        symbol: String,
    },
}
