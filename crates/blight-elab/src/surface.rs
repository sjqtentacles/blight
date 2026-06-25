//! The surface AST (spec §5): named binders and tower sugar, before elaboration to core terms.
//! UNTRUSTED. Names here are real identifiers (not yet de Bruijn).

/// A surface-level binder `(x A)` or `(x A ρ)` with an optional grade.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binder {
    pub name: String,
    pub ty: Surface,
    /// Surface grade; `None` means the default `ω`.
    pub grade: Option<Surface>,
}

/// A `match` clause `[(Con args...) body]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause {
    pub constructor: String,
    pub binders: Vec<String>,
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
    /// `(match scrut clauses...)` — sugar; elaborates to `Elim`.
    Match(Box<Surface>, Vec<Clause>),
    /// A universe `(Type ℓ)`.
    Univ(usize),
}

/// A top-level surface declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    /// `(defdata D (params...) (Con (field ty)...)...)`.
    DefData {
        name: String,
        params: Vec<Binder>,
        constructors: Vec<(String, Vec<Binder>)>,
    },
    /// `(define-rec name body)` — a (possibly recursive) definition.
    DefineRec { name: String, body: Surface },
    /// `(define name body)` — a non-recursive definition.
    Define { name: String, body: Surface },
}
