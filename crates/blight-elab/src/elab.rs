//! The bidirectional elaborator (spec §6.1): surface terms to core kernel terms. UNTRUSTED.
//!
//! This is the §1.3 governing rule applied to the type checker itself: even "the type system
//! the user experiences" is untrusted tower code. Whatever core term `elaborate` produces is
//! re-checked by the spore; a wrong result is simply rejected (spec §6.1).

use crate::sexpr::Sexpr;
use crate::surface::{Binder, Clause, Decl, Surface};
use blight_kernel::Term;

/// An elaboration error (parsing-into-surface or surface-into-core).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElabError {
    /// A symbol was not in scope.
    Unbound(String),
    /// The s-expression was not a valid surface form.
    BadForm(String),
    /// A `match` did not cover its constructors / referenced an unknown one.
    BadMatch(String),
}

/// The elaboration environment: known top-level definitions and inductive declarations,
/// accumulated as the REPL processes forms.
#[derive(Debug, Clone, Default)]
pub struct ElabEnv {
    /// Top-level definitions: name → (its elaborated core term, optional closed type). When a type
    /// is known, references inline as an ascription so the kernel can infer through applications.
    globals: std::collections::HashMap<String, (Term, Option<Term>)>,
    /// Constructor metadata: constructor name → (data name, recursive-arg flags in order).
    constructors: std::collections::HashMap<String, ConInfo>,
    /// Data declarations: data name → ordered list of constructor names.
    datas: std::collections::HashMap<String, Vec<String>>,
    /// The kernel signature mirroring the declared inductives, used at check time.
    signature: blight_kernel::Signature,
}

/// Per-constructor info the elaborator needs to desugar `match`/`Con`.
#[derive(Debug, Clone)]
struct ConInfo {
    data: String,
    /// For each argument, whether it is recursive (a value of the data type).
    rec_flags: Vec<bool>,
}

impl ElabEnv {
    pub fn new() -> Self {
        ElabEnv::default()
    }

    /// The kernel signature accumulated from `defdata` declarations.
    pub fn signature(&self) -> &blight_kernel::Signature {
        &self.signature
    }

    /// The elaborated core term for a global definition, if defined.
    pub fn global_term(&self, name: &str) -> Option<&Term> {
        self.globals.get(name).map(|(t, _)| t)
    }

    /// Register a global definition's elaborated core term together with an optional (closed) type.
    pub fn define_global(&mut self, name: String, term: Term, ty: Option<Term>) {
        self.globals.insert(name, (term, ty));
    }

    /// Process a top-level declaration, updating the environment. For `defdata` it also extends the
    /// kernel signature; for `define`/`define-rec` it elaborates and stores the body. A declared
    /// core type may be supplied (required for `define-rec`, whose motive is read off the type).
    pub fn declare(&mut self, decl: &Decl, ty: Option<&Term>) -> Result<(), ElabError> {
        match decl {
            Decl::DefData {
                name,
                params,
                constructors,
            } => self.declare_data(name, params, constructors),
            Decl::Define { name, body } => {
                let term = match ty {
                    Some(t) => elaborate_against(self, body, t)?,
                    None => elaborate(self, body)?,
                };
                self.define_global(name.clone(), term, ty.cloned());
                Ok(())
            }
            Decl::DefineRec { name, body } => {
                let t = ty.ok_or_else(|| {
                    ElabError::BadForm(format!("`define-rec {name}` requires a declared type"))
                })?;
                let term = elaborate_rec(self, name, body, t)?;
                self.define_global(name.clone(), term, Some(t.clone()));
                Ok(())
            }
        }
    }

    fn declare_data(
        &mut self,
        name: &str,
        params: &[Binder],
        constructors: &[(String, Vec<Binder>)],
    ) -> Result<(), ElabError> {
        use blight_kernel::{Arg, Constructor, DataDecl, DataName, ConName};
        if !params.is_empty() {
            return Err(ElabError::BadForm(
                "M0 supports only non-parameterized inductives".into(),
            ));
        }
        let data_name = DataName(name.to_string());
        let mut kernel_ctors = Vec::new();
        let mut ctor_order = Vec::new();
        for (cname, fields) in constructors {
            let mut args = Vec::new();
            let mut rec_flags = Vec::new();
            for f in fields {
                // A field is recursive iff its type is exactly the data being defined.
                let is_rec = matches!(&f.ty, Surface::Var(v) if v == name);
                if is_rec {
                    args.push(Arg::Rec);
                    rec_flags.push(true);
                } else {
                    let ty = elaborate(self, &f.ty)?;
                    args.push(Arg::NonRec(ty));
                    rec_flags.push(false);
                }
            }
            kernel_ctors.push(Constructor {
                name: ConName(cname.clone()),
                args,
            });
            self.constructors.insert(
                cname.clone(),
                ConInfo {
                    data: name.to_string(),
                    rec_flags,
                },
            );
            ctor_order.push(cname.clone());
        }
        self.datas.insert(name.to_string(), ctor_order);
        self.signature.declare(DataDecl {
            name: data_name,
            params: vec![],
            level: 0,
            constructors: kernel_ctors,
            path_constructors: vec![],
        });
        Ok(())
    }
}

/// Parse a raw s-expression into a surface term.
pub fn parse_surface(s: &Sexpr) -> Result<Surface, ElabError> {
    match s {
        Sexpr::Atom(a) => Ok(Surface::Var(a.clone())),
        Sexpr::List(items) => parse_list(items),
    }
}

fn sym(s: &Sexpr) -> Result<String, ElabError> {
    match s {
        Sexpr::Atom(a) => Ok(a.clone()),
        _ => Err(ElabError::BadForm("expected a symbol".into())),
    }
}

fn parse_list(items: &[Sexpr]) -> Result<Surface, ElabError> {
    let head = items
        .first()
        .ok_or_else(|| ElabError::BadForm("empty list".into()))?;
    if let Sexpr::Atom(kw) = head {
        match kw.as_str() {
            "the" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(the T e)".into()));
                }
                let ty = parse_surface(&items[1])?;
                let e = parse_surface(&items[2])?;
                return Ok(Surface::The(Box::new(ty), Box::new(e)));
            }
            "lam" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(lam (x ...) body)".into()));
                }
                let names = parse_name_list(&items[1])?;
                let body = parse_surface(&items[2])?;
                return Ok(Surface::Lam(names, Box::new(body)));
            }
            "Pi" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(Pi ((x A) ...) B)".into()));
                }
                let binders = parse_binders(&items[1])?;
                let cod = parse_surface(&items[2])?;
                return Ok(Surface::Pi(binders, Box::new(cod)));
            }
            "Path" => {
                if items.len() != 4 {
                    return Err(ElabError::BadForm("(Path A x y)".into()));
                }
                return Ok(Surface::Path(
                    Box::new(parse_surface(&items[1])?),
                    Box::new(parse_surface(&items[2])?),
                    Box::new(parse_surface(&items[3])?),
                ));
            }
            "plam" => {
                if items.len() != 3 {
                    return Err(ElabError::BadForm("(plam (i) body)".into()));
                }
                let dims = parse_name_list(&items[1])?;
                if dims.len() != 1 {
                    return Err(ElabError::BadForm("(plam (i) body): one dim".into()));
                }
                let body = parse_surface(&items[2])?;
                return Ok(Surface::PLam(dims.into_iter().next().unwrap(), Box::new(body)));
            }
            "match" => {
                if items.len() < 2 {
                    return Err(ElabError::BadForm("(match scrut clauses...)".into()));
                }
                let scrut = parse_surface(&items[1])?;
                let mut clauses = Vec::new();
                for c in &items[2..] {
                    clauses.push(parse_clause(c)?);
                }
                return Ok(Surface::Match(Box::new(scrut), clauses));
            }
            "Type" => {
                if items.len() != 2 {
                    return Err(ElabError::BadForm("(Type ℓ)".into()));
                }
                let lvl: usize = sym(&items[1])?
                    .parse()
                    .map_err(|_| ElabError::BadForm("(Type ℓ): ℓ must be a nat".into()))?;
                return Ok(Surface::Univ(lvl));
            }
            _ => {}
        }
    }

    // Path application sugar: `(p @ r)`.
    if items.len() == 3 {
        if let Sexpr::Atom(at) = &items[1] {
            if at == "@" {
                return Ok(Surface::PApp(
                    Box::new(parse_surface(&items[0])?),
                    Box::new(parse_surface(&items[2])?),
                ));
            }
        }
    }

    // Otherwise an application `(f a ...)`.
    let f = parse_surface(&items[0])?;
    let mut args = Vec::new();
    for a in &items[1..] {
        args.push(parse_surface(a)?);
    }
    if args.is_empty() {
        Ok(f)
    } else {
        Ok(Surface::App(Box::new(f), args))
    }
}

/// Parse `(x y z)` as a list of names.
fn parse_name_list(s: &Sexpr) -> Result<Vec<String>, ElabError> {
    match s {
        Sexpr::List(items) => items.iter().map(sym).collect(),
        _ => Err(ElabError::BadForm("expected a list of names".into())),
    }
}

/// Parse `((x A) (y B) ...)` as binders (grade defaults to ω).
fn parse_binders(s: &Sexpr) -> Result<Vec<Binder>, ElabError> {
    let items = match s {
        Sexpr::List(items) => items,
        _ => return Err(ElabError::BadForm("expected a binder telescope".into())),
    };
    let mut out = Vec::new();
    for b in items {
        match b {
            Sexpr::List(parts) if parts.len() == 2 => out.push(Binder {
                name: sym(&parts[0])?,
                ty: parse_surface(&parts[1])?,
                grade: None,
            }),
            Sexpr::List(parts) if parts.len() == 3 => out.push(Binder {
                name: sym(&parts[0])?,
                ty: parse_surface(&parts[1])?,
                grade: Some(parse_surface(&parts[2])?),
            }),
            _ => return Err(ElabError::BadForm("binder must be (x A) or (x A ρ)".into())),
        }
    }
    Ok(out)
}

/// Parse a match clause `[(Con args...) body]`.
fn parse_clause(s: &Sexpr) -> Result<Clause, ElabError> {
    let items = match s {
        Sexpr::List(items) if items.len() == 2 => items,
        _ => return Err(ElabError::BadMatch("clause must be [(Con args...) body]".into())),
    };
    let pat = match &items[0] {
        Sexpr::List(p) if !p.is_empty() => p,
        _ => return Err(ElabError::BadMatch("clause pattern must be (Con args...)".into())),
    };
    let constructor = sym(&pat[0])?;
    let mut binders = Vec::new();
    for b in &pat[1..] {
        binders.push(sym(b)?);
    }
    let body = parse_surface(&items[1])?;
    Ok(Clause {
        constructor,
        binders,
        body,
    })
}

/// Parse a raw s-expression into a top-level declaration.
pub fn parse_decl(s: &Sexpr) -> Result<Decl, ElabError> {
    let items = match s {
        Sexpr::List(items) if !items.is_empty() => items,
        _ => return Err(ElabError::BadForm("a declaration must be a non-empty list".into())),
    };
    let kw = sym(&items[0])?;
    match kw.as_str() {
        "defdata" => {
            // (defdata D (params...) (Con (field ty)...)...)
            if items.len() < 3 {
                return Err(ElabError::BadForm("(defdata D (params) ctors...)".into()));
            }
            let name = sym(&items[1])?;
            let params = parse_binders(&items[2])?;
            let mut constructors = Vec::new();
            for c in &items[3..] {
                let parts = match c {
                    Sexpr::List(parts) if !parts.is_empty() => parts,
                    _ => return Err(ElabError::BadForm("constructor must be (Con fields...)".into())),
                };
                let cname = sym(&parts[0])?;
                let fields = if parts.len() == 1 {
                    Vec::new()
                } else {
                    // each field is (fieldname Type)
                    let mut fs = Vec::new();
                    for f in &parts[1..] {
                        match f {
                            Sexpr::List(fp) if fp.len() == 2 => fs.push(Binder {
                                name: sym(&fp[0])?,
                                ty: parse_surface(&fp[1])?,
                                grade: None,
                            }),
                            _ => {
                                return Err(ElabError::BadForm(
                                    "constructor field must be (name Type)".into(),
                                ))
                            }
                        }
                    }
                    fs
                };
                constructors.push((cname, fields));
            }
            Ok(Decl::DefData {
                name,
                params,
                constructors,
            })
        }
        "define-rec" => {
            if items.len() != 3 {
                return Err(ElabError::BadForm("(define-rec name body)".into()));
            }
            Ok(Decl::DefineRec {
                name: sym(&items[1])?,
                body: parse_surface(&items[2])?,
            })
        }
        "define" => {
            if items.len() != 3 {
                return Err(ElabError::BadForm("(define name body)".into()));
            }
            Ok(Decl::Define {
                name: sym(&items[1])?,
                body: parse_surface(&items[2])?,
            })
        }
        other => Err(ElabError::BadForm(format!("unknown declaration `{other}`"))),
    }
}

/// Elaborate a surface term to a core kernel term in inference mode (no expected type).
pub fn elaborate(env: &ElabEnv, term: &Surface) -> Result<Term, ElabError> {
    let scope = Scope::new();
    elab(env, &scope, term, None)
}

/// Elaborate a surface term against an expected core type (checking mode). Required to desugar a
/// `match` whose motive is read off the expected type (spec §6.2).
pub fn elaborate_against(env: &ElabEnv, term: &Surface, expected: &Term) -> Result<Term, ElabError> {
    let scope = Scope::new();
    elab(env, &scope, term, Some(expected))
}

/// A lexical scope tracking term-variable and dimension-variable names (each its own de Bruijn
/// space), plus an optional recursive self-name and the variable it structurally recurses on.
#[derive(Clone)]
struct Scope {
    /// Term variables, innermost last. de Bruijn index of name = `len - 1 - position`.
    vars: Vec<String>,
    /// Each term variable's type (in the de Bruijn scope at its binding site), when known.
    var_types: Vec<Option<Term>>,
    /// Dimension variables, innermost last.
    dims: Vec<String>,
    /// The name of the recursive function currently being elaborated, with the name of its
    /// recursion argument and the set of induction-hypothesis bindings available.
    rec: Option<RecCtx>,
}

#[derive(Clone)]
struct RecCtx {
    /// The function's own name (recursive self-reference).
    self_name: String,
    /// Map from "the structural sub-term variable name" → its IH variable name in scope.
    ih: std::collections::HashMap<String, String>,
}

impl Scope {
    fn new() -> Self {
        Scope {
            vars: Vec::new(),
            var_types: Vec::new(),
            dims: Vec::new(),
            rec: None,
        }
    }

    fn push_var(&self, name: &str) -> Self {
        self.push_var_ty(name, None)
    }

    fn push_var_ty(&self, name: &str, ty: Option<Term>) -> Self {
        let mut s = self.clone();
        s.vars.push(name.to_string());
        s.var_types.push(ty);
        s
    }

    fn push_dim(&self, name: &str) -> Self {
        let mut s = self.clone();
        s.dims.push(name.to_string());
        s
    }

    fn var_index(&self, name: &str) -> Option<usize> {
        self.vars
            .iter()
            .rev()
            .position(|n| n == name)
    }

    fn dim_index(&self, name: &str) -> Option<usize> {
        self.dims.iter().rev().position(|n| n == name)
    }
}

/// Resolve a surface interval expression (a dimension variable or an endpoint) to a kernel
/// [`Interval`].
fn elab_interval(scope: &Scope, term: &Surface) -> Result<blight_kernel::Interval, ElabError> {
    use blight_kernel::Interval;
    match term {
        Surface::Var(v) if v == "i0" => Ok(Interval::I0),
        Surface::Var(v) if v == "i1" => Ok(Interval::I1),
        Surface::Var(v) => scope
            .dim_index(v)
            .map(Interval::Dim)
            .ok_or_else(|| ElabError::Unbound(format!("dimension `{v}`"))),
        _ => Err(ElabError::BadForm("expected an interval expression".into())),
    }
}

fn elab(
    env: &ElabEnv,
    scope: &Scope,
    term: &Surface,
    expected: Option<&Term>,
) -> Result<Term, ElabError> {
    use blight_kernel::ConName;
    match term {
        Surface::Var(name) => {
            // 1) a bound term variable.
            if let Some(i) = scope.var_index(name) {
                return Ok(Term::Var(i));
            }
            // 2) a recursive self-reference is not directly representable; handled at call sites.
            // 3) a nullary constructor.
            if let Some(info) = env.constructors.get(name) {
                if info.rec_flags.is_empty() {
                    return Ok(Term::Con(ConName(name.clone()), vec![]));
                }
            }
            // 4) a data type name with no params.
            if env.datas.contains_key(name) {
                return Ok(Term::Data(blight_kernel::DataName(name.clone()), vec![], vec![]));
            }
            // 5) a global definition: inline it. When a type is known, wrap in an ascription so
            //    the kernel can infer through applications of an otherwise-bare `Lam`.
            if let Some((t, ty)) = env.globals.get(name) {
                return Ok(match ty {
                    Some(ty) => Term::Ann(Box::new(t.clone()), Box::new(ty.clone())),
                    None => t.clone(),
                });
            }
            Err(ElabError::Unbound(name.clone()))
        }

        Surface::The(ty, e) => {
            let ty_c = elab(env, scope, ty, None)?;
            let e_c = elab(env, scope, e, Some(&ty_c))?;
            Ok(Term::Ann(Box::new(e_c), Box::new(ty_c)))
        }

        Surface::Univ(l) => Ok(Term::Univ(nat_level(*l))),

        Surface::Lam(names, body) => {
            // Peel the expected Pi-telescope binder-by-binder, recording each binder's domain type
            // so that a `match` on an outer binder can generalize over later binders.
            let mut sc = scope.clone();
            let mut cur = expected.cloned();
            for n in names {
                let (dom, cod) = match cur {
                    Some(Term::Pi(_, dom, cod)) => (Some(*dom), Some(*cod)),
                    _ => (None, None),
                };
                sc = sc.push_var_ty(n, dom);
                cur = cod;
            }
            let mut core = elab(env, &sc, body, cur.as_ref())?;
            for _ in names {
                core = Term::Lam(Box::new(core));
            }
            Ok(core)
        }

        Surface::Pi(binders, cod) => elab_pi(env, scope, binders, cod),

        Surface::App(f, args) => {
            if let Some(t) = elab_app_head(env, scope, f, args)? {
                return Ok(t);
            }
            let mut head = elab(env, scope, f, None)?;
            for a in args {
                head = Term::App(Box::new(head), Box::new(elab(env, scope, a, None)?));
            }
            Ok(head)
        }

        Surface::Path(a, x, y) => {
            let sc_dim = scope.push_dim("_");
            let family = elab(env, &sc_dim, a, None)?;
            let lhs = elab(env, scope, x, None)?;
            let rhs = elab(env, scope, y, None)?;
            Ok(Term::PathP {
                family: Box::new(family),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
        }

        Surface::PLam(dim, body) => {
            let sc = scope.push_dim(dim);
            let core = elab(env, &sc, body, None)?;
            Ok(Term::PLam(Box::new(core)))
        }

        Surface::PApp(p, r) => {
            let pc = elab(env, scope, p, None)?;
            let rc = elab_interval(scope, r)?;
            Ok(Term::PApp(Box::new(pc), rc))
        }

        Surface::Match(scrut, clauses) => {
            let motive = expected.ok_or_else(|| {
                ElabError::BadMatch("cannot elaborate `match` without an expected type".into())
            })?;
            elab_match(env, scope, scrut, clauses, motive)
        }
    }
}

fn nat_level(n: usize) -> blight_kernel::Level {
    let mut l = blight_kernel::Level::Zero;
    for _ in 0..n {
        l = blight_kernel::Level::Suc(Box::new(l));
    }
    l
}

fn elab_pi(
    env: &ElabEnv,
    scope: &Scope,
    binders: &[Binder],
    cod: &Surface,
) -> Result<Term, ElabError> {
    use blight_kernel::Grade;
    match binders.split_first() {
        None => elab(env, scope, cod, None),
        Some((b, rest)) => {
            let dom = elab(env, scope, &b.ty, None)?;
            let sc = scope.push_var(&b.name);
            let cod_c = elab_pi(env, &sc, rest, cod)?;
            // M0: all surface Pi binders default to ω (grade surface syntax reserved for later).
            Ok(Term::Pi(Grade::Omega, Box::new(dom), Box::new(cod_c)))
        }
    }
}

/// Try to elaborate an application whose head is a constructor or a recursive self-call. Returns
/// `Ok(Some(term))` when handled specially, `Ok(None)` to fall back to plain application.
fn elab_app_head(
    env: &ElabEnv,
    scope: &Scope,
    f: &Surface,
    args: &[Surface],
) -> Result<Option<Term>, ElabError> {
    use blight_kernel::ConName;
    if let Surface::Var(name) = f {
        // Constructor application `(Con a ...)`.
        if let Some(info) = env.constructors.get(name) {
            if info.rec_flags.len() == args.len() {
                let mut cargs = Vec::new();
                for a in args {
                    cargs.push(elab(env, scope, a, None)?);
                }
                return Ok(Some(Term::Con(ConName(name.clone()), cargs)));
            }
        }
        // Recursive self-call `(self subterm ...)`: if the first argument is the recursion
        // variable, replace the call by its induction hypothesis applied to the remaining args.
        if let Some(rec) = &scope.rec {
            if &rec.self_name == name {
                if let Some(Surface::Var(first)) = args.first() {
                    if let Some(ih_name) = rec.ih.get(first) {
                        if let Some(idx) = scope.var_index(ih_name) {
                            let mut head = Term::Var(idx);
                            for a in &args[1..] {
                                head = Term::App(Box::new(head), Box::new(elab(env, scope, a, None)?));
                            }
                            return Ok(Some(head));
                        }
                    }
                }
                return Err(ElabError::BadMatch(format!(
                    "recursive call to `{name}` must be on the structural sub-term"
                )));
            }
        }
    }
    Ok(None)
}

/// Elaborate a `define-rec` body. The body must be `(lam (x ...) (match xi clauses))` where the
/// match is on one of the lambda binders; recursion is realized structurally as the `Elim`'s
/// induction hypotheses (spec §6.2). Requires the definition's declared core type.
fn elaborate_rec(
    env: &ElabEnv,
    name: &str,
    body: &Surface,
    ty: &Term,
) -> Result<Term, ElabError> {
    let mut scope = Scope::new();
    scope.rec = Some(RecCtx {
        self_name: name.to_string(),
        ih: std::collections::HashMap::new(),
    });
    elab(env, &scope, body, Some(ty))
}

/// Desugar `(match scrut clauses...)` to a kernel `Elim`. `expected` is the type the match must
/// inhabit, in the *current* de Bruijn scope; it becomes the eliminator's motive by abstracting
/// the scrutinee variable.
fn elab_match(
    env: &ElabEnv,
    scope: &Scope,
    scrut: &Surface,
    clauses: &[Clause],
    expected: &Term,
) -> Result<Term, ElabError> {
    use blight_kernel::{DataName, Grade};

    // M0: the scrutinee must be a variable, so the motive is a clean abstraction over it.
    let scrut_name = match scrut {
        Surface::Var(v) => v.clone(),
        _ => {
            return Err(ElabError::BadMatch(
                "M0 `match` requires a variable scrutinee".into(),
            ))
        }
    };
    let scrut_idx = scope
        .var_index(&scrut_name)
        .ok_or_else(|| ElabError::Unbound(scrut_name.clone()))?;

    // Binders introduced *after* the scrutinee (de Bruijn index < scrut_idx) must be generalized:
    // the eliminator's motive ranges over them, and every method re-binds them. `trailing[0]` is
    // the innermost (Var 0). Their declared types come from the scope.
    let mut trailing: Vec<Term> = Vec::new();
    for i in 0..scrut_idx {
        let pos = scope.vars.len() - 1 - i; // absolute position in `vars`
        let ty = scope.var_types[pos]
            .clone()
            .ok_or_else(|| ElabError::BadMatch("cannot generalize an untyped binder".into()))?;
        trailing.push(ty);
    }
    let m = trailing.len();

    // Which inductive does this match on?
    let first = clauses
        .first()
        .ok_or_else(|| ElabError::BadMatch("empty match".into()))?;
    let data_name = env
        .constructors
        .get(&first.constructor)
        .map(|i| i.data.clone())
        .ok_or_else(|| ElabError::BadMatch(format!("unknown constructor {}", first.constructor)))?;
    let ctor_order = env
        .datas
        .get(&data_name)
        .cloned()
        .ok_or_else(|| ElabError::BadMatch(format!("unknown data type {data_name}")))?;

    // Motive `λ s. Pi (t_{m-1}) ... Pi (t_0). expected`. Because the scrutinee binds *outside* the
    // trailing binders originally, the de Bruijn structure of `expected` already matches this
    // reconstruction; we only abstract the scrutinee occurrences.
    let mut motive_body = expected.clone();
    for ty in trailing.iter() {
        motive_body = Term::Pi(Grade::Omega, Box::new(ty.clone()), Box::new(motive_body));
    }
    let motive = Term::Lam(Box::new(abstract_var(&motive_body, scrut_idx)));

    // Build methods in declaration order.
    let mut methods = Vec::with_capacity(ctor_order.len());
    for cname in &ctor_order {
        let clause = clauses
            .iter()
            .find(|c| &c.constructor == cname)
            .ok_or_else(|| ElabError::BadMatch(format!("missing clause for {cname}")))?;
        let info = env
            .constructors
            .get(cname)
            .expect("constructor info present");
        if clause.binders.len() != info.rec_flags.len() {
            return Err(ElabError::BadMatch(format!(
                "constructor {cname} expects {} args, clause binds {}",
                info.rec_flags.len(),
                clause.binders.len()
            )));
        }

        // Method scope: add one binder per constructor arg, with an IH binder after each recursive
        // arg, then re-introduce the trailing binders.
        let mut sc = scope.clone();
        let mut rec = sc.rec.clone();
        let mut n_con_binders = 0usize;
        for (arg_name, &is_rec) in clause.binders.iter().zip(&info.rec_flags) {
            sc = sc.push_var(arg_name);
            n_con_binders += 1;
            if is_rec {
                let ih_name = format!("{arg_name}#ih");
                sc = sc.push_var(&ih_name);
                n_con_binders += 1;
                if let Some(r) = rec.as_mut() {
                    r.ih.insert(arg_name.clone(), ih_name);
                }
            }
        }
        sc.rec = rec;

        // Re-introduce the trailing binders (outermost-first so t_0 ends up at Var0 in the body).
        for i in (0..m).rev() {
            let pos = scope.vars.len() - 1 - i;
            let name = scope.vars[pos].clone();
            sc = sc.push_var_ty(&name, Some(trailing[i].clone()));
        }

        let body = elab(env, &sc, &clause.body, None)?;
        // Wrap: innermost are the trailing binders, then the constructor/IH binders.
        let mut method = body;
        for _ in 0..m {
            method = Term::Lam(Box::new(method));
        }
        for _ in 0..n_con_binders {
            method = Term::Lam(Box::new(method));
        }
        methods.push(method);
    }

    let elim = Term::Elim {
        data: DataName(data_name),
        motive: Box::new(motive),
        methods,
        scrutinee: Box::new(Term::Var(scrut_idx)),
    };

    // The match produced a value of `motive scrut`, i.e. `Pi(trailing) expected`. Re-apply it to
    // the trailing binders so the surrounding lambdas see a value of `expected`.
    let mut applied = elim;
    for i in (0..m).rev() {
        applied = Term::App(Box::new(applied), Box::new(Term::Var(i)));
    }
    Ok(applied)
}

/// Abstract the de Bruijn variable `k` out of `term`, producing a body valid under one fresh
/// outermost-of-this-scope binder: `Var(k)` becomes `Var(0)`, every other free `Var(j)` is shifted
/// up by one to account for the new binder.
fn abstract_var(term: &Term, k: usize) -> Term {
    abstract_var_at(term, k, 0)
}

/// `depth` counts binders crossed since entering the abstraction.
fn abstract_var_at(term: &Term, k: usize, depth: usize) -> Term {
    use blight_kernel::Term as T;
    let r = |t: &T| abstract_var_at(t, k, depth);
    let r1 = |t: &T| abstract_var_at(t, k, depth + 1);
    match term {
        T::Var(i) => {
            if *i == k + depth {
                T::Var(depth)
            } else if *i >= depth {
                T::Var(i + 1)
            } else {
                T::Var(*i)
            }
        }
        T::Univ(l) => T::Univ(l.clone()),
        T::Pi(g, a, b) => T::Pi(g.clone(), Box::new(r(a)), Box::new(r1(b))),
        T::Lam(b) => T::Lam(Box::new(r1(b))),
        T::App(f, a) => T::App(Box::new(r(f)), Box::new(r(a))),
        T::Sigma(a, b) => T::Sigma(Box::new(r(a)), Box::new(r1(b))),
        T::Pair(a, b) => T::Pair(Box::new(r(a)), Box::new(r(b))),
        T::Fst(a) => T::Fst(Box::new(r(a))),
        T::Snd(a) => T::Snd(Box::new(r(a))),
        T::Ann(a, b) => T::Ann(Box::new(r(a)), Box::new(r(b))),
        T::Data(d, ps, is) => T::Data(
            d.clone(),
            ps.iter().map(r).collect(),
            is.iter().map(r).collect(),
        ),
        T::Con(c, args) => T::Con(c.clone(), args.iter().map(r).collect()),
        T::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => T::Elim {
            data: data.clone(),
            // motive binds one variable (the scrutinee).
            motive: Box::new(r1(motive)),
            methods: methods.iter().map(r).collect(),
            scrutinee: Box::new(r(scrutinee)),
        },
        T::Interval(iv) => T::Interval(iv.clone()),
        T::PathP { family, lhs, rhs } => T::PathP {
            // family binds one dimension variable, not a term variable: keep term depth.
            family: Box::new(r(family)),
            lhs: Box::new(r(lhs)),
            rhs: Box::new(r(rhs)),
        },
        T::PLam(b) => T::PLam(Box::new(r(b))),
        T::PApp(p, iv) => T::PApp(Box::new(r(p)), iv.clone()),
        T::Partial(c, a) => T::Partial(c.clone(), Box::new(r(a))),
        T::System(_) => term.clone(),
        T::Transp { family, cofib, base } => T::Transp {
            family: Box::new(r(family)),
            cofib: cofib.clone(),
            base: Box::new(r(base)),
        },
        T::HComp {
            ty,
            cofib,
            tube,
            base,
        } => T::HComp {
            ty: Box::new(r(ty)),
            cofib: cofib.clone(),
            tube: Box::new(r(tube)),
            base: Box::new(r(base)),
        },
        T::Comp {
            family,
            cofib,
            tube,
            base,
        } => T::Comp {
            family: Box::new(r(family)),
            cofib: cofib.clone(),
            tube: Box::new(r(tube)),
            base: Box::new(r(base)),
        },
        T::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => T::Glue {
            base: Box::new(r(base)),
            cofib: cofib.clone(),
            ty: Box::new(r(ty)),
            equiv: Box::new(r(equiv)),
        },
        T::GlueTerm {
            cofib,
            partial,
            base,
        } => T::GlueTerm {
            cofib: cofib.clone(),
            partial: Box::new(r(partial)),
            base: Box::new(r(base)),
        },
        T::Unglue(a) => T::Unglue(Box::new(r(a))),
    }
}
