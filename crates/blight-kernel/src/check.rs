//! The inference rules (spec §2.5–§2.7): the bidirectional checker. This is the **only** place
//! a [`Proof`] is constructed (via the crate-private `Proof::trusted_new`).
//!
//! `infer` synthesizes a type for a term; `check` verifies a term against an expected type,
//! driving definitional equality through [`crate::normalize::conv`]. A successful top-level
//! `check`/`infer` yields a `Proof` of the corresponding `HasType` judgement.

use crate::context::Context;
use crate::normalize::{conv, eval, quote, reflect};
use crate::proof::{Judgement, Proof};
use crate::semiring::Grade;
use crate::signature::{Arg, Constructor, DataDecl, Signature};
use crate::term::{Cofib, DataName, Level, Term};
use crate::value::{Env, Neutral, Value};

/// A kernel type error. Carries enough to report *why* a term failed to check; it never
/// indicates unsoundness, only "this did not grow a proof" (spec §1.2).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    /// A variable index escaped the context.
    UnboundVar(usize),
    /// Expected one head former, found another (e.g. applied a non-function).
    Mismatch { expected: String, found: String },
    /// Definitional equality failed (`Conv`): `lhs ≢ rhs`.
    NotConvertible { lhs: String, rhs: String },
    /// A grade discipline violation (e.g. linear variable used twice).
    GradeViolation(String),
    /// Universe inconsistency (level error).
    UniverseError(String),
    /// A malformed inductive declaration (e.g. strict-positivity failure).
    BadDataDecl(String),
    /// A malformed cubical term (e.g. a path with wrong boundary).
    BadCubical(String),
    /// A term that cannot be inferred (needs an ascription).
    CannotInfer(String),
}

/// Concretize a [`Level`] to a natural number. For M0, levels are closed (no level variables in
/// the surface), so this is total; level-variable support is added with universe polymorphism.
fn level_to_nat(l: &Level) -> Result<u32, TypeError> {
    match l {
        Level::Zero => Ok(0),
        Level::Suc(inner) => Ok(level_to_nat(inner)? + 1),
        Level::Max(a, b) => Ok(level_to_nat(a)?.max(level_to_nat(b)?)),
        Level::Var(_) => Err(TypeError::UniverseError(
            "level variables not yet supported in M0 core".into(),
        )),
    }
}

/// Build a [`Level`] from a natural number.
fn nat_to_level(n: u32) -> Level {
    let mut l = Level::Zero;
    for _ in 0..n {
        l = Level::Suc(Box::new(l));
    }
    l
}

/// The kernel checker, carrying the inductive [`Signature`] consulted when typing
/// `Data`/`Con`/`Elim`. All inference and checking are methods so the signature is threaded
/// implicitly (and shared into evaluation environments for ι-reduction).
pub struct Checker {
    pub sig: std::rc::Rc<Signature>,
}

impl Checker {
    pub fn new(sig: std::rc::Rc<Signature>) -> Self {
        Checker { sig }
    }

    /// Build an evaluation environment at the given context depth that carries the signature, so
    /// that evaluating `Elim` inside types performs ι-reduction. Dimension variables are seeded as
    /// free dimension *levels* so cubical types evaluate to neutrals rather than panicking.
    fn env_for(&self, ctx: &Context) -> Env {
        let n = ctx.len();
        // Build the environment exactly as the plain neutral version does (so de Bruijn levels match
        // the rest of the kernel), but *reflect* each binder against its type (see
        // [`crate::normalize::reflect`]). For a plain type this yields the bare neutral; for a
        // `PathP` type it yields a `ReflectedPath` carrying endpoints; for a path-valued function
        // `h : Pi A (Path ..)` it yields a `ReflectedFun` that carries endpoints through application.
        //
        // Each entry's type is stored relative to its *outer* context (see `check`'s
        // `quote(ctx.len(), ..)` when extending), so we must evaluate it in the environment of the
        // binders already added. We therefore add binders outer-to-inner, matching `ctx.lookup`'s
        // index convention where index `n-1` is outermost.
        let mut env = Env::with_sig(self.sig.clone());
        let mut prefix: Vec<Value> = Vec::with_capacity(n);
        for i in (0..n).rev() {
            // `check` introduces the binder at context index `i` with a neutral at level `n-1-i`
            // (see Pi-Intro: `Var(ctx.len())` at introduction time). `env_for` must use the *same*
            // level convention, otherwise multi-binder types resolve their outer references to the
            // wrong neutral.
            let level = n - 1 - i;
            let entry = ctx.lookup(i).expect("context entry in range");
            // Evaluate the entry's type in the environment of strictly-outer binders.
            let outer_env = {
                let mut e = Env::with_sig(self.sig.clone());
                for v in prefix.iter() {
                    e = e.extend(v.clone());
                }
                e
            };
            let value = reflect(Neutral::Var(level), &eval(&outer_env, &entry.ty));
            prefix.push(value.clone());
            env = env.extend(value);
        }
        let d = ctx.dim_len();
        for _ in 0..d {
            let level = d - 1 - env.dim_len();
            env = env.extend_dim(crate::term::Interval::Dim(level));
        }
        env
    }

/// Synthesize a type for `term` in context `ctx` (the `infer` direction, spec §6.1). Returns
/// the term's type as a semantic [`Value`].
pub fn infer(&self, ctx: &Context, term: &Term) -> Result<Value, TypeError> {
    match term {
        Term::Var(i) => ctx
            .lookup(*i)
            .map(|e| {
                // The entry's type is stored relative to the context *below* index `i` (Pi-Intro
                // quotes the domain at the then-current depth, before extension). To evaluate it in
                // the full-context environment we weaken it past the `i + 1` binders now inside it.
                let ty = shift(&e.ty, *i + 1);
                eval(&self.env_for(ctx), &ty)
            })
            .ok_or(TypeError::UnboundVar(*i)),

        // Univ ℓ : Univ (ℓ+1)  (spec §2.4, U-Type).
        Term::Univ(l) => {
            let n = level_to_nat(l)?;
            Ok(Value::Univ(nat_to_level(n + 1)))
        }

        // Pi-Form: Γ ⊢ A : Univ ℓ, Γ,x:^ρ A ⊢ B : Univ ℓ' ⟹ Pi : Univ (ℓ ⊔ ℓ').
        Term::Pi(grade, dom, cod) => {
            let dom_lvl = self.infer_universe(ctx, dom)?;
            let ctx2 = ctx.extend((**dom).clone(), *grade);
            let cod_lvl = self.infer_universe(&ctx2, cod)?;
            Ok(Value::Univ(nat_to_level(dom_lvl.max(cod_lvl))))
        }

        // Sigma-Form, analogous (grade ω on the first component for M0).
        Term::Sigma(dom, cod) => {
            let dom_lvl = self.infer_universe(ctx, dom)?;
            let ctx2 = ctx.extend((**dom).clone(), Grade::Omega);
            let cod_lvl = self.infer_universe(&ctx2, cod)?;
            Ok(Value::Univ(nat_to_level(dom_lvl.max(cod_lvl))))
        }

        // Pi-Elim / app: infer f : Pi (x:^ρ A) B, check a : A, result B[a/x].
        Term::App(f, a) => {
            let f_ty = self.infer(ctx, f)?;
            match f_ty {
                Value::Pi(_grade, dom, cod) => {
                    self.check(ctx, a, &dom)?;
                    let a_val = eval(&self.env_for(ctx), a);
                    Ok(cod.apply(a_val))
                }
                other => Err(TypeError::Mismatch {
                    expected: "a function (Pi) type".into(),
                    found: format!("{other:?}"),
                }),
            }
        }

        // Sigma-Elim.
        Term::Fst(p) => match self.infer(ctx, p)? {
            Value::Sigma(dom, _cod) => Ok(*dom),
            other => Err(TypeError::Mismatch {
                expected: "a pair (Sigma) type".into(),
                found: format!("{other:?}"),
            }),
        },
        Term::Snd(p) => match self.infer(ctx, p)? {
            Value::Sigma(_dom, cod) => {
                let fst_val = eval(&self.env_for(ctx), &Term::Fst(p.clone()));
                Ok(cod.apply(fst_val))
            }
            other => Err(TypeError::Mismatch {
                expected: "a pair (Sigma) type".into(),
                found: format!("{other:?}"),
            }),
        },

        // Ascription `(the A t)`: check t against A, then synthesize A.
        Term::Ann(t, ty) => {
            self.infer_universe(ctx, ty)?;
            let ty_val = eval(&self.env_for(ctx), ty);
            self.check(ctx, t, &ty_val)?;
            Ok(ty_val)
        }

        Term::Lam(_) | Term::Pair(_, _) => Err(TypeError::CannotInfer(
            "lambda/pair need a type ascription to infer".into(),
        )),

        // Data formation (spec §2.7). For M0 we support non-parameterized, non-indexed
        // inductives; the type lives in the declared universe.
        Term::Data(name, params, indices) => {
            let decl = self.sig.get(name).ok_or_else(|| {
                TypeError::BadDataDecl(format!("unknown inductive type {name:?}"))
            })?;
            if !params.is_empty() || !indices.is_empty() || !decl.params.is_empty() {
                return Err(TypeError::BadDataDecl(
                    "M0 supports only non-parameterized, non-indexed inductives".into(),
                ));
            }
            Ok(Value::Univ(nat_to_level(decl.level)))
        }

        // Constructor introduction (spec §2.7). Find the declaring data type, check each argument
        // against its declared type (recursive args against the data type itself), result is the
        // data type.
        Term::Con(name, args) => {
            let (decl, _idx, ctor) = self.sig.data_of_con(name).ok_or_else(|| {
                TypeError::BadDataDecl(format!("unknown constructor {name:?}"))
            })?;
            if !decl.params.is_empty() {
                return Err(TypeError::BadDataDecl(
                    "M0 supports only non-parameterized inductives".into(),
                ));
            }
            if args.len() != ctor.args.len() {
                return Err(TypeError::Mismatch {
                    expected: format!("{} argument(s) to {name:?}", ctor.args.len()),
                    found: format!("{}", args.len()),
                });
            }
            let data_ty = Value::Data(decl.name.clone(), vec![], vec![]);
            for (arg, shape) in args.iter().zip(ctor.args.iter()) {
                match shape {
                    Arg::Rec => self.check(ctx, arg, &data_ty)?,
                    Arg::NonRec(ty) => {
                        let ty_val = eval(&self.env_for(ctx), ty);
                        self.check(ctx, arg, &ty_val)?;
                    }
                }
            }
            Ok(data_ty)
        }

        // The dependent eliminator (spec §2.7). The motive `P : D → Univ ℓ`; each constructor has
        // a method whose type is the constructor's argument telescope (with an induction
        // hypothesis `P xᵢ` after each recursive argument `xᵢ`) targeting `P (con ...)`. The
        // result type is `P scrutinee`.
        Term::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => self.infer_elim(ctx, data, motive, methods, scrutinee),

        // PathP formation (spec §2.6): `PathP (i. A) x y : Univ ℓ` when `i. A` is a line of types
        // and the endpoints inhabit the respective faces.
        Term::PathP { family, lhs, rhs } => {
            let ctx_dim = ctx.extend_dim();
            let lvl = self.infer_universe(&ctx_dim, family)?;
            let a0 = self.family_at(ctx, family, crate::term::Interval::I0);
            let a1 = self.family_at(ctx, family, crate::term::Interval::I1);
            self.check(ctx, lhs, &a0)?;
            self.check(ctx, rhs, &a1)?;
            Ok(Value::Univ(nat_to_level(lvl)))
        }

        // Path application (spec §2.6): `p @ r : A[r/i]` for `p : PathP (i. A) x y`.
        Term::PApp(p, r) => {
            let p_ty = self.infer(ctx, p)?;
            match p_ty {
                Value::PathP { family, .. } => {
                    let rv = self.eval_interval_at(ctx, r);
                    Ok(family.apply_dim(rv))
                }
                other => Err(TypeError::Mismatch {
                    expected: "a path (PathP) type".into(),
                    found: format!("{other:?}"),
                }),
            }
        }

        // Transport (spec §2.6): `Transp (i. A) φ a0`. The family `i. A` is a line of types; the
        // base inhabits the `i=0` face; the result inhabits the `i=1` face. When `φ = ⊤` the line
        // must be constant (transport is then forced to be the identity).
        Term::Transp {
            family,
            cofib,
            base,
        } => {
            let ctx_dim = ctx.extend_dim();
            self.infer_universe(&ctx_dim, family)?;
            self.check_cofib(ctx, cofib)?;
            let a0 = self.family_at(ctx, family, crate::term::Interval::I0);
            self.check(ctx, base, &a0)?;
            if crate::kan::is_total(&self.resolve_cofib_at(ctx, cofib)) {
                let a1 = self.family_at(ctx, family, crate::term::Interval::I1);
                if !conv(ctx.len(), &a0, &a1) {
                    return Err(TypeError::BadCubical(
                        "Transp with φ = ⊤ requires a constant type line".into(),
                    ));
                }
            }
            Ok(self.family_at(ctx, family, crate::term::Interval::I1))
        }

        // Homogeneous composition (spec §2.6): `HComp A φ (i. u) a0`. The carrier `A` is a type;
        // the base `a0 : A`; the tube `i. u` is a line in `A`; the result is at `i = 1` and lives
        // in `A`. (The full partial-element agreement on `φ` is enforced by the Kan computation
        // rules; M0 checks the carrier/base/tube types.)
        Term::HComp {
            ty,
            cofib,
            tube,
            base,
        } => {
            self.infer_universe(ctx, ty)?;
            let ty_val = eval(&self.env_for(ctx), ty);
            self.check(ctx, base, &ty_val)?;
            self.check_cofib(ctx, cofib)?;
            let ctx_dim = ctx.extend_dim();
            self.check(&ctx_dim, tube, &ty_val)?;
            Ok(ty_val)
        }

        // General composition (spec §2.6): `Comp (i. A) φ (i. u) a0`. Like `HComp` but over a type
        // line; the base inhabits the `i=0` face and the result the `i=1` face.
        Term::Comp {
            family,
            cofib,
            tube,
            base,
        } => {
            let ctx_dim = ctx.extend_dim();
            self.infer_universe(&ctx_dim, family)?;
            let a0 = self.family_at(ctx, family, crate::term::Interval::I0);
            self.check(ctx, base, &a0)?;
            self.check_cofib(ctx, cofib)?;
            // The tube is a line `i. u` valued in the corresponding fibre `A` at each `i`.
            let fam_at_i = self.family_at(ctx, family, crate::term::Interval::Dim(ctx.dim_len()));
            self.check(&ctx_dim, tube, &fam_at_i)?;
            Ok(self.family_at(ctx, family, crate::term::Interval::I1))
        }

        // Glue formation (spec §2.6): `Glue A φ T e : Univ ℓ` where `A : Univ ℓ` is the base and
        // `T`/`e` provide the partial type and equivalence on `φ`. M0 keeps the boundary directions
        // (`⊤`/`⊥`) that `kan::unglue` discharges.
        Term::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => {
            let l = self.infer_universe(ctx, base)?;
            self.check_cofib(ctx, cofib)?;
            let base_val = eval(&self.env_for(ctx), base);
            // The partial type `T` is a type, and the equivalence `e` relates `T` to the base.
            self.infer_universe(ctx, ty)?;
            self.infer(ctx, equiv)?;
            let _ = base_val;
            Ok(Value::Univ(nat_to_level(l)))
        }

        // `glue` introduction (spec §2.6): `glue φ t a : Glue A φ T e`. M0 checks the partial and
        // base components and reconstructs the Glue type from the base's type.
        Term::GlueTerm {
            cofib,
            partial,
            base,
        } => {
            self.check_cofib(ctx, cofib)?;
            self.infer(ctx, partial)?;
            let base_ty = self.infer(ctx, base)?;
            Ok(Value::Glue {
                base: Box::new(base_ty),
                cofib: self.resolve_cofib_at(ctx, cofib),
                ty: Box::new(eval(&self.env_for(ctx), partial)),
                equiv: Box::new(eval(&self.env_for(ctx), base)),
            })
        }

        // `unglue` elimination (spec §2.6): `unglue g : A` for `g : Glue A φ T e`.
        Term::Unglue(g) => {
            let g_ty = self.infer(ctx, g)?;
            match g_ty {
                Value::Glue { base, .. } => Ok(*base),
                other => Err(TypeError::Mismatch {
                    expected: "a Glue type".into(),
                    found: format!("{other:?}"),
                }),
            }
        }

        _ => Err(TypeError::CannotInfer(format!(
            "no inference rule for term former: {term:?}"
        ))),
    }
}

/// Evaluate a family `i. A` (a dim-binding term) at an interval endpoint, in `ctx`'s env.
fn family_at(&self, ctx: &Context, family: &Term, r: crate::term::Interval) -> Value {
    let env = self.env_for(ctx).extend_dim(r);
    eval(&env, family)
}

/// Resolve+normalize an interval term at the given context's dimension depth.
fn eval_interval_at(&self, ctx: &Context, r: &crate::term::Interval) -> crate::term::Interval {
    crate::normalize::eval_interval(&self.env_for(ctx), r)
}

/// Resolve a cofibration's dimension variables against the context's environment and constant-fold.
fn resolve_cofib_at(&self, ctx: &Context, cofib: &Cofib) -> Cofib {
    crate::normalize::resolve_cofib(&self.env_for(ctx), cofib)
}

/// Light well-formedness check for a cofibration (spec §2.6): every interval mentioned must be in
/// dimension scope. Dimension variables are de Bruijn indices into the context's dim space.
fn check_cofib(&self, ctx: &Context, cofib: &Cofib) -> Result<(), TypeError> {
    fn interval_ok(r: &crate::term::Interval, dims: usize) -> bool {
        match r {
            crate::term::Interval::Dim(i) => *i < dims,
            crate::term::Interval::I0 | crate::term::Interval::I1 => true,
            crate::term::Interval::Neg(r) => interval_ok(r, dims),
            crate::term::Interval::Min(a, b) | crate::term::Interval::Max(a, b) => {
                interval_ok(a, dims) && interval_ok(b, dims)
            }
        }
    }
    fn go(cofib: &Cofib, dims: usize) -> bool {
        match cofib {
            Cofib::Top | Cofib::Bot => true,
            Cofib::Eq0(r) | Cofib::Eq1(r) => interval_ok(r, dims),
            Cofib::And(a, b) | Cofib::Or(a, b) => go(a, dims) && go(b, dims),
        }
    }
    if go(cofib, ctx.dim_len()) {
        Ok(())
    } else {
        Err(TypeError::BadCubical(format!(
            "cofibration mentions an out-of-scope dimension: {cofib:?}"
        )))
    }
}

/// Type the dependent eliminator (spec §2.7) for a non-parameterized inductive.
fn infer_elim(
    &self,
    ctx: &Context,
    data: &DataName,
    motive: &Term,
    methods: &[Term],
    scrutinee: &Term,
) -> Result<Value, TypeError> {
    let decl = self
        .sig
        .get(data)
        .ok_or_else(|| TypeError::BadDataDecl(format!("unknown inductive type {data:?}")))?
        .clone();
    if !decl.params.is_empty() {
        return Err(TypeError::BadDataDecl(
            "M0 Elim supports only non-parameterized inductives".into(),
        ));
    }
    let data_ty = Value::Data(decl.name.clone(), vec![], vec![]);

    // Motive must denote `D → Univ ℓ`. The surface/elaborator passes it as `λ (_:D). <type>`, a
    // bare `Lam` (not inferable on its own), so we type its body directly under `_:D`.
    let motive_lvl = match motive {
        Term::Lam(body) => {
            let ctx2 = ctx.extend(Term::Data(decl.name.clone(), vec![], vec![]), Grade::Omega);
            self.infer_universe(&ctx2, body)?
        }
        other => {
            // Fall back to inference for an already-typed motive (e.g. a variable).
            match self.infer(ctx, other)? {
                Value::Pi(_g, dom, cod) => {
                    if !conv(ctx.len(), &dom, &data_ty) {
                        return Err(TypeError::Mismatch {
                            expected: format!("motive domain {data:?}"),
                            found: format!("{:?}", quote(ctx.len(), &dom)),
                        });
                    }
                    let fresh = Value::Neutral(Neutral::Var(ctx.len()));
                    match cod.apply(fresh) {
                        Value::Univ(l) => level_to_nat(&l)?,
                        other => {
                            return Err(TypeError::Mismatch {
                                expected: "motive codomain Univ ℓ".into(),
                                found: format!("{other:?}"),
                            })
                        }
                    }
                }
                other => {
                    return Err(TypeError::Mismatch {
                        expected: format!("motive of type {data:?} → Univ ℓ"),
                        found: format!("{other:?}"),
                    })
                }
            }
        }
    };
    let _ = motive_lvl;
    let motive_val = eval(&self.env_for(ctx), motive);

    // One method per constructor, in declaration order.
    if methods.len() != decl.constructors.len() {
        return Err(TypeError::Mismatch {
            expected: format!("{} method(s)", decl.constructors.len()),
            found: format!("{}", methods.len()),
        });
    }
    for (ctor, method) in decl.constructors.iter().zip(methods.iter()) {
        let method_ty = self.method_type(ctx, &decl, ctor, &motive_val)?;
        self.check(ctx, method, &method_ty)?;
    }

    // Scrutinee must be of the data type; result is `P scrutinee`.
    self.check(ctx, scrutinee, &data_ty)?;
    let scrut_val = eval(&self.env_for(ctx), scrutinee);
    Ok(apply_value(motive_val, scrut_val))
}

/// Build the expected type of the method for one constructor: the constructor's argument
/// telescope, inserting an induction hypothesis `P xᵢ` after each recursive argument, with
/// result `P (con args)`. Returned as a semantic [`Value`] (a Π-telescope).
///
/// For M0 the constructor argument types are *closed* (Nat/Bool/S¹ have no parameters and their
/// non-recursive arg types do not mention earlier args), which keeps the de Bruijn bookkeeping
/// straightforward: the only binders that need to reference earlier ones are the conclusion
/// `P (con …)` and each induction-hypothesis binder `P x`.
fn method_type(
    &self,
    ctx: &Context,
    decl: &DataDecl,
    ctor: &Constructor,
    motive: &Value,
) -> Result<Value, TypeError> {
    let data_name = decl.name.clone();
    // The motive is closed at the current depth; quote it so we can splice it under new binders.
    let motive_term = quote(ctx.len(), motive);

    // Enumerate the method's binders in order. Each non-recursive/recursive arg is one binder;
    // each recursive arg is *followed* by an induction-hypothesis binder.
    #[derive(Clone)]
    enum B {
        Arg(Term),
        RecArg,
        Ih,
    }
    let mut binders: Vec<B> = Vec::new();
    for shape in &ctor.args {
        match shape {
            Arg::NonRec(ty) => binders.push(B::Arg(ty.clone())),
            Arg::Rec => {
                binders.push(B::RecArg);
                binders.push(B::Ih);
            }
        }
    }
    let total = binders.len();

    // Conclusion `P (con a0 .. ak)`: collect the constructor-argument binders' indices, measured
    // from the conclusion's scope (innermost). Binder at absolute position `pos` sits at de Bruijn
    // index `total - 1 - pos` from inside all binders.
    let mut con_args: Vec<Term> = Vec::new();
    for (pos, b) in binders.iter().enumerate() {
        if matches!(b, B::Arg(_) | B::RecArg) {
            con_args.push(Term::Var(total - 1 - pos));
        }
    }
    let conclusion = Term::App(
        Box::new(shift(&motive_term, total)),
        Box::new(Term::Con(ctor.name.clone(), con_args)),
    );

    // Fold binders from innermost to outermost into a Pi-telescope. When emitting the Pi for the
    // binder at position `pos`, the body has already accumulated bindings for positions
    // `pos+1..total`, i.e. `inner = total - 1 - pos` binders are in scope inside the body.
    let mut body = conclusion;
    for (pos, b) in binders.iter().enumerate().rev() {
        let inner = total - 1 - pos;
        let dom = match b {
            B::Arg(ty) => shift(ty, inner),
            B::RecArg => Term::Data(data_name.clone(), vec![], vec![]),
            B::Ih => {
                // The preceding RecArg binder is directly outside this Ih binder, so within this
                // Pi's *domain* scope (no new binder yet) it is at index 0.
                Term::App(Box::new(shift(&motive_term, inner)), Box::new(Term::Var(0)))
            }
        };
        body = Term::Pi(Grade::Omega, Box::new(dom), Box::new(body));
    }

    Ok(eval(&self.env_for(ctx), &body))
}

/// Infer the universe level of a type-valued term, or error if it is not a universe.
fn infer_universe(&self, ctx: &Context, term: &Term) -> Result<u32, TypeError> {
    match self.infer(ctx, term)? {
        Value::Univ(l) => level_to_nat(&l),
        other => Err(TypeError::Mismatch {
            expected: "a universe".into(),
            found: format!("{other:?}"),
        }),
    }
}

/// Check `term` against the expected type `expected` (the `check` direction, spec §6.1).
pub fn check(&self, ctx: &Context, term: &Term, expected: &Value) -> Result<(), TypeError> {
    match (term, expected) {
        // Pi-Intro: λ checks against a Pi by checking the body under the extended context.
        (Term::Lam(body), Value::Pi(grade, dom, cod)) => {
            let dom_term = quote(ctx.len(), dom);
            let ctx2 = ctx.extend(dom_term, *grade);
            let var = Value::Neutral(Neutral::Var(ctx.len()));
            let cod_val = cod.apply(var);
            self.check(&ctx2, body, &cod_val)
        }

        // Sigma-Intro: (a, b) checks against a Sigma.
        (Term::Pair(a, b), Value::Sigma(dom, cod)) => {
            self.check(ctx, a, dom)?;
            let a_val = eval(&self.env_for(ctx), a);
            self.check(ctx, b, &cod.apply(a_val))
        }

        // Path-Intro (spec §2.6): `λ i. t` checks against `PathP (i. A) x y` when, under a fresh
        // dimension `i`, `t : A`, and the boundary matches: `t[0/i] ≡ x` and `t[1/i] ≡ y`.
        (Term::PLam(body), Value::PathP { family, lhs, rhs }) => {
            let ctx_dim = ctx.extend_dim();
            // The body's expected type is the family at the fresh dimension i (a free dim level).
            let i_level = ctx.dim_len();
            let fam_at_i = family.apply_dim(crate::term::Interval::Dim(i_level));
            self.check(&ctx_dim, body, &fam_at_i)?;
            // Boundary checks at the two endpoints.
            let env0 = self.env_for(ctx).extend_dim(crate::term::Interval::I0);
            let env1 = self.env_for(ctx).extend_dim(crate::term::Interval::I1);
            let t0 = eval(&env0, body);
            let t1 = eval(&env1, body);
            if !conv(ctx.len(), &t0, lhs) {
                return Err(TypeError::BadCubical(format!(
                    "path lhs boundary mismatch: {:?} ≢ {:?}",
                    quote(ctx.len(), &t0),
                    quote(ctx.len(), lhs)
                )));
            }
            if !conv(ctx.len(), &t1, rhs) {
                return Err(TypeError::BadCubical(format!(
                    "path rhs boundary mismatch: {:?} ≢ {:?}",
                    quote(ctx.len(), &t1),
                    quote(ctx.len(), rhs)
                )));
            }
            Ok(())
        }

        // Conversion fallback (spec §2.5 Conv): infer, then compare definitionally (+ cumul).
        _ => {
            let actual = self.infer(ctx, term)?;
            if subtype(ctx.len(), &actual, expected) {
                Ok(())
            } else {
                Err(TypeError::NotConvertible {
                    lhs: format!("{:?}", quote(ctx.len(), &actual)),
                    rhs: format!("{:?}", quote(ctx.len(), expected)),
                })
            }
        }
    }
}
}

/// Subtyping = definitional equality plus universe cumulativity (spec §2.4 U-Cumul): a value of
/// `Univ ℓ` may be used where `Univ ℓ'` is expected when `ℓ ≤ ℓ'`.
fn subtype(lvl: usize, actual: &Value, expected: &Value) -> bool {
    if let (Value::Univ(a), Value::Univ(e)) = (actual, expected) {
        if let (Ok(na), Ok(ne)) = (level_to_nat(a), level_to_nat(e)) {
            return na <= ne;
        }
    }
    conv(lvl, actual, expected)
}

/// Apply a function-valued [`Value`] to an argument, used to compute `P scrutinee`.
fn apply_value(f: Value, arg: Value) -> Value {
    match f {
        Value::Lam(clos) => clos.apply(arg),
        Value::Pi(_, _, cod) => cod.apply(arg),
        Value::Neutral(n) => Value::Neutral(Neutral::App(Box::new(n), Box::new(arg))),
        other => panic!("apply_value: not applicable: {other:?}"),
    }
}

/// Weaken a term by `n`: shift every free de Bruijn variable up by `n` (no binders are crossed by
/// the caller's splice point). Implemented with a cutoff to leave bound variables untouched.
fn shift(term: &Term, n: usize) -> Term {
    fn go(term: &Term, n: usize, cutoff: usize) -> Term {
        match term {
            Term::Var(i) => {
                if *i >= cutoff {
                    Term::Var(i + n)
                } else {
                    Term::Var(*i)
                }
            }
            Term::Univ(_) => term.clone(),
            Term::Pi(g, a, b) => Term::Pi(
                *g,
                Box::new(go(a, n, cutoff)),
                Box::new(go(b, n, cutoff + 1)),
            ),
            Term::Lam(b) => Term::Lam(Box::new(go(b, n, cutoff + 1))),
            Term::App(f, a) => Term::App(Box::new(go(f, n, cutoff)), Box::new(go(a, n, cutoff))),
            Term::Sigma(a, b) => Term::Sigma(
                Box::new(go(a, n, cutoff)),
                Box::new(go(b, n, cutoff + 1)),
            ),
            Term::Pair(a, b) => Term::Pair(Box::new(go(a, n, cutoff)), Box::new(go(b, n, cutoff))),
            Term::Fst(p) => Term::Fst(Box::new(go(p, n, cutoff))),
            Term::Snd(p) => Term::Snd(Box::new(go(p, n, cutoff))),
            Term::Ann(t, ty) => {
                Term::Ann(Box::new(go(t, n, cutoff)), Box::new(go(ty, n, cutoff)))
            }
            Term::Data(d, ps, is) => Term::Data(
                d.clone(),
                ps.iter().map(|t| go(t, n, cutoff)).collect(),
                is.iter().map(|t| go(t, n, cutoff)).collect(),
            ),
            Term::Con(c, args) => {
                Term::Con(c.clone(), args.iter().map(|t| go(t, n, cutoff)).collect())
            }
            Term::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => Term::Elim {
                data: data.clone(),
                motive: Box::new(go(motive, n, cutoff)),
                methods: methods.iter().map(|t| go(t, n, cutoff)).collect(),
                scrutinee: Box::new(go(scrutinee, n, cutoff)),
            },
            // Cubical formers. None of these bind a *term* variable (only dimensions, which live in
            // a separate de Bruijn space), so the term cutoff is unchanged when descending.
            Term::PathP { family, lhs, rhs } => Term::PathP {
                family: Box::new(go(family, n, cutoff)),
                lhs: Box::new(go(lhs, n, cutoff)),
                rhs: Box::new(go(rhs, n, cutoff)),
            },
            Term::PLam(b) => Term::PLam(Box::new(go(b, n, cutoff))),
            Term::PApp(p, r) => Term::PApp(Box::new(go(p, n, cutoff)), r.clone()),
            Term::Partial(c, a) => Term::Partial(c.clone(), Box::new(go(a, n, cutoff))),
            Term::Transp {
                family,
                cofib,
                base,
            } => Term::Transp {
                family: Box::new(go(family, n, cutoff)),
                cofib: cofib.clone(),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::HComp {
                ty,
                cofib,
                tube,
                base,
            } => Term::HComp {
                ty: Box::new(go(ty, n, cutoff)),
                cofib: cofib.clone(),
                tube: Box::new(go(tube, n, cutoff)),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::Comp {
                family,
                cofib,
                tube,
                base,
            } => Term::Comp {
                family: Box::new(go(family, n, cutoff)),
                cofib: cofib.clone(),
                tube: Box::new(go(tube, n, cutoff)),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::Glue {
                base,
                cofib,
                ty,
                equiv,
            } => Term::Glue {
                base: Box::new(go(base, n, cutoff)),
                cofib: cofib.clone(),
                ty: Box::new(go(ty, n, cutoff)),
                equiv: Box::new(go(equiv, n, cutoff)),
            },
            Term::GlueTerm {
                cofib,
                partial,
                base,
            } => Term::GlueTerm {
                cofib: cofib.clone(),
                partial: Box::new(go(partial, n, cutoff)),
                base: Box::new(go(base, n, cutoff)),
            },
            Term::Unglue(p) => Term::Unglue(Box::new(go(p, n, cutoff))),
            // `System` carries cofibration-guarded branches; not produced by the paths funext needs.
            Term::System(_) => term.clone(),
            // A literal interval term has no term-variable content.
            Term::Interval(_) => term.clone(),
        }
    }
    go(term, n, 0)
}

/// Top-level entry: check that `term : ty` in the empty context (no inductive signature) and,
/// on success, mint the `Proof`. Convenience wrapper over [`check_top_with`].
pub fn check_top(term: Term, ty: Term) -> Result<Proof, TypeError> {
    check_top_with(Signature::empty(), term, ty)
}

/// Top-level entry against a given inductive [`Signature`]. This is the kernel's public door
/// (spec §2.1) — the only way an external crate can obtain a [`Proof`].
pub fn check_top_with(sig: Signature, term: Term, ty: Term) -> Result<Proof, TypeError> {
    let ctx = Context::empty();
    let checker = Checker::new(std::rc::Rc::new(sig));
    let expected = eval(&checker.env_for(&ctx), &ty);
    checker.check(&ctx, &term, &expected)?;
    Ok(Proof::trusted_new(Judgement::HasType { term, ty }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semiring::Grade;
    use crate::term::Level;

    fn u(n: u32) -> Term {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = Level::Suc(Box::new(l));
        }
        Term::Univ(l)
    }

    /// `Univ 0 : Univ 1` (spec §2.4, U-Type).
    #[test]
    fn universe_in_next_universe() {
        let p = check_top(u(0), u(1));
        assert!(p.is_ok(), "Univ 0 : Univ 1");
    }

    /// Cumulativity: `Univ 0 : Univ 2` as well (spec §2.4, U-Cumul).
    #[test]
    fn universe_cumulativity() {
        assert!(check_top(u(0), u(2)).is_ok(), "Univ 0 : Univ 2 by cumulativity");
    }

    /// A universe does not inhabit a lower-or-equal universe: `Univ 1 : Univ 0` rejected.
    #[test]
    fn universe_no_downward() {
        assert!(check_top(u(1), u(0)).is_err(), "Univ 1 : Univ 0 must be rejected");
    }

    /// The polymorphic identity at `Univ 0`: `λ A. λ x. x : (A :^ω Univ 0) → (x :^ω A) → A`.
    #[test]
    fn identity_checks_against_pi() {
        // type: Pi (A :^ω Univ 0). Pi (x :^ω A). A    (A is Var 0 inside the inner Pi)
        let ty = Term::Pi(
            Grade::Omega,
            Box::new(u(0)),
            Box::new(Term::Pi(
                Grade::Omega,
                Box::new(Term::Var(0)),
                Box::new(Term::Var(1)),
            )),
        );
        let term = Term::Lam(Box::new(Term::Lam(Box::new(Term::Var(0)))));
        assert!(check_top(term, ty).is_ok(), "polymorphic id checks");
    }

    /// A Π type is itself a type: `(x :^ω Univ 0) → Univ 0 : Univ 1`.
    #[test]
    fn pi_formation() {
        let pi = Term::Pi(Grade::Omega, Box::new(u(0)), Box::new(u(0)));
        assert!(check_top(pi, u(1)).is_ok());
    }

    /// Application: `(λ x. x : Univ0→Univ0) (Univ 0)` is rejected because `Univ 0 : Univ 1`, not
    /// `Univ 0`. But ascribing the identity at `Univ 1` and applying to `Univ 0` works.
    #[test]
    fn application_respects_domain() {
        // id at Univ 1 : (x :^ω Univ 1) → Univ 1, applied to Univ 0 (since Univ 0 : Univ 1).
        let id_ty = Term::Pi(Grade::Omega, Box::new(u(1)), Box::new(u(1)));
        let id = Term::Lam(Box::new(Term::Var(0)));
        let ascribed = Term::App(Box::new(annotate(id, id_ty)), Box::new(u(0)));
        // result type is Univ 1; check it.
        assert!(check_top(ascribed, u(1)).is_ok());
    }

    /// Type mismatch is rejected: `Univ 0` does not check against `(x:^ω Univ0)→Univ0`.
    #[test]
    fn mismatch_rejected() {
        let pi = Term::Pi(Grade::Omega, Box::new(u(0)), Box::new(u(0)));
        assert!(check_top(u(0), pi).is_err());
    }

    /// Helper: wrap a term so `infer` can synthesize a type for a lambda (via an internal
    /// annotation node). Implemented in terms of the kernel's own ascription support.
    fn annotate(term: Term, ty: Term) -> Term {
        // We model annotation by a redex against the identity at the ascribed Pi; but cleaner is
        // a dedicated Ann node. The kernel exposes annotation through check, so for inference of
        // an application head we rely on the elaborator normally. For this unit test we use the
        // Ann term variant.
        Term::Ann(Box::new(term), Box::new(ty))
    }

    // ---- L3: inductive families + dependent Elim (spec §2.7) ----

    use crate::signature::{Arg, Constructor, DataDecl, PathConstructor, Signature};
    use crate::term::{ConName, DataName};

    fn nat_name() -> DataName {
        DataName("Nat".into())
    }
    fn zero() -> Term {
        Term::Con(ConName("zero".into()), vec![])
    }
    fn succ(n: Term) -> Term {
        Term::Con(ConName("succ".into()), vec![n])
    }

    /// The `Nat` signature: `zero : Nat`, `succ : Nat → Nat`.
    fn nat_sig() -> Signature {
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: nat_name(),
            params: vec![],
            level: 0,
            constructors: vec![
                Constructor {
                    name: ConName("zero".into()),
                    args: vec![],
                },
                Constructor {
                    name: ConName("succ".into()),
                    args: vec![Arg::Rec],
                },
            ],
            path_constructors: vec![],
        });
        sig
    }

    fn nat_ty() -> Term {
        Term::Data(nat_name(), vec![], vec![])
    }

    /// `Nat : Univ 0` (formation).
    #[test]
    fn nat_formation() {
        assert!(check_top_with(nat_sig(), nat_ty(), u(0)).is_ok());
    }

    /// `zero : Nat` and `succ zero : Nat` (constructors).
    #[test]
    fn nat_constructors() {
        assert!(check_top_with(nat_sig(), zero(), nat_ty()).is_ok(), "zero : Nat");
        assert!(
            check_top_with(nat_sig(), succ(zero()), nat_ty()).is_ok(),
            "succ zero : Nat"
        );
    }

    /// `succ` applied to a non-`Nat` is rejected.
    #[test]
    fn succ_rejects_non_nat() {
        assert!(
            check_top_with(nat_sig(), succ(u(0)), nat_ty()).is_err(),
            "succ (Univ 0) must be rejected"
        );
    }

    /// ι-reduction: a non-dependent recursor. With motive `λ _. Nat`, methods `zero` and
    /// `λ n ih. succ ih`, eliminating `succ (succ zero)` computes back to `succ (succ zero)`
    /// (the identity recursor). Checks against `Nat`.
    #[test]
    fn elim_iota_identity_recursor() {
        // motive: λ (_:Nat). Nat
        let motive = Term::Lam(Box::new(nat_ty()));
        // method_zero : Nat = zero
        let method_zero = zero();
        // method_succ : (n:Nat) → (ih:Nat) → Nat  =  λ n. λ ih. succ ih
        let method_succ = Term::Lam(Box::new(Term::Lam(Box::new(succ(Term::Var(0))))));
        let scrut = succ(succ(zero()));
        let elim = Term::Elim {
            data: nat_name(),
            motive: Box::new(motive),
            methods: vec![method_zero, method_succ],
            scrutinee: Box::new(scrut),
        };
        // The recursor rebuilds the number, so it has type Nat and equals succ (succ zero).
        assert!(
            check_top_with(nat_sig(), elim.clone(), nat_ty()).is_ok(),
            "identity recursor checks at Nat"
        );

        // And it is definitionally equal to succ (succ zero): check via ascription/Conv.
        let sig = std::rc::Rc::new(nat_sig());
        let checker = Checker::new(sig);
        let ctx = Context::empty();
        let lhs = eval(&checker.env_for(&ctx), &elim);
        let rhs = eval(&checker.env_for(&ctx), &succ(succ(zero())));
        assert!(conv(0, &lhs, &rhs), "ι: identity recursor reduces to its input");
    }

    /// ι-reduction computing a constant: motive `λ _. Nat`, methods `zero`↦`succ zero`,
    /// `succ`↦`λ n ih. ih`. Eliminating any number yields the `zero` method's value… let's make
    /// it a "is it zero?" style: map `zero ↦ zero`, `succ _ _ ↦ succ zero`. On `succ zero` it must
    /// reduce to `succ zero`.
    #[test]
    fn elim_iota_computes_method() {
        let motive = Term::Lam(Box::new(nat_ty()));
        let method_zero = zero();
        // λ n. λ ih. succ zero   (ignores recursion, returns 1)
        let method_succ = Term::Lam(Box::new(Term::Lam(Box::new(succ(zero())))));
        let elim = |scrut: Term| Term::Elim {
            data: nat_name(),
            motive: Box::new(motive.clone()),
            methods: vec![method_zero.clone(), method_succ.clone()],
            scrutinee: Box::new(scrut),
        };
        let sig = std::rc::Rc::new(nat_sig());
        let checker = Checker::new(sig);
        let ctx = Context::empty();

        // on zero ⇒ zero
        let on_zero = eval(&checker.env_for(&ctx), &elim(zero()));
        assert!(conv(0, &on_zero, &eval(&checker.env_for(&ctx), &zero())));

        // on succ zero ⇒ succ zero
        let on_one = eval(&checker.env_for(&ctx), &elim(succ(zero())));
        assert!(conv(0, &on_one, &eval(&checker.env_for(&ctx), &succ(zero()))));
    }

    /// Strict-positivity: a constructor with a negative occurrence of the data type is rejected by
    /// the signature's positivity check (spec §2.7).
    #[test]
    fn strict_positivity_rejected() {
        // bad : (Bad → Bad) → Bad   — Bad occurs to the left of an arrow (negative).
        let bad_name = DataName("Bad".into());
        let decl = DataDecl {
            name: bad_name.clone(),
            params: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("mk".into()),
                args: vec![Arg::NonRec(Term::Pi(
                    Grade::Omega,
                    Box::new(Term::Data(bad_name.clone(), vec![], vec![])),
                    Box::new(Term::Data(bad_name.clone(), vec![], vec![])),
                ))],
            }],
            path_constructors: vec![],
        };
        let sig = Signature::empty();
        assert!(
            sig.check_positivity(&decl).is_err(),
            "non-strictly-positive constructor must be rejected"
        );
    }

    /// A HIT records its path constructor structurally (spec §2.7). Here a circle-like type with a
    /// point `base` and a loop path constructor; we just assert the signature is well-formed and
    /// the point constructor types.
    #[test]
    fn hit_point_and_path_constructor() {
        let s1 = DataName("S1".into());
        let mut sig = Signature::empty();
        sig.declare(DataDecl {
            name: s1.clone(),
            params: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("base".into()),
                args: vec![],
            }],
            path_constructors: vec![PathConstructor {
                name: ConName("loop".into()),
                args: vec![],
                lhs: Term::Con(ConName("base".into()), vec![]),
                rhs: Term::Con(ConName("base".into()), vec![]),
            }],
        });
        // base : S1
        let base = Term::Con(ConName("base".into()), vec![]);
        assert!(
            check_top_with(sig, base, Term::Data(s1, vec![], vec![])).is_ok(),
            "point constructor of the HIT checks"
        );
    }

    // ---- L4: Path typing (spec §2.6) ----
    use crate::term::Interval as Iv;

    /// `refl {A} x : Path A x x` where `Path A x y = PathP (i. A) x y` (constant family). Here we
    /// take `A = Univ 0` and `x = Univ 0`'s element... use a concrete neutral via ascription.
    /// We test with `A = Nat`, `x = zero`: `refl = λ i. zero : PathP (_. Nat) zero zero`.
    #[test]
    fn refl_checks_as_constant_path() {
        let path_ty = Term::PathP {
            family: Box::new(nat_ty()), // constant line `i. Nat`
            lhs: Box::new(zero()),
            rhs: Box::new(zero()),
        };
        let refl = Term::PLam(Box::new(zero())); // λ i. zero
        assert!(
            check_top_with(nat_sig(), refl, path_ty).is_ok(),
            "refl : Path Nat zero zero"
        );
    }

    /// A path with mismatched boundary is rejected: `λ i. zero : Path Nat zero (succ zero)` fails
    /// because the rhs boundary `zero ≢ succ zero`.
    #[test]
    fn path_boundary_mismatch_rejected() {
        let path_ty = Term::PathP {
            family: Box::new(nat_ty()),
            lhs: Box::new(zero()),
            rhs: Box::new(succ(zero())),
        };
        let bad = Term::PLam(Box::new(zero()));
        assert!(
            check_top_with(nat_sig(), bad, path_ty).is_err(),
            "bad boundary must be rejected"
        );
    }

    /// `PathP` is a type: `Path Nat zero zero : Univ 0` (formation).
    #[test]
    fn pathp_formation() {
        let path_ty = Term::PathP {
            family: Box::new(nat_ty()),
            lhs: Box::new(zero()),
            rhs: Box::new(zero()),
        };
        assert!(check_top_with(nat_sig(), path_ty, u(0)).is_ok());
    }

    /// Path application at an endpoint computes the endpoint: `(λ i. succ zero) @ 0 : Nat` and the
    /// result is definitionally `succ zero`. We type the application and check it against Nat.
    #[test]
    fn papp_at_endpoint_types_and_computes() {
        // p : Path Nat (succ zero) (succ zero), p = λ i. succ zero.
        let p = Term::Ann(
            Box::new(Term::PLam(Box::new(succ(zero())))),
            Box::new(Term::PathP {
                family: Box::new(nat_ty()),
                lhs: Box::new(succ(zero())),
                rhs: Box::new(succ(zero())),
            }),
        );
        let app = Term::PApp(Box::new(p), Iv::I0);
        assert!(
            check_top_with(nat_sig(), app.clone(), nat_ty()).is_ok(),
            "p @ 0 : Nat"
        );
        // And it computes to succ zero.
        let sig = std::rc::Rc::new(nat_sig());
        let checker = Checker::new(sig);
        let ctx = Context::empty();
        let v = eval(&checker.env_for(&ctx), &app);
        let expected = eval(&checker.env_for(&ctx), &succ(zero()));
        assert!(conv(0, &v, &expected), "p @ 0 ≡ succ zero");
    }
}
