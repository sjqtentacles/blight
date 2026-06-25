//! Normalization by evaluation (spec §2.5/§2.8): the engine behind `Conv`.
//!
//! Includes β, η (Π and Σ), ι (eliminators on constructors), the De Morgan interval theory,
//! the path boundary rules, and the per-type-former Kan computation rules (delegated to
//! [`crate::kan`]).

use crate::term::{DataName, Interval, Term};
use crate::value::{Closure, Env, Neutral, Value};

/// Evaluate a term in an environment to a semantic value (the "eval" half of NbE).
pub fn eval(env: &Env, term: &Term) -> Value {
    match term {
        Term::Var(i) => env
            .lookup(*i)
            .cloned()
            .unwrap_or_else(|| panic!("eval: unbound de Bruijn index {i}")),
        Term::Univ(l) => Value::Univ(l.clone()),
        Term::Pi(grade, dom, cod) => Value::Pi(
            *grade,
            Box::new(eval(env, dom)),
            Closure {
                env: env.clone(),
                body: (**cod).clone(),
            },
        ),
        Term::Lam(body) => Value::Lam(Closure {
            env: env.clone(),
            body: (**body).clone(),
        }),
        Term::App(f, a) => {
            let vf = eval(env, f);
            let va = eval(env, a);
            apply(vf, va)
        }
        Term::Sigma(dom, cod) => Value::Sigma(
            Box::new(eval(env, dom)),
            Closure {
                env: env.clone(),
                body: (**cod).clone(),
            },
        ),
        Term::Pair(a, b) => Value::Pair(Box::new(eval(env, a)), Box::new(eval(env, b))),
        Term::Fst(p) => vfst(eval(env, p)),
        Term::Snd(p) => vsnd(eval(env, p)),
        // Ascription is transparent at runtime: evaluate the underlying term.
        Term::Ann(t, _ty) => eval(env, t),

        // ---- data / recursion (spec §2.7) ----
        Term::Data(name, params, indices) => Value::Data(
            name.clone(),
            params.iter().map(|t| eval(env, t)).collect(),
            indices.iter().map(|t| eval(env, t)).collect(),
        ),
        Term::Con(name, args) => {
            Value::Con(name.clone(), args.iter().map(|t| eval(env, t)).collect())
        }
        Term::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => {
            let motive_v = eval(env, motive);
            let method_vs: Vec<Value> = methods.iter().map(|t| eval(env, t)).collect();
            let scrut_v = eval(env, scrutinee);
            do_elim(env, data, motive_v, method_vs, scrut_v)
        }

        // ---- cubical path layer (spec §2.6) ----
        Term::PathP { family, lhs, rhs } => Value::PathP {
            family: Closure {
                env: env.clone(),
                body: (**family).clone(),
            },
            lhs: Box::new(eval(env, lhs)),
            rhs: Box::new(eval(env, rhs)),
        },
        Term::PLam(body) => Value::PLam(Closure {
            env: env.clone(),
            body: (**body).clone(),
        }),
        Term::PApp(p, r) => {
            let vp = eval(env, p);
            let vr = eval_interval(env, r);
            papp(vp, vr)
        }

        // ---- cubical Kan operations (spec §2.6); delegated to crate::kan ----
        Term::Transp {
            family,
            cofib,
            base,
        } => {
            let fam = Closure {
                env: env.clone(),
                body: (**family).clone(),
            };
            let cof = resolve_cofib(env, cofib);
            let b = eval(env, base);
            crate::kan::transp(&fam, &cof, &b)
        }
        Term::HComp {
            ty,
            cofib,
            tube,
            base,
        } => {
            let t = eval(env, ty);
            let cof = resolve_cofib(env, cofib);
            let tube_clos = Closure {
                env: env.clone(),
                body: (**tube).clone(),
            };
            let b = eval(env, base);
            crate::kan::hcomp(&t, &cof, &tube_clos, &b)
        }
        Term::Comp {
            family,
            cofib,
            tube,
            base,
        } => {
            let fam = Closure {
                env: env.clone(),
                body: (**family).clone(),
            };
            let cof = resolve_cofib(env, cofib);
            let tube_clos = Closure {
                env: env.clone(),
                body: (**tube).clone(),
            };
            let b = eval(env, base);
            crate::kan::comp(&fam, &cof, &tube_clos, &b)
        }
        Term::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => Value::Glue {
            base: Box::new(eval(env, base)),
            cofib: resolve_cofib(env, cofib),
            ty: Box::new(eval(env, ty)),
            equiv: Box::new(eval(env, equiv)),
        },
        Term::Unglue(g) => crate::kan::unglue(&eval(env, g)),

        // `Interval`/`Partial`/`System`/`GlueTerm` only appear in dimension/partial position and
        // are handled by their enclosing former; a bare occurrence is a malformed term.
        _ => todo!("eval: term former not valid in value position (Interval/Partial/System)"),
    }
}

/// Resolve dimension variables inside a cofibration against the environment, then constant-fold
/// the resulting `r = 0` / `r = 1` faces where the interval became a constant.
pub fn resolve_cofib(env: &Env, cofib: &crate::term::Cofib) -> crate::term::Cofib {
    use crate::term::Cofib;
    match cofib {
        Cofib::Top => Cofib::Top,
        Cofib::Bot => Cofib::Bot,
        Cofib::Eq0(r) => match eval_interval(env, r) {
            Interval::I0 => Cofib::Top,
            Interval::I1 => Cofib::Bot,
            other => Cofib::Eq0(other),
        },
        Cofib::Eq1(r) => match eval_interval(env, r) {
            Interval::I1 => Cofib::Top,
            Interval::I0 => Cofib::Bot,
            other => Cofib::Eq1(other),
        },
        Cofib::And(a, b) => Cofib::And(
            Box::new(resolve_cofib(env, a)),
            Box::new(resolve_cofib(env, b)),
        ),
        Cofib::Or(a, b) => Cofib::Or(
            Box::new(resolve_cofib(env, a)),
            Box::new(resolve_cofib(env, b)),
        ),
    }
}

/// Apply a (possibly neutral) function value to an argument.
pub fn apply(f: Value, arg: Value) -> Value {
    match f {
        Value::Lam(clos) => clos.apply(arg),
        // A reflected path-valued function: reflect the applied spine at the instantiated codomain.
        Value::ReflectedFun { neutral, cod, .. } => {
            let result_ty = cod.apply(arg.clone());
            reflect(Neutral::App(Box::new(neutral), Box::new(arg)), &result_ty)
        }
        Value::Neutral(n) => Value::Neutral(Neutral::App(Box::new(n), Box::new(arg))),
        other => panic!("apply: not a function: {other:?}"),
    }
}

/// Reflect a neutral spine against its type (the NbE *reflection*/η-expansion). This is what lets
/// the kernel see that an applied neutral of `PathP` type has computable boundaries:
///
/// - a neutral of `PathP` type becomes a [`Value::ReflectedPath`] carrying its endpoints, so
///   `@0`/`@1` reduce;
/// - a neutral of `Pi` type becomes a [`Value::ReflectedFun`] that reflects each applied spine at
///   the instantiated codomain (so a path-valued function carries endpoints through application);
/// - a neutral of `Sigma` type is reflected component-wise on its projections;
/// - anything else stays a bare neutral.
pub fn reflect(neutral: Neutral, ty: &Value) -> Value {
    match ty {
        Value::PathP { lhs, rhs, .. } => Value::ReflectedPath {
            neutral,
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        },
        Value::Pi(_grade, dom, cod) => Value::ReflectedFun {
            neutral,
            dom: dom.clone(),
            cod: cod.clone(),
        },
        Value::Sigma(dom, cod) => {
            // η for pairs: reflect the first projection against `dom`, the second against `cod`
            // instantiated at the (reflected) first projection.
            let fst = reflect(Neutral::Fst(Box::new(neutral.clone())), dom);
            let snd_ty = cod.apply(fst.clone());
            let snd = reflect(Neutral::Snd(Box::new(neutral)), &snd_ty);
            Value::Pair(Box::new(fst), Box::new(snd))
        }
        _ => Value::Neutral(neutral),
    }
}

/// Apply a path value at an interval (`p @ r`). β for paths: `(λ i. t) @ r → t[r/i]`. On a
/// neutral path it builds a stuck `PApp` neutral; the endpoint boundary rules `p @ 0 = lhs`,
/// `p @ 1 = rhs` are realized by the typed layer (the path's type carries the endpoints).
fn papp(p: Value, r: Interval) -> Value {
    match p {
        Value::PLam(clos) => clos.apply_dim(r),
        Value::ReflectedPath { neutral, lhs, rhs } => match r {
            Interval::I0 => *lhs,
            Interval::I1 => *rhs,
            other => Value::Neutral(Neutral::PApp(Box::new(neutral), other)),
        },
        Value::Neutral(n) => Value::Neutral(Neutral::PApp(Box::new(n), r)),
        other => panic!("papp: not a path: {other:?}"),
    }
}

/// First projection on a (possibly neutral) pair value.
pub fn vfst(p: Value) -> Value {
    match p {
        Value::Pair(a, _) => *a,
        Value::Neutral(n) => Value::Neutral(Neutral::Fst(Box::new(n))),
        other => panic!("fst: not a pair: {other:?}"),
    }
}

/// Second projection on a (possibly neutral) pair value.
pub fn vsnd(p: Value) -> Value {
    match p {
        Value::Pair(_, b) => *b,
        Value::Neutral(n) => Value::Neutral(Neutral::Snd(Box::new(n))),
        other => panic!("snd: not a pair: {other:?}"),
    }
}

impl Closure {
    /// Apply the closure to an argument value, evaluating the body in the extended environment.
    pub fn apply(&self, arg: Value) -> Value {
        eval(&self.env.extend(arg), &self.body)
    }

    /// Apply a dimension-binding closure (a path family or a `PLam` body) at an interval.
    pub fn apply_dim(&self, dim: Interval) -> Value {
        eval(&self.env.extend_dim(dim), &self.body)
    }
}

/// Evaluate an interval term to a (resolved, normalized) interval, looking up dimension variables
/// in the environment's dimension stack and applying the De Morgan simplifier.
pub fn eval_interval(env: &Env, r: &Interval) -> Interval {
    let resolved = resolve_interval(env, r);
    normalize_interval(&resolved)
}

/// Substitute environment dimension bindings into an interval term.
fn resolve_interval(env: &Env, r: &Interval) -> Interval {
    match r {
        Interval::I0 => Interval::I0,
        Interval::I1 => Interval::I1,
        Interval::Dim(i) => env
            .lookup_dim(*i)
            .cloned()
            .unwrap_or_else(|| Interval::Dim(*i)),
        Interval::Min(a, b) => Interval::Min(
            Box::new(resolve_interval(env, a)),
            Box::new(resolve_interval(env, b)),
        ),
        Interval::Max(a, b) => Interval::Max(
            Box::new(resolve_interval(env, a)),
            Box::new(resolve_interval(env, b)),
        ),
        Interval::Neg(a) => Interval::Neg(Box::new(resolve_interval(env, a))),
    }
}

/// Run the dependent eliminator (spec §2.7). On a constructor `Con c args`, perform ι-reduction:
/// select the method for `c` and apply it to the constructor's arguments, inserting an induction
/// hypothesis (a recursive `Elim` over the same motive/methods) immediately after each recursive
/// argument. On a neutral scrutinee, build a stuck neutral `Elim`.
fn do_elim(
    env: &Env,
    data: &DataName,
    motive: Value,
    methods: Vec<Value>,
    scrut: Value,
) -> Value {
    match scrut {
        Value::Con(con, args) => {
            // Find the constructor's index and its argument shape from the signature.
            let sig = env
                .sig()
                .unwrap_or_else(|| panic!("do_elim: no signature in scope for {data:?}"));
            let decl = sig
                .get(data)
                .unwrap_or_else(|| panic!("do_elim: unknown data type {data:?}"));
            let (idx, ctor) = decl
                .constructor(&con)
                .unwrap_or_else(|| panic!("do_elim: {con:?} is not a constructor of {data:?}"));
            let method = methods
                .get(idx)
                .cloned()
                .unwrap_or_else(|| panic!("do_elim: missing method for constructor index {idx}"));

            // Apply the method to each argument; after each recursive argument, also apply the
            // induction hypothesis = Elim over that sub-term.
            let mut result = method;
            for (arg, arg_shape) in args.iter().zip(ctor.args.iter()) {
                result = apply(result, arg.clone());
                if matches!(arg_shape, crate::signature::Arg::Rec) {
                    let ih = do_elim(
                        env,
                        data,
                        motive.clone(),
                        methods.clone(),
                        arg.clone(),
                    );
                    result = apply(result, ih);
                }
            }
            result
        }
        Value::Neutral(n) => Value::Neutral(Neutral::Elim {
            data: data.clone(),
            motive: Box::new(motive),
            methods,
            scrutinee: Box::new(n),
        }),
        // A reflected path is, underneath, a neutral; eliminating it is stuck on that neutral.
        Value::ReflectedPath { neutral, .. } => Value::Neutral(Neutral::Elim {
            data: data.clone(),
            motive: Box::new(motive),
            methods,
            scrutinee: Box::new(neutral),
        }),
        other => panic!("do_elim: scrutinee is neither a constructor nor neutral: {other:?}"),
    }
}

/// Read a value back to a normal-form term at the given context depth `lvl` (the "quote" half).
///
/// `lvl` is the number of term binders in scope. Neutral variables are stored as de Bruijn
/// *levels*; quoting converts a level `k` back to the index `lvl - k - 1`. Dimension binders are
/// tracked separately by `dlvl` inside [`quote_at`].
pub fn quote(lvl: usize, value: &Value) -> Term {
    quote_at(lvl, 0, value)
}

/// Quote with explicit term-level `lvl` and dimension-level `dlvl` (public for the Kan table, which
/// builds synthetic type lines by quoting a family's value under a fresh dimension).
pub fn quote_value_at(lvl: usize, dlvl: usize, value: &Value) -> Term {
    quote_at(lvl, dlvl, value)
}

/// Quote with explicit term-level `lvl` and dimension-level `dlvl`.
fn quote_at(lvl: usize, dlvl: usize, value: &Value) -> Term {
    match value {
        Value::Neutral(n) => quote_neutral(lvl, dlvl, n),
        Value::Univ(l) => Term::Univ(l.clone()),
        Value::Pi(grade, dom, cod) => Term::Pi(
            *grade,
            Box::new(quote_at(lvl, dlvl, dom)),
            Box::new(quote_closure(lvl, dlvl, cod)),
        ),
        Value::Lam(clos) => Term::Lam(Box::new(quote_closure(lvl, dlvl, clos))),
        Value::Sigma(dom, cod) => Term::Sigma(
            Box::new(quote_at(lvl, dlvl, dom)),
            Box::new(quote_closure(lvl, dlvl, cod)),
        ),
        Value::Pair(a, b) => Term::Pair(
            Box::new(quote_at(lvl, dlvl, a)),
            Box::new(quote_at(lvl, dlvl, b)),
        ),
        Value::Data(name, params, indices) => Term::Data(
            name.clone(),
            params.iter().map(|v| quote_at(lvl, dlvl, v)).collect(),
            indices.iter().map(|v| quote_at(lvl, dlvl, v)).collect(),
        ),
        Value::Con(name, args) => Term::Con(
            name.clone(),
            args.iter().map(|v| quote_at(lvl, dlvl, v)).collect(),
        ),
        Value::PathP { family, lhs, rhs } => Term::PathP {
            family: Box::new(quote_dim_closure(lvl, dlvl, family)),
            lhs: Box::new(quote_at(lvl, dlvl, lhs)),
            rhs: Box::new(quote_at(lvl, dlvl, rhs)),
        },
        Value::PLam(clos) => Term::PLam(Box::new(quote_dim_closure(lvl, dlvl, clos))),
        Value::ReflectedPath { neutral, .. } => {
            // η-expand: a reflected path quotes to `λ i. p @ i`, where `p` is the underlying neutral.
            // The neutral lives outside the freshly-introduced dimension binder, so it is quoted at
            // the current `dlvl`; the bound `i` is dimension index 0.
            Term::PLam(Box::new(Term::PApp(
                Box::new(quote_neutral(lvl, dlvl, neutral)),
                Interval::Dim(0),
            )))
        }
        Value::ReflectedFun { neutral, cod, .. } => {
            // η-expand: a reflected function quotes to `λ x. (n x)` with the body reflected at the
            // codomain, then quoted under the fresh binder.
            let arg = Value::Neutral(Neutral::Var(lvl));
            let result_ty = cod.apply(arg.clone());
            let body = reflect(Neutral::App(Box::new(neutral.clone()), Box::new(arg)), &result_ty);
            Term::Lam(Box::new(quote_at(lvl + 1, dlvl, &body)))
        }
        Value::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => Term::Glue {
            base: Box::new(quote_at(lvl, dlvl, base)),
            cofib: cofib.clone(),
            ty: Box::new(quote_at(lvl, dlvl, ty)),
            equiv: Box::new(quote_at(lvl, dlvl, equiv)),
        },
    }
}

/// Quote a term-binding closure by introducing a fresh neutral variable (at level `lvl`) and
/// quoting the body at depth `lvl + 1` — this is where η is realized structurally.
fn quote_closure(lvl: usize, dlvl: usize, clos: &Closure) -> Term {
    let body = clos.apply(Value::Neutral(Neutral::Var(lvl)));
    quote_at(lvl + 1, dlvl, &body)
}

/// Quote a dimension-binding closure (path family / `PLam` body) by instantiating its bound
/// dimension with a fresh dimension *level* and quoting the body at `dlvl + 1`.
fn quote_dim_closure(lvl: usize, dlvl: usize, clos: &Closure) -> Term {
    let body = clos.apply_dim(Interval::Dim(dlvl));
    quote_at(lvl, dlvl + 1, &body)
}

/// Quote an interval value (whose free `Dim`s are *levels*) to a term (whose `Dim`s are indices).
fn quote_interval(dlvl: usize, r: &Interval) -> Interval {
    match r {
        Interval::I0 => Interval::I0,
        Interval::I1 => Interval::I1,
        Interval::Dim(k) => Interval::Dim(dlvl - k - 1),
        Interval::Min(a, b) => Interval::Min(
            Box::new(quote_interval(dlvl, a)),
            Box::new(quote_interval(dlvl, b)),
        ),
        Interval::Max(a, b) => Interval::Max(
            Box::new(quote_interval(dlvl, a)),
            Box::new(quote_interval(dlvl, b)),
        ),
        Interval::Neg(a) => Interval::Neg(Box::new(quote_interval(dlvl, a))),
    }
}

fn quote_neutral(lvl: usize, dlvl: usize, n: &Neutral) -> Term {
    match n {
        Neutral::Var(k) => Term::Var(lvl - k - 1),
        Neutral::App(f, a) => Term::App(
            Box::new(quote_neutral(lvl, dlvl, f)),
            Box::new(quote_at(lvl, dlvl, a)),
        ),
        Neutral::Fst(p) => Term::Fst(Box::new(quote_neutral(lvl, dlvl, p))),
        Neutral::Snd(p) => Term::Snd(Box::new(quote_neutral(lvl, dlvl, p))),
        Neutral::PApp(p, r) => Term::PApp(
            Box::new(quote_neutral(lvl, dlvl, p)),
            quote_interval(dlvl, r),
        ),
        Neutral::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => Term::Elim {
            data: data.clone(),
            motive: Box::new(quote_at(lvl, dlvl, motive)),
            methods: methods.iter().map(|m| quote_at(lvl, dlvl, m)).collect(),
            scrutinee: Box::new(quote_neutral(lvl, dlvl, scrutinee)),
        },
    }
}

/// Weak-head normal form of a value (already in WHNF in this NbE: values are head-normal).
pub fn whnf(value: &Value) -> Value {
    value.clone()
}

/// Decide definitional equality `Γ ⊢ a ≡ b` by comparing values up to β and η (spec §2.8).
///
/// η is handled directly here: comparing functions (or a function and a neutral) applies both to
/// a fresh neutral argument; comparing pairs (or a pair and a neutral) compares projections.
pub fn conv(lvl: usize, a: &Value, b: &Value) -> bool {
    conv_at(lvl, 0, a, b)
}

/// Definitional equality with explicit term-level and dimension-level counters.
fn conv_at(lvl: usize, dlvl: usize, a: &Value, b: &Value) -> bool {
    match (a, b) {
        // η for functions: compare on a fresh argument regardless of which side is a Lam (or a
        // reflected function).
        (Value::Lam(_), _)
        | (_, Value::Lam(_))
        | (Value::ReflectedFun { .. }, _)
        | (_, Value::ReflectedFun { .. }) => {
            let fresh = Value::Neutral(Neutral::Var(lvl));
            conv_at(
                lvl + 1,
                dlvl,
                &apply(a.clone(), fresh.clone()),
                &apply(b.clone(), fresh),
            )
        }
        // η for pairs: compare both projections.
        (Value::Pair(_, _), _) | (_, Value::Pair(_, _)) => {
            conv_at(lvl, dlvl, &vfst(a.clone()), &vfst(b.clone()))
                && conv_at(lvl, dlvl, &vsnd(a.clone()), &vsnd(b.clone()))
        }
        // η for paths: compare on a fresh dimension regardless of which side is a PLam/reflected path.
        (Value::PLam(_), _)
        | (_, Value::PLam(_))
        | (Value::ReflectedPath { .. }, _)
        | (_, Value::ReflectedPath { .. }) => {
            let fresh = Interval::Dim(dlvl);
            conv_at(
                lvl,
                dlvl + 1,
                &papp(a.clone(), fresh.clone()),
                &papp(b.clone(), fresh),
            )
        }
        (Value::Univ(l1), Value::Univ(l2)) => l1 == l2,
        (Value::Pi(g1, d1, c1), Value::Pi(g2, d2, c2)) => {
            g1 == g2 && conv_at(lvl, dlvl, d1, d2) && conv_closure(lvl, dlvl, c1, c2)
        }
        (Value::Sigma(d1, c1), Value::Sigma(d2, c2)) => {
            conv_at(lvl, dlvl, d1, d2) && conv_closure(lvl, dlvl, c1, c2)
        }
        (
            Value::PathP {
                family: f1,
                lhs: l1,
                rhs: r1,
            },
            Value::PathP {
                family: f2,
                lhs: l2,
                rhs: r2,
            },
        ) => {
            conv_dim_closure(lvl, dlvl, f1, f2)
                && conv_at(lvl, dlvl, l1, l2)
                && conv_at(lvl, dlvl, r1, r2)
        }
        (Value::Data(n1, p1, i1), Value::Data(n2, p2, i2)) => {
            n1 == n2
                && p1.len() == p2.len()
                && i1.len() == i2.len()
                && p1.iter().zip(p2).all(|(a, b)| conv_at(lvl, dlvl, a, b))
                && i1.iter().zip(i2).all(|(a, b)| conv_at(lvl, dlvl, a, b))
        }
        (Value::Con(n1, a1), Value::Con(n2, a2)) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1.iter().zip(a2).all(|(a, b)| conv_at(lvl, dlvl, a, b))
        }
        (Value::Neutral(n1), Value::Neutral(n2)) => {
            quote_neutral(lvl, dlvl, n1) == quote_neutral(lvl, dlvl, n2)
        }
        _ => false,
    }
}

/// Compare two term-binding closures by instantiating both with the same fresh neutral variable.
fn conv_closure(lvl: usize, dlvl: usize, c1: &Closure, c2: &Closure) -> bool {
    let fresh = Value::Neutral(Neutral::Var(lvl));
    conv_at(lvl + 1, dlvl, &c1.apply(fresh.clone()), &c2.apply(fresh))
}

/// Compare two dimension-binding closures by instantiating both with the same fresh dimension.
fn conv_dim_closure(lvl: usize, dlvl: usize, c1: &Closure, c2: &Closure) -> bool {
    let fresh = Interval::Dim(dlvl);
    conv_at(lvl, dlvl + 1, &c1.apply_dim(fresh.clone()), &c2.apply_dim(fresh))
}

/// Normalize an interval term to a canonical De Morgan form (spec §2.6 lattice equations).
///
/// We push negation to atoms (`¬0=1`, `¬1=0`, `¬¬r=r`, `¬(a∧b)=¬a∨¬b`, `¬(a∨b)=¬a∧¬b`) and apply
/// the bounded-lattice unit/absorbing laws (`r∧1=r`, `r∧0=0`, `r∨0=r`, `r∨1=1`), idempotence, and
/// commutative ordering of atoms, yielding a stable form sufficient to decide equality for the
/// fragments M0 exercises.
pub fn normalize_interval(r: &Interval) -> Interval {
    nf_to_interval(dnf(r))
}

/// A disjunctive normal form: a set of conjunctive clauses, each a set of literals. We represent
/// literals as `(dim_index, negated)` and treat the empty product as `1` and the empty sum as `0`.
/// Constants are folded during construction.
type Lit = (usize, bool);

#[derive(Clone)]
enum Dnf {
    /// The constant `0`.
    Zero,
    /// The constant `1`.
    One,
    /// A sum of products of literals (each inner vec sorted+deduped, outer deduped).
    Sum(Vec<Vec<Lit>>),
}

fn dnf(r: &Interval) -> Dnf {
    match r {
        Interval::I0 => Dnf::Zero,
        Interval::I1 => Dnf::One,
        Interval::Dim(i) => Dnf::Sum(vec![vec![(*i, false)]]),
        Interval::Neg(a) => dnf_neg(a),
        Interval::Min(a, b) => dnf_and(dnf(a), dnf(b)),
        Interval::Max(a, b) => dnf_or(dnf(a), dnf(b)),
    }
}

fn dnf_neg(r: &Interval) -> Dnf {
    match r {
        Interval::I0 => Dnf::One,
        Interval::I1 => Dnf::Zero,
        Interval::Dim(i) => Dnf::Sum(vec![vec![(*i, true)]]),
        Interval::Neg(a) => dnf(a),
        // De Morgan: ¬(a∧b) = ¬a ∨ ¬b ; ¬(a∨b) = ¬a ∧ ¬b.
        Interval::Min(a, b) => dnf_or(dnf_neg(a), dnf_neg(b)),
        Interval::Max(a, b) => dnf_and(dnf_neg(a), dnf_neg(b)),
    }
}

fn dnf_or(a: Dnf, b: Dnf) -> Dnf {
    match (a, b) {
        (Dnf::One, _) | (_, Dnf::One) => Dnf::One,
        (Dnf::Zero, x) | (x, Dnf::Zero) => x,
        (Dnf::Sum(mut xs), Dnf::Sum(ys)) => {
            xs.extend(ys);
            simplify_sum(xs)
        }
    }
}

fn dnf_and(a: Dnf, b: Dnf) -> Dnf {
    match (a, b) {
        (Dnf::Zero, _) | (_, Dnf::Zero) => Dnf::Zero,
        (Dnf::One, x) | (x, Dnf::One) => x,
        (Dnf::Sum(xs), Dnf::Sum(ys)) => {
            let mut out: Vec<Vec<Lit>> = Vec::new();
            for cx in &xs {
                for cy in &ys {
                    let mut clause = cx.clone();
                    clause.extend(cy.iter().cloned());
                    if let Some(c) = normalize_clause(clause) {
                        out.push(c);
                    }
                    // a clause containing both x and ¬x is `0` and is dropped.
                }
            }
            simplify_sum(out)
        }
    }
}

/// Sort+dedup a clause's literals; return `None` if it is contradictory (contains `x` and `¬x`),
/// which makes the whole product `0`.
fn normalize_clause(mut clause: Vec<Lit>) -> Option<Vec<Lit>> {
    clause.sort();
    clause.dedup();
    for w in clause.windows(2) {
        if w[0].0 == w[1].0 && w[0].1 != w[1].1 {
            return None;
        }
    }
    Some(clause)
}

fn simplify_sum(clauses: Vec<Vec<Lit>>) -> Dnf {
    let mut norm: Vec<Vec<Lit>> = Vec::new();
    for c in clauses {
        if let Some(c) = normalize_clause(c) {
            if c.is_empty() {
                // empty product = 1, absorbs the whole sum.
                return Dnf::One;
            }
            norm.push(c);
        }
    }
    norm.sort();
    norm.dedup();
    if norm.is_empty() {
        Dnf::Zero
    } else {
        Dnf::Sum(norm)
    }
}

fn nf_to_interval(d: Dnf) -> Interval {
    match d {
        Dnf::Zero => Interval::I0,
        Dnf::One => Interval::I1,
        Dnf::Sum(clauses) => {
            let mut sum: Option<Interval> = None;
            for clause in clauses {
                let mut prod: Option<Interval> = None;
                for (i, neg) in clause {
                    let lit = if neg {
                        Interval::Neg(Box::new(Interval::Dim(i)))
                    } else {
                        Interval::Dim(i)
                    };
                    prod = Some(match prod {
                        None => lit,
                        Some(p) => Interval::Min(Box::new(p), Box::new(lit)),
                    });
                }
                let prod = prod.unwrap_or(Interval::I1);
                sum = Some(match sum {
                    None => prod,
                    Some(s) => Interval::Max(Box::new(s), Box::new(prod)),
                });
            }
            sum.unwrap_or(Interval::I0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{Level, Term};
    use crate::value::Env;

    fn u0() -> Term {
        Term::Univ(Level::Zero)
    }

    /// The identity function `λ. 0` applied to `Univ 0` β-reduces to `Univ 0`.
    #[test]
    fn beta_reduces_application() {
        // (λ x. x) (Univ 0)
        let id = Term::Lam(Box::new(Term::Var(0)));
        let app = Term::App(Box::new(id), Box::new(u0()));
        let v = eval(&Env::empty(), &app);
        assert_eq!(quote(0, &v), u0());
    }

    /// eval then quote on a closed normal form is the identity (roundtrip).
    #[test]
    fn eval_quote_roundtrip_pi() {
        // Pi (x :^ω Univ 0). Univ 0
        let pi = Term::Pi(
            crate::semiring::Grade::Omega,
            Box::new(u0()),
            Box::new(u0()),
        );
        let v = eval(&Env::empty(), &pi);
        assert_eq!(quote(0, &v), pi);
    }

    /// `Conv` accepts definitionally equal terms: `(λ x. x) (Univ 0) ≡ Univ 0`.
    #[test]
    fn conv_accepts_equal() {
        let id_app = Term::App(Box::new(Term::Lam(Box::new(Term::Var(0)))), Box::new(u0()));
        let a = eval(&Env::empty(), &id_app);
        let b = eval(&Env::empty(), &u0());
        assert!(conv(0, &a, &b));
    }

    /// `Conv` rejects distinct normal forms: `Univ 0 ≢ Univ 1`.
    #[test]
    fn conv_rejects_unequal() {
        let a = eval(&Env::empty(), &Term::Univ(Level::Zero));
        let b = eval(&Env::empty(), &Term::Univ(Level::Suc(Box::new(Level::Zero))));
        assert!(!conv(0, &a, &b));
    }

    /// η for functions: `λ x. (f x) ≡ f` under a neutral `f`.
    #[test]
    fn eta_for_functions() {
        // In context with one free var f at level 0, compare (λ. f 0) with f.
        // We model f as a neutral by quoting at depth 1.
        let lam_eta = Term::Lam(Box::new(Term::App(
            Box::new(Term::Var(1)),
            Box::new(Term::Var(0)),
        )));
        // Evaluate under an env where Var(0) (the f) is a neutral variable at level 0.
        let env = Env::empty().extend(Value::Neutral(crate::value::Neutral::Var(0)));
        let v_lam = eval(&env, &lam_eta);
        let v_f = eval(&env, &Term::Var(0));
        assert!(conv(1, &v_lam, &v_f), "eta: λx. f x ≡ f");
    }

    // ---- L4: interval De Morgan algebra (spec §2.6) ----
    use crate::term::Interval as Iv;

    fn dim(i: usize) -> Iv {
        Iv::Dim(i)
    }
    fn neg(r: Iv) -> Iv {
        Iv::Neg(Box::new(r))
    }
    fn imin(a: Iv, b: Iv) -> Iv {
        Iv::Min(Box::new(a), Box::new(b))
    }
    fn imax(a: Iv, b: Iv) -> Iv {
        Iv::Max(Box::new(a), Box::new(b))
    }
    fn nf_eq(a: Iv, b: Iv) -> bool {
        normalize_interval(&a) == normalize_interval(&b)
    }

    #[test]
    fn interval_negation_constants() {
        assert_eq!(normalize_interval(&neg(Iv::I0)), Iv::I1);
        assert_eq!(normalize_interval(&neg(Iv::I1)), Iv::I0);
        assert_eq!(normalize_interval(&neg(neg(dim(0)))), dim(0));
    }

    #[test]
    fn interval_lattice_units_and_absorbers() {
        assert!(nf_eq(imin(dim(0), Iv::I1), dim(0)));
        assert!(nf_eq(imin(dim(0), Iv::I0), Iv::I0));
        assert!(nf_eq(imax(dim(0), Iv::I0), dim(0)));
        assert!(nf_eq(imax(dim(0), Iv::I1), Iv::I1));
    }

    #[test]
    fn interval_idempotence_and_commutativity() {
        assert!(nf_eq(imin(dim(0), dim(0)), dim(0)));
        assert!(nf_eq(imin(dim(0), dim(1)), imin(dim(1), dim(0))));
        assert!(nf_eq(imax(dim(0), dim(1)), imax(dim(1), dim(0))));
    }

    #[test]
    fn interval_de_morgan() {
        assert!(nf_eq(
            neg(imin(dim(0), dim(1))),
            imax(neg(dim(0)), neg(dim(1)))
        ));
        assert!(nf_eq(
            neg(imax(dim(0), dim(1))),
            imin(neg(dim(0)), neg(dim(1)))
        ));
    }

    #[test]
    fn interval_contradiction_is_zero() {
        assert_eq!(normalize_interval(&imin(dim(0), neg(dim(0)))), Iv::I0);
    }

    /// `PApp (PLam (i. t)) r` β-reduces by substituting `r` for `i` (path β).
    #[test]
    fn path_beta() {
        let env = Env::empty().extend(Value::Neutral(crate::value::Neutral::Var(0)));
        let p = Term::PLam(Box::new(Term::Var(0)));
        let papp0 = Term::PApp(Box::new(p), Iv::I0);
        let v = eval(&env, &papp0);
        let point = eval(&env, &Term::Var(0));
        assert!(conv(1, &v, &point), "path β: (λ i. x) @ 0 ≡ x");
    }
}
