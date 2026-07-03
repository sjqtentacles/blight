//! The independent NbE engine: `eval` (term → value), `quote` (value → normal-form term), and the
//! semantic operators (`apply`, `papp`, `vfst`, `vsnd`, `do_elim`) plus `reflect` for η and path
//! boundaries. This mirrors the kernel's NbE design but is a wholly separate implementation over
//! this crate's own [`RValue`]; two independent NbEs deciding the same equality is the point.

use crate::term::{RInterval, RTerm};
use crate::value::{Closure, DimClosure, Env, Neutral, RValue};
use blight_kernel::signature::{Arg, Signature};
use std::rc::Rc;

impl Closure {
    pub fn apply(&self, sig: &Signature, arg: RValue) -> RValue {
        eval(sig, &self.env.extend(arg), &self.body)
    }
}

impl DimClosure {
    pub fn apply_dim(&self, sig: &Signature, r: RInterval) -> RValue {
        eval(sig, &self.env.extend_dim(r), &self.body)
    }
}

/// Evaluate a term in an environment to a value.
pub fn eval(sig: &Signature, env: &Env, t: &RTerm) -> RValue {
    match t {
        RTerm::Var(i) => env
            .lookup(*i)
            .cloned()
            .unwrap_or(RValue::Neutral(Neutral::Var(usize::MAX))), // unbound: a fresh stuck var
        RTerm::Univ(l) => RValue::Univ(*l),
        RTerm::Pi(g, dom, cod) => RValue::Pi(
            *g,
            Box::new(eval(sig, env, dom)),
            Closure {
                env: env.clone(),
                body: Rc::new((**cod).clone()),
            },
        ),
        RTerm::Lam(body) => RValue::Lam(Closure {
            env: env.clone(),
            body: Rc::new((**body).clone()),
        }),
        RTerm::App(f, a) => {
            let vf = eval(sig, env, f);
            let va = eval(sig, env, a);
            apply(sig, vf, va)
        }
        RTerm::Sigma(dom, cod) => RValue::Sigma(
            Box::new(eval(sig, env, dom)),
            Closure {
                env: env.clone(),
                body: Rc::new((**cod).clone()),
            },
        ),
        RTerm::Pair(a, b) => RValue::Pair(Box::new(eval(sig, env, a)), Box::new(eval(sig, env, b))),
        RTerm::Fst(p) => vfst(eval(sig, env, p)),
        RTerm::Snd(p) => vsnd(sig, eval(sig, env, p)),
        RTerm::Ann(e, _ty) => eval(sig, env, e),
        RTerm::Data(name, ps, is) => RValue::Data(
            name.clone(),
            ps.iter().map(|x| eval(sig, env, x)).collect(),
            is.iter().map(|x| eval(sig, env, x)).collect(),
        ),
        RTerm::Con(name, args) => RValue::Con(
            name.clone(),
            args.iter().map(|x| eval(sig, env, x)).collect(),
        ),
        RTerm::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => {
            let m = eval(sig, env, motive);
            let ms: Vec<RValue> = methods.iter().map(|x| eval(sig, env, x)).collect();
            let s = eval(sig, env, scrutinee);
            do_elim(sig, data, m, ms, s)
        }
        RTerm::PathP { family, lhs, rhs } => RValue::PathP {
            family: DimClosure {
                env: env.clone(),
                body: Rc::new((**family).clone()),
            },
            lhs: Box::new(eval(sig, env, lhs)),
            rhs: Box::new(eval(sig, env, rhs)),
        },
        RTerm::PLam(body) => RValue::PLam(DimClosure {
            env: env.clone(),
            body: Rc::new((**body).clone()),
        }),
        RTerm::PApp(p, r) => {
            let vp = eval(sig, env, p);
            let vr = eval_interval(env, r);
            papp(sig, vp, vr)
        }
        RTerm::Interval(r) => RValue::Interval(eval_interval(env, r)),

        RTerm::Transp {
            family,
            cofib,
            base,
        } => crate::kan::eval_transp(sig, env, family, cofib, base),
        RTerm::HComp {
            ty,
            cofib,
            tube,
            base,
        } => crate::kan::eval_hcomp(sig, env, ty, cofib, tube, base),
        RTerm::Comp {
            family,
            cofib,
            tube,
            base,
        } => crate::kan::eval_comp(sig, env, family, cofib, tube, base),

        RTerm::Delay(a) => RValue::Delay(Box::new(eval(sig, env, a))),
        RTerm::Now(a) => RValue::Now(Box::new(eval(sig, env, a))),
        RTerm::Later(d) => RValue::Later(Box::new(eval(sig, env, d))),
        RTerm::Force(d) => do_force(eval(sig, env, d)),

        // ---- effects and handlers (spec §4) ----
        // `! E A` is *definitionally its payload* `A` at the value level: it evaluates to `eval A`,
        // dropping the wrapper exactly as the kernel does (`normalize.rs`'s `EffTy(_row, a) => eval a`).
        // The effect row `E` is not part of the value — it is tracked separately as the threaded
        // `RRow` (B2). This is what makes an `! E A`-annotated definition whose body is a bare
        // `perform`/pure value re-check: the body infers payload type `A` (with row `E`), and `A`
        // converts against the collapsed annotation `A` rather than against a spurious `EffTy A`.
        // `perform`/`handle` appear in term position; the re-checker does not run effect semantics, so
        // they evaluate to *stuck* neutrals that only round-trip through `quote`.
        RTerm::EffTy(a) => eval(sig, env, a),
        RTerm::Op {
            effect,
            op,
            type_args,
            arg,
        } => RValue::Neutral(Neutral::Op {
            effect: effect.clone(),
            op: op.clone(),
            type_args: type_args.iter().map(|t| eval(sig, env, t)).collect(),
            arg: Box::new(eval(sig, env, arg)),
        }),
        RTerm::Handle {
            body,
            return_clause,
            op_clauses,
        } => RValue::Neutral(Neutral::Handle {
            env: env.clone(),
            body: Box::new(eval(sig, env, body)),
            return_clause: Rc::new((**return_clause).clone()),
            op_clauses: op_clauses
                .iter()
                .map(|(op, clause)| (op.clone(), Rc::new((**clause).clone())))
                .collect(),
        }),

        // ---- primitive machine integers (M11) ----
        RTerm::IntTy => RValue::IntTy,
        RTerm::IntLit(n) => RValue::IntLit(*n),
        RTerm::IntPrim { op, lhs, rhs } => int_prim(*op, eval(sig, env, lhs), eval(sig, env, rhs)),
    }
}

/// Compute a primitive `Int` operation, independently mirroring the kernel's `int_prim`: fold two
/// literals (definitional reduction), else stay stuck. Division by zero stays stuck; arithmetic
/// wraps; comparisons yield `1`/`0`.
pub fn int_prim(op: blight_kernel::IntPrimOp, lhs: RValue, rhs: RValue) -> RValue {
    use blight_kernel::IntPrimOp;
    match (&lhs, &rhs) {
        (RValue::IntLit(a), RValue::IntLit(b)) => {
            let (a, b) = (*a, *b);
            match op {
                IntPrimOp::Add => RValue::IntLit(a.wrapping_add(b)),
                IntPrimOp::Sub => RValue::IntLit(a.wrapping_sub(b)),
                IntPrimOp::Mul => RValue::IntLit(a.wrapping_mul(b)),
                IntPrimOp::Div => {
                    if b == 0 {
                        RValue::Neutral(Neutral::IntPrim {
                            op,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        })
                    } else {
                        RValue::IntLit(a.wrapping_div(b))
                    }
                }
                IntPrimOp::Eq => RValue::IntLit(if a == b { 1 } else { 0 }),
                IntPrimOp::Lt => RValue::IntLit(if a < b { 1 } else { 0 }),
            }
        }
        _ => RValue::Neutral(Neutral::IntPrim {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }),
    }
}

/// Resolve environment dimension bindings into an interval, then normalize the De Morgan form.
pub fn eval_interval(env: &Env, r: &RInterval) -> RInterval {
    fn resolve(env: &Env, r: &RInterval) -> RInterval {
        match r {
            RInterval::I0 | RInterval::I1 => r.clone(),
            RInterval::Dim(i) => env.lookup_dim(*i).cloned().unwrap_or(RInterval::Dim(*i)),
            RInterval::Min(a, b) => {
                RInterval::Min(Box::new(resolve(env, a)), Box::new(resolve(env, b)))
            }
            RInterval::Max(a, b) => {
                RInterval::Max(Box::new(resolve(env, a)), Box::new(resolve(env, b)))
            }
            RInterval::Neg(a) => RInterval::Neg(Box::new(resolve(env, a))),
        }
    }
    nf_interval(&resolve(env, r))
}

/// Normalize a De Morgan interval to canonical form (constant-fold endpoints, push negation).
pub fn nf_interval(r: &RInterval) -> RInterval {
    match r {
        RInterval::I0 | RInterval::I1 | RInterval::Dim(_) => r.clone(),
        RInterval::Neg(a) => match nf_interval(a) {
            RInterval::I0 => RInterval::I1,
            RInterval::I1 => RInterval::I0,
            RInterval::Neg(b) => *b,
            other => RInterval::Neg(Box::new(other)),
        },
        RInterval::Min(a, b) => {
            let a = nf_interval(a);
            let b = nf_interval(b);
            match (&a, &b) {
                (RInterval::I0, _) | (_, RInterval::I0) => RInterval::I0,
                (RInterval::I1, _) => b,
                (_, RInterval::I1) => a,
                _ if a == b => a,
                _ => RInterval::Min(Box::new(a), Box::new(b)),
            }
        }
        RInterval::Max(a, b) => {
            let a = nf_interval(a);
            let b = nf_interval(b);
            match (&a, &b) {
                (RInterval::I1, _) | (_, RInterval::I1) => RInterval::I1,
                (RInterval::I0, _) => b,
                (_, RInterval::I0) => a,
                _ if a == b => a,
                _ => RInterval::Max(Box::new(a), Box::new(b)),
            }
        }
    }
}

/// Apply a function value to an argument (β / η / neutral spine).
pub fn apply(sig: &Signature, f: RValue, a: RValue) -> RValue {
    match f {
        RValue::Lam(clos) => clos.apply(sig, a),
        RValue::ReflectedFun { neutral, cod } => {
            let result_ty = cod.apply(sig, a.clone());
            reflect(
                sig,
                Neutral::App(Box::new(neutral), Box::new(a)),
                &result_ty,
            )
        }
        RValue::Neutral(n) => RValue::Neutral(Neutral::App(Box::new(n), Box::new(a))),
        other => panic!("apply: not a function: {other:?}"),
    }
}

/// First projection.
pub fn vfst(p: RValue) -> RValue {
    match p {
        RValue::Pair(a, _) => *a,
        RValue::Neutral(n) => RValue::Neutral(Neutral::Fst(Box::new(n))),
        other => panic!("vfst: not a pair: {other:?}"),
    }
}

/// Second projection.
pub fn vsnd(_sig: &Signature, p: RValue) -> RValue {
    match p {
        RValue::Pair(_, b) => *b,
        RValue::Neutral(n) => RValue::Neutral(Neutral::Snd(Box::new(n))),
        other => panic!("vsnd: not a pair: {other:?}"),
    }
}

/// Force a delay value (spec §4.5). `force (now a) ⇝ a`; `force (later d)` stays guarded; a
/// neutral reflects to a stuck `force`.
pub fn do_force(d: RValue) -> RValue {
    match d {
        RValue::Now(a) => *a,
        RValue::Later(inner) => RValue::Force(Box::new(RValue::Later(inner))),
        RValue::Neutral(n) => RValue::Neutral(Neutral::Force(Box::new(n))),
        other => panic!("do_force: not a delay: {other:?}"),
    }
}

/// Path application (`p @ r`): β for path lambdas, boundary rules for reflected paths.
pub fn papp(sig: &Signature, p: RValue, r: RInterval) -> RValue {
    match p {
        RValue::PLam(clos) => clos.apply_dim(sig, r),
        RValue::ReflectedPath { neutral, lhs, rhs } => match nf_interval(&r) {
            RInterval::I0 => *lhs,
            RInterval::I1 => *rhs,
            other => RValue::Neutral(Neutral::PApp(Box::new(neutral), other)),
        },
        RValue::Neutral(n) => RValue::Neutral(Neutral::PApp(Box::new(n), nf_interval(&r))),
        other => panic!("papp: not a path: {other:?}"),
    }
}

/// The dependent eliminator: ι-reduction on a constructor, stuck on a neutral.
pub fn do_elim(
    sig: &Signature,
    data: &blight_kernel::DataName,
    motive: RValue,
    methods: Vec<RValue>,
    scrut: RValue,
) -> RValue {
    match scrut {
        RValue::Con(con, args) => {
            let decl = sig.get(data).expect("do_elim: unknown data type");
            let (idx, ctor) = decl.constructor(&con).expect("do_elim: not a constructor");
            let method = methods.get(idx).cloned().expect("do_elim: missing method");
            let mut result = method;
            for (arg, shape) in args.iter().zip(ctor.args.iter()) {
                result = apply(sig, result, arg.clone());
                if matches!(shape, Arg::Rec(_)) {
                    let ih = do_elim(sig, data, motive.clone(), methods.clone(), arg.clone());
                    result = apply(sig, result, ih);
                }
            }
            result
        }
        RValue::Neutral(n) => RValue::Neutral(Neutral::Elim {
            data: data.clone(),
            motive: Box::new(motive),
            methods,
            scrutinee: Box::new(n),
        }),
        RValue::ReflectedPath { neutral, .. } => RValue::Neutral(Neutral::Elim {
            data: data.clone(),
            motive: Box::new(motive),
            methods,
            scrutinee: Box::new(neutral),
        }),
        other => panic!("do_elim: bad scrutinee: {other:?}"),
    }
}

/// Reflect a neutral against its type to realize η (functions, pairs) and path boundaries.
pub fn reflect(sig: &Signature, neutral: Neutral, ty: &RValue) -> RValue {
    match ty {
        RValue::PathP { lhs, rhs, .. } => RValue::ReflectedPath {
            neutral,
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        },
        RValue::Pi(_g, _dom, cod) => RValue::ReflectedFun {
            neutral,
            cod: cod.clone(),
        },
        RValue::Sigma(dom, cod) => {
            let fst = reflect(sig, Neutral::Fst(Box::new(neutral.clone())), dom);
            let snd_ty = cod.apply(sig, fst.clone());
            let snd = reflect(sig, Neutral::Snd(Box::new(neutral)), &snd_ty);
            RValue::Pair(Box::new(fst), Box::new(snd))
        }
        _ => RValue::Neutral(neutral),
    }
}

/// Quote a value back to a normal-form term at term-level `lvl` and dimension-level `dlvl`.
pub fn quote(sig: &Signature, lvl: usize, dlvl: usize, v: &RValue) -> RTerm {
    match v {
        RValue::Neutral(n) => quote_neutral(sig, lvl, dlvl, n),
        RValue::Univ(l) => RTerm::Univ(*l),
        RValue::Pi(g, dom, cod) => RTerm::Pi(
            *g,
            Box::new(quote(sig, lvl, dlvl, dom)),
            Box::new(quote_closure(sig, lvl, dlvl, cod)),
        ),
        RValue::Lam(clos) => RTerm::Lam(Box::new(quote_closure(sig, lvl, dlvl, clos))),
        RValue::Sigma(dom, cod) => RTerm::Sigma(
            Box::new(quote(sig, lvl, dlvl, dom)),
            Box::new(quote_closure(sig, lvl, dlvl, cod)),
        ),
        RValue::Pair(a, b) => RTerm::Pair(
            Box::new(quote(sig, lvl, dlvl, a)),
            Box::new(quote(sig, lvl, dlvl, b)),
        ),
        RValue::Data(name, ps, is) => RTerm::Data(
            name.clone(),
            ps.iter().map(|x| quote(sig, lvl, dlvl, x)).collect(),
            is.iter().map(|x| quote(sig, lvl, dlvl, x)).collect(),
        ),
        RValue::Con(name, args) => RTerm::Con(
            name.clone(),
            args.iter().map(|x| quote(sig, lvl, dlvl, x)).collect(),
        ),
        RValue::PathP { family, lhs, rhs } => RTerm::PathP {
            family: Box::new(quote_dim_closure(sig, lvl, dlvl, family)),
            lhs: Box::new(quote(sig, lvl, dlvl, lhs)),
            rhs: Box::new(quote(sig, lvl, dlvl, rhs)),
        },
        RValue::PLam(clos) => RTerm::PLam(Box::new(quote_dim_closure(sig, lvl, dlvl, clos))),
        RValue::ReflectedPath { neutral, .. } => {
            // η-expand: `λ i. p @ i`. The neutral lives outside the fresh dimension binder, so it
            // is quoted at the current `dlvl`; the bound `i` is dimension index 0.
            RTerm::PLam(Box::new(RTerm::PApp(
                Box::new(quote_neutral(sig, lvl, dlvl, neutral)),
                RInterval::Dim(0),
            )))
        }
        RValue::ReflectedFun { neutral, cod } => {
            // η-expand: `λ x. n x`.
            let arg = RValue::Neutral(Neutral::Var(lvl));
            let result_ty = cod.apply(sig, arg.clone());
            let body = reflect(
                sig,
                Neutral::App(Box::new(neutral.clone()), Box::new(arg)),
                &result_ty,
            );
            RTerm::Lam(Box::new(quote(sig, lvl + 1, dlvl, &body)))
        }
        RValue::Interval(r) => RTerm::Interval(nf_interval(r)),
        RValue::Delay(a) => RTerm::Delay(Box::new(quote(sig, lvl, dlvl, a))),
        RValue::Now(a) => RTerm::Now(Box::new(quote(sig, lvl, dlvl, a))),
        RValue::Later(d) => RTerm::Later(Box::new(quote(sig, lvl, dlvl, d))),
        RValue::Force(d) => RTerm::Force(Box::new(quote(sig, lvl, dlvl, d))),
        RValue::IntTy => RTerm::IntTy,
        RValue::IntLit(n) => RTerm::IntLit(*n),
    }
}

/// Quote a term-binder closure: open it with a fresh variable at level `lvl`, quote under `lvl+1`.
fn quote_closure(sig: &Signature, lvl: usize, dlvl: usize, clos: &Closure) -> RTerm {
    let fresh = RValue::Neutral(Neutral::Var(lvl));
    let body = clos.apply(sig, fresh);
    quote(sig, lvl + 1, dlvl, &body)
}

/// Quote a dimension-binder closure: open with a fresh dimension at level `dlvl`.
fn quote_dim_closure(sig: &Signature, lvl: usize, dlvl: usize, clos: &DimClosure) -> RTerm {
    let body = clos.apply_dim(sig, RInterval::Dim(dlvl));
    quote(sig, lvl, dlvl + 1, &body)
}

/// Quote a neutral, converting de Bruijn *levels* back to indices.
fn quote_neutral(sig: &Signature, lvl: usize, dlvl: usize, n: &Neutral) -> RTerm {
    match n {
        Neutral::Var(k) => {
            // A free variable stored as a level; convert to an index. An unbound sentinel
            // (usize::MAX) quotes to itself as a (very large) index — it should never occur in a
            // well-scoped term.
            if *k == usize::MAX {
                RTerm::Var(usize::MAX)
            } else {
                RTerm::Var(lvl - 1 - *k)
            }
        }
        Neutral::App(f, a) => RTerm::App(
            Box::new(quote_neutral(sig, lvl, dlvl, f)),
            Box::new(quote(sig, lvl, dlvl, a)),
        ),
        Neutral::Fst(p) => RTerm::Fst(Box::new(quote_neutral(sig, lvl, dlvl, p))),
        Neutral::Snd(p) => RTerm::Snd(Box::new(quote_neutral(sig, lvl, dlvl, p))),
        Neutral::PApp(p, r) => RTerm::PApp(
            Box::new(quote_neutral(sig, lvl, dlvl, p)),
            quote_interval(dlvl, r),
        ),
        Neutral::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => RTerm::Elim {
            data: data.clone(),
            motive: Box::new(quote(sig, lvl, dlvl, motive)),
            methods: methods.iter().map(|m| quote(sig, lvl, dlvl, m)).collect(),
            scrutinee: Box::new(quote_neutral(sig, lvl, dlvl, scrutinee)),
        },
        Neutral::Force(d) => RTerm::Force(Box::new(quote_neutral(sig, lvl, dlvl, d))),
        Neutral::Op {
            effect,
            op,
            type_args,
            arg,
        } => RTerm::Op {
            effect: effect.clone(),
            op: op.clone(),
            type_args: type_args.iter().map(|t| quote(sig, lvl, dlvl, t)).collect(),
            arg: Box::new(quote(sig, lvl, dlvl, arg)),
        },
        Neutral::Handle {
            env,
            body,
            return_clause,
            op_clauses,
        } => {
            // Re-open each clause under fresh variables at the current level, mirroring the kernel's
            // binder structure: the return clause binds 1 (`x`), each op clause binds 2 (`x`, `k`).
            // The captured env supplies the free-variable bindings; the fresh vars stand for the
            // binders so the body quotes back to a term with the right de Bruijn indices.
            let ret_env = env.extend(RValue::Neutral(Neutral::Var(lvl)));
            let ret_v = eval(sig, &ret_env, return_clause);
            let ret_t = quote(sig, lvl + 1, dlvl, &ret_v);
            let clauses_t: Vec<(blight_kernel::signature::OpName, Box<RTerm>)> = op_clauses
                .iter()
                .map(|(op, clause)| {
                    let clause_env = env
                        .extend(RValue::Neutral(Neutral::Var(lvl)))
                        .extend(RValue::Neutral(Neutral::Var(lvl + 1)));
                    let v = eval(sig, &clause_env, clause);
                    (op.clone(), Box::new(quote(sig, lvl + 2, dlvl, &v)))
                })
                .collect();
            RTerm::Handle {
                body: Box::new(quote(sig, lvl, dlvl, body)),
                return_clause: Box::new(ret_t),
                op_clauses: clauses_t,
            }
        }
        Neutral::IntPrim { op, lhs, rhs } => RTerm::IntPrim {
            op: *op,
            lhs: Box::new(quote(sig, lvl, dlvl, lhs)),
            rhs: Box::new(quote(sig, lvl, dlvl, rhs)),
        },
    }
}

/// Quote an interval, converting dimension levels back to indices.
fn quote_interval(dlvl: usize, r: &RInterval) -> RInterval {
    match nf_interval(r) {
        RInterval::I0 => RInterval::I0,
        RInterval::I1 => RInterval::I1,
        RInterval::Dim(k) => RInterval::Dim(dlvl.saturating_sub(1).saturating_sub(k)),
        RInterval::Min(a, b) => RInterval::Min(
            Box::new(quote_interval(dlvl, &a)),
            Box::new(quote_interval(dlvl, &b)),
        ),
        RInterval::Max(a, b) => RInterval::Max(
            Box::new(quote_interval(dlvl, &a)),
            Box::new(quote_interval(dlvl, &b)),
        ),
        RInterval::Neg(a) => RInterval::Neg(Box::new(quote_interval(dlvl, &a))),
    }
}
