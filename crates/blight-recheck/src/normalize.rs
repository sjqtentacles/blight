//! The independent NbE engine: `eval` (term → value), `quote` (value → normal-form term), and the
//! semantic operators (`apply`, `papp`, `vfst`, `vsnd`, `do_elim`) plus `reflect` for η and path
//! boundaries. This mirrors the kernel's NbE design but is a wholly separate implementation over
//! this crate's own [`RValue`]; two independent NbEs deciding the same equality is the point.

use crate::term::{RInterval, RTerm};
use crate::value::{Closure, DimClosure, Env, Neutral, RValue};
use blight_kernel::signature::{Arg, Signature};
use std::rc::Rc;

std::thread_local! {
    /// Arc N / N5 instrumentation, mirroring the kernel's counter *independently* (the two-engine
    /// discipline applies to instrumentation too): how many induction hypotheses this engine's
    /// `do_elim` has computed on this thread. Read/reset only by the N5 scaling tests.
    static IH_COMPUTED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };

    /// Arc N / N5: IHs *skipped* because the receiving method provably discards its binder.
    static IH_DISCARDED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Read and reset this thread's IH counter (arc N / N5; see the kernel twin
/// `blight_kernel::normalize::take_ih_computed`).
pub fn take_ih_computed() -> u64 {
    IH_COMPUTED.replace(0)
}

/// Read and reset this thread's discarded-IH counter (arc N / N5).
pub fn take_ih_discarded() -> u64 {
    IH_DISCARDED.replace(0)
}

/// `BL_NO_DEAD_IH=1` disables the N5 dead-IH skip in this engine too (one flag, two independent
/// implementations — the A/B toggle must flip both or the differential harnesses would disagree
/// with themselves).
fn dead_ih_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var("BL_NO_DEAD_IH").is_ok_and(|v| v == "1"))
}

/// Whether `t` references the de Bruijn *term* variable `depth` term-binders above (arc N / N5).
/// The binder map mirrors this crate's `shift_free_cut` exactly (its own authoritative
/// enumeration, independent of the kernel's): `Lam`/`Pi`-codomain/`Sigma`-second bind one,
/// `Handle`'s return clause binds one and each op clause two; dimension binders (`PLam`,
/// `family`/`tube` lines) live in a separate index space. Over-approximating "used" is safe
/// (costs an unnecessary IH). `System`/`Partial` are declined at translation; `Glue`/`GlueTerm`/
/// `Unglue` are present in `RTerm` and traversed here (one term-index space, dimensions separate).
fn uses_binder(t: &RTerm, depth: usize) -> bool {
    match t {
        RTerm::Var(i) => *i == depth,
        RTerm::Univ(_) | RTerm::Interval(_) | RTerm::IntTy | RTerm::IntLit(_) => false,
        RTerm::Pi(_, a, b) => uses_binder(a, depth) || uses_binder(b, depth + 1),
        RTerm::Lam(b) => uses_binder(b, depth + 1),
        RTerm::Sigma(a, b) => uses_binder(a, depth) || uses_binder(b, depth + 1),
        RTerm::App(f, a) | RTerm::Pair(f, a) | RTerm::Ann(f, a) => {
            uses_binder(f, depth) || uses_binder(a, depth)
        }
        RTerm::Fst(p) | RTerm::Snd(p) | RTerm::PLam(p) | RTerm::PApp(p, _) => uses_binder(p, depth),
        RTerm::Data(_, ps, is) => {
            ps.iter().any(|t| uses_binder(t, depth)) || is.iter().any(|t| uses_binder(t, depth))
        }
        RTerm::Con(_, args) => args.iter().any(|t| uses_binder(t, depth)),
        RTerm::Elim {
            motive,
            methods,
            scrutinee,
            ..
        } => {
            uses_binder(motive, depth)
                || methods.iter().any(|t| uses_binder(t, depth))
                || uses_binder(scrutinee, depth)
        }
        RTerm::PathP { family, lhs, rhs } => {
            uses_binder(family, depth) || uses_binder(lhs, depth) || uses_binder(rhs, depth)
        }
        RTerm::Transp { family, base, .. } => {
            uses_binder(family, depth) || uses_binder(base, depth)
        }
        RTerm::HComp { ty, tube, base, .. } => {
            uses_binder(ty, depth) || uses_binder(tube, depth) || uses_binder(base, depth)
        }
        RTerm::Comp {
            family, tube, base, ..
        } => uses_binder(family, depth) || uses_binder(tube, depth) || uses_binder(base, depth),
        RTerm::Glue {
            base, ty, equiv, ..
        } => uses_binder(base, depth) || uses_binder(ty, depth) || uses_binder(equiv, depth),
        RTerm::GlueTerm { partial, base, .. } => {
            uses_binder(partial, depth) || uses_binder(base, depth)
        }
        RTerm::Unglue(g) => uses_binder(g, depth),
        RTerm::Delay(a) | RTerm::Now(a) | RTerm::Later(a) | RTerm::Force(a) | RTerm::EffTy(a) => {
            uses_binder(a, depth)
        }
        RTerm::Op { type_args, arg, .. } => {
            type_args.iter().any(|t| uses_binder(t, depth)) || uses_binder(arg, depth)
        }
        RTerm::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            uses_binder(body, depth)
                || uses_binder(return_clause, depth + 1)
                || op_clauses.iter().any(|(_, e)| uses_binder(e, depth + 2))
        }
        RTerm::IntPrim { lhs, rhs, .. } => uses_binder(lhs, depth) || uses_binder(rhs, depth),
        RTerm::IfZero {
            scrut,
            then_,
            else_,
            ..
        } => uses_binder(scrut, depth) || uses_binder(then_, depth) || uses_binder(else_, depth),
    }
}

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
        RTerm::Univ(l) => RValue::Univ(l.clone()),
        RTerm::Pi(g, dom, cod) => RValue::Pi(
            *g,
            Rc::new(eval(sig, env, dom)),
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
            Rc::new(eval(sig, env, dom)),
            Closure {
                env: env.clone(),
                body: Rc::new((**cod).clone()),
            },
        ),
        RTerm::Pair(a, b) => RValue::Pair(Rc::new(eval(sig, env, a)), Rc::new(eval(sig, env, b))),
        RTerm::Fst(p) => vfst(eval(sig, env, p)),
        RTerm::Snd(p) => vsnd(sig, eval(sig, env, p)),
        // Reflect a stuck result against its ascribed type so path boundaries (`@0`/`@1`) and
        // η for functions/pairs fire on ascribed neutrals — mirroring the kernel's `Term::Ann`
        // (`kernel/normalize.rs`). Dropping the annotation (the previous behavior) left a bare
        // neutral stuck, making recheck falsely *Reject* proofs the kernel accepts (soundness
        // audit 2026-07-03, R-P3).
        RTerm::Ann(e, ty) => match eval(sig, env, e) {
            RValue::Neutral(n) => reflect(sig, n, &eval(sig, env, ty)),
            other => other,
        },
        RTerm::Data(name, ps, is) => RValue::Data(
            name.clone(),
            Rc::new(ps.iter().map(|x| eval(sig, env, x)).collect()),
            Rc::new(is.iter().map(|x| eval(sig, env, x)).collect()),
        ),
        RTerm::Con(name, args) => RValue::Con(
            name.clone(),
            Rc::new(args.iter().map(|x| eval(sig, env, x)).collect()),
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
            lhs: Rc::new(eval(sig, env, lhs)),
            rhs: Rc::new(eval(sig, env, rhs)),
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

        // Univalence (spec §2.6), modeled independently (F1). CCHM boundary reductions: on a total
        // face the Glue *is* its glued type `T` (`ty`), on an empty face it *is* its base `A`
        // (`base`) — this is what makes `(ua e) @ i0 ≡ A` / `@ i1 ≡ B` hold definitionally. Only a
        // *proper* face survives as an `RValue::Glue`. Mirrors kernel `normalize.rs:426-450`.
        RTerm::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => {
            let cofib = crate::kan::resolve_cofib(env, cofib);
            if crate::kan::is_total(&cofib) {
                eval(sig, env, ty)
            } else if crate::kan::is_empty_face(&cofib) {
                eval(sig, env, base)
            } else {
                RValue::Glue {
                    base: Rc::new(eval(sig, env, base)),
                    cofib,
                    ty: Rc::new(eval(sig, env, ty)),
                    equiv: Rc::new(eval(sig, env, equiv)),
                }
            }
        }
        // `unglue`: project the base off a `Glue` value; the identity on the total/empty boundary
        // (where the glued value is already an `A`/`T`-value, not a `Glue`) and on a stuck neutral —
        // mirroring kernel `kan::unglue` exactly (recheck models no effect-neutrals to bubble).
        RTerm::Unglue(g) => match eval(sig, env, g) {
            RValue::Glue { base, .. } => crate::value::unshare_rvalue(base),
            other => other,
        },
        // `glue` introduction: on a boundary it collapses to `partial` (⊤) / `base` (⊥); off a proper
        // face it has no first-class value node (its only eliminator is `unglue`, which reduces via
        // the boundary above). The kernel has no `GlueTerm` eval arm at all — a bare `GlueTerm` in
        // value position is malformed there and hits eval's catch-all `todo!`; recheck instead reduces
        // the ⊤/⊥ boundary faces (to `partial`/`base`) and fail-safe-panics only off-boundary.
        // A proper-face `glue` intro value is not produced by any corpus judgement (`transp_glue` acts
        // on Glue *types*, not glue intros), so this stays fail-safe.
        RTerm::GlueTerm {
            cofib,
            partial,
            base,
        } => {
            let cofib = crate::kan::resolve_cofib(env, cofib);
            if crate::kan::is_total(&cofib) {
                eval(sig, env, partial)
            } else if crate::kan::is_empty_face(&cofib) {
                eval(sig, env, base)
            } else {
                unimplemented!(
                    "recheck eval: off-boundary `glue` introduction value is out of the implemented \
                     fragment (unreachable from the corpus — fail-safe, never an acceptance)"
                )
            }
        }

        RTerm::Delay(a) => RValue::Delay(Rc::new(eval(sig, env, a))),
        RTerm::Now(a) => RValue::Now(Rc::new(eval(sig, env, a))),
        RTerm::Later(d) => RValue::Later(Rc::new(eval(sig, env, d))),
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
            arg: Rc::new(eval(sig, env, arg)),
        }),
        RTerm::Handle {
            body,
            return_clause,
            op_clauses,
        } => RValue::Neutral(Neutral::Handle {
            env: env.clone(),
            body: Rc::new(eval(sig, env, body)),
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
        // `if-zero` (T1a): fold on a literal scrutinee (evaluating only the taken branch), else stay
        // stuck as a `Neutral::IfZero` — independently mirroring the kernel's `eval`.
        RTerm::IfZero {
            scrut,
            then_,
            else_,
        } => match eval(sig, env, scrut) {
            RValue::IntLit(0) => eval(sig, env, then_),
            RValue::IntLit(_) => eval(sig, env, else_),
            other => RValue::Neutral(Neutral::IfZero {
                scrut: Rc::new(other),
                then_: Rc::new(eval(sig, env, then_)),
                else_: Rc::new(eval(sig, env, else_)),
            }),
        },
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
                            lhs: Rc::new(lhs),
                            rhs: Rc::new(rhs),
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
            lhs: Rc::new(lhs),
            rhs: Rc::new(rhs),
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
            reflect(sig, Neutral::App(Rc::new(neutral), Rc::new(a)), &result_ty)
        }
        RValue::Neutral(n) => RValue::Neutral(Neutral::App(Rc::new(n), Rc::new(a))),
        other => panic!("apply: not a function: {other:?}"),
    }
}

/// First projection.
pub fn vfst(p: RValue) -> RValue {
    match p {
        RValue::Pair(a, _) => crate::value::unshare_rvalue(a),
        RValue::Neutral(n) => RValue::Neutral(Neutral::Fst(Rc::new(n))),
        other => panic!("vfst: not a pair: {other:?}"),
    }
}

/// Second projection.
pub fn vsnd(_sig: &Signature, p: RValue) -> RValue {
    match p {
        RValue::Pair(_, b) => crate::value::unshare_rvalue(b),
        RValue::Neutral(n) => RValue::Neutral(Neutral::Snd(Rc::new(n))),
        other => panic!("vsnd: not a pair: {other:?}"),
    }
}

/// Force a delay value (spec §4.5). `force (now a) ⇝ a`; `force (later d)` stays guarded; a
/// neutral reflects to a stuck `force`.
pub fn do_force(d: RValue) -> RValue {
    match d {
        RValue::Now(a) => crate::value::unshare_rvalue(a),
        RValue::Later(inner) => RValue::Force(Rc::new(RValue::Later(inner))),
        RValue::Neutral(n) => RValue::Neutral(Neutral::Force(Rc::new(n))),
        other => panic!("do_force: not a delay: {other:?}"),
    }
}

/// Path application (`p @ r`): β for path lambdas, boundary rules for reflected paths.
pub fn papp(sig: &Signature, p: RValue, r: RInterval) -> RValue {
    match p {
        RValue::PLam(clos) => clos.apply_dim(sig, r),
        RValue::ReflectedPath { neutral, lhs, rhs } => match nf_interval(&r) {
            RInterval::I0 => crate::value::unshare_rvalue(lhs),
            RInterval::I1 => crate::value::unshare_rvalue(rhs),
            other => RValue::Neutral(Neutral::PApp(Rc::new(neutral), other)),
        },
        RValue::Neutral(n) => RValue::Neutral(Neutral::PApp(Rc::new(n), nf_interval(&r))),
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
                    // N5: skip the eager IH when the method provably discards its IH binder —
                    // same idea as the kernel's do_elim, independently implemented (see the
                    // kernel twin's doc-comment for the sentinel/soundness argument).
                    let ih_dead = !dead_ih_disabled()
                        && matches!(&result,
                            RValue::Lam(clos) if !uses_binder(&clos.body, 0));
                    if ih_dead {
                        IH_DISCARDED.set(IH_DISCARDED.get() + 1);
                        result = apply(sig, result, RValue::Neutral(Neutral::Var(usize::MAX)));
                    } else {
                        IH_COMPUTED.set(IH_COMPUTED.get() + 1);
                        let ih = do_elim(sig, data, motive.clone(), methods.clone(), arg.clone());
                        result = apply(sig, result, ih);
                    }
                }
            }
            result
        }
        RValue::Neutral(n) => RValue::Neutral(Neutral::Elim {
            data: data.clone(),
            motive: Rc::new(motive),
            methods,
            scrutinee: Rc::new(n),
        }),
        RValue::ReflectedPath { neutral, .. } => RValue::Neutral(Neutral::Elim {
            data: data.clone(),
            motive: Rc::new(motive),
            methods,
            scrutinee: Rc::new(neutral),
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
            let fst = reflect(sig, Neutral::Fst(Rc::new(neutral.clone())), dom);
            let snd_ty = cod.apply(sig, fst.clone());
            let snd = reflect(sig, Neutral::Snd(Rc::new(neutral)), &snd_ty);
            RValue::Pair(Rc::new(fst), Rc::new(snd))
        }
        _ => RValue::Neutral(neutral),
    }
}

/// Quote a value back to a normal-form term at term-level `lvl` and dimension-level `dlvl`.
pub fn quote(sig: &Signature, lvl: usize, dlvl: usize, v: &RValue) -> RTerm {
    match v {
        RValue::Neutral(n) => quote_neutral(sig, lvl, dlvl, n),
        RValue::Univ(l) => RTerm::Univ(l.clone()),
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
                Neutral::App(Rc::new(neutral.clone()), Rc::new(arg)),
                &result_ty,
            );
            RTerm::Lam(Box::new(quote(sig, lvl + 1, dlvl, &body)))
        }
        RValue::Interval(r) => RTerm::Interval(nf_interval(r)),
        RValue::Glue {
            base,
            cofib,
            ty,
            equiv,
        } => RTerm::Glue {
            base: Box::new(quote(sig, lvl, dlvl, base)),
            cofib: cofib.clone(),
            ty: Box::new(quote(sig, lvl, dlvl, ty)),
            equiv: Box::new(quote(sig, lvl, dlvl, equiv)),
        },
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
        Neutral::IfZero {
            scrut,
            then_,
            else_,
        } => RTerm::IfZero {
            scrut: Box::new(quote(sig, lvl, dlvl, scrut)),
            then_: Box::new(quote(sig, lvl, dlvl, then_)),
            else_: Box::new(quote(sig, lvl, dlvl, else_)),
        },
    }
}

/// Quote an interval, converting dimension levels back to indices.
fn quote_interval(dlvl: usize, r: &RInterval) -> RInterval {
    match nf_interval(r) {
        RInterval::I0 => RInterval::I0,
        RInterval::I1 => RInterval::I1,
        // Injective level→index conversion (`dlvl - k - 1`), matching the kernel's `quote_interval`
        // (`kernel/normalize.rs`). `wrapping_sub` keeps it injective even when a dimension escaped
        // its binder (`k >= dlvl`, reachable via `family_is_constant`'s conv at `dlvl = 0`): the
        // wrapped values stay distinct, so `conv` never equates distinct stuck path apps. The
        // previous `saturating_sub` collapsed every escaped level to `Dim(0)` — a false-`Ok`
        // (soundness audit 2026-07-03, R-P1). For the valid case `k < dlvl` both agree (`dlvl-k-1`).
        RInterval::Dim(k) => RInterval::Dim(dlvl.wrapping_sub(k).wrapping_sub(1)),
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

#[cfg(test)]
mod rp3_tests {
    use super::*;

    /// R-P3 (soundness audit 2026-07-03): `eval` must reflect an ascribed neutral against its
    /// type so path boundaries fire — `(the (Path A x y) <stuck>) @ 0` reduces to `x`, mirroring
    /// the kernel (`kernel/normalize.rs` `Term::Ann`). Before the fix, recheck's `Ann` arm dropped
    /// the annotation, leaving a bare neutral whose `@ 0` stayed stuck — a spurious mismatch that
    /// made recheck falsely *Reject* proofs the kernel accepts (`flat_esc`, `spore_codegen_meta`).
    #[test]
    fn ann_reflects_path_neutral_so_boundary_fires() {
        let sig = Signature::empty();
        // Bind de Bruijn 0 to a stuck neutral variable.
        let env = Env::new().extend(RValue::Neutral(Neutral::Var(0)));
        // `(the (PathP (_.Univ0) (Univ 3) (Univ 7)) x0) @ 0`
        let path_ty = RTerm::PathP {
            family: Box::new(RTerm::Univ(crate::term::rlevel_of_nat(0))),
            lhs: Box::new(RTerm::Univ(crate::term::rlevel_of_nat(3))),
            rhs: Box::new(RTerm::Univ(crate::term::rlevel_of_nat(7))),
        };
        let term = RTerm::PApp(
            Box::new(RTerm::Ann(Box::new(RTerm::Var(0)), Box::new(path_ty))),
            RInterval::I0,
        );
        assert!(
            matches!(eval(&sig, &env, &term), RValue::Univ(ref l) if *l == crate::term::rlevel_of_nat(3)),
            "@0 through an ascribed path neutral must reduce to lhs (Univ 3)"
        );
    }

    /// The `@ 1` twin: the same ascription reduces to `rhs`.
    #[test]
    fn ann_reflects_path_neutral_rhs_boundary() {
        let sig = Signature::empty();
        let env = Env::new().extend(RValue::Neutral(Neutral::Var(0)));
        let path_ty = RTerm::PathP {
            family: Box::new(RTerm::Univ(crate::term::rlevel_of_nat(0))),
            lhs: Box::new(RTerm::Univ(crate::term::rlevel_of_nat(3))),
            rhs: Box::new(RTerm::Univ(crate::term::rlevel_of_nat(7))),
        };
        let term = RTerm::PApp(
            Box::new(RTerm::Ann(Box::new(RTerm::Var(0)), Box::new(path_ty))),
            RInterval::I1,
        );
        assert!(
            matches!(eval(&sig, &env, &term), RValue::Univ(ref l) if *l == crate::term::rlevel_of_nat(7))
        );
    }
}

#[cfg(test)]
mod rp1_tests {
    use super::*;

    /// R-P1 (soundness audit 2026-07-03): `quote_interval` must be injective. `family_is_constant`
    /// (`kan.rs`) convs at `dlvl = 0`, so a stuck path application carrying a dimension level from
    /// an outer scope is quoted with `k >= dlvl`. `dlvl.saturating_sub(1).saturating_sub(k)`
    /// collapsed all such to `Dim(0)` — so `conv` equated distinct stuck path apps (a genuinely
    /// non-constant family judged constant → mis-reduction → false-`Ok`). The valid in-scope case
    /// (`k < dlvl`) is unchanged; only the escaped case is repaired to stay injective.
    #[test]
    fn quote_interval_is_injective_on_escaped_dims() {
        assert_ne!(
            quote_interval(0, &RInterval::Dim(0)),
            quote_interval(0, &RInterval::Dim(1)),
            "distinct escaped dimensions must quote to distinct indices"
        );
        // In-scope quoting is unaffected: k < dlvl still gives dlvl - k - 1.
        assert_eq!(quote_interval(2, &RInterval::Dim(0)), RInterval::Dim(1));
        assert_eq!(quote_interval(2, &RInterval::Dim(1)), RInterval::Dim(0));
    }
}

#[cfg(test)]
mod glue_eval_tests {
    use super::*;
    use crate::term::{RCofib, RInterval};

    /// F1 (spec §2.6): the CCHM `Glue` boundary reductions in `eval` — `Glue A ⊤ T e ≡ T` and
    /// `Glue A ⊥ T e ≡ A`. `eval` applies these before any `RValue::Glue` is formed and never
    /// consults the `equiv` slot (an eval-irrelevant dummy here); a proper (non-constant) face
    /// instead survives as a distinct `RValue::Glue`. This is the plan's isolated step-3
    /// `Glue A ⊤ T e ≡ T` conversion test, complementing the end-to-end `ua` positive in
    /// `tests/recheck.rs`.
    #[test]
    fn glue_boundary_reductions_in_eval() {
        let sig = Signature::new();
        let env = Env::new();
        let a = || Box::new(RTerm::Univ(crate::term::rlevel_of_nat(0))); // A = Type 0
        let t = || Box::new(RTerm::IntTy); // T = Int, distinct from A
        let eq = || Box::new(RTerm::Univ(crate::term::rlevel_of_nat(5))); // equiv slot: eval-irrelevant
        let glue = |cofib| RTerm::Glue {
            base: a(),
            cofib,
            ty: t(),
            equiv: eq(),
        };
        let cv = |x: &RValue, y: &RValue| crate::conv::conv(&sig, 0, 0, x, y);

        // ⊤ collapses to the glued type T; ⊥ collapses to the base A; the two are NOT interchanged.
        assert!(cv(
            &eval(&sig, &env, &glue(RCofib::Top)),
            &eval(&sig, &env, &t())
        ));
        assert!(cv(
            &eval(&sig, &env, &glue(RCofib::Bot)),
            &eval(&sig, &env, &a())
        ));
        assert!(!cv(
            &eval(&sig, &env, &glue(RCofib::Top)),
            &eval(&sig, &env, &a())
        ));

        // A proper (non-constant) face survives as a distinct `Glue` value, collapsed to neither.
        let env_i = env.extend_dim(RInterval::Dim(0));
        let proper = eval(&sig, &env_i, &glue(RCofib::Eq0(RInterval::Dim(0))));
        assert!(matches!(proper, RValue::Glue { .. }));
    }
}

#[cfg(test)]
mod n5_tests {
    use super::*;
    use crate::term::{RCofib, RGrade, RInterval};

    /// N5: the independent engine's `uses_binder` mirror, pinned arm-by-arm exactly like the
    /// kernel twin (`blight_kernel::normalize::tests::uses_binder_pins_every_arm_and_shift`) —
    /// the mutation sweep showed every `||` and `+1`/`+2` here was mutable unnoticed too. One
    /// probe per field of every multi-field arm (kills `||`→`&&`), shift probes at depth 1
    /// distinguishing `+1` from `-1`/`×1`, and the dimension-binder no-shift pin.
    #[test]
    fn uses_binder_pins_every_arm_and_shift() {
        let z = || Box::new(RTerm::Univ(crate::term::rlevel_of_nat(0)));
        let v = |i: usize| Box::new(RTerm::Var(i));
        let d = 1usize;

        assert!(uses_binder(&RTerm::Var(1), d));
        assert!(!uses_binder(&RTerm::Var(0), d));
        assert!(!uses_binder(&RTerm::Var(2), d));

        for (label, shifted_uses, shifted_not) in [
            (
                "Pi cod",
                RTerm::Pi(RGrade::Omega, z(), v(2)),
                RTerm::Pi(RGrade::Omega, z(), v(1)),
            ),
            ("Lam body", RTerm::Lam(v(2)), RTerm::Lam(v(1))),
            (
                "Sigma snd",
                RTerm::Sigma(z(), v(2)),
                RTerm::Sigma(z(), v(1)),
            ),
        ] {
            assert!(
                uses_binder(&shifted_uses, d),
                "{label}: Var(d+1) under the binder"
            );
            assert!(
                !uses_binder(&shifted_not, d),
                "{label}: Var(d) under the binder differs"
            );
        }
        assert!(
            uses_binder(&RTerm::Pi(RGrade::Omega, v(1), z()), d),
            "Pi dom unshifted"
        );
        assert!(
            uses_binder(&RTerm::Sigma(v(1), z()), d),
            "Sigma fst unshifted"
        );

        let handle = |body: Box<RTerm>, ret: Box<RTerm>, cl: Box<RTerm>| RTerm::Handle {
            body,
            return_clause: ret,
            op_clauses: vec![("op".to_string(), cl)],
        };
        assert!(
            uses_binder(&handle(v(1), z(), z()), d),
            "Handle body unshifted"
        );
        assert!(uses_binder(&handle(z(), v(2), z()), d), "Handle return +1");
        assert!(
            uses_binder(&handle(z(), z(), v(3)), d),
            "Handle op clause +2"
        );
        assert!(
            !uses_binder(&handle(z(), v(1), z()), d),
            "Handle return: Var(d) differs"
        );
        assert!(
            !uses_binder(&handle(z(), z(), v(2)), d),
            "Handle clause: Var(d+1) differs"
        );

        assert!(
            uses_binder(&RTerm::PLam(v(1)), d),
            "PLam binds a dimension, not a term var"
        );

        let probes: Vec<(&str, RTerm)> = vec![
            ("App lhs", RTerm::App(v(1), z())),
            ("App rhs", RTerm::App(z(), v(1))),
            ("Pair lhs", RTerm::Pair(v(1), z())),
            ("Pair rhs", RTerm::Pair(z(), v(1))),
            ("Ann lhs", RTerm::Ann(v(1), z())),
            ("Ann rhs", RTerm::Ann(z(), v(1))),
            ("Fst", RTerm::Fst(v(1))),
            ("Snd", RTerm::Snd(v(1))),
            ("PApp", RTerm::PApp(v(1), RInterval::I0)),
            (
                "Data params",
                RTerm::Data(
                    blight_kernel::DataName("D".to_string()),
                    vec![RTerm::Var(1)],
                    vec![],
                ),
            ),
            (
                "Data indices",
                RTerm::Data(
                    blight_kernel::DataName("D".to_string()),
                    vec![],
                    vec![RTerm::Var(1)],
                ),
            ),
            (
                "Con args",
                RTerm::Con(blight_kernel::ConName("c".to_string()), vec![RTerm::Var(1)]),
            ),
            (
                "Elim motive",
                RTerm::Elim {
                    data: blight_kernel::DataName("D".to_string()),
                    motive: v(1),
                    methods: vec![],
                    scrutinee: z(),
                },
            ),
            (
                "Elim methods",
                RTerm::Elim {
                    data: blight_kernel::DataName("D".to_string()),
                    motive: z(),
                    methods: vec![RTerm::Var(1)],
                    scrutinee: z(),
                },
            ),
            (
                "Elim scrutinee",
                RTerm::Elim {
                    data: blight_kernel::DataName("D".to_string()),
                    motive: z(),
                    methods: vec![],
                    scrutinee: v(1),
                },
            ),
            (
                "PathP family",
                RTerm::PathP {
                    family: v(1),
                    lhs: z(),
                    rhs: z(),
                },
            ),
            (
                "PathP lhs",
                RTerm::PathP {
                    family: z(),
                    lhs: v(1),
                    rhs: z(),
                },
            ),
            (
                "PathP rhs",
                RTerm::PathP {
                    family: z(),
                    lhs: z(),
                    rhs: v(1),
                },
            ),
            (
                "Transp family",
                RTerm::Transp {
                    family: v(1),
                    cofib: RCofib::Top,
                    base: z(),
                },
            ),
            (
                "Transp base",
                RTerm::Transp {
                    family: z(),
                    cofib: RCofib::Top,
                    base: v(1),
                },
            ),
            (
                "HComp ty",
                RTerm::HComp {
                    ty: v(1),
                    cofib: RCofib::Top,
                    tube: z(),
                    base: z(),
                },
            ),
            (
                "HComp tube",
                RTerm::HComp {
                    ty: z(),
                    cofib: RCofib::Top,
                    tube: v(1),
                    base: z(),
                },
            ),
            (
                "HComp base",
                RTerm::HComp {
                    ty: z(),
                    cofib: RCofib::Top,
                    tube: z(),
                    base: v(1),
                },
            ),
            (
                "Comp family",
                RTerm::Comp {
                    family: v(1),
                    cofib: RCofib::Top,
                    tube: z(),
                    base: z(),
                },
            ),
            (
                "Comp tube",
                RTerm::Comp {
                    family: z(),
                    cofib: RCofib::Top,
                    tube: v(1),
                    base: z(),
                },
            ),
            (
                "Comp base",
                RTerm::Comp {
                    family: z(),
                    cofib: RCofib::Top,
                    tube: z(),
                    base: v(1),
                },
            ),
            (
                "Op type_args",
                RTerm::Op {
                    effect: blight_kernel::row::EffName::new("E"),
                    op: "o".to_string(),
                    type_args: vec![RTerm::Var(1)],
                    arg: z(),
                },
            ),
            (
                "Op arg",
                RTerm::Op {
                    effect: blight_kernel::row::EffName::new("E"),
                    op: "o".to_string(),
                    type_args: vec![],
                    arg: v(1),
                },
            ),
            ("EffTy", RTerm::EffTy(v(1))),
            ("Delay", RTerm::Delay(v(1))),
            ("Now", RTerm::Now(v(1))),
            ("Later", RTerm::Later(v(1))),
            ("Force", RTerm::Force(v(1))),
            (
                "IntPrim lhs",
                RTerm::IntPrim {
                    op: blight_kernel::IntPrimOp::Add,
                    lhs: v(1),
                    rhs: z(),
                },
            ),
            (
                "IntPrim rhs",
                RTerm::IntPrim {
                    op: blight_kernel::IntPrimOp::Add,
                    lhs: z(),
                    rhs: v(1),
                },
            ),
            (
                "IfZero scrut",
                RTerm::IfZero {
                    scrut: v(1),
                    then_: z(),
                    else_: z(),
                },
            ),
            (
                "IfZero then_",
                RTerm::IfZero {
                    scrut: z(),
                    then_: v(1),
                    else_: z(),
                },
            ),
            (
                "IfZero else_",
                RTerm::IfZero {
                    scrut: z(),
                    then_: z(),
                    else_: v(1),
                },
            ),
        ];
        for (label, t) in &probes {
            assert!(
                uses_binder(t, d),
                "{label}: the single using field must be found"
            );
        }
        assert!(!uses_binder(&RTerm::Univ(crate::term::rlevel_of_nat(0)), d));
        assert!(!uses_binder(&RTerm::IntTy, d));
    }
}
