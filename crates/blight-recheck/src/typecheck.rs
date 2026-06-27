//! The independent bidirectional checker over values: `infer`/`check` with the kernel's
//! grade-usage discipline, but a wholly separate implementation built on this crate's value-based
//! NbE. Free variables are reflected against their types so η and path boundaries fire correctly.

use crate::conv::{conv, fresh_var, subtype};
use crate::normalize::{apply, eval, quote};
use crate::term::{RGrade, RInterval, RTerm};
use crate::value::{Env, RValue};
use crate::RecheckError;
use blight_kernel::signature::{Arg, Constructor, DataDecl, Signature};
use blight_kernel::DataName;

type RResult<T> = Result<T, RecheckError>;

fn reject(msg: impl Into<String>) -> RecheckError {
    RecheckError::Rejected(msg.into())
}

/// An *honest refusal*: the judgement uses a construct outside the supported core fragment, so the
/// re-checker neither accepts nor (unsoundly) rejects it. The build treats this as "not re-checked"
/// rather than a soundness alarm.
fn decline(msg: impl Into<String>) -> RecheckError {
    RecheckError::Declined(msg.into())
}

/// A usage vector: demand on each in-scope variable (index 0 = innermost).
#[derive(Debug, Clone)]
struct Usage(Vec<RGrade>);

impl Usage {
    fn zero(n: usize) -> Self {
        Usage(vec![RGrade::Zero; n])
    }
    fn unit(i: usize, n: usize, sigma: RGrade) -> Self {
        let mut v = vec![RGrade::Zero; n];
        if i < n {
            v[i] = sigma;
        }
        Usage(v)
    }
    fn add(&self, other: &Usage) -> Usage {
        Usage(
            self.0
                .iter()
                .zip(&other.0)
                .map(|(a, b)| a.add(*b))
                .collect(),
        )
    }
    fn pop(&self) -> (RGrade, Usage) {
        let mut v = self.0.clone();
        let head = if v.is_empty() {
            RGrade::Zero
        } else {
            v.remove(0)
        };
        (head, Usage(v))
    }
    /// Keep only the demand on the innermost-... outermost `n` ambient variables, dropping the
    /// leading entries that correspond to locally-introduced (method) binders.
    fn truncate(&self, n: usize) -> Usage {
        let len = self.0.len();
        if n >= len {
            Usage(self.0.clone())
        } else {
            Usage(self.0[len - n..].to_vec())
        }
    }
}

/// One term-binder context entry: its *type as a value*, and the binder grade.
#[derive(Debug, Clone)]
struct Entry {
    ty: RValue,
    #[allow(dead_code)]
    grade: RGrade,
}

/// The typing context: a list of term entries (index 0 = innermost), the evaluation environment
/// that binds each as a reflected fresh variable, and dimension counters.
#[derive(Clone)]
struct Ctx {
    entries: Vec<Entry>, // innermost-first
    env: Env,            // value environment (term + dim bindings)
    lvl: usize,          // number of term binders (de Bruijn level depth)
    dlvl: usize,         // number of dimension binders
}

impl Ctx {
    fn empty() -> Self {
        Ctx {
            entries: Vec::new(),
            env: Env::new(),
            lvl: 0,
            dlvl: 0,
        }
    }

    fn len(&self) -> usize {
        self.entries.len()
    }

    /// Extend with a term binder of value-type `ty` at grade `g`, binding it in the environment as
    /// a reflected fresh variable at the current level.
    fn extend(&self, sig: &Signature, ty: RValue, g: RGrade) -> Ctx {
        let fresh = fresh_var(sig, self.lvl, &ty);
        let mut entries = self.entries.clone();
        entries.insert(0, Entry { ty, grade: g });
        Ctx {
            entries,
            env: self.env.extend(fresh),
            lvl: self.lvl + 1,
            dlvl: self.dlvl,
        }
    }

    /// Extend with a term binder whose environment value is `val` (rather than a fresh variable):
    /// used by dependent pattern matching to bind a constructor argument that unification has
    /// *forced* to a specific value, while still recording the binder's declared type.
    fn extend_with(&self, _sig: &Signature, ty: RValue, g: RGrade, val: RValue) -> Ctx {
        let mut entries = self.entries.clone();
        entries.insert(0, Entry { ty, grade: g });
        Ctx {
            entries,
            env: self.env.extend(val),
            lvl: self.lvl + 1,
            dlvl: self.dlvl,
        }
    }

    /// Extend with a dimension binder, binding a fresh dimension level in the environment.
    fn extend_dim(&self) -> Ctx {
        Ctx {
            entries: self.entries.clone(),
            env: self.env.extend_dim(RInterval::Dim(self.dlvl)),
            lvl: self.lvl,
            dlvl: self.dlvl + 1,
        }
    }

    fn lookup(&self, i: usize) -> Option<RValue> {
        self.entries.get(i).map(|e| e.ty.clone())
    }

    /// Apply per-branch ambient index specializations `(level, value)`: rebind those levels in the
    /// environment so subsequent evaluation sees the refined indices (dependent pattern matching).
    fn refine_ambient(&self, ambient: &[(usize, RValue)]) -> Ctx {
        let mut c = self.clone();
        for (lvl, v) in ambient {
            c.env = c.env.set_level(*lvl, v.clone());
        }
        c
    }
}

/// The re-checker over a fixed signature.
pub struct Recheck<'a> {
    sig: &'a Signature,
}

impl<'a> Recheck<'a> {
    pub fn new(sig: &'a Signature) -> Self {
        Recheck { sig }
    }

    /// Top-level re-check: `term : ty` in the empty context, demanded once.
    pub fn check_top(&self, term: &RTerm, ty: &RTerm) -> RResult<()> {
        let ctx = Ctx::empty();
        self.infer_universe(&ctx, ty)?;
        let ty_val = eval(self.sig, &ctx.env, ty);
        let _u = self.check(&ctx, term, &ty_val, RGrade::One)?;
        Ok(())
    }

    /// Infer the (value) type of `term` and its usage vector, at ambient demand `sigma`.
    fn infer(&self, ctx: &Ctx, term: &RTerm, sigma: RGrade) -> RResult<(RValue, Usage)> {
        let n = ctx.len();
        match term {
            RTerm::Var(i) => {
                let ty = ctx
                    .lookup(*i)
                    .ok_or_else(|| reject(format!("unbound de Bruijn index {i}")))?;
                Ok((ty, Usage::unit(*i, n, sigma)))
            }
            RTerm::Univ(l) => Ok((RValue::Univ(l + 1), Usage::zero(n))),
            RTerm::Pi(grade, dom, cod) => {
                let dl = self.infer_universe(ctx, dom)?;
                let dom_v = eval(self.sig, &ctx.env, dom);
                let ctx2 = ctx.extend(self.sig, dom_v, *grade);
                let cl = self.infer_universe(&ctx2, cod)?;
                Ok((RValue::Univ(dl.max(cl)), Usage::zero(n)))
            }
            RTerm::Sigma(dom, cod) => {
                let dl = self.infer_universe(ctx, dom)?;
                let dom_v = eval(self.sig, &ctx.env, dom);
                let ctx2 = ctx.extend(self.sig, dom_v, RGrade::Omega);
                let cl = self.infer_universe(&ctx2, cod)?;
                Ok((RValue::Univ(dl.max(cl)), Usage::zero(n)))
            }
            RTerm::App(f, a) => {
                let (f_ty, usage_f) = self.infer(ctx, f, sigma)?;
                match f_ty {
                    RValue::Pi(rho, dom, cod) => {
                        let usage_a = self.check(ctx, a, &dom, sigma.mul(rho))?;
                        let a_val = eval(self.sig, &ctx.env, a);
                        let result = cod.apply(self.sig, a_val);
                        Ok((result, usage_f.add(&usage_a)))
                    }
                    other => Err(reject(format!("applied a non-function of type {other:?}"))),
                }
            }
            RTerm::Fst(p) => {
                let (p_ty, usage) = self.infer(ctx, p, sigma)?;
                match p_ty {
                    RValue::Sigma(dom, _cod) => Ok((*dom, usage)),
                    other => Err(reject(format!("Fst of a non-pair of type {other:?}"))),
                }
            }
            RTerm::Snd(p) => {
                let (p_ty, usage) = self.infer(ctx, p, sigma)?;
                match p_ty {
                    RValue::Sigma(_dom, cod) => {
                        let p_val = eval(self.sig, &ctx.env, p);
                        let fst = crate::normalize::vfst(p_val);
                        Ok((cod.apply(self.sig, fst), usage))
                    }
                    other => Err(reject(format!("Snd of a non-pair of type {other:?}"))),
                }
            }
            RTerm::Ann(t, ty) => {
                self.infer_universe(ctx, ty)?;
                let ty_v = eval(self.sig, &ctx.env, ty);
                let usage = self.check(ctx, t, &ty_v, sigma)?;
                Ok((ty_v, usage))
            }
            RTerm::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => self.infer_elim(ctx, data, motive, methods, scrutinee, sigma),
            RTerm::PApp(p, r) => {
                let (p_ty, usage) = self.infer(ctx, p, sigma)?;
                match p_ty {
                    RValue::PathP { family, .. } => {
                        let r_v = crate::normalize::eval_interval(&ctx.env, r);
                        Ok((family.apply_dim(self.sig, r_v), usage))
                    }
                    other => Err(reject(format!("path-applied a non-path of type {other:?}"))),
                }
            }
            RTerm::PathP { family, lhs, rhs } => {
                let ctx_dim = ctx.extend_dim();
                let l = self.infer_universe(&ctx_dim, family)?;
                // Endpoints inhabit the family at 0 and 1.
                let fam0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, family)
                };
                let fam1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, family)
                };
                self.check(ctx, lhs, &fam0, RGrade::Zero)?;
                self.check(ctx, rhs, &fam1, RGrade::Zero)?;
                Ok((RValue::Univ(l), Usage::zero(n)))
            }
            RTerm::Data(name, _ps, _is) => {
                let decl = self
                    .sig
                    .get(name)
                    .ok_or_else(|| reject(format!("unknown inductive type {name:?}")))?;
                Ok((RValue::Univ(decl.level), Usage::zero(n)))
            }
            RTerm::Lam(_) | RTerm::Pair(_, _) | RTerm::Con(_, _) | RTerm::PLam(_) => Err(reject(
                format!("term needs a type annotation to be inferred: {term:?}"),
            )),
            RTerm::Interval(_) => Err(reject("a bare interval has no type in the term layer")),

            // Cubical Kan operations: re-derive the result type independently (the kernel already
            // checked the inputs; we re-evaluate the family/endpoints to read off the conclusion).
            // `Transp (i.A) φ a0 : A i1`; `HComp A φ u a0 : A`; `Comp (i.A) φ u a0 : A i1`.
            // The base inhabits the *source* type (`A i0` for transp/comp, `A` for hcomp), so we
            // **check** it there (it may be a bare constructor needing the expected type) and read
            // the conclusion off the *target* (`A i1` / `A`).
            RTerm::Transp { family, base, .. } => {
                let ctx_dim = ctx.extend_dim();
                self.infer_universe(&ctx_dim, family)?;
                let ty_at_0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, family)
                };
                let b_usage = self.check(ctx, base, &ty_at_0, sigma)?;
                let ty_at_1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, family)
                };
                Ok((ty_at_1, b_usage))
            }
            RTerm::HComp { ty, base, .. } => {
                self.infer_universe(ctx, ty)?;
                let ty_val = eval(self.sig, &ctx.env, ty);
                let b_usage = self.check(ctx, base, &ty_val, sigma)?;
                Ok((ty_val, b_usage))
            }
            RTerm::Comp { family, base, .. } => {
                let ctx_dim = ctx.extend_dim();
                self.infer_universe(&ctx_dim, family)?;
                let ty_at_0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, family)
                };
                let b_usage = self.check(ctx, base, &ty_at_0, sigma)?;
                let ty_at_1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, family)
                };
                Ok((ty_at_1, b_usage))
            }

            // Partiality (spec §4.5), modeled independently. We re-derive only the *types*; the
            // re-checker does not track effect rows, so the proof-boundary `Partial` discipline
            // (which the kernel enforces) is intentionally not re-modeled here.
            // `Delay A : Univ ℓ` when `A : Univ ℓ`.
            RTerm::Delay(a) => {
                let l = self.infer_universe(ctx, a)?;
                Ok((RValue::Univ(l), Usage::zero(n)))
            }
            // `now a : Delay A` where `A` is the inferred type of `a`.
            RTerm::Now(a) => {
                let (a_ty, usage) = self.infer(ctx, a, sigma)?;
                Ok((RValue::Delay(Box::new(a_ty)), usage))
            }
            // `later d : Delay A` where `d : Delay A` (the inferred type of `d` is already a Delay).
            RTerm::Later(d) => {
                let (d_ty, usage) = self.infer(ctx, d, sigma)?;
                match d_ty {
                    RValue::Delay(_) => Ok((d_ty, usage)),
                    other => Err(reject(format!("`later` of a non-Delay of type {other:?}"))),
                }
            }
            // `force d : A` when `d : Delay A`.
            RTerm::Force(d) => {
                let (d_ty, usage) = self.infer(ctx, d, sigma)?;
                match d_ty {
                    RValue::Delay(inner) => Ok((*inner, usage)),
                    other => Err(reject(format!("`force` of a non-Delay of type {other:?}"))),
                }
            }

            // Effects and handlers (spec §4), modeled at the TYPE LEVEL only (M7). The re-checker
            // re-derives the *types* via the signature's operation signatures, ignoring effect rows
            // and continuation grades (the kernel's soundness responsibility) — the same honest
            // precedent the partiality layer above follows.
            // `! E A : Univ ℓ` when `A : Univ ℓ` (the row is dropped at translation time).
            RTerm::EffTy(a) => {
                let l = self.infer_universe(ctx, a)?;
                Ok((RValue::Univ(l), Usage::zero(n)))
            }
            // `perform op a`: look up the op; check `a` against `param_ty`; the type is
            // `result_ty[a/x]` (the result type evaluated with the arg bound at de Bruijn 0).
            RTerm::Op { effect, op, arg } => {
                let (eff, opsig) = self
                    .sig
                    .op_of(op)
                    .ok_or_else(|| reject(format!("unknown operation {op:?}")))?;
                if &eff.name != effect {
                    return Err(reject(format!(
                        "operation {op:?} belongs to effect {:?}, not {effect:?}",
                        eff.name
                    )));
                }
                // Translate and evaluate the op's parameter/result types (closed kernel terms).
                let param_rt = crate::term::from_kernel(&opsig.param_ty)?;
                let result_rt = crate::term::from_kernel(&opsig.result_ty)?;
                let param_val = eval(self.sig, &Env::new(), &param_rt);
                let usage = self.check(ctx, arg, &param_val, sigma)?;
                // `result_ty` mentions the parameter as de Bruijn 0: evaluate it in an env that
                // binds the argument's value.
                let arg_val = eval(self.sig, &ctx.env, arg);
                let result_env = Env::new().extend(arg_val);
                let result_val = eval(self.sig, &result_env, &result_rt);
                Ok((result_val, usage))
            }
            // `handle body { return x. r ; (op x k. e)... }`: infer body's type `A`; the return
            // clause binds `x:A` and infers the result type `C`; each op clause is checked against
            // `C` under `x:Aᵢ`, `k:Π(_:Bᵢ).C`. The Handle's type is `C`. Rows and continuation
            // grades are ignored (the kernel checks those).
            RTerm::Handle {
                body,
                return_clause,
                op_clauses,
            } => self.infer_handle(ctx, body, return_clause, op_clauses, sigma),

            // ---- primitive machine integers (M11) ----
            RTerm::IntTy => Ok((RValue::Univ(0), Usage::zero(n))),
            RTerm::IntLit(_) => Ok((RValue::IntTy, Usage::zero(n))),
            RTerm::IntPrim { lhs, rhs, .. } => {
                let ul = self.check(ctx, lhs, &RValue::IntTy, sigma)?;
                let ur = self.check(ctx, rhs, &RValue::IntTy, sigma)?;
                Ok((RValue::IntTy, ul.add(&ur)))
            }
        }
    }

    /// Infer a term that must be a type, returning its universe level.
    fn infer_universe(&self, ctx: &Ctx, ty: &RTerm) -> RResult<u32> {
        let (k, _u) = self.infer(ctx, ty, RGrade::Zero)?;
        match k {
            RValue::Univ(l) => Ok(l),
            other => Err(reject(format!(
                "expected a type (Univ ℓ) but found {other:?}"
            ))),
        }
    }

    /// Re-derive a `handle`'s result type `C` (spec §4.3), an independent port of the kernel's
    /// `Handle` rule with the row-discharge and continuation-grade checks dropped (the re-checker
    /// does not track rows/grades). Infer the body's type `A`; bind `x:A` and infer the return
    /// clause's type `C`; for each op clause bind `x:Aᵢ` then `k:Π(_:Bᵢ).C` and check the clause
    /// body against `C`. The Handle's type is `C`.
    fn infer_handle(
        &self,
        ctx: &Ctx,
        body: &RTerm,
        return_clause: &RTerm,
        op_clauses: &[(blight_kernel::signature::OpName, Box<RTerm>)],
        sigma: RGrade,
    ) -> RResult<(RValue, Usage)> {
        // 1. Infer the body's type `A`.
        let (body_ty, body_usage) = self.infer(ctx, body, sigma)?;

        // 2. Return clause: bind `x : A`, infer its type `C`.
        let ctx_ret = ctx.extend(self.sig, body_ty, sigma);
        let (c_ty, ret_usage) = self.infer(&ctx_ret, return_clause, sigma)?;
        // `C` must live at `ctx.len()` (it may not mention the bound `x`); quote it there and
        // re-evaluate in the ambient env so it is reusable under the op clauses' binders.
        let c_term = quote(self.sig, ctx.lvl, ctx.dlvl, &c_ty);
        let c_val = eval(self.sig, &ctx.env, &c_term);
        let (_demand_x, ret_usage) = ret_usage.pop();
        let mut total_usage = body_usage.add(&ret_usage);

        // 3. Operation clauses: each binds `x:Aᵢ` (the op parameter) then `k:Π(_:Bᵢ).C`.
        for (op, clause) in op_clauses.iter() {
            let (_eff, opsig) = self
                .sig
                .op_of(op)
                .ok_or_else(|| reject(format!("handler clause for unknown operation {op:?}")))?;
            let param_rt = crate::term::from_kernel(&opsig.param_ty)?;
            let result_rt = crate::term::from_kernel(&opsig.result_ty)?;
            // `Aᵢ` is closed over the ambient context.
            let param_val = eval(self.sig, &Env::new(), &param_rt);
            let ctx_x = ctx.extend(self.sig, param_val, sigma);
            // `Bᵢ = result_ty[x]` lives in `x:Aᵢ`'s scope (de Bruijn 0 = x). Build the
            // continuation type `k : Π(_:Bᵢ). C` (where `C` is weakened past the `x` binder by 1,
            // becoming weakened by 2 inside the Pi's codomain), evaluate it in `ctx_x`'s env.
            let k_dom_val = eval(self.sig, &ctx_x.env, &result_rt);
            // The continuation's codomain ignores its own binder: it is `C` shifted past `x`+`_`.
            let cod_closure_body = shift_free(&c_term, 2);
            let k_ty = RValue::Pi(
                RGrade::Omega,
                Box::new(k_dom_val),
                crate::value::Closure {
                    env: ctx_x.env.clone(),
                    body: std::rc::Rc::new(cod_closure_body),
                },
            );
            let ctx_xk = ctx_x.extend(self.sig, k_ty, RGrade::Omega);
            // Check the clause body against `C` (under the two binders `x`, `k`). `C` is closed at
            // `ctx.len()`, so it is invariant under the extra binders when evaluated in `ctx`'s env.
            let c_val_xk = c_val.clone();
            let clause_usage = self.check(&ctx_xk, clause, &c_val_xk, sigma)?;
            // Pop the two binders (`k` then `x`); the re-checker ignores the continuation grade.
            let (_demand_k, clause_usage) = clause_usage.pop();
            let (_demand_x, clause_usage) = clause_usage.pop();
            total_usage = total_usage.add(&clause_usage);
        }

        Ok((c_val, total_usage))
    }

    /// Check `term` against expected value-type `expected` at ambient demand `sigma`.
    fn check(&self, ctx: &Ctx, term: &RTerm, expected: &RValue, sigma: RGrade) -> RResult<Usage> {
        match (term, expected) {
            (RTerm::Lam(body), RValue::Pi(grade, dom, cod)) => {
                let ctx2 = ctx.extend(self.sig, (**dom).clone(), *grade);
                // The bound variable's value in the extended env is the fresh var at ctx.lvl.
                let fresh = fresh_var(self.sig, ctx.lvl, dom);
                let cod_inst = cod.apply(self.sig, fresh);
                let body_usage = self.check(&ctx2, body, &cod_inst, sigma)?;
                let (demand_x, rest) = body_usage.pop();
                if !demand_x.leq(*grade) {
                    return Err(reject(format!(
                        "λ-binder at grade {grade:?} but body demands it at {demand_x:?}"
                    )));
                }
                Ok(rest)
            }
            (RTerm::Pair(a, b), RValue::Sigma(dom, cod)) => {
                let usage_a = self.check(ctx, a, dom, sigma)?;
                let a_val = eval(self.sig, &ctx.env, a);
                let cod_inst = cod.apply(self.sig, a_val);
                let usage_b = self.check(ctx, b, &cod_inst, sigma)?;
                Ok(usage_a.add(&usage_b))
            }
            (RTerm::Con(name, args), RValue::Data(d_name, params, exp_indices)) => {
                self.check_con(ctx, name, args, d_name, params, exp_indices, sigma)
            }
            // `now a : Delay A` — check the payload against `A` (so a bare-constructor payload is
            // accepted, mirroring `Con`/`Pair` checking). `later d : Delay A` — check `d` against
            // the same `Delay A`.
            (RTerm::Now(a), RValue::Delay(inner)) => self.check(ctx, a, inner, sigma),
            (RTerm::Later(d), RValue::Delay(_)) => self.check(ctx, d, expected, sigma),
            (RTerm::PLam(body), RValue::PathP { family, lhs, rhs }) => {
                let ctx_dim = ctx.extend_dim();
                let fam_at_i = family.apply_dim(self.sig, RInterval::Dim(ctx.dlvl));
                let body_usage = self.check(&ctx_dim, body, &fam_at_i, sigma)?;
                // Boundary: body[0/i] ≡ lhs, body[1/i] ≡ rhs.
                let b0 = {
                    let e = ctx.env.extend_dim(RInterval::I0);
                    eval(self.sig, &e, body)
                };
                let b1 = {
                    let e = ctx.env.extend_dim(RInterval::I1);
                    eval(self.sig, &e, body)
                };
                if !conv(self.sig, ctx.lvl, ctx.dlvl, &b0, lhs) {
                    return Err(reject("path lhs boundary mismatch"));
                }
                if !conv(self.sig, ctx.lvl, ctx.dlvl, &b1, rhs) {
                    return Err(reject("path rhs boundary mismatch"));
                }
                Ok(body_usage)
            }
            _ => {
                let (actual, usage) = self.infer(ctx, term, sigma)?;
                if subtype(self.sig, ctx.lvl, ctx.dlvl, &actual, expected) {
                    Ok(usage)
                } else {
                    Err(reject(format!(
                        "type mismatch: inferred {actual:?} but expected {expected:?}"
                    )))
                }
            }
        }
    }

    /// Check a constructor application against an expected `Data` family (spec §2.7).
    #[allow(clippy::too_many_arguments)]
    fn check_con(
        &self,
        ctx: &Ctx,
        name: &blight_kernel::ConName,
        args: &[RTerm],
        d_name: &DataName,
        params: &[RValue],
        exp_indices: &[RValue],
        sigma: RGrade,
    ) -> RResult<Usage> {
        let (decl, _idx, ctor) = self
            .sig
            .data_of_con(name)
            .ok_or_else(|| reject(format!("unknown constructor {name:?}")))?;
        let decl = decl.clone();
        let ctor = ctor.clone();
        if &decl.name != d_name {
            return Err(reject(format!(
                "constructor {name:?} belongs to {:?}, not {d_name:?}",
                decl.name
            )));
        }
        if args.len() != ctor.args.len() {
            return Err(reject(format!(
                "constructor {name:?} expects {} args, got {}",
                ctor.args.len(),
                args.len()
            )));
        }
        // Local value env for arg/index types: params bound outermost, then each checked arg value.
        let mut env = Env::new();
        for p in params {
            env = env.extend(p.clone());
        }
        let mut usage = Usage::zero(ctx.len());
        for (arg, shape) in args.iter().zip(ctor.args.iter()) {
            match shape {
                Arg::Rec(rec_indices) => {
                    let rec_index_vals: Vec<RValue> = rec_indices
                        .iter()
                        .map(|t| {
                            let rt = crate::term::from_kernel(t)?;
                            Ok::<RValue, RecheckError>(eval(self.sig, &env, &rt))
                        })
                        .collect::<RResult<_>>()?;
                    let rec_ty = RValue::Data(decl.name.clone(), params.to_vec(), rec_index_vals);
                    let u = self.check(ctx, arg, &rec_ty, sigma)?;
                    usage = usage.add(&u);
                }
                Arg::NonRec(ty) => {
                    let ty_t = crate::term::from_kernel(ty)?;
                    let ty_val = eval(self.sig, &env, &ty_t);
                    let u = self.check(ctx, arg, &ty_val, sigma)?;
                    usage = usage.add(&u);
                }
            }
            let arg_val = eval(self.sig, &ctx.env, arg);
            env = env.extend(arg_val);
        }
        // Result indices must match the expected family indices.
        for (rix, exp) in ctor.result_indices.iter().zip(exp_indices.iter()) {
            let rix_t = crate::term::from_kernel(rix)?;
            let got = eval(self.sig, &env, &rix_t);
            if !conv(self.sig, ctx.lvl, ctx.dlvl, &got, exp) {
                return Err(reject("constructor result index mismatch"));
            }
        }
        Ok(usage)
    }

    /// Re-check a dependent eliminator (spec §2.7): an independent port of the kernel's
    /// `infer_elim` over full N-parameter / M-index families (the earlier ≤1/≤1 cap is lifted). The
    /// indexed case threads all indices through the motive (`λ i… . λ (_:D ps i…). T`) and concludes
    /// `P idx… scrut`; the non-indexed case is `λ (_:D ps). T` concluding `P scrut`.
    #[allow(clippy::too_many_arguments)]
    fn infer_elim(
        &self,
        ctx: &Ctx,
        data: &DataName,
        motive: &RTerm,
        methods: &[RTerm],
        scrutinee: &RTerm,
        sigma: RGrade,
    ) -> RResult<(RValue, Usage)> {
        let decl = self
            .sig
            .get(data)
            .ok_or_else(|| reject(format!("unknown inductive type {data:?}")))?
            .clone();
        let nindices = decl.indices.len();
        let indexed = nindices != 0;

        // Infer the scrutinee's type; recover the family's params and (all) index values.
        let (scrut_ty, scrut_usage) = self.infer(ctx, scrutinee, sigma)?;
        let (eparams, scrut_indices) = match &scrut_ty {
            RValue::Data(d, ps, is) if d == data => (ps.clone(), is.clone()),
            other => {
                return Err(reject(format!(
                    "Elim scrutinee not of type {data:?}: {other:?}"
                )))
            }
        };

        // Type-check the motive in its expected shape (it arrives as a bare `Lam`, not inferable on
        // its own): non-indexed `λ (_:D ps). T : Univ ℓ`, indexed `λ i1..im. λ (_:D ps i1..im). T`.
        match motive {
            RTerm::Lam(_) if indexed => {
                // Peel `nindices` index binders, threading each index type (which may reference the
                // params and earlier indices) through the context and env.
                let mut ctx_acc = ctx.clone();
                let mut idx_vars: Vec<RValue> = Vec::with_capacity(nindices);
                for idx_ty_term in decl.indices.iter() {
                    let kt = crate::term::from_kernel(idx_ty_term)?;
                    let mut env = Env::new();
                    for p in &eparams {
                        env = env.extend(p.clone());
                    }
                    for v in &idx_vars {
                        env = env.extend(v.clone());
                    }
                    let index_ty = eval(self.sig, &env, &kt);
                    idx_vars.push(RValue::Neutral(crate::value::Neutral::Var(ctx_acc.lvl)));
                    ctx_acc = ctx_acc.extend(self.sig, index_ty, RGrade::Omega);
                }
                let mut body = motive;
                for _ in 0..nindices {
                    match body {
                        RTerm::Lam(inner) => body = inner,
                        other => {
                            return Err(reject(format!(
                            "indexed Elim motive needs {nindices} index binder(s), got {other:?}"
                        )))
                        }
                    }
                }
                let dty = RValue::Data(decl.name.clone(), eparams.clone(), idx_vars.clone());
                let ctx_id = ctx_acc.extend(self.sig, dty, RGrade::Omega);
                match body {
                    RTerm::Lam(inner) => {
                        // A motive whose conclusion is itself a Π — i.e. the result type is a
                        // *function* — arises when a binder that is still in scope at the `match`
                        // (e.g. a second vector matched in a nested `match`) is lifted into the
                        // motive by the elaborator. In that shape the elaborator emits an
                        // index-ignoring, higher-order motive that we cannot faithfully refine per
                        // branch without reconstructing it (which needs the original surface type).
                        // Rather than raise a spurious soundness alarm, we *decline* this judgement —
                        // an honest refusal, narrowly scoped to higher-order eliminator motives.
                        if matches!(inner.as_ref(), RTerm::Pi(..)) {
                            return Err(decline(
                                "higher-order (Π-conclusion) eliminator motive: \
                                 dependent refinement of a post-match binder is unsupported",
                            ));
                        }
                        self.infer_universe(&ctx_id, inner)?;
                    }
                    other => {
                        return Err(reject(format!(
                            "indexed Elim motive must be `λ i1..im. λ (_:D ps i1..im). T`, got {other:?}"
                        )))
                    }
                }
            }
            RTerm::Lam(body) => {
                let dty = RValue::Data(decl.name.clone(), eparams.clone(), vec![]);
                let ctx2 = ctx.extend(self.sig, dty, RGrade::Omega);
                self.infer_universe(&ctx2, body)?;
            }
            other => {
                return Err(reject(format!(
                    "Elim motive must be a lambda (`λ … . T`), got {other:?}"
                )))
            }
        }
        // Motive strengthening (dependent-motive recovery). The elaborator sometimes hands us a
        // motive whose body mentions the *ambient* scrutinee-index variable directly (e.g.
        // `λ i. λ s. Vec B n`) instead of the bound index `i` (`λ i. λ s. Vec B i`). Both yield the
        // SAME eliminator result `motive scrut_indices scrut` when a scrutinee index is exactly that
        // ambient variable `n` (since `i` is instantiated to `n`), but only the bound-index form lets
        // the per-branch refinement specialize the conclusion. So, soundly, for each scrutinee index
        // that is a bare ambient variable `Var(L)`, rewrite occurrences of `L` inside the motive body
        // to the corresponding index binder. This recovers the dependent motive a stronger elaborator
        // would have produced, without changing the eliminator's overall type.
        let strengthened = self.strengthen_motive(ctx, motive, nindices, &scrut_indices);
        let motive = &strengthened;
        let motive_v = eval(self.sig, &ctx.env, motive);

        if methods.len() != decl.constructors.len() {
            return Err(reject(format!(
                "Elim expects {} method(s), got {}",
                decl.constructors.len(),
                methods.len()
            )));
        }
        let mut usage = scrut_usage;
        for (ctor, method) in decl.constructors.iter().zip(methods.iter()) {
            // Dependent pattern matching (spec §2.7): refine the branch against the scrutinee's
            // indices. Unifying the constructor's result indices with the scrutinee indices either
            // (a) reveals a head-constructor CLASH — the branch is unreachable for this scrutinee
            // and is vacuously well-typed (we skip it), or (b) SOLVES some constructor arguments,
            // letting us check the body under the refined (specialized) context. When unification is
            // stuck (e.g. a bare-variable scrutinee index that constrains nothing), we fall back to
            // the plain `method_type` check, matching the kernel's behavior exactly on that fragment.
            match self.refine_method(ctx, ctor, &eparams, &scrut_indices)? {
                Refinement::Unreachable => {
                    // Vacuous branch: nothing to check, contributes no usage.
                }
                Refinement::Solved { args, ambient } => {
                    let u = self.check_refined_method(
                        ctx,
                        &decl,
                        ctor,
                        method,
                        motive,
                        &eparams,
                        &scrut_indices,
                        &args,
                        &ambient,
                        sigma,
                    )?;
                    usage = usage.add(&u);
                }
                Refinement::Stuck => {
                    let method_ty = self.method_type(ctx, &decl, ctor, &motive_v, &eparams)?;
                    let u = self.check(ctx, method, &method_ty, sigma)?;
                    usage = usage.add(&u);
                }
            }
        }

        // Result: non-indexed `P scrutinee`; indexed `P idx1..idxm scrutinee`.
        let scrut_v = eval(self.sig, &ctx.env, scrutinee);
        let result = if indexed {
            if scrut_indices.len() != nindices {
                return Err(reject(format!(
                    "indexed Elim scrutinee has {} index value(s), expected {nindices}",
                    scrut_indices.len()
                )));
            }
            let mut acc = motive_v;
            for idx in scrut_indices.into_iter() {
                acc = apply(self.sig, acc, idx);
            }
            apply(self.sig, acc, scrut_v)
        } else {
            apply(self.sig, motive_v, scrut_v)
        };
        Ok((result, usage))
    }

    /// Recover a dependent motive from an index-ignoring one (see the call site in `infer_elim`).
    /// For each scrutinee index that is a bare ambient variable `Var(L)`, rewrite occurrences of that
    /// ambient variable inside the motive body to the corresponding index binder. Sound because it
    /// preserves `motive scrut_indices scrut` while making the per-branch conclusion index-dependent.
    fn strengthen_motive(
        &self,
        ctx: &Ctx,
        motive: &RTerm,
        nindices: usize,
        scrut_indices: &[RValue],
    ) -> RTerm {
        // Collect (ambient level L → index-binder position j) for bare-variable scrutinee indices.
        let mut remap: Vec<(usize, usize)> = Vec::new();
        for (j, ix) in scrut_indices.iter().enumerate().take(nindices) {
            if let RValue::Neutral(crate::value::Neutral::Var(l)) = ix {
                if *l < ctx.lvl {
                    remap.push((*l, j));
                }
            }
        }
        if remap.is_empty() {
            return motive.clone();
        }
        // Peel the `nindices` index binders and the scrutinee binder, rewriting the body underneath.
        fn rebuild(
            t: &RTerm,
            peel: usize,
            ctx_lvl: usize,
            depth: usize,
            remap: &[(usize, usize)],
        ) -> RTerm {
            if peel > 0 {
                if let RTerm::Lam(inner) = t {
                    return RTerm::Lam(Box::new(rebuild(
                        inner,
                        peel - 1,
                        ctx_lvl,
                        depth + 1,
                        remap,
                    )));
                }
                return t.clone();
            }
            subst_ambient_to_binder(t, ctx_lvl, depth, remap)
        }
        // Rewrite, tracking `depth` = binders entered since the motive root. A `Var(i)` with
        // `i >= depth` is free of the motive's binders and refers to ambient level
        // `ctx_lvl - 1 - (i - depth)`; if that level is a remapped scrutinee index, replace it with the
        // de Bruijn index of the corresponding (locally bound) motive index binder `Var(depth-1-j)`.
        fn subst_ambient_to_binder(
            t: &RTerm,
            ctx_lvl: usize,
            depth: usize,
            remap: &[(usize, usize)],
        ) -> RTerm {
            match t {
                RTerm::Var(i) => {
                    if *i >= depth {
                        // Ambient level this index refers to: (ctx_lvl - 1) - (i - depth).
                        let amb = (ctx_lvl)
                            .checked_sub(1)
                            .and_then(|x| x.checked_sub(*i - depth));
                        if let Some(amb) = amb {
                            for (l, j) in remap {
                                if *l == amb {
                                    return RTerm::Var(depth - 1 - j);
                                }
                            }
                        }
                    }
                    t.clone()
                }
                RTerm::Pi(g, a, b) => RTerm::Pi(
                    *g,
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(b, ctx_lvl, depth + 1, remap)),
                ),
                RTerm::Sigma(a, b) => RTerm::Sigma(
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(b, ctx_lvl, depth + 1, remap)),
                ),
                RTerm::Lam(b) => RTerm::Lam(Box::new(subst_ambient_to_binder(
                    b,
                    ctx_lvl,
                    depth + 1,
                    remap,
                ))),
                RTerm::App(f, a) => RTerm::App(
                    Box::new(subst_ambient_to_binder(f, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                ),
                RTerm::Pair(a, b) => RTerm::Pair(
                    Box::new(subst_ambient_to_binder(a, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(b, ctx_lvl, depth, remap)),
                ),
                RTerm::Fst(p) => {
                    RTerm::Fst(Box::new(subst_ambient_to_binder(p, ctx_lvl, depth, remap)))
                }
                RTerm::Snd(p) => {
                    RTerm::Snd(Box::new(subst_ambient_to_binder(p, ctx_lvl, depth, remap)))
                }
                RTerm::Ann(e, ty) => RTerm::Ann(
                    Box::new(subst_ambient_to_binder(e, ctx_lvl, depth, remap)),
                    Box::new(subst_ambient_to_binder(ty, ctx_lvl, depth, remap)),
                ),
                RTerm::Data(d, ps, is) => RTerm::Data(
                    d.clone(),
                    ps.iter()
                        .map(|x| subst_ambient_to_binder(x, ctx_lvl, depth, remap))
                        .collect(),
                    is.iter()
                        .map(|x| subst_ambient_to_binder(x, ctx_lvl, depth, remap))
                        .collect(),
                ),
                RTerm::Con(c, xs) => RTerm::Con(
                    c.clone(),
                    xs.iter()
                        .map(|x| subst_ambient_to_binder(x, ctx_lvl, depth, remap))
                        .collect(),
                ),
                // The supported motive bodies are built from Π/Σ/App/Data/Con/projections over the
                // params and indices; anything else is left structurally unchanged (it cannot mention
                // the ambient index variable in the fragment the kernel supports).
                other => other.clone(),
            }
        }
        rebuild(motive, nindices + 1, ctx.lvl, 0, &remap)
    }

    /// Build the expected method-type *value* for one constructor — a faithful, independent port of
    /// the kernel's `method_type` (spec §2.7): a Π-telescope over the constructor's argument shapes
    /// (with an induction-hypothesis binder after each recursive argument) concluding
    /// `motive (con args)`, handling the one-parameter inductive families the prelude uses. Built as
    /// a closed `RTerm` then `eval`'d once.
    fn method_type(
        &self,
        ctx: &Ctx,
        decl: &DataDecl,
        ctor: &Constructor,
        motive: &RValue,
        params: &[RValue],
    ) -> RResult<RValue> {
        let data_name = decl.name.clone();
        let indexed = !decl.indices.is_empty();
        let nparams = params.len();
        let motive_term = quote(self.sig, ctx.lvl, ctx.dlvl, motive);
        let param_terms: Vec<RTerm> = params
            .iter()
            .map(|p| quote(self.sig, ctx.lvl, ctx.dlvl, p))
            .collect();

        // Binder layout: each arg is one binder; each recursive arg is followed by an IH binder.
        // `arg_pos[k]` is the telescope position of constructor arg `k`. For an indexed family the
        // recursive argument's index expressions are carried on both the RecArg and its IH binder.
        #[derive(Clone)]
        enum B {
            Arg,
            RecArg(Vec<RTerm>),
            Ih(Vec<RTerm>),
        }
        let mut binders: Vec<B> = Vec::new();
        let mut arg_pos: Vec<usize> = Vec::new();
        for shape in &ctor.args {
            match shape {
                Arg::NonRec(_) => {
                    arg_pos.push(binders.len());
                    binders.push(B::Arg);
                }
                Arg::Rec(rec_indices) => {
                    let ix: Vec<RTerm> = rec_indices
                        .iter()
                        .map(crate::term::from_kernel)
                        .collect::<RResult<_>>()?;
                    arg_pos.push(binders.len());
                    binders.push(B::RecArg(ix.clone()));
                    binders.push(B::Ih(ix));
                }
            }
        }
        let total = binders.len();

        // Translate a constructor-scope term (sees `[args.. , params..]` innermost-first) into the
        // method telescope at `depth` binders, via a simultaneous substitution — a direct port of
        // the kernel's `translate`.
        let translate = |t: &RTerm, args_before: usize, depth: usize| -> RTerm {
            let m = args_before + nparams;
            let mut repls: Vec<RTerm> = Vec::with_capacity(m);
            for i in 0..args_before {
                let ctor_arg_index = args_before - 1 - i;
                let method_binder_pos = arg_pos[ctor_arg_index];
                repls.push(RTerm::Var(depth - 1 - method_binder_pos));
            }
            for pj in 0..nparams {
                let param_index = nparams - 1 - pj;
                repls.push(shift_free(&param_terms[param_index], depth));
            }
            translate_go(t, 0, m, &repls)
        };

        // Conclusion: non-indexed `motive (con args)`; indexed `motive rix (con args)` where `rix`
        // is the constructor's result index translated into the method telescope.
        let con_args: Vec<RTerm> = (0..ctor.args.len())
            .map(|k| RTerm::Var(total - 1 - arg_pos[k]))
            .collect();
        let con_term = RTerm::Con(ctor.name.clone(), con_args);
        let mut body = if indexed {
            // Apply the motive to every result index (translated into the method telescope), then
            // the constructor term: `motive rix_1 .. rix_m (con args)`.
            let mut acc = shift_free(&motive_term, total);
            for rix_k in ctor.result_indices.iter() {
                let rix_k = crate::term::from_kernel(rix_k)?;
                let rix = translate(&rix_k, ctor.args.len(), total);
                acc = RTerm::App(Box::new(acc), Box::new(rix));
            }
            RTerm::App(Box::new(acc), Box::new(con_term))
        } else {
            RTerm::App(
                Box::new(shift_free(&motive_term, total)),
                Box::new(con_term),
            )
        };

        // `args_before` at each binder position.
        let mut args_before_at: Vec<usize> = Vec::with_capacity(total);
        {
            let mut count = 0usize;
            for b in &binders {
                args_before_at.push(count);
                if matches!(b, B::Arg | B::RecArg(_)) {
                    count += 1;
                }
            }
        }
        let nonrec_tys: Vec<Option<RTerm>> = ctor
            .args
            .iter()
            .map(|a| match a {
                Arg::NonRec(ty) => Some(crate::term::from_kernel(ty)),
                Arg::Rec(_) => None,
            })
            .map(|o| o.transpose())
            .collect::<RResult<_>>()?;

        for (pos, b) in binders.iter().enumerate().rev() {
            let depth = pos;
            let args_before = args_before_at[pos];
            let dom = match b {
                B::Arg => {
                    let k = arg_pos.iter().position(|&p| p == pos).unwrap();
                    let ty = nonrec_tys[k].clone().unwrap();
                    translate(&ty, args_before, depth)
                }
                B::RecArg(rec_indices) => {
                    let ps: Vec<RTerm> = param_terms.iter().map(|t| shift_free(t, depth)).collect();
                    let ix: Vec<RTerm> = rec_indices
                        .iter()
                        .map(|t| translate(t, args_before, depth))
                        .collect();
                    RTerm::Data(data_name.clone(), ps, ix)
                }
                B::Ih(rec_indices) => {
                    let p_motive = shift_free(&motive_term, depth);
                    let rec_pos = pos - 1;
                    let xs_var = RTerm::Var(depth - 1 - rec_pos);
                    if indexed {
                        // The rec index references constructor args preceding the RecArg; the
                        // args-before count at the IH includes the RecArg itself, so subtract one.
                        let mut acc = p_motive;
                        for ix_k in rec_indices.iter() {
                            let ix = translate(ix_k, args_before - 1, depth);
                            acc = RTerm::App(Box::new(acc), Box::new(ix));
                        }
                        RTerm::App(Box::new(acc), Box::new(xs_var))
                    } else {
                        RTerm::App(Box::new(p_motive), Box::new(xs_var))
                    }
                }
            };
            body = RTerm::Pi(RGrade::Omega, Box::new(dom), Box::new(body));
        }

        let result_mty = eval(self.sig, &ctx.env, &body);
        Ok(result_mty)
    }

    /// Decide how to check one constructor's method under dependent pattern matching, by unifying
    /// the constructor's *result indices* (as functions of fresh argument placeholders) with the
    /// scrutinee's actual indices. Two kinds of unknown are solvable: the constructor's argument
    /// *placeholders* (de Bruijn levels `≥ ctx.lvl`) and the scrutinee's own index *variables*
    /// (ambient levels `< ctx.lvl`), which get *specialized* per branch — this is the substitution
    /// that dependent pattern matching performs. A head-constructor clash means the branch is
    /// unreachable for this scrutinee (vacuously well-typed); no progress means the plain
    /// `method_type` check is already exact (kernel-faithful fallback).
    fn refine_method(
        &self,
        ctx: &Ctx,
        ctor: &Constructor,
        params: &[RValue],
        scrut_indices: &[RValue],
    ) -> RResult<Refinement> {
        // Build placeholder values for the constructor arguments and the env that types/evaluates
        // the (param + preceding-arg) scope, exactly as `check_con` does — but with fresh neutral
        // *levels* (≥ ctx.lvl) so unification can recognize them as the solvable unknowns.
        let nargs = ctor.args.len();
        let mut env = Env::new();
        for p in params {
            env = env.extend(p.clone());
        }
        for k in 0..nargs {
            env = env.extend(RValue::Neutral(crate::value::Neutral::Var(ctx.lvl + k)));
        }
        let mut sol = Solution {
            args: vec![None; nargs],
            ambient: Vec::new(),
        };
        let mut any = false;
        for (rix_t, scrut_ix) in ctor.result_indices.iter().zip(scrut_indices.iter()) {
            let rt = crate::term::from_kernel(rix_t)?;
            let got = eval(self.sig, &env, &rt);
            match self.unify_index(ctx, &got, scrut_ix, &mut sol)? {
                Unify::Clash => return Ok(Refinement::Unreachable),
                Unify::Progress => any = true,
                Unify::Trivial => {}
                Unify::Stuck => return Ok(Refinement::Stuck),
            }
        }
        if any {
            Ok(Refinement::Solved {
                args: sol.args,
                ambient: sol.ambient,
            })
        } else {
            Ok(Refinement::Stuck)
        }
    }

    /// First-order unification of a constructor result-index value `got` (which may mention argument
    /// placeholders at levels `≥ ctx.lvl`) against the scrutinee index value `want` (which may
    /// mention ambient context variables at levels `< ctx.lvl`). Solves placeholders (the branch's
    /// constructor arguments) and ambient index variables (the per-branch specialization).
    fn unify_index(
        &self,
        ctx: &Ctx,
        got: &RValue,
        want: &RValue,
        sol: &mut Solution,
    ) -> RResult<Unify> {
        // Flexible placeholder on the `got` side ⇒ solve the constructor argument.
        if let RValue::Neutral(crate::value::Neutral::Var(l)) = got {
            if *l >= ctx.lvl {
                let k = *l - ctx.lvl;
                if k < sol.args.len() {
                    return Ok(match &sol.args[k] {
                        None => {
                            sol.args[k] = Some(want.clone());
                            Unify::Progress
                        }
                        Some(prev) => {
                            if conv(self.sig, ctx.lvl, ctx.dlvl, prev, want) {
                                Unify::Trivial
                            } else {
                                Unify::Stuck
                            }
                        }
                    });
                }
            }
        }
        // Flexible ambient index variable on the `want` side ⇒ specialize it to `got`. `got` may
        // mention the constructor's argument placeholders (they become this branch's bound
        // variables); it must not contain a *stuck* neutral (an application/eliminator), which we
        // cannot soundly turn into an equation.
        if let RValue::Neutral(crate::value::Neutral::Var(l)) = want {
            if *l < ctx.lvl && self.solvable_index(got) {
                for (lvl, v) in sol.ambient.iter() {
                    if lvl == l {
                        return Ok(if conv(self.sig, ctx.lvl, ctx.dlvl, v, got) {
                            Unify::Trivial
                        } else {
                            Unify::Stuck
                        });
                    }
                }
                sol.ambient.push((*l, got.clone()));
                return Ok(Unify::Progress);
            }
        }
        match (got, want) {
            // Same data head: decompose parameters and indices.
            (RValue::Data(n1, p1, i1), RValue::Data(n2, p2, i2)) => {
                if n1 != n2 || p1.len() != p2.len() || i1.len() != i2.len() {
                    return Ok(Unify::Clash);
                }
                self.unify_seq(ctx, p1.iter().zip(p2).chain(i1.iter().zip(i2)), sol)
            }
            // Same constructor head: decompose arguments. Different heads are a genuine CLASH — the
            // branch is unreachable for this scrutinee.
            (RValue::Con(c1, a1), RValue::Con(c2, a2)) => {
                if c1 != c2 || a1.len() != a2.len() {
                    return Ok(Unify::Clash);
                }
                self.unify_seq(ctx, a1.iter().zip(a2), sol)
            }
            (RValue::IntLit(a), RValue::IntLit(b)) => {
                Ok(if a == b { Unify::Trivial } else { Unify::Clash })
            }
            // Otherwise: rigidly equal ⇒ trivial; not provably so ⇒ stuck (fall back to the plain
            // method type rather than risk an unsound accept).
            _ => Ok(if conv(self.sig, ctx.lvl, ctx.dlvl, got, want) {
                Unify::Trivial
            } else {
                Unify::Stuck
            }),
        }
    }

    /// Unify a sequence of value pairs, combining their outcomes (clash/stuck short-circuit).
    fn unify_seq<'b>(
        &self,
        ctx: &Ctx,
        pairs: impl Iterator<Item = (&'b RValue, &'b RValue)>,
        sol: &mut Solution,
    ) -> RResult<Unify> {
        let mut progressed = false;
        for (a, b) in pairs {
            match self.unify_index(ctx, a, b, sol)? {
                Unify::Clash => return Ok(Unify::Clash),
                Unify::Progress => progressed = true,
                Unify::Trivial => {}
                Unify::Stuck => return Ok(Unify::Stuck),
            }
        }
        Ok(if progressed {
            Unify::Progress
        } else {
            Unify::Trivial
        })
    }

    /// May `v` be used as the right-hand side of an index equation (ambient specialization)? It must
    /// be a value built only from variables (ambient context vars or constructor-argument
    /// placeholders), data/constructor heads, and literals — never a *stuck* neutral such as an
    /// application or eliminator, which we cannot soundly equate.
    fn solvable_index(&self, v: &RValue) -> bool {
        match v {
            RValue::Neutral(crate::value::Neutral::Var(_)) => true,
            RValue::Neutral(_) => false,
            RValue::Data(_, ps, is) => {
                ps.iter().all(|x| self.solvable_index(x))
                    && is.iter().all(|x| self.solvable_index(x))
            }
            RValue::Con(_, xs) => xs.iter().all(|x| self.solvable_index(x)),
            RValue::Univ(_) | RValue::IntTy | RValue::IntLit(_) => true,
            _ => false,
        }
    }

    /// Check a constructor's method body under the refinement solved by [`Self::refine_method`]. The
    /// ambient index variables are *specialized* (re-bound in the environment), the motive is
    /// re-evaluated under that specialization, each constructor argument is bound either to its
    /// *solved* value or a fresh variable (recursive arguments also get an induction-hypothesis
    /// binder), and the body is checked against the dependent conclusion
    /// `motive (specialized scrut_indices) (con args)`.
    #[allow(clippy::too_many_arguments)]
    fn check_refined_method(
        &self,
        ctx: &Ctx,
        decl: &DataDecl,
        ctor: &Constructor,
        method: &RTerm,
        motive_term: &RTerm,
        params: &[RValue],
        scrut_indices: &[RValue],
        solved: &[Option<RValue>],
        ambient: &[(usize, RValue)],
        sigma: RGrade,
    ) -> RResult<Usage> {
        let mut cur = ctx.clone();
        let mut body = method;
        // `arg_env` evaluates the constructor's arg/index types (param scope, then bound args), in
        // the same convention as `check_con`.
        let mut arg_env = Env::new();
        for p in params {
            arg_env = arg_env.extend(p.clone());
        }
        let mut arg_vals: Vec<RValue> = Vec::with_capacity(ctor.args.len());
        // Map each constructor-argument placeholder (used during unification as `Var(ctx.lvl + k)`)
        // to the actual value bound for that argument here, so ambient index equations expressed
        // over placeholders can be re-expressed over the branch's real binders.
        let mut placeholder_map: Vec<(usize, RValue)> = Vec::with_capacity(ctor.args.len());
        for (k, shape) in ctor.args.iter().enumerate() {
            // Domain type of this argument, in the current refined context. For a recursive arg we
            // also remember its index *values* (computed against the args bound *before* this one)
            // to build the induction-hypothesis binder below.
            let mut rec_ix: Option<Vec<RValue>> = None;
            let dom = match shape {
                Arg::NonRec(ty) => {
                    let ty_t = crate::term::from_kernel(ty)?;
                    eval(self.sig, &arg_env, &ty_t)
                }
                Arg::Rec(rec_indices) => {
                    let ix: Vec<RValue> = rec_indices
                        .iter()
                        .map(|t| {
                            let rt = crate::term::from_kernel(t)?;
                            Ok::<RValue, RecheckError>(eval(self.sig, &arg_env, &rt))
                        })
                        .collect::<RResult<_>>()?;
                    rec_ix = Some(ix.clone());
                    RValue::Data(decl.name.clone(), params.to_vec(), ix)
                }
            };
            // Open the method's lambda for this argument.
            let inner = match body {
                RTerm::Lam(inner) => inner.as_ref(),
                other => {
                    return Err(reject(format!(
                        "indexed Elim method for {:?} expected a lambda, got {other:?}",
                        ctor.name
                    )))
                }
            };
            // Bind the argument to its solved value if forced, else to a fresh variable of `dom`.
            let arg_val = match &solved[k] {
                Some(v) => v.clone(),
                None => fresh_var(self.sig, cur.lvl, &dom),
            };
            placeholder_map.push((ctx.lvl + k, arg_val.clone()));
            // The body's binder still ranges over `dom`; record the entry at that type and bind the
            // (possibly forced) value in the environment so later types/the conclusion see it.
            cur = cur.extend_with(self.sig, dom, RGrade::Omega, arg_val.clone());
            arg_vals.push(arg_val.clone());
            arg_env = arg_env.extend(arg_val.clone());
            body = inner;

            // After a recursive argument, the method also binds an induction hypothesis
            // `P (rec indices) xs`, using the recursive argument's indices computed above. The IH's
            // motive must be re-evaluated under the ambient refinement so its index types line up.
            if let Some(ix) = rec_ix {
                let ix: Vec<RValue> = ix
                    .iter()
                    .map(|v| self.subst_levels(v, &placeholder_map))
                    .collect();
                // The induction hypothesis is the recursive result on the *shorter* structure, so it
                // is typed at the recursive argument's *own* indices, not the conclusion's. Refine the
                // ambient scrutinee-index variables by unifying them against this recursive argument's
                // indices (e.g. for `vec-map`, the scrutinee index `n` becomes the tail's length `m`),
                // then evaluate the motive under that refinement. This recovers `P (rec ix) xs` even
                // when the elaborator handed us an index-ignoring motive `λ i. λ s. Vec B n`.
                let ih_ambient = {
                    let mut sol = Solution {
                        args: vec![None; 0],
                        ambient: Vec::new(),
                    };
                    for (sx, rx) in scrut_indices.iter().zip(ix.iter()) {
                        let _ = self.unify_index(ctx, rx, sx, &mut sol)?;
                    }
                    sol.ambient
                };
                let motive_here = {
                    let env_here = ctx.refine_ambient(&ih_ambient).env;
                    eval(self.sig, &env_here, motive_term)
                };
                let mut ih_ty = motive_here;
                for v in ix {
                    let v = self.subst_levels(&v, &ih_ambient);
                    ih_ty = apply(self.sig, ih_ty, v);
                }
                ih_ty = apply(self.sig, ih_ty, arg_val);
                let inner2 = match body {
                    RTerm::Lam(inner) => inner.as_ref(),
                    other => {
                        return Err(reject(format!(
                            "indexed Elim method for {:?} expected an IH lambda, got {other:?}",
                            ctor.name
                        )))
                    }
                };
                let ih_val = fresh_var(self.sig, cur.lvl, &ih_ty);
                cur = cur.extend_with(self.sig, ih_ty, RGrade::Omega, ih_val);
                body = inner2;
            }
        }
        // Apply the per-branch refinement now that the constructor's arguments are in scope: the
        // ambient index variables are specialized to their solutions (re-expressed over the bound
        // arguments), the context environment is updated, and the motive/scrutinee indices are
        // re-evaluated so the conclusion `motive (refined indices) (con args)` reflects the branch's
        // index equations. This is exactly the substitution dependent pattern matching performs.
        let refined_ambient = self.resolve_ambient(ambient, &placeholder_map);
        cur = cur.refine_ambient(&refined_ambient);
        // Evaluate the motive against the *ambient* environment (refined), not `cur.env`: the motive
        // term's free variables are de Bruijn indices into the ambient context, and `cur.env` has the
        // method binders appended (which would shift those indices). Applying the resulting closure
        // to the indices/scrutinee is level-agnostic, so the conclusion comes out correct.
        let motive = eval(
            self.sig,
            &ctx.refine_ambient(&refined_ambient).env,
            motive_term,
        );
        let con_val = RValue::Con(ctor.name.clone(), arg_vals);
        let mut concl = motive;
        for ix in scrut_indices {
            let ix = self.subst_levels(ix, &refined_ambient);
            concl = apply(self.sig, concl, ix);
        }
        concl = apply(self.sig, concl, con_val);
        let u = self.check(&cur, body, &concl, sigma)?;
        // The method binders are not part of the ambient usage vector; truncate to ambient length.
        Ok(u.truncate(ctx.len()))
    }

    /// Re-express the ambient index solutions (computed over constructor-argument placeholders) in
    /// terms of the branch's actually-bound argument values.
    fn resolve_ambient(
        &self,
        ambient: &[(usize, RValue)],
        placeholder_map: &[(usize, RValue)],
    ) -> Vec<(usize, RValue)> {
        ambient
            .iter()
            .map(|(lvl, v)| (*lvl, self.subst_levels(v, placeholder_map)))
            .collect()
    }

    /// Substitute neutral variables at the given levels by the mapped values throughout `v`.
    fn subst_levels(&self, v: &RValue, map: &[(usize, RValue)]) -> RValue {
        match v {
            RValue::Neutral(crate::value::Neutral::Var(l)) => {
                for (lvl, val) in map {
                    if lvl == l {
                        return val.clone();
                    }
                }
                v.clone()
            }
            RValue::Data(n, ps, is) => RValue::Data(
                n.clone(),
                ps.iter().map(|x| self.subst_levels(x, map)).collect(),
                is.iter().map(|x| self.subst_levels(x, map)).collect(),
            ),
            RValue::Con(c, xs) => RValue::Con(
                c.clone(),
                xs.iter().map(|x| self.subst_levels(x, map)).collect(),
            ),
            other => other.clone(),
        }
    }
}

/// How a constructor's branch relates to the scrutinee's indices under dependent pattern matching.
enum Refinement {
    /// The constructor can never produce the scrutinee's indices: the branch is vacuous.
    Unreachable,
    /// The branch is reachable; some constructor arguments are forced (`args`) and some ambient
    /// scrutinee-index variables are specialized (`ambient`: `(level, value)`).
    Solved {
        args: Vec<Option<RValue>>,
        ambient: Vec<(usize, RValue)>,
    },
    /// Unification made no progress; check with the plain method type (kernel-faithful default).
    Stuck,
}

/// Accumulated unification solution: per-argument placeholder solutions and ambient index-variable
/// specializations (`(level, value)`).
struct Solution {
    args: Vec<Option<RValue>>,
    ambient: Vec<(usize, RValue)>,
}

/// The result of unifying one index pair.
enum Unify {
    /// Head-constructor clash ⇒ the branch is unreachable.
    Clash,
    /// A placeholder was solved (or a sub-unification solved something).
    Progress,
    /// Already definitionally equal; no new information.
    Trivial,
    /// Cannot decide ⇒ fall back to the plain method-type check.
    Stuck,
}

/// The recursive worker of the constructor-scope→method-scope translation (port of the kernel's
/// `go`): replace the lowest `m` de Bruijn indices `>= depth_in` by `repls` (shifted into scope),
/// and shift everything above down by `m`.
fn translate_go(t: &RTerm, depth_in: usize, m: usize, repls: &[RTerm]) -> RTerm {
    match t {
        RTerm::Var(i) => {
            if *i < depth_in {
                RTerm::Var(*i)
            } else if *i < depth_in + m {
                shift_free(&repls[*i - depth_in], depth_in)
            } else {
                RTerm::Var(*i - m)
            }
        }
        RTerm::Univ(_) | RTerm::Interval(_) => t.clone(),
        RTerm::Pi(g, a, b) => RTerm::Pi(
            *g,
            Box::new(translate_go(a, depth_in, m, repls)),
            Box::new(translate_go(b, depth_in + 1, m, repls)),
        ),
        RTerm::Sigma(a, b) => RTerm::Sigma(
            Box::new(translate_go(a, depth_in, m, repls)),
            Box::new(translate_go(b, depth_in + 1, m, repls)),
        ),
        RTerm::Lam(b) => RTerm::Lam(Box::new(translate_go(b, depth_in + 1, m, repls))),
        RTerm::App(f, a) => RTerm::App(
            Box::new(translate_go(f, depth_in, m, repls)),
            Box::new(translate_go(a, depth_in, m, repls)),
        ),
        RTerm::Pair(a, b) => RTerm::Pair(
            Box::new(translate_go(a, depth_in, m, repls)),
            Box::new(translate_go(b, depth_in, m, repls)),
        ),
        RTerm::Fst(p) => RTerm::Fst(Box::new(translate_go(p, depth_in, m, repls))),
        RTerm::Snd(p) => RTerm::Snd(Box::new(translate_go(p, depth_in, m, repls))),
        RTerm::Ann(e, ty) => RTerm::Ann(
            Box::new(translate_go(e, depth_in, m, repls)),
            Box::new(translate_go(ty, depth_in, m, repls)),
        ),
        RTerm::Data(d, ps, ix) => RTerm::Data(
            d.clone(),
            ps.iter()
                .map(|x| translate_go(x, depth_in, m, repls))
                .collect(),
            ix.iter()
                .map(|x| translate_go(x, depth_in, m, repls))
                .collect(),
        ),
        RTerm::Con(c, xs) => RTerm::Con(
            c.clone(),
            xs.iter()
                .map(|x| translate_go(x, depth_in, m, repls))
                .collect(),
        ),
        // Constructor argument/index types in the supported fragment never carry eliminators,
        // paths, or Kan operations; leave anything else structurally untouched.
        RTerm::Elim { .. }
        | RTerm::PathP { .. }
        | RTerm::PLam(_)
        | RTerm::PApp(_, _)
        | RTerm::Transp { .. }
        | RTerm::HComp { .. }
        | RTerm::Comp { .. }
        | RTerm::Delay(_)
        | RTerm::Now(_)
        | RTerm::Later(_)
        | RTerm::Force(_) => t.clone(),
        // Effects/handlers: recurse over term children, honoring the handler clause binders
        // (return clause: +1; each op clause: +2).
        RTerm::EffTy(a) => RTerm::EffTy(Box::new(translate_go(a, depth_in, m, repls))),
        RTerm::Op { effect, op, arg } => RTerm::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(translate_go(arg, depth_in, m, repls)),
        },
        RTerm::Handle {
            body,
            return_clause,
            op_clauses,
        } => RTerm::Handle {
            body: Box::new(translate_go(body, depth_in, m, repls)),
            return_clause: Box::new(translate_go(return_clause, depth_in + 1, m, repls)),
            op_clauses: op_clauses
                .iter()
                .map(|(op, clause)| {
                    (
                        op.clone(),
                        Box::new(translate_go(clause, depth_in + 2, m, repls)),
                    )
                })
                .collect(),
        },
        // Int type/literal carry no de Bruijn content; an IntPrim's operands must be translated.
        RTerm::IntTy | RTerm::IntLit(_) => t.clone(),
        RTerm::IntPrim { op, lhs, rhs } => RTerm::IntPrim {
            op: *op,
            lhs: Box::new(translate_go(lhs, depth_in, m, repls)),
            rhs: Box::new(translate_go(rhs, depth_in, m, repls)),
        },
    }
}

/// Shift free de Bruijn indices `>= 0` upward by `d` (closed-term weakening helper for building
/// method-type telescopes as terms).
fn shift_free(t: &RTerm, d: usize) -> RTerm {
    shift_free_cut(t, d, 0)
}

fn shift_free_cut(t: &RTerm, d: usize, cut: usize) -> RTerm {
    match t {
        RTerm::Var(i) => {
            if *i >= cut {
                RTerm::Var(i + d)
            } else {
                RTerm::Var(*i)
            }
        }
        RTerm::Univ(_) | RTerm::Interval(_) => t.clone(),
        RTerm::Pi(g, a, b) => RTerm::Pi(
            *g,
            Box::new(shift_free_cut(a, d, cut)),
            Box::new(shift_free_cut(b, d, cut + 1)),
        ),
        RTerm::Lam(b) => RTerm::Lam(Box::new(shift_free_cut(b, d, cut + 1))),
        RTerm::App(f, a) => RTerm::App(
            Box::new(shift_free_cut(f, d, cut)),
            Box::new(shift_free_cut(a, d, cut)),
        ),
        RTerm::Sigma(a, b) => RTerm::Sigma(
            Box::new(shift_free_cut(a, d, cut)),
            Box::new(shift_free_cut(b, d, cut + 1)),
        ),
        RTerm::Pair(a, b) => RTerm::Pair(
            Box::new(shift_free_cut(a, d, cut)),
            Box::new(shift_free_cut(b, d, cut)),
        ),
        RTerm::Fst(p) => RTerm::Fst(Box::new(shift_free_cut(p, d, cut))),
        RTerm::Snd(p) => RTerm::Snd(Box::new(shift_free_cut(p, d, cut))),
        RTerm::Ann(e, ty) => RTerm::Ann(
            Box::new(shift_free_cut(e, d, cut)),
            Box::new(shift_free_cut(ty, d, cut)),
        ),
        RTerm::Data(n, ps, is) => RTerm::Data(
            n.clone(),
            ps.iter().map(|x| shift_free_cut(x, d, cut)).collect(),
            is.iter().map(|x| shift_free_cut(x, d, cut)).collect(),
        ),
        RTerm::Con(n, args) => RTerm::Con(
            n.clone(),
            args.iter().map(|x| shift_free_cut(x, d, cut)).collect(),
        ),
        RTerm::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => RTerm::Elim {
            data: data.clone(),
            motive: Box::new(shift_free_cut(motive, d, cut)),
            methods: methods.iter().map(|m| shift_free_cut(m, d, cut)).collect(),
            scrutinee: Box::new(shift_free_cut(scrutinee, d, cut)),
        },
        RTerm::PathP { family, lhs, rhs } => RTerm::PathP {
            family: Box::new(shift_free_cut(family, d, cut)),
            lhs: Box::new(shift_free_cut(lhs, d, cut)),
            rhs: Box::new(shift_free_cut(rhs, d, cut)),
        },
        RTerm::PLam(b) => RTerm::PLam(Box::new(shift_free_cut(b, d, cut))),
        RTerm::PApp(p, r) => RTerm::PApp(Box::new(shift_free_cut(p, d, cut)), r.clone()),
        RTerm::Transp {
            family,
            cofib,
            base,
        } => RTerm::Transp {
            family: Box::new(shift_free_cut(family, d, cut)),
            cofib: cofib.clone(),
            base: Box::new(shift_free_cut(base, d, cut)),
        },
        RTerm::HComp {
            ty,
            cofib,
            tube,
            base,
        } => RTerm::HComp {
            ty: Box::new(shift_free_cut(ty, d, cut)),
            cofib: cofib.clone(),
            tube: Box::new(shift_free_cut(tube, d, cut)),
            base: Box::new(shift_free_cut(base, d, cut)),
        },
        RTerm::Comp {
            family,
            cofib,
            tube,
            base,
        } => RTerm::Comp {
            family: Box::new(shift_free_cut(family, d, cut)),
            cofib: cofib.clone(),
            tube: Box::new(shift_free_cut(tube, d, cut)),
            base: Box::new(shift_free_cut(base, d, cut)),
        },
        RTerm::Delay(a) => RTerm::Delay(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Now(a) => RTerm::Now(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Later(a) => RTerm::Later(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Force(a) => RTerm::Force(Box::new(shift_free_cut(a, d, cut))),
        RTerm::EffTy(a) => RTerm::EffTy(Box::new(shift_free_cut(a, d, cut))),
        RTerm::Op { effect, op, arg } => RTerm::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(shift_free_cut(arg, d, cut)),
        },
        RTerm::Handle {
            body,
            return_clause,
            op_clauses,
        } => RTerm::Handle {
            body: Box::new(shift_free_cut(body, d, cut)),
            return_clause: Box::new(shift_free_cut(return_clause, d, cut + 1)),
            op_clauses: op_clauses
                .iter()
                .map(|(op, clause)| (op.clone(), Box::new(shift_free_cut(clause, d, cut + 2))))
                .collect(),
        },
        RTerm::IntTy | RTerm::IntLit(_) => t.clone(),
        RTerm::IntPrim { op, lhs, rhs } => RTerm::IntPrim {
            op: *op,
            lhs: Box::new(shift_free_cut(lhs, d, cut)),
            rhs: Box::new(shift_free_cut(rhs, d, cut)),
        },
    }
}
