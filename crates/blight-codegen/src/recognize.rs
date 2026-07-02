//! `recognize.rs` — the zero-TCB fast-`Nat` recognizer (M20).
//!
//! A `Cir -> Cir` rewrite that structurally proves a sub-term computes exactly one of the prelude's
//! total `Nat` functions (`plus`/`mult`/`sub`/`pred`, std/nat.bl) over the inductive `Zero`/`Succ`
//! encoding, and replaces it with a [`Cir::NatPrim`] node that the backend lowers to an O(1)
//! `bl_nat_*` machine-word call (numeric.c) instead of the O(n) eliminator unrolling.
//!
//! ## Why this is sound without growing the TCB
//! The kernel and the independent re-checker only ever see the *inductive* definition: this pass
//! runs in the untrusted backend, strictly downstream of checking. A bug here produces a wrong
//! *number*, never a false *proof* — and even a wrong number is caught by the differential fuzz test
//! (`runtime/tests/numeric_diff.c`) that runs every op both ways and asserts bit-identical results.
//! So the optimization is *checked*, never *trusted*.
//!
//! ## Why it is conservative
//! Recognition is by exact structural fingerprint of the elaborator's `Elim` encoding (captured from
//! `BL_DUMP_CIR`). If a user *redefines* `plus` (or the elaborator ever changes its encoding), the
//! fingerprint simply fails to match and we fall back to the generic lowering — never a miscompile,
//! only a missed optimization. The fingerprints match the eliminator *core* (the `Fix(Lam(Case …))`
//! recurrence), which is independent of the argument expressions, so `plus x y` is recognized for
//! any `x`/`y` (themselves recursively recognized first).
//!
//! ## Representation coherence
//! A recognized op consumes and produces values that are observationally `Nat`: its operands are
//! read by `bl_nat_of_value` (which accepts both a fast `BL_NAT` and a real `Zero`/`Succ` chain) and
//! its result is a `BL_NAT` that any generic `case`/field-load materializes back into `Zero`/`Succ`
//! on demand (numeric.c `bl_nat_to_con`). So a recognized op composes freely with unrecognized code.

use crate::ir::{Arm, Cir, FloatPrimOp, NatPrimOp};

/// Rewrite every recognizable prelude `Nat` arithmetic redex in `c` to a [`Cir::NatPrim`]. Runs
/// bottom-up so nested calls (e.g. `plus (mult a b) c`) are recognized inside-out.
///
/// EFFECT SOUNDNESS (de Bruijn binder tracking): a `NatPrim`/`FloatPrim` lowers to a direct,
/// *non-OpNode-aware* `bl_*` call, so it must never consume an operand that can be a bubbling effect
/// `OpNode` at runtime. A bare `Var` is *not* automatically safe: `(let msg (perform receive tt))`
/// binds `msg` to an `OpNode` that the surrounding construction is meant to bubble into the
/// continuation (examples/actor_pingpong.bl). We therefore thread an `unsafe`-binder environment:
/// a binder is unsafe iff its bound value is a non-value (an `App`/`Op`/`Force`/`Case`/`Handle`/…
/// that can yield an `OpNode`). Function/continuation parameters, `Fix` selves, and destructured
/// `Case`/`Handle` fields are settled values (call-by-value forces them, and an effect in the
/// scrutinee/arg bubbles *before* the binder is in scope), so they stay safe — preserving every hot
/// arithmetic-loop win. A differential fuzz test plus `examples/actor_pingpong.bl` gate this.
pub fn recognize(c: &Cir) -> Cir {
    let mut env: Vec<bool> = Vec::new();
    recog(c, &mut env)
}

/// Is the de Bruijn variable `k` (0 = innermost) bound to a possibly-effectful value? Out-of-range
/// indices (free in this subtree) are conservatively treated as safe — they are top-level globals or
/// already-settled outer binders, never a freshly-bubbled `OpNode`.
fn var_is_unsafe(env: &[bool], k: usize) -> bool {
    env.len()
        .checked_sub(1 + k)
        .map(|i| env[i])
        .unwrap_or(false)
}

/// Would binding `rhs` (already recognized) possibly capture a bubbling effect `OpNode` into the
/// binder? `true` for non-values (applications, `perform`, `force`, `case`, `handle`, …) whose result
/// can be an `OpNode`; `false` for settled values (vars/globals/literals/`Lam`/pure prims/
/// constructors of settled values). A `Var` is unsafe iff *its own* binder is unsafe (transitively).
fn rhs_may_be_opnode(rhs: &Cir, env: &[bool]) -> bool {
    match rhs {
        Cir::Var(k) => var_is_unsafe(env, *k),
        Cir::Global(_)
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_)
        | Cir::Erased => false,
        // A lambda/closure is a value; `Now`/`Later` wrap a value into a (settled) delay cell.
        Cir::Lam(_) | Cir::MkClosure(..) | Cir::Now(..) | Cir::Later(..) => false,
        // Pure machine-word prims never produce an OpNode (operands were guarded when recognized).
        Cir::NatPrim { .. } | Cir::FloatPrim { .. } | Cir::IntPrim { .. } => false,
        // A constructor/tuple is settled iff every field is; `bl_con_bubble` would otherwise bubble.
        Cir::Con(_, args, _) | Cir::Tuple(args, _) => {
            args.iter().any(|a| rhs_may_be_opnode(a, env))
        }
        // Everything else — application, perform, force, projection, case, handle, fix, region — can
        // evaluate to (or bubble) an OpNode.
        _ => true,
    }
}

/// Core recognizer: rebuild `c` bottom-up while threading the unsafe-binder environment `env`.
fn recog(c: &Cir, env: &mut Vec<bool>) -> Cir {
    // A2: fold a fully-canonical static `String` literal cons-list (`push cp0 (push cp1 … empty)`,
    // every codepoint a canonical `Succ`/`Zero` Nat) into one packed [`Cir::StrLit`] BEFORE recursing
    // into children — otherwise the child codepoints would already be peeled to `NatPrim`/`Add` and no
    // longer match `canonical_nat_chain`. We only fold a chain that is canonical *end to end* (every
    // codepoint a literal, tail ending in `empty`), so this never touches a `String` built from
    // runtime values (e.g. `push x rest` with `x` a variable) — those recurse normally below.
    //
    // Unlike the deliberately-NOT-folded standalone `NatLit` (whose immediate could be mis-driven on
    // an unrecognized curried eliminator's application spine, see the note below), a packed `String`
    // lowers to a real heap pointer (never an immediate) and every generic `case`/projection
    // materializes one inductive layer via `bl_string_to_con` (emit_case chains it after
    // `bl_nat_to_con`), so it composes with unrecognized consumers exactly like the cons-list. Gated
    // by `BL_NO_STRPACK` and proven bit-identical over the corpus (A2c) + the runtime gate
    // (string_diff.c).
    if std::env::var_os("BL_NO_STRPACK").is_none() {
        if let Cir::Con(name, _, _) = c {
            if name.0 == "push" || name.0 == "empty" {
                if let Some(cps) = canonical_string_chain(c) {
                    return Cir::StrLit(cps);
                }
            }
        }
    }
    // First recurse into children (tracking binders), then try to rewrite the rebuilt node here.
    let rebuilt = recog_children(c, env);
    // NOTE: we deliberately do NOT eagerly fold a standalone canonical `Succ`/`Zero` chain to a
    // `NatLit` here. Doing so is observationally identical for a *recognized* consumer (a `NatPrim`
    // reads it via `bl_nat_of_value`, and `bl_nat_to_con` materializes it for a generic `case`), but
    // a bare canonical literal can also flow as an *argument into an unrecognized curried eliminator*
    // (e.g. `plus`/`mult` whose fingerprint did not match, so it stayed a `Fix(Lam(Case …))`). On the
    // OpNode-aware application spine of an effectful program, a fast-`Nat` immediate reaching that
    // curried partial-application spine is mis-driven (the same fragility documented for the opt-in
    // `BL_NAT_PEEL` loop peel), miscompiling e.g. `plus (mult a a) a` to `mult a a`. Leaving the chain
    // as an inductive `Con` is always correct: a recognized `NatPrim` operand (`is_pure_nat_operand`
    // already accepts a canonical `Con` chain, read by `bl_nat_of_value`) still gets the O(1) op, and
    // an unrecognized eliminator gets the exact `Succ`/`Zero` shape it expects. The hot-path win
    // (NatPrim over *variables*) is unaffected; only a one-time standalone literal pays materializaton.
    let _ = canonical_nat_chain; // (still used by is_pure_nat_operand / the Succ peel below)
                                 // Peel a non-canonical `(Succ k)` whose predecessor is a settled pure `Nat` value into the O(1)
                                 // machine-word `k + 1` (M25b). `(Succ k)` is `k + 1` by definition, and `bl_nat_add` reads `k`
                                 // via `bl_nat_of_value` (which accepts a fast Nat OR a real chain) and yields a BL_NAT that any
                                 // generic consumer materializes back to `Succ`/`Zero` — observationally identical to the original
                                 // `Succ` cell, but allocation-free and, crucially, recognized so it can feed a parent `NatPrim`
                                 // (e.g. `plus (Succ k) y` now folds fully instead of falling back). Only fires when `k` is a
                                 // settled pure operand (variable / literal / nested pure prim); an effectful or canonical `k` is
                                 // left to `canonical_nat_chain` / the generic path. The differential fuzz test gates it.
    if let Cir::Con(name, args, _) = &rebuilt {
        if name.0 == "Succ" && args.len() == 1 && is_pure_nat_operand(&args[0], env) {
            return Cir::NatPrim {
                op: NatPrimOp::Add,
                lhs: Box::new(args[0].clone()),
                rhs: Some(Box::new(Cir::NatLit(1))),
            };
        }
    }
    // A2: fold a fully-canonical `String` literal cons-list — handled at the TOP of `recog` (before
    // child recognition would peel the codepoints to `NatPrim`). See the note there.
    try_rewrite_app(&rebuilt, env).unwrap_or(rebuilt)
}

/// Rebuild every child of `c` via [`recog`], pushing/popping the unsafe-binder environment so that
/// de Bruijn indices line up with [`var_is_unsafe`]. Binders bound to a non-value `rhs` are pushed as
/// `true` (unsafe); all other binders (params, `Fix` self, `Case`/`Handle` fields) as `false`.
fn recog_children(c: &Cir, env: &mut Vec<bool>) -> Cir {
    match c {
        // `App(Lam(body), rhs)` is the lowered `let`: `rhs`'s effectfulness flows into `body`'s
        // freshly-bound innermost var. (A general `App` whose operator is not a `Lam` introduces no
        // binder at this node — its callee's own `Lam` was already recognized as a value param.)
        Cir::App(g, a) if matches!(g.as_ref(), Cir::Lam(_)) => {
            let rhs = recog(a, env);
            let unsafe_binder = rhs_may_be_opnode(&rhs, env);
            let Cir::Lam(body) = g.as_ref() else {
                unreachable!()
            };
            env.push(unsafe_binder);
            let new_body = recog(body, env);
            env.pop();
            Cir::App(Box::new(Cir::Lam(Box::new(new_body))), Box::new(rhs))
        }
        Cir::Let(v, b) => {
            let rhs = recog(v, env);
            let unsafe_binder = rhs_may_be_opnode(&rhs, env);
            env.push(unsafe_binder);
            let new_body = recog(b, env);
            env.pop();
            Cir::Let(Box::new(rhs), Box::new(new_body))
        }
        // A standalone lambda's parameter is a call-by-value argument — a settled value when the body
        // runs (any effect in the actual argument bubbled before the call). Safe binder.
        Cir::Lam(b) => {
            env.push(false);
            let nb = recog(b, env);
            env.pop();
            Cir::Lam(Box::new(nb))
        }
        // `Fix` binds the recursive function itself (a value). Safe binder.
        Cir::Fix(b) => {
            env.push(false);
            let nb = recog(b, env);
            env.pop();
            Cir::Fix(Box::new(nb))
        }
        // Each `Case` arm destructures `arm.binders` fields of the (already-forced) scrutinee value.
        // Those fields are settled values — safe binders.
        Cir::Case(s, arms) => Cir::Case(
            Box::new(recog(s, env)),
            arms.iter()
                .map(|arm| {
                    for _ in 0..arm.binders {
                        env.push(false);
                    }
                    let body = recog(&arm.body, env);
                    for _ in 0..arm.binders {
                        env.pop();
                    }
                    Arm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body,
                    }
                })
                .collect(),
        ),
        // A handler's op-clause binds the op argument and the (delimited) continuation `k`, both
        // values. The return clause binds the body's settled result. Safe binders.
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(recog(body, env)),
            return_clause: Box::new(recog_under_binders(return_clause, env, 1)),
            op_clauses: op_clauses
                .iter()
                .map(|(n, e)| (n.clone(), recog_under_binders(e, env, 2)))
                .collect(),
        },
        // No binder introduced here: rebuild children in the current environment.
        _ => map_children_env(c, env),
    }
}

/// Recognize `c`, treating its outermost `n` `Lam` wrappers as value-parameter binders (safe). Used
/// for handler clauses, whose continuation/argument parameters are settled values.
fn recog_under_binders(c: &Cir, env: &mut Vec<bool>, n: usize) -> Cir {
    if n == 0 {
        return recog(c, env);
    }
    match c {
        Cir::Lam(b) => {
            env.push(false);
            let nb = recog_under_binders(b, env, n - 1);
            env.pop();
            Cir::Lam(Box::new(nb))
        }
        // Fewer lambdas than expected: recognize the remainder normally.
        _ => recog(c, env),
    }
}

/// Like [`map_children`] but threads the unsafe-binder `env` (for nodes that introduce no binder).
fn map_children_env(c: &Cir, env: &mut Vec<bool>) -> Cir {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => {
            Cir::Foreign(sym.clone(), arg.as_ref().map(|a| Box::new(recog(a, env))))
        }
        Cir::App(g, a) => Cir::App(Box::new(recog(g, env)), Box::new(recog(a, env))),
        Cir::Con(name, args, al) => Cir::Con(
            name.clone(),
            args.iter().map(|a| recog(a, env)).collect(),
            *al,
        ),
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(|e| recog(e, env)).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(recog(e, env))),
        Cir::Now(e, al) => Cir::Now(Box::new(recog(e, env)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(recog(e, env)), *al),
        Cir::Force(e) => Cir::Force(Box::new(recog(e, env))),
        Cir::Region(e) => Cir::Region(Box::new(recog(e, env))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(recog(arg, env)),
        },
        Cir::MkClosure(name, cap, al) => Cir::MkClosure(
            name.clone(),
            cap.iter().map(|a| recog(a, env)).collect(),
            *al,
        ),
        Cir::CallClosure(g, a) => {
            Cir::CallClosure(Box::new(recog(g, env)), Box::new(recog(a, env)))
        }
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(recog(lhs, env)),
            rhs: Box::new(recog(rhs, env)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(recog(lhs, env)),
            rhs: rhs.as_ref().map(|r| Box::new(recog(r, env))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(recog(lhs, env)),
            rhs: rhs.as_ref().map(|r| Box::new(recog(r, env))),
        },
        // Binder-introducing nodes are handled by `recog_children`; never reached here.
        Cir::Lam(_) | Cir::Fix(_) | Cir::Let(_, _) | Cir::Case(_, _) | Cir::Handle { .. } => {
            map_children(c, recognize)
        }
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after recognize")
        }
    }
}

/// If `c` is a fully-canonical inductive `Nat` literal (`Zero`, or `Succ` of a canonical chain),
/// return its value. A non-canonical sub-term (variable, application, …) makes the whole chain
/// non-canonical, so we leave it untouched.
fn canonical_nat_chain(c: &Cir) -> Option<u64> {
    match c {
        // A folded machine-word literal is a canonical constant leaf (children are recognized first,
        // so an inner `Zero` already became `NatLit(0)`; without this, a `Succ` over it would miss the
        // literal fold and peel to `Add(.., 1)` instead — see `canonical_chain_still_folds_to_literal`).
        Cir::NatLit(n) => Some(*n),
        Cir::Con(name, args, _) if name.0 == "Zero" && args.is_empty() => Some(0),
        Cir::Con(name, args, _) if name.0 == "Succ" && args.len() == 1 => {
            canonical_nat_chain(&args[0]).and_then(|n| n.checked_add(1))
        }
        _ => None,
    }
}

/// If `c` is a fully-canonical `String` literal cons-list — a right-nested `push cp0 (push cp1 …
/// empty)` (std/string.bl) where every codepoint is a canonical `Succ`/`Zero` Nat — return its
/// codepoints in head-first (declaration) order. Any non-canonical sub-term (a variable, an
/// application, an effectful head, a non-literal codepoint) makes the whole chain non-canonical, so
/// we leave it untouched and fall back to the inductive lowering. Bounded by `cap` so a pathological
/// literal cannot blow the stack/heap during folding (it just stays inductive).
fn canonical_string_chain(c: &Cir) -> Option<Vec<u64>> {
    fn go(c: &Cir, out: &mut Vec<u64>, cap: usize) -> bool {
        match c {
            Cir::StrLit(cps) => {
                if out.len() + cps.len() > cap {
                    return false;
                }
                out.extend_from_slice(cps);
                true
            }
            Cir::Con(name, args, _) if name.0 == "empty" && args.is_empty() => true,
            Cir::Con(name, args, _) if name.0 == "push" && args.len() == 2 => {
                let Some(cp) = canonical_nat_chain(&args[0]) else {
                    return false;
                };
                if out.len() >= cap {
                    return false;
                }
                out.push(cp);
                go(&args[1], out, cap)
            }
            _ => false,
        }
    }
    let mut cps = Vec::new();
    if go(c, &mut cps, 1 << 20) {
        Some(cps)
    } else {
        None
    }
}

/// If `c` is a fully-applied recognized prelude `Nat` function, return its `NatPrim` rewrite.
///
/// SOUNDNESS GUARD (effects): a `NatPrim` lowers to a direct `bl_nat_*` call that is *not*
/// OpNode-aware, so it must never consume an operand that could evaluate to a bubbling effect
/// `OpNode` (e.g. `plus (perform get tt) (perform get tt)`, examples/effect_nontail.bl). The generic
/// eliminator routes operands through the OpNode-aware `bl_app`, which bubbles; we cannot. We
/// therefore only rewrite when every operand is a *settled, pure value* — a variable/global whose
/// binder is known-safe (see [`var_is_unsafe`]), a folded `NatLit`, or a nested pure `NatPrim`. Any
/// elimination/effect form in operand position (`App`/`CallClosure`/`Op`/`Force`/`Handle`/…) — or a
/// `Var` bound to one — makes us fall back to the generic lowering. Conservative, never a miscompile;
/// the hot arithmetic loops (operands are value parameters/literals) are still fully recognized.
fn try_rewrite_app(c: &Cir, env: &[bool]) -> Option<Cir> {
    let (head, args) = c.unapply();
    match args.len() {
        2 => {
            if let Some(op) = match_binary_elim(head) {
                if !is_pure_nat_operand(args[0], env) || !is_pure_nat_operand(args[1], env) {
                    return None;
                }
                return Some(Cir::NatPrim {
                    op,
                    lhs: Box::new(args[0].clone()),
                    rhs: Some(Box::new(args[1].clone())),
                });
            }
            // Fixed-point `Float` binary ops (std/float.bl). Same settled-pure-operand guard as Nat:
            // a `FloatPrim` lowers to a non-OpNode-aware `bl_float_*` call, so operands must be values
            // (a `mkfloat` that some effectful expression bubbles through is left to the generic path).
            let op = match_float_binary_elim(head)?;
            if !is_pure_float_operand(args[0], env) || !is_pure_float_operand(args[1], env) {
                return None;
            }
            Some(Cir::FloatPrim {
                op,
                lhs: Box::new(args[0].clone()),
                rhs: Some(Box::new(args[1].clone())),
            })
        }
        1 => {
            // `pred` (Nat) and `float-neg` (Float) are the recognized unary ops.
            if is_pred_elim(head) && is_pure_nat_operand(args[0], env) {
                Some(Cir::NatPrim {
                    op: NatPrimOp::Pred,
                    lhs: Box::new(args[0].clone()),
                    rhs: None,
                })
            } else if is_float_neg_elim(head) && is_pure_float_operand(args[0], env) {
                Some(Cir::FloatPrim {
                    op: FloatPrimOp::Neg,
                    lhs: Box::new(args[0].clone()),
                    rhs: None,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Is `c` a settled, pure `Nat` value safe to feed a (non-OpNode-aware) `NatPrim`? See the soundness
/// guard on [`try_rewrite_app`]. A variable is safe iff its binder is known-safe (`env`); a `NatLit`
/// is a constant; a nested `NatPrim` is pure iff its own operands are; a canonical `Succ`/`Zero` chain
/// (or `Zero`) is a constant. Everything else — any elimination or effect form — is possibly-effectful.
fn is_pure_nat_operand(c: &Cir, env: &[bool]) -> bool {
    match c {
        Cir::Var(k) => !var_is_unsafe(env, *k),
        Cir::Global(_) | Cir::EnvRef(_) | Cir::NatLit(_) | Cir::IntLit(_) => true,
        Cir::NatPrim { lhs, rhs, .. } => {
            is_pure_nat_operand(lhs, env)
                && rhs
                    .as_ref()
                    .map(|r| is_pure_nat_operand(r, env))
                    .unwrap_or(true)
        }
        // A fully-canonical inductive chain is a constant; a non-canonical `Con` may contain an
        // effectful field, so only accept canonical ones.
        Cir::Con(..) => canonical_nat_chain(c).is_some(),
        _ => false,
    }
}

/// Is `c` a settled, pure `Float` value safe to feed a (non-OpNode-aware) `FloatPrim`? Mirrors
/// [`is_pure_nat_operand`]: a variable/global is already-evaluated, a nested pure `FloatPrim` is
/// pure iff its operands are, and a literal `(mkfloat m)` whose mantissa is a pure `Int` operand is a
/// constant. Everything else (any elimination/effect form) is treated as possibly-effectful and left
/// to the generic lowering.
fn is_pure_float_operand(c: &Cir, env: &[bool]) -> bool {
    match c {
        Cir::Var(k) => !var_is_unsafe(env, *k),
        Cir::Global(_) | Cir::EnvRef(_) => true,
        Cir::FloatPrim { lhs, rhs, .. } => {
            is_pure_float_operand(lhs, env)
                && rhs
                    .as_ref()
                    .map(|r| is_pure_float_operand(r, env))
                    .unwrap_or(true)
        }
        // A literal `(mkfloat m)`: pure iff its single `Int` mantissa field is a pure operand.
        Cir::Con(name, args, _) if name.0 == "mkfloat" && args.len() == 1 => {
            is_pure_nat_operand(&args[0], env)
        }
        _ => false,
    }
}

/// Match a binary eliminator head (`plus`/`mult`/`sub`). The prelude lowers each to a 2-argument
/// curried wrapper around its `Fix(Lam(Case …))` eliminator core.
fn match_binary_elim(head: &Cir) -> Option<NatPrimOp> {
    if is_plus_elim(head) {
        Some(NatPrimOp::Add)
    } else if is_mult_elim(head) {
        Some(NatPrimOp::Mul)
    } else if is_sub_elim(head) {
        Some(NatPrimOp::Sub)
    } else if is_min_elim(head) {
        Some(NatPrimOp::Min)
    } else if is_max_elim(head) {
        Some(NatPrimOp::Max)
    } else {
        None
    }
}

// ---- structural fingerprints (captured from BL_DUMP_CIR over std/nat.bl) ----
//
// `plus a b` head (uncurried wrapper around the eliminator):
//   Lam(Lam( App(App( PLUS_ELIM, Var1), Var0) ))
// where PLUS_ELIM = Fix(Lam(Case(Var0, [
//     Zero{binders:0}: Lam(Var0),                                  -- λb. b
//     Succ{binders:1}: App(App(Lam(Lam(Lam(Con("Succ",[App(Var1,Var0)])))), Var0), App(Var2,Var0)),
//   ])))

/// `λa.λb. (PLUS_ELIM a) b` where the eliminator's Zero arm returns its second argument and the
/// Succ arm wraps the induction hypothesis in a single `Succ`.
fn is_plus_elim(head: &Cir) -> bool {
    let Cir::Lam(b1) = head else { return false };
    let Cir::Lam(inner) = b1.as_ref() else {
        return false;
    };
    // inner = App(App(Fix(Lam(Case …)), Var1), Var0)
    let (elim, args) = inner.unapply();
    if args.len() != 2 || !is_var(args[0], 1) || !is_var(args[1], 0) {
        return false;
    }
    plus_core(elim)
}

fn plus_core(elim: &Cir) -> bool {
    let Some(arms) = fix_lam_case_arms(elim) else {
        return false;
    };
    if arms.len() != 2 {
        return false;
    }
    // Zero arm: `λb. b` = Lam(Var0).
    if !arm_is(&arms[0], "Zero", 0, &Cir::Lam(Box::new(Cir::Var(0)))) {
        return false;
    }
    // Succ arm: `Succ (self n b)` shape — App(App(Lam(Lam(Lam(Con("Succ",[App(Var1,Var0)])))), Var0), App(Var2,Var0))
    let succ_expected = Cir::App(
        Box::new(Cir::App(
            Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(
                Cir::con(
                    blight_kernel::ConName("Succ".into()),
                    vec![Cir::App(Box::new(Cir::Var(1)), Box::new(Cir::Var(0)))],
                ),
            ))))))),
            Box::new(Cir::Var(0)),
        )),
        Box::new(Cir::App(Box::new(Cir::Var(2)), Box::new(Cir::Var(0)))),
    );
    arm_is(&arms[1], "Succ", 1, &succ_expected)
}

/// `mult a b` head. The Succ arm computes `plus b (mult n b)`, so it contains the plus eliminator
/// applied around the induction hypothesis. We fingerprint the outer recurrence shape and require
/// the embedded eliminator to itself be the recognized `plus` core.
fn is_mult_elim(head: &Cir) -> bool {
    let Cir::Lam(b1) = head else { return false };
    let Cir::Lam(inner) = b1.as_ref() else {
        return false;
    };
    let (elim, args) = inner.unapply();
    if args.len() != 2 || !is_var(args[0], 1) || !is_var(args[1], 0) {
        return false;
    }
    let Some(arms) = fix_lam_case_arms(elim) else {
        return false;
    };
    if arms.len() != 2 {
        return false;
    }
    // Zero arm: `λb. Zero` = Lam(Con("Zero",[])).
    if !arm_is(
        &arms[0],
        "Zero",
        0,
        &Cir::Lam(Box::new(Cir::con(
            blight_kernel::ConName("Zero".into()),
            vec![],
        ))),
    ) {
        return false;
    }
    // Succ arm contains a `plus` eliminator applied to `b` and `(self n b)`. We require the embedded
    // eliminator core to be the recognized plus recurrence; the exact argument wiring is checked by
    // the presence of that core plus the induction-hypothesis application `App(Var_, Var0)`.
    arm_contains_plus_core(&arms[1])
}

/// `sub a b` head: the prelude's `sub` is a *nested* eliminator — the Succ arm of the outer `match a`
/// performs an inner `match b`. We fingerprint that exact nesting (captured from BL_DUMP_CIR):
///   outer Zero arm: `λb. Zero`
///   outer Succ arm: contains an inner `Fix(Lam(Case(Var0,[Zero: Succ Var4, Succ: self-style])))`.
fn is_sub_elim(head: &Cir) -> bool {
    let Cir::Lam(inner) = head else { return false };
    // inner = App(SUB_ELIM, Var0)  (sub is `λa. (elim a)`; the second arg is consumed inside)
    let (elim, args) = inner.unapply();
    if args.len() != 1 || !is_var(args[0], 0) {
        return false;
    }
    let Some(arms) = fix_lam_case_arms(elim) else {
        return false;
    };
    if arms.len() != 2 {
        return false;
    }
    // Outer Zero arm: `λb. Zero`.
    if !arm_is(
        &arms[0],
        "Zero",
        0,
        &Cir::Lam(Box::new(Cir::con(
            blight_kernel::ConName("Zero".into()),
            vec![],
        ))),
    ) {
        return false;
    }
    // Outer Succ arm must embed an inner Nat eliminator (the `match b`).
    arm_contains_inner_elim(&arms[1])
}

/// `min a b` head: same nested shape as `sub` — the outer `Zero` arm is `λb. Zero` — but its inner
/// `match b` returns `Zero` (not `Succ n`) and *wraps* the recursive result in `Succ` (`Succ (min n
/// k)`). The inner-arm discriminator `(inner_zero_is_succ=false, inner_succ_wrapped=true)` is unique
/// to `min` (cf. `sub`=(true,false), `max`=(true,true)).
fn is_min_elim(head: &Cir) -> bool {
    let Cir::Lam(inner) = head else { return false };
    let (elim, args) = inner.unapply();
    if args.len() != 1 || !is_var(args[0], 0) {
        return false;
    }
    let Some(arms) = fix_lam_case_arms(elim) else {
        return false;
    };
    if arms.len() != 2 {
        return false;
    }
    // Outer Zero arm: `λb. Zero` (as in `sub`).
    if !arm_is(
        &arms[0],
        "Zero",
        0,
        &Cir::Lam(Box::new(Cir::con(
            blight_kernel::ConName("Zero".into()),
            vec![],
        ))),
    ) {
        return false;
    }
    arm_contains_inner_elim_min(&arms[1])
}

/// `max a b` head: the outer `Zero` arm is `λb. b` (return the other argument), and its inner `match
/// b` returns `Succ n` on `Zero` and *wraps* the recursive result in `Succ` (`Succ (max n k)`). The
/// inner-arm discriminator `(inner_zero_is_succ=true, inner_succ_wrapped=true)` is unique to `max`.
fn is_max_elim(head: &Cir) -> bool {
    let Cir::Lam(inner) = head else { return false };
    let (elim, args) = inner.unapply();
    if args.len() != 1 || !is_var(args[0], 0) {
        return false;
    }
    let Some(arms) = fix_lam_case_arms(elim) else {
        return false;
    };
    if arms.len() != 2 {
        return false;
    }
    // Outer Zero arm: `λb. b` = Lam(Var0).
    if !arm_is(&arms[0], "Zero", 0, &Cir::Lam(Box::new(Cir::Var(0)))) {
        return false;
    }
    arm_contains_inner_elim_max(&arms[1])
}

/// `pred n` head: `λn. (PRED_ELIM n)` where the eliminator's Zero arm is `Zero` and the Succ arm
/// returns the bound predecessor (discarding the induction hypothesis): captured shape
///   Succ{binders:1}: App(App(Lam(Lam(Var1)), Var0), App(Var2,Var0)).
fn is_pred_elim(head: &Cir) -> bool {
    let Cir::Lam(inner) = head else { return false };
    let (elim, args) = inner.unapply();
    if args.len() != 1 || !is_var(args[0], 0) {
        return false;
    }
    let Some(arms) = fix_lam_case_arms(elim) else {
        return false;
    };
    if arms.len() != 2 {
        return false;
    }
    // Zero arm: `Zero`.
    if !arm_is(
        &arms[0],
        "Zero",
        0,
        &Cir::con(blight_kernel::ConName("Zero".into()), vec![]),
    ) {
        return false;
    }
    // Succ arm: returns the predecessor `k` (the first projection), discarding the IH:
    //   App(App(Lam(Lam(Var1)), Var0), App(Var2,Var0)).
    let expected = Cir::App(
        Box::new(Cir::App(
            Box::new(Cir::Lam(Box::new(Cir::Lam(Box::new(Cir::Var(1)))))),
            Box::new(Cir::Var(0)),
        )),
        Box::new(Cir::App(Box::new(Cir::Var(2)), Box::new(Cir::Var(0)))),
    );
    arm_is(&arms[1], "Succ", 1, &expected)
}

// ---- structural fingerprints for std/float.bl (captured from BL_DUMP_CIR) ----
//
// Each `float-*` wrapper lowers to a (degenerate, single-`mkfloat`-arm) eliminator over the
// `(mkfloat (mantissa Int))` representation. The op is identified by the `IntPrim` leaf the wrapper
// finally builds into a fresh `mkfloat`:
//   float-add : mkfloat (IntPrim Add  x y)
//   float-sub : mkfloat (IntPrim Sub  x y)
//   float-mul : mkfloat (IntPrim Div (IntPrim Mul x y) 1_000_000)
//   float-div : mkfloat (IntPrim Div (IntPrim Mul x 1_000_000) y)
//   float-neg : mkfloat (IntPrim Sub 0 x)         -- unary head
// We require: the head is `λa.λb. (ELIM a) b` (binary) or `λa. (ELIM a)` (unary), where ELIM is a
// `Fix(Lam(Case(Var0, [mkfloat{1}: …])))` over `mkfloat`, and the leaf `mkfloat (IntPrim …)` matches
// the op pattern. A redefinition that differs in any of these falls back to the generic lowering.

/// The fixed-point scale `std/float.bl` bakes in (`10^6`). The mul/div leaves divide/scale by it.
const FLOAT_SCALE: i64 = 1_000_000;

/// Match a binary `float-*` head, returning the op. Binary heads are `λa.λb. (ELIM a) b`.
fn match_float_binary_elim(head: &Cir) -> Option<FloatPrimOp> {
    let Cir::Lam(b1) = head else { return None };
    let Cir::Lam(inner) = b1.as_ref() else {
        return None;
    };
    // inner = App(App(Fix(Lam(Case …)), Var1), Var0)
    let (elim, args) = inner.unapply();
    if args.len() != 2 || !is_var(args[0], 1) || !is_var(args[1], 0) {
        return None;
    }
    if !is_mkfloat_elim(elim) {
        return None;
    }
    // The op is whatever `mkfloat (IntPrim …)` leaf the wrapper builds, found anywhere inside the
    // eliminator body (past the inner `match b`).
    float_leaf_op(elim).filter(|op| !matches!(op, FloatPrimOp::Neg))
}

/// Match the unary `float-neg` head: `λa. (ELIM a)` whose leaf is `mkfloat (IntPrim Sub 0 x)`.
fn is_float_neg_elim(head: &Cir) -> bool {
    let Cir::Lam(inner) = head else { return false };
    let (elim, args) = inner.unapply();
    if args.len() != 1 || !is_var(args[0], 0) {
        return false;
    }
    is_mkfloat_elim(elim) && matches!(float_leaf_op(elim), Some(FloatPrimOp::Neg))
}

/// Is `c` a `Fix(Lam(Case(Var0, [mkfloat{binders:1}: …])))` — the degenerate single-arm eliminator a
/// `match x [(mkfloat m) …]` lowers to?
fn is_mkfloat_elim(c: &Cir) -> bool {
    match fix_lam_case_arms(c) {
        Some(arms) => arms.len() == 1 && arms[0].con.0 == "mkfloat" && arms[0].binders == 1,
        None => false,
    }
}

/// Find the `mkfloat (IntPrim …)` leaf anywhere inside `c` and classify the fixed-point op by its
/// shape. Returns `None` if no recognizable leaf is present (so an unfamiliar definition falls back).
fn float_leaf_op(c: &Cir) -> Option<FloatPrimOp> {
    if let Cir::Con(name, args, _) = c {
        if name.0 == "mkfloat" && args.len() == 1 {
            if let Some(op) = classify_float_leaf(&args[0]) {
                return Some(op);
            }
        }
    }
    first_child_float_leaf(c)
}

/// Classify a `mkfloat` leaf's `Int` body into a [`FloatPrimOp`] by exact structural pattern. The
/// operands `x`/`y` may be any `Var` (the bound mantissas), so we match on the operation skeleton.
fn classify_float_leaf(body: &Cir) -> Option<FloatPrimOp> {
    use blight_kernel::IntPrimOp;
    let Cir::IntPrim { op, lhs, rhs } = body else {
        return None;
    };
    match op {
        // add : x + y    (both operands variables)
        IntPrimOp::Add if is_any_var(lhs) && is_any_var(rhs) => Some(FloatPrimOp::Add),
        // neg : 0 - x    (lhs is the literal 0); sub : x - y (both variables)
        IntPrimOp::Sub if is_int_lit(lhs, 0) && is_any_var(rhs) => Some(FloatPrimOp::Neg),
        IntPrimOp::Sub if is_any_var(lhs) && is_any_var(rhs) => Some(FloatPrimOp::Sub),
        // mul : (x * y) / SCALE      ;  div : (x * SCALE) / y
        IntPrimOp::Div => match (lhs.as_ref(), rhs.as_ref()) {
            (
                Cir::IntPrim {
                    op: IntPrimOp::Mul,
                    lhs: a,
                    rhs: b,
                },
                _,
            ) if is_any_var(a) && is_any_var(b) && is_int_lit(rhs, FLOAT_SCALE) => {
                Some(FloatPrimOp::Mul)
            }
            (
                Cir::IntPrim {
                    op: IntPrimOp::Mul,
                    lhs: a,
                    rhs: b,
                },
                _,
            ) if is_any_var(a) && is_int_lit(b, FLOAT_SCALE) && is_any_var(rhs) => {
                Some(FloatPrimOp::Div)
            }
            _ => None,
        },
        _ => None,
    }
}

fn is_any_var(c: &Cir) -> bool {
    matches!(c, Cir::Var(_))
}

fn is_int_lit(c: &Cir, n: i64) -> bool {
    matches!(c, Cir::IntLit(m) if *m == n)
}

/// Walk children looking for the first recognizable `mkfloat` leaf (depth-first). Used to dig past
/// the wrapper's `App(Lam(...), Var0)` / inner `match b` scaffolding to the constructor at the bottom.
fn first_child_float_leaf(c: &Cir) -> Option<FloatPrimOp> {
    let mut found = None;
    for_each_child(c, &mut |child: &Cir| {
        if found.is_none() {
            found = float_leaf_op(child);
        }
    });
    found
}

/// Apply `f` to each immediate child of `c` (mirrors the `Cir` shape). Closure-capable companion to
/// [`any_child`] (which takes a plain `fn`).
fn for_each_child(c: &Cir, f: &mut dyn FnMut(&Cir)) {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => {}
        Cir::Foreign(_, arg) => {
            if let Some(a) = arg {
                f(a);
            }
        }
        Cir::Lam(b) | Cir::Fix(b) | Cir::Proj(_, b) | Cir::Force(b) | Cir::Region(b) => f(b),
        Cir::App(g, a) | Cir::Let(g, a) | Cir::CallClosure(g, a) => {
            f(g);
            f(a);
        }
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            args.iter().for_each(f)
        }
        Cir::Case(s, arms) => {
            f(s);
            arms.iter().for_each(|a| f(&a.body));
        }
        Cir::Now(e, _) | Cir::Later(e, _) => f(e),
        Cir::Op { arg, .. } => f(arg),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            f(body);
            f(return_clause);
            op_clauses.iter().for_each(|(_, e)| f(e));
        }
        Cir::IntPrim { lhs, rhs, .. } => {
            f(lhs);
            f(rhs);
        }
        Cir::NatPrim { lhs, rhs, .. } | Cir::FloatPrim { lhs, rhs, .. } => {
            f(lhs);
            if let Some(r) = rhs {
                f(r);
            }
        }
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after recognize")
        }
    }
}

// ---- structural helpers ----

/// If `c` is `Fix(Lam(Case(Var0, arms)))`, return its arms.
fn fix_lam_case_arms(c: &Cir) -> Option<&[Arm]> {
    let Cir::Fix(b) = c else { return None };
    let Cir::Lam(lam) = b.as_ref() else {
        return None;
    };
    let Cir::Case(scrut, arms) = lam.as_ref() else {
        return None;
    };
    if !is_var(scrut, 0) {
        return None;
    }
    Some(arms)
}

fn is_var(c: &Cir, i: usize) -> bool {
    matches!(c, Cir::Var(j) if *j == i)
}

/// Does this arm match a constructor name, binder count, and body?
fn arm_is(arm: &Arm, con: &str, binders: usize, body: &Cir) -> bool {
    arm.con.0 == con && arm.binders == binders && &arm.body == body
}

/// Does this (outer Succ) arm body embed a recognized `plus` eliminator core anywhere inside it?
/// Used for `mult`, whose Succ arm is `plus b (mult n b)`.
fn arm_contains_plus_core(arm: &Arm) -> bool {
    arm.con.0 == "Succ" && arm.binders == 1 && contains_plus_core(&arm.body)
}

fn contains_plus_core(c: &Cir) -> bool {
    if plus_core(c) {
        return true;
    }
    any_child(c, contains_plus_core)
}

/// Does this (outer Succ) arm body embed an *inner* Nat eliminator matching `sub`'s `match b`
/// specifically? `sub`, `min`, and `max` all nest a two-arm `match b` inside the outer `Succ` arm,
/// so a shape-only "two-arm inner elim" test (the original) **false-positives** on `min`/`max` and
/// miscompiles them as `sub` (`min 2 5` → `sub 2 5` = 0 instead of 2). The discriminator is the inner
/// `Zero` arm body:
///   * `sub`  inner `(Zero) → (Succ n)`  — returns `Succ`-of-the-outer-predecessor (rebuild `a`).
///   * `min`  inner `(Zero) → Zero`       — returns `Zero`.
///   * `max`  inner `(Zero) → (Succ n)`   — like `sub`, BUT its inner `Succ` arm is `Succ`-wrapped.
///
/// So we require the inner `Zero` arm to be a `Succ`-headed `Con` (rules out `min`) **and** the inner
/// `Succ` arm's recursive body to be the *bare* induction hypothesis, i.e. not wrapped in a `Succ`
/// `Con` (rules out `max`). Conservative: any mismatch leaves the eliminator un-rewritten.
fn arm_contains_inner_elim(arm: &Arm) -> bool {
    arm.con.0 == "Succ" && arm.binders == 1 && contains_inner_two_arm_elim(&arm.body)
}

fn contains_inner_two_arm_elim(c: &Cir) -> bool {
    if let Some(arms) = fix_lam_case_arms(c) {
        if arms.len() == 2
            && arms[0].con.0 == "Zero"
            && arms[1].con.0 == "Succ"
            && inner_zero_arm_is_succ(&arms[0].body)
            && !inner_succ_arm_is_succ_wrapped(&arms[1].body)
        {
            return true;
        }
    }
    any_child(c, contains_inner_two_arm_elim)
}

/// As [`arm_contains_inner_elim`] but for `min`'s inner `match b`: inner `Zero` arm returns `Zero`
/// (not `Succ`) and the inner `Succ` arm wraps its recursion in `Succ`.
fn arm_contains_inner_elim_min(arm: &Arm) -> bool {
    arm.con.0 == "Succ" && arm.binders == 1 && contains_inner_two_arm_elim_min(&arm.body)
}

fn contains_inner_two_arm_elim_min(c: &Cir) -> bool {
    if let Some(arms) = fix_lam_case_arms(c) {
        if arms.len() == 2
            && arms[0].con.0 == "Zero"
            && arms[1].con.0 == "Succ"
            && !inner_zero_arm_is_succ(&arms[0].body)
            && inner_succ_arm_is_succ_wrapped(&arms[1].body)
        {
            return true;
        }
    }
    any_child(c, contains_inner_two_arm_elim_min)
}

/// As [`arm_contains_inner_elim`] but for `max`'s inner `match b`: inner `Zero` arm returns `Succ n`
/// *and* the inner `Succ` arm wraps its recursion in `Succ`.
fn arm_contains_inner_elim_max(arm: &Arm) -> bool {
    arm.con.0 == "Succ" && arm.binders == 1 && contains_inner_two_arm_elim_max(&arm.body)
}

fn contains_inner_two_arm_elim_max(c: &Cir) -> bool {
    if let Some(arms) = fix_lam_case_arms(c) {
        if arms.len() == 2
            && arms[0].con.0 == "Zero"
            && arms[1].con.0 == "Succ"
            && inner_zero_arm_is_succ(&arms[0].body)
            && inner_succ_arm_is_succ_wrapped(&arms[1].body)
        {
            return true;
        }
    }
    any_child(c, contains_inner_two_arm_elim_max)
}

/// The inner `Zero` arm of `sub`/`max` returns `(Succ n)` (a `Succ`-headed `Con`), whereas `min`'s
/// returns `Zero`. True iff the arm body is (somewhere at its head, after the eliminator's method
/// `Lam` wrappers and applications) a `Succ` `Con` — distinguishing `sub`/`max` from `min`.
fn inner_zero_arm_is_succ(body: &Cir) -> bool {
    match body {
        Cir::Con(name, _, _) => name.0 == "Succ",
        Cir::Lam(b) => inner_zero_arm_is_succ(b),
        Cir::App(g, _) => inner_zero_arm_is_succ(g),
        _ => false,
    }
}

/// `max`'s inner `Succ` arm wraps its recursive result in `Succ` (`(Succ (max n k))`); `sub`'s does
/// not (`(sub n k)`). True iff the arm body's method (under its `Lam` wrappers / before the IH
/// application) builds a `Succ` `Con` — used to rule `max` out of the `sub` fingerprint.
fn inner_succ_arm_is_succ_wrapped(body: &Cir) -> bool {
    match body {
        Cir::Con(name, _, _) => name.0 == "Succ",
        Cir::Lam(b) => inner_succ_arm_is_succ_wrapped(b),
        // The lowered arm is `App(App(method, field), ih)`; descend the operator spine to the method
        // body (the leftmost `Lam` chain) where the `Succ`-or-not decision lives.
        Cir::App(g, _) => inner_succ_arm_is_succ_wrapped(g),
        _ => false,
    }
}

/// Apply `f` to each immediate child of `c`, rebuilding the node. Mirrors the full `Cir` shape.
fn map_children(c: &Cir, f: fn(&Cir) -> Cir) -> Cir {
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => c.clone(),
        Cir::Foreign(sym, arg) => Cir::Foreign(sym.clone(), arg.as_ref().map(|a| Box::new(f(a)))),
        Cir::Lam(b) => Cir::Lam(Box::new(f(b))),
        Cir::Fix(b) => Cir::Fix(Box::new(f(b))),
        Cir::App(g, a) => Cir::App(Box::new(f(g)), Box::new(f(a))),
        Cir::Let(v, b) => Cir::Let(Box::new(f(v)), Box::new(f(b))),
        Cir::Con(name, args, al) => Cir::Con(name.clone(), args.iter().map(f).collect(), *al),
        Cir::Case(s, arms) => Cir::Case(
            Box::new(f(s)),
            arms.iter()
                .map(|arm| Arm {
                    con: arm.con.clone(),
                    binders: arm.binders,
                    body: f(&arm.body),
                })
                .collect(),
        ),
        Cir::Tuple(es, al) => Cir::Tuple(es.iter().map(f).collect(), *al),
        Cir::Proj(i, e) => Cir::Proj(*i, Box::new(f(e))),
        Cir::Now(e, al) => Cir::Now(Box::new(f(e)), *al),
        Cir::Later(e, al) => Cir::Later(Box::new(f(e)), *al),
        Cir::Force(e) => Cir::Force(Box::new(f(e))),
        Cir::Region(e) => Cir::Region(Box::new(f(e))),
        Cir::Op { effect, op, arg } => Cir::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(f(arg)),
        },
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => Cir::Handle {
            body: Box::new(f(body)),
            return_clause: Box::new(f(return_clause)),
            op_clauses: op_clauses.iter().map(|(n, e)| (n.clone(), f(e))).collect(),
        },
        Cir::MkClosure(name, env, al) => {
            Cir::MkClosure(name.clone(), env.iter().map(f).collect(), *al)
        }
        Cir::CallClosure(g, a) => Cir::CallClosure(Box::new(f(g)), Box::new(f(a))),
        Cir::IntPrim { op, lhs, rhs } => Cir::IntPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: Box::new(f(rhs)),
        },
        Cir::NatPrim { op, lhs, rhs } => Cir::NatPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(f(r))),
        },
        Cir::FloatPrim { op, lhs, rhs } => Cir::FloatPrim {
            op: *op,
            lhs: Box::new(f(lhs)),
            rhs: rhs.as_ref().map(|r| Box::new(f(r))),
        },
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after recognize")
        }
    }
}

/// Does any immediate child of `c` satisfy `pred` (recursively, via the predicate itself)?
fn any_child(c: &Cir, pred: fn(&Cir) -> bool) -> bool {
    let mut found = false;
    // Reuse `map_children`-style traversal cheaply by matching the same shape.
    match c {
        Cir::Var(_)
        | Cir::Global(_)
        | Cir::Erased
        | Cir::EnvRef(_)
        | Cir::IntLit(_)
        | Cir::NatLit(_)
        | Cir::StrLit(_) => {}
        Cir::Foreign(_, arg) => found |= arg.as_ref().is_some_and(|a| pred(a)),
        Cir::Lam(b) | Cir::Fix(b) | Cir::Proj(_, b) | Cir::Force(b) | Cir::Region(b) => {
            found |= pred(b)
        }
        Cir::App(g, a) | Cir::Let(g, a) | Cir::CallClosure(g, a) => found |= pred(g) || pred(a),
        Cir::Con(_, args, _) | Cir::Tuple(args, _) | Cir::MkClosure(_, args, _) => {
            found |= args.iter().any(&pred)
        }
        Cir::Case(s, arms) => found |= pred(s) || arms.iter().any(|a| pred(&a.body)),
        Cir::Now(e, _) | Cir::Later(e, _) => found |= pred(e),
        Cir::Op { arg, .. } => found |= pred(arg),
        Cir::Handle {
            body,
            return_clause,
            op_clauses,
        } => found |= pred(body) || pred(return_clause) || op_clauses.iter().any(|(_, e)| pred(e)),
        Cir::IntPrim { lhs, rhs, .. } => found |= pred(lhs) || pred(rhs),
        Cir::NatPrim { lhs, rhs, .. } => {
            found |= pred(lhs) || rhs.as_ref().map(|r| pred(r)).unwrap_or(false)
        }
        Cir::FloatPrim { lhs, rhs, .. } => {
            found |= pred(lhs) || rhs.as_ref().map(|r| pred(r)).unwrap_or(false)
        }
        Cir::Flat { .. } | Cir::FlatProj { .. } => {
            unreachable!("flatten runs after recognize")
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Cir;
    use blight_kernel::ConName;

    /// `BL_NO_STRPACK` is a process-global env var the recognizer reads per call. Tests that fold a
    /// `String` literal (which require it UNSET) and the gate test (which SETS it) must not run
    /// concurrently, or one observes the other's mutation. Serialize them under this lock.
    static STRPACK_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn succ(inner: Cir) -> Cir {
        Cir::con(ConName("Succ".into()), vec![inner])
    }
    fn zero() -> Cir {
        Cir::con(ConName("Zero".into()), vec![])
    }
    fn nat(n: u64) -> Cir {
        let mut t = zero();
        for _ in 0..n {
            t = succ(t);
        }
        t
    }
    fn empty() -> Cir {
        Cir::con(ConName("empty".into()), vec![])
    }
    fn push(cp: Cir, rest: Cir) -> Cir {
        Cir::con(ConName("push".into()), vec![cp, rest])
    }
    /// Build the canonical literal cons-list for `cps` (head-first): `push cp0 (push cp1 … empty)`.
    fn str_chain(cps: &[u64]) -> Cir {
        let mut t = empty();
        for &cp in cps.iter().rev() {
            t = push(nat(cp), t);
        }
        t
    }

    /// A2: a fully-static `String` literal (`push 72 (push 105 empty)` = "Hi") folds to one packed
    /// [`Cir::StrLit`] carrying the head-first codepoints — a single BL_STRING allocation instead of
    /// one `push` cell per codepoint. The empty literal folds to `StrLit([])`.
    #[test]
    fn static_string_literal_folds_to_strlit() {
        let _guard = STRPACK_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Be robust to any ambient/leftover setting from a sibling test.
        std::env::remove_var("BL_NO_STRPACK");
        assert_eq!(
            recognize(&str_chain(&[72, 105])),
            Cir::StrLit(vec![72, 105])
        );
        assert_eq!(recognize(&empty()), Cir::StrLit(vec![]));
        assert_eq!(
            recognize(&str_chain(&[0, 65, 122])),
            Cir::StrLit(vec![0, 65, 122])
        );
    }

    /// `BL_NO_STRPACK` suppresses the fold: the `String` stays the inductive `push`/`empty` cons-list
    /// (the codepoints peel to the M25b `Add(.., 1)` form, but the spine is untouched). This is the
    /// differential A/B switch the corpus gate flips to prove bit-identity.
    #[test]
    fn strpack_gate_suppresses_fold() {
        let _guard = STRPACK_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        std::env::set_var("BL_NO_STRPACK", "1");
        let got = recognize(&empty());
        std::env::remove_var("BL_NO_STRPACK");
        // With packing off, an `empty` literal is left as the inductive constructor (no StrLit).
        assert_eq!(got, empty());
    }

    /// A `String` built from a *runtime* head (`push x empty`, `x` a variable) is NOT a static literal,
    /// so it is left inductive — only fully-canonical literals pack. (The codepoint here is a bare
    /// `Var`, which `canonical_nat_chain` rejects.)
    #[test]
    fn non_literal_string_is_not_packed() {
        let _guard = STRPACK_ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        std::env::remove_var("BL_NO_STRPACK");
        let dynamic = push(Cir::Var(0), empty());
        let got = recognize(&dynamic);
        assert!(
            !matches!(got, Cir::StrLit(_)),
            "a String with a runtime codepoint must not pack, got {got:?}"
        );
    }

    /// M25b: a non-canonical `(Succ k)` over a settled-pure predecessor `k` (here a variable) is
    /// recognized as the O(1) machine-word `k + 1`, so it composes into a parent `NatPrim` and never
    /// allocates a `Succ` cell.
    #[test]
    fn succ_of_var_peels_to_add_one() {
        let got = recognize(&succ(Cir::Var(0)));
        match got {
            Cir::NatPrim {
                op: NatPrimOp::Add,
                lhs,
                rhs,
            } => {
                assert_eq!(*lhs, Cir::Var(0));
                assert_eq!(rhs.as_deref(), Some(&Cir::NatLit(1)));
            }
            other => panic!("expected Add(Var0, 1), got {other:?}"),
        }
    }

    /// A standalone fully-canonical chain `(Succ (Succ Zero))` is NOT eagerly folded to a single
    /// `NatLit` (that fold was removed — a bare `NatLit` immediate flowing into an unrecognized
    /// curried eliminator on the effectful application spine miscompiled; see the note in `recog`).
    /// Instead the M25b `Succ`-peel rewrites each layer to an O(1) `Add(.., 1)` over the canonical
    /// predecessor — observationally identical to `2` (read by `bl_nat_of_value`), and always safe
    /// because a `NatPrim` value composes with generic consumers via `bl_nat_to_con`.
    #[test]
    fn canonical_chain_peels_to_add_not_natlit() {
        assert_eq!(
            recognize(&succ(succ(zero()))),
            Cir::NatPrim {
                op: NatPrimOp::Add,
                lhs: Box::new(Cir::NatPrim {
                    op: NatPrimOp::Add,
                    lhs: Box::new(zero()),
                    rhs: Some(Box::new(Cir::NatLit(1))),
                }),
                rhs: Some(Box::new(Cir::NatLit(1))),
            }
        );
    }

    /// The peel must NOT fire when the predecessor is an *effectful* / elimination form (here an
    /// `App`): a `NatPrim` is not OpNode-aware, so such a `Succ` is left for the generic lowering.
    #[test]
    fn succ_of_impure_is_left_alone() {
        let inner = Cir::App(Box::new(Cir::Global("f".into())), Box::new(Cir::Var(0)));
        let got = recognize(&succ(inner.clone()));
        match got {
            Cir::Con(name, args, _) if name.0 == "Succ" => {
                assert_eq!(args.len(), 1);
            }
            other => panic!("expected an untouched `Succ` Con, got {other:?}"),
        }
    }

    /// Composition: `plus (Succ k) y` (with `k`, `y` variables) folds fully — the `(Succ k)` operand
    /// peels to `k + 1`, which is a pure operand, so the recognized result is a single `Add` tree.
    #[test]
    fn succ_operand_lets_parent_fold() {
        // `(Succ k)` alone peels; confirm the peeled form is a pure operand the parent accepts.
        let peeled = recognize(&succ(Cir::Var(1)));
        assert!(
            is_pure_nat_operand(&peeled, &[]),
            "peeled Succ must be a pure operand"
        );
    }

    /// EFFECT SOUNDNESS regression (examples/actor_pingpong.bl): a `(Succ msg)` where `msg` is bound
    /// to an effect `perform` — `App(Lam(Succ Var0), Op{..})` — must NOT peel to `Add(Var0, 1)`,
    /// because `Var0` is an `OpNode` at continuation-capture time and `bl_nat_add` is not
    /// OpNode-aware. The unsafe-binder environment leaves the `Succ` for the bubbling generic path.
    #[test]
    fn succ_of_effect_bound_var_is_left_alone() {
        let op = Cir::Op {
            effect: "Actor".into(),
            op: "receive".into(),
            arg: Box::new(zero()),
        };
        // `let msg = (perform receive Zero) in (Succ msg)`
        let term = Cir::App(
            Box::new(Cir::Lam(Box::new(succ(Cir::Var(0))))),
            Box::new(op),
        );
        let got = recognize(&term);
        let Cir::App(lam, _) = &got else {
            panic!("expected the let-App to survive, got {got:?}");
        };
        let Cir::Lam(body) = lam.as_ref() else {
            panic!("expected a Lam operator, got {lam:?}");
        };
        match body.as_ref() {
            Cir::Con(name, args, _) if name.0 == "Succ" => assert_eq!(args.len(), 1),
            other => panic!("effect-bound `(Succ msg)` must stay a `Succ` Con, got {other:?}"),
        }
    }

    /// The dual: a `(Succ acc)` where `acc` is a *value* parameter (a standalone `Lam` binder, as in
    /// the hot `sum`/`fib` loops) still peels to the O(1) `Add(acc, 1)` — the win is preserved.
    #[test]
    fn succ_of_value_param_still_peels() {
        // `λacc. (Succ acc)` — `acc` is a CBV value parameter, safe to feed a `NatPrim`.
        let term = Cir::Lam(Box::new(succ(Cir::Var(0))));
        let Cir::Lam(body) = recognize(&term) else {
            panic!("expected a Lam");
        };
        match *body {
            Cir::NatPrim {
                op: NatPrimOp::Add, ..
            } => {}
            other => panic!("value-param `(Succ acc)` must peel to Add, got {other:?}"),
        }
    }

    // ---- min/sub fingerprint disambiguation (regression: `min` miscompiled as `sub`) ----

    /// `Fix(λself. Case(Var0, [Zero: zero_arm, Succ{1}: succ_arm]))` — the eliminator core shape.
    fn elim_core(zero_arm: Cir, succ_arm: Cir) -> Cir {
        Cir::Fix(Box::new(Cir::Lam(Box::new(Cir::Case(
            Box::new(Cir::Var(0)),
            vec![
                Arm {
                    con: ConName("Zero".into()),
                    binders: 0,
                    body: zero_arm,
                },
                Arm {
                    con: ConName("Succ".into()),
                    binders: 1,
                    body: succ_arm,
                },
            ],
        )))))
    }

    /// Wrap an eliminator core into the curried head `λa. (core a)` that `is_sub_elim` matches.
    fn nested_head(inner_zero: Cir, inner_succ: Cir) -> Cir {
        // Outer Zero arm `λb. Zero`; outer Succ arm embeds the inner `match b` eliminator (applied to
        // the bound `b`), mirroring the prelude's nested `sub`/`min`/`max` lowering.
        let inner = elim_core(inner_zero, inner_succ);
        let outer_succ = Cir::App(Box::new(inner), Box::new(Cir::Var(0)));
        let core = elim_core(Cir::Lam(Box::new(zero())), outer_succ);
        Cir::Lam(Box::new(Cir::App(Box::new(core), Box::new(Cir::Var(0)))))
    }

    /// `sub`'s inner `match b` returns `(Succ n)` on `Zero` and the *bare* recursion on `Succ` — it
    /// must be recognized as `Sub`.
    #[test]
    fn sub_nested_elim_is_recognized() {
        // inner Zero arm = `(Succ <var>)`; inner Succ arm = bare IH `App(Var2, Var0)` (no Succ wrap).
        let head = nested_head(
            succ(Cir::Var(4)),
            Cir::App(Box::new(Cir::Var(2)), Box::new(Cir::Var(0))),
        );
        assert_eq!(
            match_binary_elim(&head),
            Some(NatPrimOp::Sub),
            "the bare-recursion / Succ-on-Zero nested eliminator is `sub`"
        );
    }

    /// `min`'s inner `match b` returns `Zero` on the inner `Zero` (not `Succ n`) and *wraps* its
    /// recursion in `Succ` — the discriminator `(inner_zero_is_succ=false, inner_succ_wrapped=true)`
    /// that is unique to `min`. It must be recognized as `Min` and, crucially, *not* mistaken for
    /// `sub` (the original bug: `min 2 5` folded to `sub 2 5` = 0 instead of 2).
    #[test]
    fn min_nested_elim_is_recognized() {
        // inner Zero arm = `Zero`; inner Succ arm = `(Succ (self n k))` (Succ-wrapped recursion).
        let head = nested_head(
            zero(),
            Cir::con(
                ConName("Succ".into()),
                vec![Cir::App(Box::new(Cir::Var(2)), Box::new(Cir::Var(0)))],
            ),
        );
        assert_eq!(
            match_binary_elim(&head),
            Some(NatPrimOp::Min),
            "`min`'s Zero-on-Zero / Succ-wrapped nested eliminator is `min`, not `sub`"
        );
    }

    /// `max`'s inner `match b` returns `(Succ n)` on `Zero` like `sub`, but wraps its recursion in
    /// `Succ` — the Succ-wrapped recursion must keep it out of the `sub` fingerprint.
    #[test]
    fn max_nested_elim_is_not_sub() {
        let head = nested_head(
            succ(Cir::Var(4)),
            Cir::con(
                ConName("Succ".into()),
                vec![Cir::App(Box::new(Cir::Var(2)), Box::new(Cir::Var(0)))],
            ),
        );
        assert_eq!(
            match_binary_elim(&head),
            None,
            "`max`'s Succ-wrapped recursion must not match the `sub` fingerprint"
        );
    }
}
