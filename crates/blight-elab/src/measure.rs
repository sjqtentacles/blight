//! `measure.rs` — surface desugaring of measure-based total definitions (UNTRUSTED tower, zero
//! kernel growth). Part of the v0.1 roadmap ergonomics arc (E6): automate the hand-written "fuel"
//! pattern so a non-structurally-recursive function can be `deftotal` without the boilerplate.
//!
//! A
//!
//! ```text
//! (deftotal f (Pi ((x1 T1) … (xn Tn)) R)
//!   (measure e_m)        ; e_m : Nat, over the lam binder names
//!   (default e_d)        ; e_d : R — the value returned if the fuel runs out
//!   (lam (x1 … xn) BODY))
//! ```
//!
//! lowers, entirely at the s-expression level, to two ordinary `deftotal`s:
//!
//! ```text
//! ; 1. a fueled helper, fuel as parameter 0 so it recurses STRUCTURALLY on the fuel (a plain Nat
//! ;    Elim); every saturated self-call (f a1 … an) in BODY is rewritten to pass the smaller fuel:
//! (deftotal msr_fueled_f (Pi ((msr_fuel Nat) (x1 T1) … (xn Tn)) R)
//!   (lam (msr_fuel x1 … xn)
//!     (match msr_fuel
//!       [(Zero) e_d]                      ; fuel exhausted → the default
//!       [(Succ msr_k) BODY'])))           ; BODY with (f a…) ⇒ (msr_fueled_f msr_k a…)
//!
//! ; 2. the wrapper, seeding the fuel with (Succ e_m):
//! (deftotal f (Pi ((x1 T1) … (xn Tn)) R)
//!   (lam (x1 … xn) (msr_fueled_f (Succ e_m) x1 … xn)))
//! ```
//!
//! ## The honest contract
//! The kernel certifies TOTALITY unconditionally — `msr_fueled_f` is a genuine structural `Elim`
//! over `Nat`, so `f` inhabits its declared type no matter what `e_m` is. What is *not* checked is
//! measure *adequacy* — that every recursive call strictly decreases `e_m`. If the measure is
//! wrong, `f` is still total and well-typed but returns `e_d` on inputs whose recursion outruns the
//! seed: **"total but possibly wrong", never "unsound"**. And the semantics stays exact: `f` *is*
//! defined as this fueled unfolding, so every in-language proof about `f` is a proof about the real
//! function including its default arm. The rewrite itself needs no trust — the kernel re-checks its
//! output; a bad rewrite fails to compile, it never mints a false result.
//!
//! Supported shape (v1): the type is a single flat `(Pi (BINDERS) R)` with explicit binders; the
//! body is `(lam (p1 … pn) BODY)` matching those binders; every self-reference to `f` is a
//! *saturated* `n`-ary application (a bare `f` or a wrong-arity call is an error — eta-expand it);
//! and the body actually contains at least one self-call (else the `measure`/`default` clauses are
//! pointless — write a plain `deftotal`). A TWO-component `(measure e1 e2)` is the LEXICOGRAPHIC
//! form (D3): see the dedicated section below — same contract, four generated forms, and an
//! Ackermann-exact adequacy story. Three or more components are rejected (fold the tail).

use crate::elab::ElabError;
use crate::sexpr::Sexpr;

fn atom(s: impl Into<String>) -> Sexpr {
    Sexpr::Atom(s.into())
}
fn list(items: Vec<Sexpr>) -> Sexpr {
    Sexpr::List(items)
}
fn bad(msg: impl Into<String>) -> ElabError {
    ElabError::BadForm(msg.into())
}
fn as_atom(s: &Sexpr) -> Option<&str> {
    match s {
        Sexpr::Atom(a) => Some(a.as_str()),
        _ => None,
    }
}
/// Map non-alphanumerics to `_` so a user name is safe to splice into a generated identifier.
fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_alphanumeric() { c } else { '_' })
        .collect()
}

/// Recognize a `(head e)` single-argument clause, returning `e`. Used for `(measure e)`/`(default e)`.
fn one_arg<'a>(form: &'a Sexpr, head: &str) -> Option<&'a Sexpr> {
    match form {
        Sexpr::List(items) if items.len() == 2 && as_atom(&items[0]) == Some(head) => {
            Some(&items[1])
        }
        _ => None,
    }
}

/// Does `s` contain a reference to `name` (as an atom) anywhere? Used to forbid self-calls inside
/// the `measure`/`default` expressions (which must not recurse).
fn mentions(s: &Sexpr, name: &str) -> bool {
    match s {
        Sexpr::Atom(a) => a == name,
        Sexpr::List(items) => items.iter().any(|i| mentions(i, name)),
    }
}

/// Whether `s` (or a sub-list) binds `name` as a `lam`/`let` binder — used to stop the self-call
/// rewrite from descending into a scope that shadows the function's own name.
fn binds_name(binder_list: &Sexpr, name: &str) -> bool {
    match binder_list {
        Sexpr::List(items) => items.iter().any(|b| match b {
            Sexpr::Atom(a) => a == name,
            // a `let` binding `((x e) …)` or a lam binder that is itself a list — check its head atom
            Sexpr::List(inner) => inner.first().and_then(as_atom) == Some(name),
        }),
        Sexpr::Atom(a) => a == name,
    }
}

/// Rewrite every saturated self-call `(f a1 … an)` in `s` to `(helper msr_k a1 … an)`, erroring on
/// a bare use of `f` or a wrong-arity call. Does not descend into a `lam`/`let` that shadows `f`.
fn rewrite_self_calls(
    s: &Sexpr,
    f: &str,
    helper: &str,
    arity: usize,
    fuel_var: &str,
) -> Result<Sexpr, ElabError> {
    match s {
        Sexpr::Atom(a) => {
            if a == f {
                return Err(bad(format!(
                    "measured `{f}`: bare reference to `{f}` — a self-reference must be a saturated \
                     call `({f} arg…)` ({arity} argument(s)); eta-expand a partial use as \
                     `(lam (…) ({f} …))`"
                )));
            }
            Ok(atom(a.clone()))
        }
        Sexpr::List(items) => {
            // Shadowing: `(lam BINDERS body)` / `(let BINDERS body)` that re-binds `f` — leave its
            // body untouched (the inner `f` is not the recursion). Rare, but keeps the rewrite honest.
            if let Some(head) = items.first().and_then(as_atom) {
                if (head == "lam" || head == "let") && items.len() == 3 && binds_name(&items[1], f)
                {
                    return Ok(s.clone());
                }
                // A saturated self-call.
                if head == f {
                    let n_args = items.len() - 1;
                    if n_args != arity {
                        return Err(bad(format!(
                            "measured `{f}`: self-call `({f} …)` has {n_args} argument(s) but `{f}` \
                             takes {arity}; every recursive call must be saturated"
                        )));
                    }
                    let mut out = vec![atom(helper.to_string()), atom(fuel_var.to_string())];
                    for a in &items[1..] {
                        out.push(rewrite_self_calls(a, f, helper, arity, fuel_var)?);
                    }
                    return Ok(list(out));
                }
            }
            Ok(list(
                items
                    .iter()
                    .map(|i| rewrite_self_calls(i, f, helper, arity, fuel_var))
                    .collect::<Result<_, _>>()?,
            ))
        }
    }
}

/// Count self-calls (saturated or not) so we can reject a measured definition that never recurses.
fn count_self_refs(s: &Sexpr, f: &str) -> usize {
    match s {
        Sexpr::Atom(a) => (a == f) as usize,
        Sexpr::List(items) => items.iter().map(|i| count_self_refs(i, f)).sum(),
    }
}

/// The `(measure e…)` clause's component expressions (1 = the E6 single measure, 2 = the
/// lexicographic pair), if `form` is a measure clause at all.
fn measure_args(form: &Sexpr) -> Option<&[Sexpr]> {
    match form {
        Sexpr::List(items) if items.len() >= 2 && as_atom(&items[0]) == Some("measure") => {
            Some(&items[1..])
        }
        _ => None,
    }
}

/// Is this the measured-`deftotal` shape — a 6-item `(deftotal name T (measure e…) (default …)
/// (lam …))`? Cheap check for the `run_form` dispatch, before committing to `desugar_measured`.
pub fn is_measured(items: &[Sexpr]) -> bool {
    items.len() == 6
        && as_atom(&items[0]) == Some("deftotal")
        && measure_args(&items[3]).is_some()
        && one_arg(&items[4], "default").is_some()
}

/// Substitute parameter-name atoms by sexprs, stopping under a `lam`/`let` that rebinds a mapped
/// name (the same shadow discipline as [`rewrite_self_calls`]).
fn subst_params(s: &Sexpr, map: &[(String, Sexpr)]) -> Sexpr {
    match s {
        Sexpr::Atom(a) => map
            .iter()
            .find(|(n, _)| n == a)
            .map(|(_, e)| e.clone())
            .unwrap_or_else(|| atom(a.clone())),
        Sexpr::List(items) => {
            if let Some(head) = items.first().and_then(as_atom) {
                if (head == "lam" || head == "let") && items.len() == 3 {
                    let live: Vec<(String, Sexpr)> = map
                        .iter()
                        .filter(|(n, _)| !binds_name(&items[1], n))
                        .cloned()
                        .collect();
                    // `let` binding *expressions* still see the full map; only the body loses the
                    // shadowed names.
                    let binders = if head == "let" {
                        match &items[1] {
                            Sexpr::List(bs) => list(
                                bs.iter()
                                    .map(|b| match b {
                                        Sexpr::List(pair) if pair.len() == 2 => {
                                            list(vec![pair[0].clone(), subst_params(&pair[1], map)])
                                        }
                                        other => other.clone(),
                                    })
                                    .collect(),
                            ),
                            other => other.clone(),
                        }
                    } else {
                        items[1].clone()
                    };
                    return list(vec![
                        items[0].clone(),
                        binders,
                        subst_params(&items[2], &live),
                    ]);
                }
            }
            list(items.iter().map(|i| subst_params(i, map)).collect())
        }
    }
}

/// Desugar a measured `(deftotal name T (measure e) (default e) (lam …))` into the fueled helper +
/// wrapper pair. Returns the two forms in order.
pub fn desugar_measured(items: &[Sexpr]) -> Result<Vec<Sexpr>, ElabError> {
    // items = [deftotal, name, T, (measure e_m), (default e_d), (lam (p…) BODY)]
    if items.len() != 6 {
        return Err(bad(
            "measured deftotal: `(deftotal name T (measure e) (default e) (lam (p…) body))`",
        ));
    }
    let name = as_atom(&items[1])
        .ok_or_else(|| bad("(deftotal name …): name must be a symbol"))?
        .to_string();
    let ty = &items[2];
    let margs = measure_args(&items[3]).ok_or_else(|| {
        bad(format!(
            "measured `{name}`: expected `(measure e)` or `(measure e1 e2)` as the 4th element"
        ))
    })?;
    if margs.len() > 2 {
        return Err(bad(format!(
            "measured `{name}`: at most two lexicographic measure components are supported \
             (got {}); fold the tail into the second component",
            margs.len()
        )));
    }
    let e_d = one_arg(&items[4], "default").ok_or_else(|| {
        bad(format!(
            "measured `{name}`: a `(measure …)` clause requires a following `(default e)` clause \
             (the fuel-exhaustion value)"
        ))
    })?;

    // A `(measure …)` / `(default …)` must not itself call `f`.
    if margs.iter().any(|m| mentions(m, &name)) || mentions(e_d, &name) {
        return Err(bad(format!(
            "measured `{name}`: the `(measure …)`/`(default …)` expressions cannot call `{name}`"
        )));
    }

    // The Pi binders (for the helper's fuel-prepended type) — must be an explicit flat telescope.
    let (binders, result) = match ty {
        Sexpr::List(t) if t.len() == 3 && as_atom(&t[0]) == Some("Pi") => match &t[1] {
            Sexpr::List(bs) => (bs.clone(), t[2].clone()),
            _ => {
                return Err(bad(format!(
                    "measured `{name}`: the `Pi` binder list must be a list"
                )))
            }
        },
        _ => {
            return Err(bad(format!(
                "measured `{name}`: the type must be a single `(Pi (binders) R)` telescope"
            )))
        }
    };
    for b in &binders {
        if let Sexpr::List(parts) = b {
            if as_atom(&parts[0]) == Some("brace") {
                return Err(bad(format!(
                    "measured `{name}`: implicit `{{…}}` binders are not supported; make them explicit"
                )));
            }
        }
    }
    let arity = binders.len();

    // The body: `(lam (p1 … pn) BODY)`.
    let (params, body) = match &items[5] {
        Sexpr::List(l) if l.len() == 3 && as_atom(&l[0]) == Some("lam") => {
            let params = match &l[1] {
                Sexpr::List(ps) => ps.clone(),
                _ => {
                    return Err(bad(format!(
                        "measured `{name}`: the `lam` params must be a list"
                    )))
                }
            };
            (params, l[2].clone())
        }
        _ => {
            return Err(bad(format!(
                "measured `{name}`: the body must be `(lam (p1 … p{arity}) BODY)`"
            )))
        }
    };
    if params.len() != arity {
        return Err(bad(format!(
            "measured `{name}`: the `lam` binds {} parameter(s) but the type takes {arity}",
            params.len()
        )));
    }
    let param_names: Vec<String> = params
        .iter()
        .map(|p| {
            as_atom(p).map(String::from).ok_or_else(|| {
                bad(format!(
                    "measured `{name}`: each `lam` parameter must be a symbol"
                ))
            })
        })
        .collect::<Result<_, _>>()?;

    // The body must actually recurse — else the measure/default are pointless. (Checked here so
    // both the single and the lexicographic path share the guard.)
    if count_self_refs(&body, &name) == 0 {
        return Err(bad(format!(
            "measured `{name}`: the body never calls `{name}` — a `(measure …)` clause is only for \
             recursive definitions; drop it and use a plain `(deftotal {name} T (lam …) )`"
        )));
    }

    // Two components ⟹ the lexicographic desugar (its own generator).
    if margs.len() == 2 {
        return desugar_lex_measured(
            &name,
            ty,
            &binders,
            &result,
            &params,
            &param_names,
            &body,
            &margs[0],
            &margs[1],
            e_d,
        );
    }
    let e_m = &margs[0];

    let helper = format!("msr_fueled_{}", sanitize(&name));
    let fuel = "msr_fuel";
    let fuel_k = "msr_k";
    // Guard against a user parameter clashing with the generated fuel binders.
    for p in &param_names {
        if p == fuel || p == fuel_k {
            return Err(bad(format!(
                "measured `{name}`: parameter `{p}` clashes with the generated fuel binder; rename it"
            )));
        }
    }

    // BODY with self-calls rewritten to thread the smaller fuel `msr_k`.
    let body_prime = rewrite_self_calls(&body, &name, &helper, arity, fuel_k)?;

    // Helper type: prepend `(msr_fuel Nat)` to the telescope.
    let mut helper_binders = vec![list(vec![atom(fuel), atom("Nat")])];
    helper_binders.extend(binders.iter().cloned());
    let helper_ty = list(vec![atom("Pi"), list(helper_binders), result]);

    // Helper lam params: fuel then the originals.
    let mut helper_params = vec![atom(fuel)];
    helper_params.extend(params.iter().cloned());

    // (match msr_fuel [(Zero) e_d] [(Succ msr_k) BODY'])
    let match_form = list(vec![
        atom("match"),
        atom(fuel),
        list(vec![list(vec![atom("Zero")]), e_d.clone()]),
        list(vec![list(vec![atom("Succ"), atom(fuel_k)]), body_prime]),
    ]);

    let helper_form = list(vec![
        atom("deftotal"),
        atom(helper.clone()),
        helper_ty,
        list(vec![atom("lam"), list(helper_params), match_form]),
    ]);

    // Wrapper: (deftotal name T (lam (p…) (helper (Succ e_m) p…)))
    let mut seed_call = vec![atom(helper), list(vec![atom("Succ"), e_m.clone()])];
    seed_call.extend(param_names.iter().map(|p| atom(p.clone())));
    let wrapper_form = list(vec![
        atom("deftotal"),
        atom(name),
        ty.clone(),
        list(vec![atom("lam"), list(params), list(seed_call)]),
    ]);

    Ok(vec![helper_form, wrapper_form])
}

// =================================================================================================
// Lexicographic measures (D3): `(measure e1 e2)`.
//
// A single fuel cannot bound a lexicographic recursion (Ackermann's step count is not a cheap
// function of either component), so the desugar generates a two-level fueled structure — every
// piece an already-certified shape:
//
//   1. `msr_cmp_f` — a dep-free CPS `Nat` comparator (structural on its first argument): calls
//      `kLt` when `a < b`, else `kGe`. Continuations take a dummy `Nat` so no `Bool`/`Unit`
//      dependency is introduced.
//   2. `msr_inner_f` — structural on the inner fuel `msr_f2`, carrying the current frame's
//      measure values `(msr_v1, msr_v2)` and `msr_step : Π(binders…) R` — the "burn one outer
//      unit" continuation. Its `Zero` arm falls back to `msr_step` (inadequate-measure safety
//      net). Every user self-call `(f a…)` becomes a DISPATCH: bind the (rewritten) arguments,
//      compute the callee's measures `m1'`/`m2'`, then
//        * `m1' <  v1`            → `(msr_step x…)`                      — burn an outer unit;
//        * `m1' ≥ v1 ∧ m2' < v2`  → `(msr_inner_f msr_j m1' m2' step x…)` — burn an inner unit;
//        * otherwise              → the default (the measure is not lexicographically decreasing
//                                   at this call — "total but possibly wrong", never unsound).
//   3. `msr_outer_f` — structural on the outer fuel `msr_f1`; its `Succ` arm seeds the inner loop
//      with a FRESH inner fuel `Succ e2(args)` and passes its own first-class induction
//      hypothesis `(msr_outer_f msr_k1)` as `msr_step` — so an outer burn re-derives the frame
//      from the callee's own arguments.
//   4. the wrapper — seeds `(Succ e1(args))`.
//
// Adequacy (why an adequate lex measure never hits the default): fuels are plain `Nat` values, so
// each branch of the call tree consumes its own copies — accounting is per root-to-leaf path. On
// a path, an outer unit burns only when `m1` strictly decreases (≤ e1+1 burns), and between outer
// burns the inner fuel was seeded past the strictly-decreasing `m2` run (≤ e2@seed+1 calls). The
// kernel certifies totality unconditionally either way — adequacy only buys exactness.
//
// v1 gate: the result type must not mention the parameters (the comparator is instantiated at it
// from a different scope). Same "total but possibly wrong, never unsound" contract as E6.
// =================================================================================================

/// Rewrite every saturated self-call in the lexicographic body to the compare-and-dispatch chain.
/// `e1`/`e2` are the measure expressions over the ORIGINAL parameter names; the callee's measures
/// are computed by substituting the let-bound argument copies into them.
#[allow(clippy::too_many_arguments)]
fn rewrite_self_calls_lex(
    s: &Sexpr,
    f: &str,
    inner: &str,
    cmp: &str,
    arity: usize,
    param_names: &[String],
    e1: &Sexpr,
    e2: &Sexpr,
    e_d: &Sexpr,
) -> Result<Sexpr, ElabError> {
    match s {
        Sexpr::Atom(a) => {
            if a == f {
                return Err(bad(format!(
                    "measured `{f}`: bare reference to `{f}` — a self-reference must be a saturated \
                     call `({f} arg…)` ({arity} argument(s)); eta-expand a partial use as \
                     `(lam (…) ({f} …))`"
                )));
            }
            Ok(atom(a.clone()))
        }
        Sexpr::List(items) => {
            if let Some(head) = items.first().and_then(as_atom) {
                if (head == "lam" || head == "let") && items.len() == 3 && binds_name(&items[1], f)
                {
                    return Ok(s.clone());
                }
                if head == f {
                    let n_args = items.len() - 1;
                    if n_args != arity {
                        return Err(bad(format!(
                            "measured `{f}`: self-call `({f} …)` has {n_args} argument(s) but `{f}` \
                             takes {arity}; every recursive call must be saturated"
                        )));
                    }
                    // Rewritten argument expressions (nested self-calls dispatch recursively).
                    let args_rw: Vec<Sexpr> = items[1..]
                        .iter()
                        .map(|a| {
                            rewrite_self_calls_lex(
                                a,
                                f,
                                inner,
                                cmp,
                                arity,
                                param_names,
                                e1,
                                e2,
                                e_d,
                            )
                        })
                        .collect::<Result<_, _>>()?;
                    // Bind the arguments once (`msr_x{i}`), then the callee's measures over them.
                    let xs: Vec<String> = (0..arity).map(|i| format!("msr_x{i}")).collect();
                    let subst_map: Vec<(String, Sexpr)> = param_names
                        .iter()
                        .cloned()
                        .zip(xs.iter().map(|x| atom(x.clone())))
                        .collect();
                    let m1n = subst_params(e1, &subst_map);
                    let m2n = subst_params(e2, &subst_map);
                    // The dispatch core (innermost expression).
                    let call_args: Vec<Sexpr> = xs.iter().map(|x| atom(x.clone())).collect();
                    let step_call = {
                        let mut c = vec![atom("msr_step")];
                        c.extend(call_args.iter().cloned());
                        list(c)
                    };
                    let inner_call = {
                        let mut c = vec![
                            atom(inner),
                            atom("msr_j"),
                            atom("msr_m1n"),
                            atom("msr_m2n"),
                            atom("msr_step"),
                        ];
                        c.extend(call_args.iter().cloned());
                        list(c)
                    };
                    let k = |body: Sexpr, binder: &str| {
                        list(vec![atom("lam"), list(vec![atom(binder)]), body])
                    };
                    let inner_cmp = list(vec![
                        atom(cmp),
                        atom("msr_m2n"),
                        atom("msr_v2"),
                        k(inner_call, "msr_u2"),
                        k(e_d.clone(), "msr_u2"),
                    ]);
                    let dispatch = list(vec![
                        atom(cmp),
                        atom("msr_m1n"),
                        atom("msr_v1"),
                        k(step_call, "msr_u"),
                        k(inner_cmp, "msr_u"),
                    ]);
                    // let msr_x{i} = arg_i in … let msr_m1n = m1' in let msr_m2n = m2' in dispatch
                    let mut out = dispatch;
                    out = list(vec![
                        atom("let"),
                        list(vec![list(vec![atom("msr_m2n"), m2n])]),
                        out,
                    ]);
                    out = list(vec![
                        atom("let"),
                        list(vec![list(vec![atom("msr_m1n"), m1n])]),
                        out,
                    ]);
                    for (x, a) in xs.iter().zip(args_rw.iter()).rev() {
                        out = list(vec![
                            atom("let"),
                            list(vec![list(vec![atom(x.clone()), a.clone()])]),
                            out,
                        ]);
                    }
                    return Ok(out);
                }
            }
            Ok(list(
                items
                    .iter()
                    .map(|i| {
                        rewrite_self_calls_lex(i, f, inner, cmp, arity, param_names, e1, e2, e_d)
                    })
                    .collect::<Result<_, _>>()?,
            ))
        }
    }
}

/// Generate the four forms of a lexicographically-measured definition (comparator, inner, outer,
/// wrapper). See the module-section comment above for the design and adequacy argument.
#[allow(clippy::too_many_arguments)]
fn desugar_lex_measured(
    name: &str,
    ty: &Sexpr,
    binders: &[Sexpr],
    result: &Sexpr,
    params: &[Sexpr],
    param_names: &[String],
    body: &Sexpr,
    e1: &Sexpr,
    e2: &Sexpr,
    e_d: &Sexpr,
) -> Result<Vec<Sexpr>, ElabError> {
    let arity = binders.len();
    // v1 gate: the comparator is instantiated at the result type from a scope without the
    // parameters, so a dependent result cannot be threaded through the dispatch.
    for p in param_names {
        if mentions(result, p) {
            return Err(bad(format!(
                "measured `{name}`: a lexicographic `(measure e1 e2)` needs a result type that \
                 does not mention the parameters (found `{p}`); use a single `(measure e)` or a \
                 non-dependent result"
            )));
        }
    }
    // Clash guards for every generated binder.
    let mut reserved: Vec<String> = [
        "msr_f1", "msr_f2", "msr_k1", "msr_j", "msr_v1", "msr_v2", "msr_step", "msr_u", "msr_u2",
        "msr_m1n", "msr_m2n",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    reserved.extend((0..arity).map(|i| format!("msr_x{i}")));
    for p in param_names {
        if reserved.contains(p) {
            return Err(bad(format!(
                "measured `{name}`: parameter `{p}` clashes with a generated lexicographic-fuel \
                 binder; rename it"
            )));
        }
    }

    let cmp = format!("msr_cmp_{}", sanitize(name));
    let inner = format!("msr_inner_{}", sanitize(name));
    let outer = format!("msr_outer_{}", sanitize(name));

    // 1. The CPS comparator: `(cmp a b kLt kGe)` — `kLt` iff `a < b`. Structural on `a`,
    //    SPECIALIZED at the (closed — see the gate above) result type: a leading `(C (Type 0))`
    //    type parameter trips the structural-recursion motive generalization, and the comparator
    //    is per-definition anyway, so nothing is lost.
    let cmp_form = {
        let k_ty = || {
            list(vec![
                atom("Pi"),
                list(vec![list(vec![atom("u"), atom("Nat")])]),
                result.clone(),
            ])
        };
        let pi = list(vec![
            atom("Pi"),
            list(vec![
                list(vec![atom("a"), atom("Nat")]),
                list(vec![atom("b"), atom("Nat")]),
                list(vec![atom("kLt"), k_ty()]),
                list(vec![atom("kGe"), k_ty()]),
            ]),
            result.clone(),
        ]);
        let klt_zero = list(vec![atom("kLt"), atom("Zero")]);
        let kge_zero = list(vec![atom("kGe"), atom("Zero")]);
        let body = list(vec![
            atom("match"),
            atom("a"),
            list(vec![
                list(vec![atom("Zero")]),
                list(vec![
                    atom("match"),
                    atom("b"),
                    list(vec![list(vec![atom("Zero")]), kge_zero.clone()]),
                    list(vec![list(vec![atom("Succ"), atom("bb")]), klt_zero]),
                ]),
            ]),
            list(vec![
                list(vec![atom("Succ"), atom("aa")]),
                list(vec![
                    atom("match"),
                    atom("b"),
                    list(vec![list(vec![atom("Zero")]), kge_zero]),
                    list(vec![
                        list(vec![atom("Succ"), atom("bb")]),
                        list(vec![
                            atom(cmp.clone()),
                            atom("aa"),
                            atom("bb"),
                            atom("kLt"),
                            atom("kGe"),
                        ]),
                    ]),
                ]),
            ]),
        ]);
        list(vec![
            atom("deftotal"),
            atom(cmp.clone()),
            pi,
            list(vec![
                atom("lam"),
                list(vec![atom("a"), atom("b"), atom("kLt"), atom("kGe")]),
                body,
            ]),
        ])
    };

    // The step continuation's type: `Π(binders…) R`.
    let step_ty = list(vec![atom("Pi"), list(binders.to_vec()), result.clone()]);

    // 2. The inner loop, structural on `msr_f2`.
    let inner_form = {
        let mut tele = vec![
            list(vec![atom("msr_f2"), atom("Nat")]),
            list(vec![atom("msr_v1"), atom("Nat")]),
            list(vec![atom("msr_v2"), atom("Nat")]),
            list(vec![atom("msr_step"), step_ty.clone()]),
        ];
        tele.extend(binders.iter().cloned());
        let pi = list(vec![atom("Pi"), list(tele), result.clone()]);
        let mut lam_params = vec![
            atom("msr_f2"),
            atom("msr_v1"),
            atom("msr_v2"),
            atom("msr_step"),
        ];
        lam_params.extend(params.iter().cloned());
        let step_fallback = {
            let mut c = vec![atom("msr_step")];
            c.extend(param_names.iter().map(|p| atom(p.clone())));
            list(c)
        };
        let body_prime =
            rewrite_self_calls_lex(body, name, &inner, &cmp, arity, param_names, e1, e2, e_d)?;
        let match_form = list(vec![
            atom("match"),
            atom("msr_f2"),
            list(vec![list(vec![atom("Zero")]), step_fallback]),
            list(vec![list(vec![atom("Succ"), atom("msr_j")]), body_prime]),
        ]);
        list(vec![
            atom("deftotal"),
            atom(inner.clone()),
            pi,
            list(vec![atom("lam"), list(lam_params), match_form]),
        ])
    };

    // 3. The outer loop, structural on `msr_f1`; the `Succ` arm seeds the inner loop with the
    //    first-class IH `(outer msr_k1)` as the step continuation.
    let outer_form = {
        let mut tele = vec![list(vec![atom("msr_f1"), atom("Nat")])];
        tele.extend(binders.iter().cloned());
        let pi = list(vec![atom("Pi"), list(tele), result.clone()]);
        let mut lam_params = vec![atom("msr_f1")];
        lam_params.extend(params.iter().cloned());
        let seed_inner = {
            let mut c = vec![
                atom(inner.clone()),
                list(vec![atom("Succ"), e2.clone()]),
                e1.clone(),
                e2.clone(),
                list(vec![atom(outer.clone()), atom("msr_k1")]),
            ];
            c.extend(param_names.iter().map(|p| atom(p.clone())));
            list(c)
        };
        let match_form = list(vec![
            atom("match"),
            atom("msr_f1"),
            list(vec![list(vec![atom("Zero")]), e_d.clone()]),
            list(vec![list(vec![atom("Succ"), atom("msr_k1")]), seed_inner]),
        ]);
        list(vec![
            atom("deftotal"),
            atom(outer.clone()),
            pi,
            list(vec![atom("lam"), list(lam_params), match_form]),
        ])
    };

    // 4. The wrapper, seeding the outer fuel with `(Succ e1)`.
    let wrapper_form = {
        let mut seed_call = vec![atom(outer), list(vec![atom("Succ"), e1.clone()])];
        seed_call.extend(param_names.iter().map(|p| atom(p.clone())));
        list(vec![
            atom("deftotal"),
            atom(name.to_string()),
            ty.clone(),
            list(vec![atom("lam"), list(params.to_vec()), list(seed_call)]),
        ])
    };

    Ok(vec![cmp_form, inner_form, outer_form, wrapper_form])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::read_all;

    fn desugar(src: &str) -> Result<Vec<Sexpr>, ElabError> {
        let forms = read_all(src).expect("reads");
        let items = match &forms[0] {
            Sexpr::List(items) => items.clone(),
            _ => panic!("not a list"),
        };
        desugar_measured(&items)
    }

    /// The generated helper prepends the fuel parameter, wraps the body in a `match msr_fuel` whose
    /// `Zero` arm is the default and `Succ` arm is the rewritten body; the wrapper seeds `(Succ e_m)`.
    #[test]
    fn desugar_emits_helper_and_wrapper() {
        let out = desugar(
            "(deftotal qsort (Pi ((xs (List Nat))) (List Nat))\n\
               (measure (length xs))\n\
               (default xs)\n\
               (lam (xs) (append (qsort xs) (qsort xs))))",
        )
        .expect("desugars");
        assert_eq!(out.len(), 2, "helper + wrapper");
        // Helper: (deftotal msr_fueled_qsort (Pi ((msr_fuel Nat) (xs …)) …) (lam (msr_fuel xs) (match msr_fuel …)))
        let Sexpr::List(h) = &out[0] else { panic!() };
        assert_eq!(as_atom(&h[1]), Some("msr_fueled_qsort"));
        // Wrapper keeps the original name and type.
        let Sexpr::List(w) = &out[1] else { panic!() };
        assert_eq!(as_atom(&w[1]), Some("qsort"));
        // The rendered helper mentions the fuel scrutinee and the rewritten self-call.
        let rendered = format!("{:?}", out[0]);
        assert!(rendered.contains("msr_fuel"), "fuel binder present");
        assert!(
            rendered.contains("msr_k"),
            "smaller fuel threaded in the Succ arm"
        );
    }

    #[test]
    fn self_call_is_rewritten_to_thread_smaller_fuel() {
        let out =
            desugar("(deftotal f (Pi ((n Nat)) Nat) (measure n) (default Zero) (lam (n) (f n)))")
                .expect("desugars");
        let rendered = format!("{:?}", out[0]);
        // (f n) becomes (msr_fueled_f msr_k n) — the helper name + the Succ-arm predecessor.
        assert!(
            rendered.contains("msr_fueled_f"),
            "self-call routed to the helper: {rendered}"
        );
    }

    #[test]
    fn rejects_measure_without_default() {
        // 5-item form: measure but no default.
        let forms =
            read_all("(deftotal f (Pi ((n Nat)) Nat) (measure n) (lam (n) (f n)))").unwrap();
        let Sexpr::List(items) = &forms[0] else {
            panic!()
        };
        assert!(
            !is_measured(items),
            "a measure without default is not the measured shape"
        );
    }

    #[test]
    fn rejects_non_recursive_body() {
        let e =
            desugar("(deftotal f (Pi ((n Nat)) Nat) (measure n) (default Zero) (lam (n) Zero))");
        assert!(e.is_err(), "a measured def that never recurses is rejected");
    }

    #[test]
    fn rejects_unsaturated_self_reference() {
        // `f` used bare (as a value), not a saturated call.
        let e =
            desugar("(deftotal f (Pi ((n Nat)) Nat) (measure n) (default Zero) (lam (n) (g f n)))");
        assert!(e.is_err(), "a bare `f` reference is rejected");
    }

    #[test]
    fn rejects_self_call_in_measure() {
        let e = desugar(
            "(deftotal f (Pi ((n Nat)) Nat) (measure (f n)) (default Zero) (lam (n) (f n)))",
        );
        assert!(e.is_err(), "the measure expression cannot call `f`");
    }
}

#[cfg(test)]
mod lex_tests {
    use super::*;
    use crate::sexpr::read_all;

    fn desugar(src: &str) -> Result<Vec<Sexpr>, ElabError> {
        let forms = read_all(src).expect("reads");
        let Sexpr::List(items) = &forms[0] else {
            panic!()
        };
        desugar_measured(items)
    }

    const ACK: &str = "(deftotal ack (Pi ((m Nat) (n Nat)) Nat)\n\
                         (measure m n)\n\
                         (default Zero)\n\
                         (lam (m n)\n\
                           (match m\n\
                             [(Zero) (Succ n)]\n\
                             [(Succ mm)\n\
                               (match n\n\
                                 [(Zero) (ack mm (Succ Zero))]\n\
                                 [(Succ nn) (ack mm (ack m nn))])])))";

    /// The lexicographic desugar emits exactly four forms — comparator, inner (fuel-2 loop with
    /// the `msr_step` continuation), outer (fuel-1 loop passing its first-class IH), wrapper —
    /// and the rewritten body dispatches through the comparator.
    #[test]
    fn lex_desugar_emits_cmp_inner_outer_wrapper() {
        let out = desugar(ACK).expect("desugars");
        assert_eq!(out.len(), 4, "cmp + inner + outer + wrapper");
        let names: Vec<String> = out
            .iter()
            .map(|f| match f {
                Sexpr::List(items) => as_atom(&items[1]).unwrap().to_string(),
                _ => panic!(),
            })
            .collect();
        assert_eq!(
            names,
            ["msr_cmp_ack", "msr_inner_ack", "msr_outer_ack", "ack"]
        );
        let inner = format!("{:?}", out[1]);
        assert!(
            inner.contains("msr_step"),
            "inner threads the step continuation"
        );
        assert!(
            inner.contains("msr_cmp_ack"),
            "self-calls dispatch through the comparator"
        );
        assert!(
            inner.contains("msr_j"),
            "inner burns thread the smaller fuel"
        );
        let outer = format!("{:?}", out[2]);
        assert!(
            outer.contains("msr_outer_ack\"), Atom(\"msr_k1"),
            "outer passes its first-class IH as the step continuation: {outer}"
        );
    }

    /// Three or more measure components are rejected with a clear message.
    #[test]
    fn rejects_three_measures() {
        let e = desugar(
            "(deftotal f (Pi ((a Nat) (b Nat) (c Nat)) Nat) (measure a b c) (default Zero) \
             (lam (a b c) (f a b c)))",
        );
        match e {
            Err(ElabError::BadForm(m)) => assert!(m.contains("two lexicographic"), "{m}"),
            other => panic!("expected the 3-component rejection, got {other:?}"),
        }
    }

    /// A lexicographic measure with a result type mentioning a parameter is rejected (the
    /// comparator is instantiated at the result from a scope without the parameters).
    #[test]
    fn rejects_dependent_result_for_lex() {
        let e = desugar(
            "(deftotal f (Pi ((A (Type 0)) (n Nat)) A) (measure n n) (default d) \
             (lam (A n) (f A n)))",
        );
        match e {
            Err(ElabError::BadForm(m)) => assert!(m.contains("does not mention"), "{m}"),
            other => panic!("expected the dependent-result rejection, got {other:?}"),
        }
    }
}
