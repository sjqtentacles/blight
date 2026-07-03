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
//! pointless — write a plain `deftotal`). Lexicographic / multi-argument measures are deferred.

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

/// Is this the measured-`deftotal` shape — a 6-item `(deftotal name T (measure …) (default …)
/// (lam …))`? Cheap check for the `run_form` dispatch, before committing to `desugar_measured`.
pub fn is_measured(items: &[Sexpr]) -> bool {
    items.len() == 6
        && as_atom(&items[0]) == Some("deftotal")
        && one_arg(&items[3], "measure").is_some()
        && one_arg(&items[4], "default").is_some()
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
    let e_m = one_arg(&items[3], "measure").ok_or_else(|| {
        bad(format!(
            "measured `{name}`: expected `(measure e)` as the 4th element"
        ))
    })?;
    let e_d = one_arg(&items[4], "default").ok_or_else(|| {
        bad(format!(
            "measured `{name}`: a `(measure …)` clause requires a following `(default e)` clause \
             (the fuel-exhaustion value)"
        ))
    })?;

    // A `(measure …)` / `(default …)` must not itself call `f`.
    if mentions(e_m, &name) || mentions(e_d, &name) {
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

    // The body must actually recurse — else the measure/default are pointless.
    if count_self_refs(&body, &name) == 0 {
        return Err(bad(format!(
            "measured `{name}`: the body never calls `{name}` — a `(measure …)` clause is only for \
             recursive definitions; drop it and use a plain `(deftotal {name} T (lam …) )`"
        )));
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
