//! `defn.rs` — surface desugaring of equation-style definitions (UNTRUSTED tower, zero kernel
//! growth). Part of the v0.1 roadmap ergonomics arc (E5).
//!
//! A top-level
//!
//! ```text
//! (defn NAME (Pi ((x1 T1) … (xn Tn)) R)
//!   [(p1_1 … p1_n) body1]
//!   [(p2_1 … p2_n) body2]
//!   …)
//! ```
//!
//! lowers, entirely at the s-expression level, to the single ordinary form the elaborator already
//! understands — a `define-rec` whose body is a **single-scrutinee** `match` on the one argument
//! column that is actually pattern-matched. The matched column gets a fresh scrutinee name; the
//! other (variable) columns become the lambda's parameters under the *user's own* names, so the
//! bodies reference them directly:
//!
//! ```text
//! ; matching on the k-th argument; every clause's k-th pattern is a constructor pattern, and its
//! ; other columns are plain variables/wildcards named consistently across clauses:
//! (define-rec NAME (Pi ((x1 T1) … (xn Tn)) R)
//!   (lam (…user-names… defn_arg{k} …user-names…)
//!     (match defn_arg{k}
//!       [pat1_k body1]
//!       [pat2_k body2]
//!       …)))
//! ```
//!
//! Naming the non-matched columns after the user's variables (rather than aliasing them with a
//! `let`) is load-bearing: a recursive call `(f A rest)` needs its leading argument `A` to be the
//! *literal* lambda parameter for the recognizer to certify the structural `Elim` — a `let` copy
//! would break recognition and drop the definition to the partial `Later` lane.
//!
//! A **single**-scrutinee `match` is the target (not multi-scrutinee `matchx`) because that is the
//! shape the recursion recognizer certifies as a structural `Elim`; `matchx` recursion is not (yet)
//! recognized. The scrutinee may be *any* argument, not just the first — `len`'s recursion is on its
//! `xs` argument, so `k` is found by which column carries the constructor patterns. First-match
//! semantics, exhaustiveness (the E3 coverage pre-pass), and nested-pattern lowering all come from
//! the existing `match` path. `define-rec` (not `deftotal`) so a structurally-total equation set
//! compiles to a kernel `Elim` while a non-structural one falls to the existing partial `Later`
//! lane — same as writing the `match` by hand. No kernel primitive is added.
//!
//! Supported shape (v1): the type is a single flat `(Pi (BINDERS) R)` whose binders are all explicit
//! (no `{…}` implicit binders); every clause is `[(p1 … pn) body]` with exactly `n` patterns; and
//! **exactly one** column is pattern-matched (has a constructor pattern in some clause) — the others
//! must be variable/wildcard patterns in every clause. Multi-column matching (a genuine `matchx`)
//! must still be written out with an explicit `define-rec` + `match`, since its recursion is not
//! kernel-recognized. Unsupported shapes produce a clear error.

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

/// The number of explicit binders in a `(Pi (BINDERS) R)` type, erroring on a non-`Pi` type or an
/// implicit `{…}` binder (read by the reader as a `(brace …)`-headed list).
fn pi_arity(ty: &Sexpr) -> Result<usize, ElabError> {
    let items = match ty {
        Sexpr::List(items) => items,
        _ => {
            return Err(bad(
                "(defn name T clauses…): T must be a `(Pi (binders) R)` type",
            ))
        }
    };
    let is_pi = matches!(items.first(), Some(Sexpr::Atom(a)) if a == "Pi");
    if !is_pi || items.len() != 3 {
        return Err(bad(
            "(defn name T clauses…): T must be a single `(Pi (binders) R)` telescope",
        ));
    }
    let binders = match &items[1] {
        Sexpr::List(bs) => bs,
        _ => return Err(bad("(defn …): the `Pi` binder list must be a list")),
    };
    for b in binders {
        // An implicit binder `{x A}` is read as `(brace x A …)`.
        if let Sexpr::List(parts) = b {
            if matches!(parts.first(), Some(Sexpr::Atom(a)) if a == "brace") {
                return Err(bad(
                    "(defn …) does not yet support implicit `{…}` binders in its type; write the \
                     definition with `define-rec` + `match` explicitly, or make the binder explicit",
                ));
            }
        }
    }
    Ok(binders.len())
}

/// Is this pattern sexp a plain variable/wildcard (a bare atom, e.g. `x` or `_`) rather than a
/// constructor pattern `(Con …)`? Used to find the single matched column.
fn is_var_pattern(p: &Sexpr) -> bool {
    matches!(p, Sexpr::Atom(_))
}

/// A parsed clause: the per-column pattern sexps and the body sexp.
struct DefnClause<'a> {
    pats: &'a [Sexpr],
    body: &'a Sexpr,
}

/// Desugar a `(defn name T clause…)` form into a single `(define-rec …)` form. Returns a one-element
/// vector for uniformity with the `run_form` dispatch loop that consumes it.
pub fn desugar_defn(items: &[Sexpr]) -> Result<Vec<Sexpr>, ElabError> {
    // items = [defn, name, T, clause0, clause1, …]
    if items.len() < 4 {
        return Err(bad(
            "(defn name T clause…): needs a name, a type, and at least one clause",
        ));
    }
    let name = match &items[1] {
        Sexpr::Atom(a) => a.clone(),
        _ => return Err(bad("(defn name T …): name must be a symbol")),
    };
    let ty = &items[2];
    let arity = pi_arity(ty)?;
    if arity == 0 {
        return Err(bad(
            "(defn …): a nullary type has no arguments to match on — use `(define name T body)`",
        ));
    }

    // Parse + validate every clause is `[(p1 … pn) body]` with exactly `arity` patterns.
    let mut clauses: Vec<DefnClause> = Vec::with_capacity(items.len() - 3);
    for (i, c) in items[3..].iter().enumerate() {
        let parts = match c {
            Sexpr::List(parts) if parts.len() == 2 => parts,
            _ => {
                return Err(bad(format!(
                    "(defn {name}): clause {} must be `[(p1 … p{arity}) body]`",
                    i + 1
                )))
            }
        };
        let pats = match &parts[0] {
            Sexpr::List(ps) => ps.as_slice(),
            _ => {
                return Err(bad(format!(
                    "(defn {name}): clause {}'s patterns must be a list `(p1 … p{arity})`",
                    i + 1
                )))
            }
        };
        if pats.len() != arity {
            return Err(bad(format!(
                "(defn {name}): clause {} has {} pattern(s) but the type takes {arity} argument(s)",
                i + 1,
                pats.len()
            )));
        }
        clauses.push(DefnClause {
            pats,
            body: &parts[1],
        });
    }

    // Find the single column that is pattern-matched (has a constructor pattern in some clause).
    // v1 supports exactly one such column; the recursion recognizer only certifies a single-
    // scrutinee `match`, so multi-column matching must be written out explicitly.
    let matched_cols: Vec<usize> = (0..arity)
        .filter(|&k| clauses.iter().any(|c| !is_var_pattern(&c.pats[k])))
        .collect();
    let k = match matched_cols.as_slice() {
        [k] => *k,
        [] => {
            return Err(bad(format!(
                "(defn {name}): no argument is pattern-matched (every clause's patterns are plain \
                 variables) — use `(define {name} T (lam … body))` for a non-matching definition"
            )))
        }
        _ => {
            return Err(bad(format!(
                "(defn {name}): v1 matches on a single argument column, but constructor patterns \
                 appear in columns {matched_cols:?}. Write multi-column matching with an explicit \
                 `define-rec` + `match` (its recursion is not kernel-recognized through `matchx`)"
            )))
        }
    };

    // Name the lambda parameters. The matched column `k` gets a fresh scrutinee name; a non-matched
    // column gets the *user's own* variable name (shared across clauses) so the bodies reference it
    // directly, with no `let` alias. A `let` alias would break recursion recognition — a recursive
    // call `(f A rest)` needs its leading argument `A` to be the *literal* parameter, not a
    // let-bound copy, for the recognizer to certify the structural `Elim`. Non-matched columns are
    // all variables/wildcards (the single-matched-column rule), so each must name its argument the
    // same way in every clause; a wildcard `_` in some clauses is fine (that clause ignores it).
    let mut params: Vec<String> = Vec::with_capacity(arity);
    for j in 0..arity {
        if j == k {
            params.push(format!("defn_arg{j}"));
            continue;
        }
        let mut chosen: Option<String> = None;
        for (ci, c) in clauses.iter().enumerate() {
            if let Sexpr::Atom(v) = &c.pats[j] {
                if v == "_" {
                    continue;
                }
                match &chosen {
                    None => chosen = Some(v.clone()),
                    Some(prev) if prev != v => {
                        return Err(bad(format!(
                            "(defn {name}): argument {j} is named `{prev}` and `{v}` in different \
                             clauses (clause {}) — a non-matched argument must use the same name in \
                             every clause",
                            ci + 1
                        )));
                    }
                    _ => {}
                }
            }
        }
        // If every clause wildcarded this column, no body references it — a fresh name is fine.
        params.push(chosen.unwrap_or_else(|| format!("defn_arg{j}")));
    }

    // Build the single-scrutinee match arms: each clause's k-th pattern is the arm pattern; the body
    // is used verbatim (the non-matched columns are already bound as the lambda's own parameters).
    let mut arms: Vec<Sexpr> = Vec::with_capacity(clauses.len());
    for c in &clauses {
        arms.push(list(vec![c.pats[k].clone(), c.body.clone()]));
    }

    // (match defn_arg{k} arm0 arm1 …)
    let mut match_form = vec![atom("match"), atom(params[k].clone())];
    match_form.extend(arms);

    // (lam (params…) (match …))
    let param_atoms: Vec<Sexpr> = params.iter().map(|p| atom(p.clone())).collect();
    let lam = list(vec![atom("lam"), list(param_atoms), list(match_form)]);

    // (define-rec NAME T (lam …))
    Ok(vec![list(vec![
        atom("define-rec"),
        atom(name),
        ty.clone(),
        lam,
    ])])
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
        desugar_defn(&items)
    }

    /// The generated form is a `define-rec` wrapping a `lam` over a *single-scrutinee* `match` on
    /// the matched column (column 0 here); the non-matched variable column is bound by a `let`.
    #[test]
    fn desugars_to_define_rec_lam_match() {
        let out = desugar(
            "(defn add (Pi ((a Nat) (b Nat)) Nat)\n\
               [((Zero) b) b]\n\
               [((Succ n) b) (Succ (add n b))])",
        )
        .expect("desugars");
        assert_eq!(out.len(), 1);
        let Sexpr::List(top) = &out[0] else {
            panic!("not a list")
        };
        assert!(matches!(&top[0], Sexpr::Atom(a) if a == "define-rec"));
        assert!(matches!(&top[1], Sexpr::Atom(a) if a == "add"));
        // top[3] = (lam (defn_arg0 defn_arg1) (match defn_arg0 …))
        let Sexpr::List(lam) = &top[3] else {
            panic!("not a lam")
        };
        assert!(matches!(&lam[0], Sexpr::Atom(a) if a == "lam"));
        let Sexpr::List(params) = &lam[1] else {
            panic!("no params")
        };
        assert_eq!(params.len(), 2, "two fresh args for the two Pi binders");
        let Sexpr::List(mx) = &lam[2] else {
            panic!("no match")
        };
        assert!(
            matches!(&mx[0], Sexpr::Atom(a) if a == "match"),
            "single-scrutinee match"
        );
        assert!(
            matches!(&mx[1], Sexpr::Atom(a) if a == "defn_arg0"),
            "scrutinee is the matched (0th) column"
        );
        assert_eq!(mx.len(), 4, "match head + scrutinee + two arms");
    }

    /// `len` matches on its *second* argument (`xs`), not the first (`A`, a plain type variable) —
    /// the matched column is found by which column carries constructor patterns.
    #[test]
    fn matches_on_the_constructor_column_not_always_the_first() {
        let out = desugar(
            "(defn len (Pi ((A (Type 0)) (xs (List A))) Nat)\n\
               [(A (nil)) Zero]\n\
               [(A (cons x rest)) (Succ (len A rest))])",
        )
        .expect("desugars");
        let Sexpr::List(top) = &out[0] else { panic!() };
        let Sexpr::List(lam) = &top[3] else { panic!() };
        let Sexpr::List(mx) = &lam[2] else { panic!() };
        assert!(
            matches!(&mx[1], Sexpr::Atom(a) if a == "defn_arg1"),
            "scrutinee is column 1 (xs), the one with constructor patterns"
        );
    }

    #[test]
    fn rejects_multi_column_matching() {
        // Both columns carry constructor patterns → not a single-scrutinee match.
        let e = desugar(
            "(defn f (Pi ((a Nat) (b Nat)) Nat)\n\
               [((Zero) (Zero)) Zero]\n\
               [(a b) a])",
        );
        assert!(e.is_err(), "multi-column matching must be rejected in v1");
    }

    #[test]
    fn rejects_wrong_pattern_count() {
        let e = desugar("(defn f (Pi ((a Nat) (b Nat)) Nat) [((Zero)) Zero])");
        assert!(
            e.is_err(),
            "one pattern for a two-arg type must be rejected"
        );
    }

    #[test]
    fn rejects_implicit_binder_type() {
        let e = desugar("(defn f (Pi ({A (Type 0)} (x A)) A) [(x) x])");
        assert!(e.is_err(), "implicit binders are not supported in v1");
    }

    #[test]
    fn rejects_non_pi_type() {
        let e = desugar("(defn f Nat [(x) x])");
        assert!(
            e.is_err(),
            "a non-Pi type has no telescope to read arity from"
        );
    }
}
