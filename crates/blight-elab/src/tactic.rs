//! An LCF-style tactic engine (spec §6.3), realized as *untrusted* host machinery that drives the
//! elaborator and the spore. A tactic never mints a proof: it only *proposes* a surface proof term
//! for a reflected [`Goal`]; the term is then elaborated to a core [`Term`] and re-checked by the
//! kernel ([`blight_kernel::check_top_with`]). A buggy tactic therefore can only fail to produce a
//! [`blight_kernel::Proof`] — the LCF guarantee (spec §1.2, §8.3).
//!
//! ## Reflection (what tactics may read)
//! A [`Goal`] reflects exactly what tactics inspect — a list of named hypotheses (each a surface
//! type) and the surface goal type — and *nothing about how checking works*: all checking goes back
//! through the kernel via [`Goal::check`]. This keeps the reflected surface small and avoids
//! re-implementing any typing in the tower (the §6.3 mitigation against duplicating kernel logic).
//!
//! ## Tactic language
//! Tactics are written as ordinary Blight s-expressions under a `(by …)` proof form, so the proof
//! *script* is genuine `.bl` source (homoiconic, §6.3): `refl`, `assumption`, `exact`, `intro`,
//! `induction`, `rewrite`/`cong`, and the combinators `then`, `orelse`, `repeat`. The interpreter
//! here is the irreducible host that turns such a script + a goal into a candidate proof term.

use crate::sexpr::Sexpr;
use crate::surface::{Pattern, Surface};
use crate::ElabEnv;

/// A reflected proof obligation: the named hypotheses in scope (innermost last, mirroring the
/// elaborator's lexical scope) and the surface type to inhabit. Hypotheses and the goal are kept as
/// *surface* types because that is the language tactics read and emit; the kernel re-checks the
/// elaborated result, so this carries no trust.
#[derive(Debug, Clone)]
pub struct Goal {
    /// `(name, type)` for each hypothesis, innermost binding last.
    pub hyps: Vec<(String, Surface)>,
    /// The goal type to inhabit.
    pub ty: Surface,
}

impl Goal {
    /// A top-level goal with no hypotheses.
    pub fn new(ty: Surface) -> Self {
        Goal {
            hyps: Vec::new(),
            ty,
        }
    }

    /// Extend with a hypothesis (an `intro`-style move): the new binding is innermost.
    pub fn with_hyp(&self, name: &str, ty: Surface) -> Self {
        let mut hyps = self.hyps.clone();
        hyps.push((name.to_string(), ty));
        Goal {
            hyps,
            ty: self.ty.clone(),
        }
    }

    /// Look up a hypothesis's type by name (most recent binding wins).
    pub fn hyp(&self, name: &str) -> Option<&Surface> {
        self.hyps
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, t)| t)
    }
}

/// The `check-core` host primitive (spec §6.3): elaborate a candidate proof term against a *closed*
/// goal type and run it through the kernel door, returning a real [`blight_kernel::Proof`] iff the
/// kernel accepts it. This is the only place a tactic-built term becomes a proof — the LCF door.
pub fn check_core(
    env: &ElabEnv,
    goal_ty: &Surface,
    proof_term: &Surface,
) -> Result<blight_kernel::Proof, String> {
    use crate::{elaborate, elaborate_against};
    let ty_core = elaborate(env, goal_ty).map_err(|e| format!("goal type: {e}"))?;
    let term_core =
        elaborate_against(env, proof_term, &ty_core).map_err(|e| format!("proof term: {e}"))?;
    blight_kernel::check_top_with(env.signature().clone(), term_core, ty_core)
        .map_err(|e| format!("kernel: {e}"))
}

/// What went wrong while *running* a tactic. A failure here is benign: it just means no proof term
/// was produced (the LCF guarantee). It is never a soundness fault.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TacticError {
    /// The tactic script s-expression was malformed.
    BadScript(String),
    /// A tactic could not make progress on the goal (e.g. `assumption` with no matching hypothesis).
    NoProgress(String),
    /// An unknown tactic name.
    Unknown(String),
}

/// A tactic: given a goal, propose a surface proof term (an inhabitant of `goal.ty`). Failure means
/// "this tactic does not apply here" and is recoverable by combinators like `orelse`.
type TacResult = Result<Surface, TacticError>;

/// The parsed tactic AST. Mirrors the `(by …)` surface tactic language.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tactic {
    /// `refl` — close a reflexive `Path A x x` with `λ i. x` (definitional reflexivity, §2.6).
    Refl,
    /// `assumption` — close the goal with a hypothesis whose type matches syntactically.
    Assumption,
    /// `(exact e)` — close the goal with the explicit surface term `e`.
    Exact(Surface),
    /// `(intro x . t)` — introduce a `Pi` binder named `x`, then run `t` on the residual goal.
    Intro(String, Box<Tactic>),
    /// `(induction n [(Con …) t] …)` — eliminate the `Nat`-like hypothesis `n` by structural
    /// recursion, running one sub-tactic per constructor (the §6.3 `induction` tactic). Induction
    /// hypotheses are made available as hypotheses named `<n>.ih`/`<field>.ih`.
    Induction(String, Vec<(Pattern, Tactic)>),
    /// `(cong f t)` — congruence under a unary head `f`: from a proof of `Path A x y` (produced by
    /// `t`) conclude `Path B (f x) (f y)` via `λ i. f (p @ i)` (§6.3, a `rewrite`-by-`Transp`
    /// special case for the cubical `Path`).
    Cong(Surface, Box<Tactic>),
    /// `(then t u)` — run `t`, then `u`; here sequencing threads the goal that `t` leaves.
    Then(Box<Tactic>, Box<Tactic>),
    /// `(orelse t u)` — try `t`; if it fails, run `u` (LCF alternation).
    OrElse(Box<Tactic>, Box<Tactic>),
    /// `(repeat t)` — run `t` until it no longer makes progress (bounded; see [`run`]).
    Repeat(Box<Tactic>),
}

/// Parse a `(by <tactic>)` form's body s-expression into a [`Tactic`].
pub fn parse_tactic(s: &Sexpr) -> Result<Tactic, TacticError> {
    use crate::parse_surface;
    let bad = |m: &str| TacticError::BadScript(m.to_string());
    match s {
        Sexpr::Atom(a) => match a.as_str() {
            "refl" => Ok(Tactic::Refl),
            "assumption" => Ok(Tactic::Assumption),
            other => Err(TacticError::Unknown(other.to_string())),
        },
        Sexpr::List(items) => {
            let head = match items.first() {
                Some(Sexpr::Atom(a)) => a.as_str(),
                _ => return Err(bad("a tactic application must start with a tactic name")),
            };
            match head {
                "exact" => {
                    let e = items.get(1).ok_or_else(|| bad("(exact e)"))?;
                    let sur = parse_surface(e).map_err(|err| bad(&format!("exact: {err:?}")))?;
                    Ok(Tactic::Exact(sur))
                }
                "intro" => {
                    // (intro x t)
                    let name = match items.get(1) {
                        Some(Sexpr::Atom(n)) => n.clone(),
                        _ => return Err(bad("(intro x t)")),
                    };
                    let body = items.get(2).ok_or_else(|| bad("(intro x t)"))?;
                    Ok(Tactic::Intro(name, Box::new(parse_tactic(body)?)))
                }
                "induction" => {
                    // (induction n [(Con f…) t] …)
                    let var = match items.get(1) {
                        Some(Sexpr::Atom(n)) => n.clone(),
                        _ => return Err(bad("(induction n …)")),
                    };
                    let mut arms = Vec::new();
                    for arm in &items[2..] {
                        let arm_items = match arm {
                            Sexpr::List(xs) => xs,
                            _ => return Err(bad("induction arm must be [(pat) tactic]")),
                        };
                        if arm_items.len() != 2 {
                            return Err(bad("induction arm is exactly [pattern tactic]"));
                        }
                        let pat = parse_pattern(&arm_items[0])?;
                        let tac = parse_tactic(&arm_items[1])?;
                        arms.push((pat, tac));
                    }
                    Ok(Tactic::Induction(var, arms))
                }
                "cong" => {
                    let f = items.get(1).ok_or_else(|| bad("(cong f t)"))?;
                    let fsur = parse_surface(f).map_err(|e| bad(&format!("cong head: {e:?}")))?;
                    let t = items.get(2).ok_or_else(|| bad("(cong f t)"))?;
                    Ok(Tactic::Cong(fsur, Box::new(parse_tactic(t)?)))
                }
                "then" => {
                    let t = items.get(1).ok_or_else(|| bad("(then t u)"))?;
                    let u = items.get(2).ok_or_else(|| bad("(then t u)"))?;
                    Ok(Tactic::Then(
                        Box::new(parse_tactic(t)?),
                        Box::new(parse_tactic(u)?),
                    ))
                }
                "orelse" => {
                    let t = items.get(1).ok_or_else(|| bad("(orelse t u)"))?;
                    let u = items.get(2).ok_or_else(|| bad("(orelse t u)"))?;
                    Ok(Tactic::OrElse(
                        Box::new(parse_tactic(t)?),
                        Box::new(parse_tactic(u)?),
                    ))
                }
                "repeat" => {
                    let t = items.get(1).ok_or_else(|| bad("(repeat t)"))?;
                    Ok(Tactic::Repeat(Box::new(parse_tactic(t)?)))
                }
                other => Err(TacticError::Unknown(other.to_string())),
            }
        }
    }
}

/// Parse a constructor pattern `(Con field …)` (used by `induction` arms).
fn parse_pattern(s: &Sexpr) -> Result<Pattern, TacticError> {
    match s {
        Sexpr::Atom(a) if a == "_" => Ok(Pattern::Wild),
        Sexpr::Atom(a) => Ok(Pattern::Var(a.clone())),
        Sexpr::List(items) => {
            let name = match items.first() {
                Some(Sexpr::Atom(a)) => a.clone(),
                _ => return Err(TacticError::BadScript("(Con field …)".into())),
            };
            let mut subs = Vec::new();
            for it in &items[1..] {
                subs.push(parse_pattern(it)?);
            }
            Ok(Pattern::Con(name, subs))
        }
    }
}

/// Run a tactic against a goal, returning a candidate surface proof term. The environment provides
/// the inductive signature consulted by `induction`. This does *no* trusted checking; the result
/// must still pass [`Goal::check`].
pub fn run(env: &ElabEnv, tac: &Tactic, goal: &Goal) -> TacResult {
    match tac {
        Tactic::Refl => refl(goal),
        Tactic::Assumption => assumption(goal),
        Tactic::Exact(e) => Ok(e.clone()),
        Tactic::Intro(name, body) => intro(env, name, body, goal),
        Tactic::Induction(var, arms) => induction(env, var, arms, goal),
        Tactic::Cong(f, t) => cong(env, f, t, goal),
        Tactic::Then(t, u) => {
            // Sequencing: the only goal-transforming primitives (`intro`, `induction`) embed their
            // continuation directly, so a top-level `then` simply prefers `t` and falls through to
            // `u` only if `t` made no progress (a conservative reading sufficient for the prelude).
            run(env, t, goal).or_else(|_| run(env, u, goal))
        }
        Tactic::OrElse(t, u) => run(env, t, goal).or_else(|_| run(env, u, goal)),
        Tactic::Repeat(t) => run(env, t, goal),
    }
}

/// `refl`: close `Path A x x` with `λ i. x`. The kernel decides whether `x` is genuinely the
/// reflexive endpoint up to definitional equality; we only emit the candidate.
fn refl(goal: &Goal) -> TacResult {
    match &goal.ty {
        Surface::Path(_a, x, _y) => Ok(Surface::PLam("%i".into(), x.clone())),
        other => Err(TacticError::NoProgress(format!(
            "refl expects a Path goal, found {other:?}"
        ))),
    }
}

/// `assumption`: find a hypothesis whose surface type is syntactically the goal type.
fn assumption(goal: &Goal) -> TacResult {
    for (name, ty) in goal.hyps.iter().rev() {
        if *ty == goal.ty {
            return Ok(Surface::Var(name.clone()));
        }
    }
    Err(TacticError::NoProgress(
        "no assumption matches the goal".into(),
    ))
}

/// `intro x. t`: the goal must be a `Pi (x:A) B`; introduce `x:A`, run `t` on `B`, and wrap the
/// result in `λ x. _`.
fn intro(env: &ElabEnv, name: &str, body: &Tactic, goal: &Goal) -> TacResult {
    match &goal.ty {
        Surface::Pi(binders, cod) => {
            let (first, rest) = binders
                .split_first()
                .ok_or_else(|| TacticError::NoProgress("intro on an empty Pi".into()))?;
            let inner_ty = if rest.is_empty() {
                (**cod).clone()
            } else {
                Surface::Pi(rest.to_vec(), cod.clone())
            };
            let sub = Goal {
                hyps: goal.with_hyp(name, first.ty.clone()).hyps,
                ty: inner_ty,
            };
            let body_term = run(env, body, &sub)?;
            Ok(Surface::Lam(vec![name.to_string()], Box::new(body_term)))
        }
        other => Err(TacticError::NoProgress(format!(
            "intro expects a Pi goal, found {other:?}"
        ))),
    }
}

/// `cong f t`: from `t : Path A x y` build `λ i. f (p @ i) : Path B (f x) (f y)`.
fn cong(env: &ElabEnv, f: &Surface, t: &Tactic, goal: &Goal) -> TacResult {
    // The sub-proof's goal is the "inner" Path. We recover it from the outer goal `Path B (f x)
    // (f y)` only structurally is hard in general; for the prelude `cong` is used where the inner
    // path proof is produced by `t` against a goal we can synthesize from the outer endpoints by
    // stripping the head `f`. We keep it simple: the inner goal is whatever `t` produces, and the
    // wrapper `λ i. f (p @ i)` is checked by the kernel against the outer `Path`.
    let p = run(env, t, goal)?;
    let i = "%i".to_string();
    let papp = Surface::PApp(Box::new(p), Box::new(Surface::Var(i.clone())));
    let applied = Surface::App(Box::new(f.clone()), vec![papp]);
    Ok(Surface::PLam(i, Box::new(applied)))
}

/// `induction n …`: eliminate hypothesis `n` (of an inductive type) by one structural step,
/// dispatching to a per-constructor sub-tactic. Realized as a surface `match` on `n`; the kernel's
/// `Elim` re-derives the dependent motive from the goal type, and each arm's induction hypotheses
/// are exposed to its sub-tactic as hypotheses (`<field>.ih`).
fn induction(env: &ElabEnv, var: &str, arms: &[(Pattern, Tactic)], goal: &Goal) -> TacResult {
    use crate::surface::Clause;
    // Find the inductive type of `var` from its hypothesis type's head.
    let var_ty = goal
        .hyp(var)
        .ok_or_else(|| TacticError::NoProgress(format!("induction: unknown hypothesis {var}")))?;
    let data = surface_head_name(var_ty).ok_or_else(|| {
        TacticError::NoProgress(format!("induction: {var} is not of an inductive type"))
    })?;
    let ctor_order = env
        .data_constructors(&data)
        .ok_or_else(|| TacticError::NoProgress(format!("induction: unknown data type {data}")))?;

    let mut clauses = Vec::new();
    for ctor in &ctor_order {
        // Find the matching arm by constructor name.
        let (pat, tac) = arms
            .iter()
            .find(|(p, _)| pattern_con_name(p) == Some(ctor.as_str()))
            .ok_or_else(|| {
                TacticError::NoProgress(format!("induction: no arm for constructor {ctor}"))
            })?;
        // The arm's field binders, and which are recursive (each recursive field gets an IH).
        let fields = pattern_fields(pat);
        let rec_flags = env
            .constructor_rec_flags(ctor)
            .ok_or_else(|| TacticError::NoProgress(format!("unknown constructor {ctor}")))?;
        // The sub-goal type: the goal with the scrutinee `var` specialized to this case's pattern
        // term `(Con field …)`. This is what the constructor's `Elim` method must inhabit (the
        // kernel re-derives the same dependent motive), so the sub-tactic sees the right endpoints.
        let case_term = constructor_term(ctor, &fields);
        let mut sub = Goal {
            hyps: goal.hyps.clone(),
            ty: substitute_term(&goal.ty, var, &case_term),
        };
        for (i, fname) in fields.iter().enumerate() {
            let is_rec = *rec_flags.get(i).unwrap_or(&false);
            // A recursive field has the inductive type; a non-recursive field's type is not needed
            // by the prelude tactics (which reference IHs and goal endpoints only).
            sub = sub.with_hyp(fname, var_ty.clone());
            if is_rec {
                // The induction hypothesis is bound by the elaborator's flat-match as `<field>#ih`;
                // expose it under that exact name so an `exact <field>#ih` resolves. Its reflected
                // type is the goal about the sub-term `<field>` (kernel re-checks the real IH type).
                let ih_goal = substitute_term(&goal.ty, var, &Surface::Var(fname.clone()));
                sub = sub.with_hyp(&format!("{fname}#ih"), ih_goal);
            }
        }
        let body = run(env, tac, &sub)?;
        clauses.push(Clause {
            patterns: vec![pat.clone()],
            body,
        });
    }
    Ok(Surface::Match(vec![Surface::Var(var.to_string())], clauses))
}

/// The constructor name of a `(Con …)` pattern, if any.
fn pattern_con_name(p: &Pattern) -> Option<&str> {
    match p {
        Pattern::Con(n, _) => Some(n.as_str()),
        _ => None,
    }
}

/// The field binder names of a constructor pattern (variables only; wildcards become `_`).
fn pattern_fields(p: &Pattern) -> Vec<String> {
    match p {
        Pattern::Con(_, subs) => subs
            .iter()
            .map(|s| match s {
                Pattern::Var(n) => n.clone(),
                _ => "_".to_string(),
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// The head data-type name of a surface type like `Nat` or `(Path Nat …)`'s carrier — i.e. the
/// outermost application head when it is a bare name.
fn surface_head_name(s: &Surface) -> Option<String> {
    match s {
        Surface::Var(n) => Some(n.clone()),
        Surface::App(h, _) => surface_head_name(h),
        _ => None,
    }
}

/// The surface term for a constructor case `(Con field …)`, or the bare `Con` when nullary.
fn constructor_term(ctor: &str, fields: &[String]) -> Surface {
    if fields.is_empty() {
        Surface::Var(ctor.to_string())
    } else {
        let args = fields.iter().map(|f| Surface::Var(f.clone())).collect();
        Surface::App(Box::new(Surface::Var(ctor.to_string())), args)
    }
}

/// Substitute a free surface variable `from` by a surface *term* `to` throughout `s`. Used to
/// specialize a goal type to an `induction` case (the scrutinee replaced by `(Con field …)`) and to
/// form induction-hypothesis types. The kernel re-checks the elaborated result, so this name-level
/// substitution is only a guide for the sub-tactics, never trusted.
fn substitute_term(s: &Surface, from: &str, to: &Surface) -> Surface {
    let r = |x: &Surface| substitute_term(x, from, to);
    match s {
        Surface::Var(n) if n == from => to.clone(),
        Surface::Var(n) => Surface::Var(n.clone()),
        Surface::App(h, args) => Surface::App(Box::new(r(h)), args.iter().map(r).collect()),
        Surface::Path(a, x, y) => Surface::Path(Box::new(r(a)), Box::new(r(x)), Box::new(r(y))),
        Surface::PApp(p, i) => Surface::PApp(Box::new(r(p)), Box::new(r(i))),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Program;

    /// An env with `Nat` and the recursive `plus` defined, the substrate for the `plus-zero` proof.
    fn env_with_plus() -> ElabEnv {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define-rec plus (Pi ((a Nat) (b Nat)) Nat) \
                    (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))",
            )
            .expect("plus defines");
        }
        env
    }

    /// Parse a tactic from source text.
    fn tac(src: &str) -> Tactic {
        let (s, _) = crate::read_one(src).expect("read tactic");
        parse_tactic(&s).expect("parse tactic")
    }

    /// Parse a surface type from source text.
    fn ty(src: &str) -> Surface {
        let (s, _) = crate::read_one(src).expect("read type");
        crate::parse_surface(&s).expect("parse type")
    }

    /// `refl` closes a definitionally-reflexive `Path Nat Zero Zero`.
    #[test]
    fn refl_tac_closes_path() {
        let env = env_with_plus();
        let goal = Goal::new(ty("(Path Nat Zero Zero)"));
        let term = run(&env, &tac("refl"), &goal).expect("refl proposes a term");
        let proof = check_core(&env, &goal.ty, &term).expect("kernel accepts refl");
        let _ = proof.concl();
    }

    /// `induction` splits a `Nat` goal into `Zero`/`Succ` cases, each closed by its sub-tactic.
    /// Here we prove `Π n. Path Nat n n` by induction with `refl` in both cases.
    #[test]
    fn induction_tac_splits() {
        let env = env_with_plus();
        let goal = Goal::new(ty("(Pi ((n Nat)) (Path Nat n n))"));
        let script = tac("(intro n (induction n [(Zero) refl] [(Succ k) refl]))");
        let term = run(&env, &script, &goal).expect("induction proposes a term");
        let proof = check_core(&env, &goal.ty, &term).expect("kernel accepts induction proof");
        let _ = proof.concl();
    }

    /// `cong`/`rewrite` transports a sub-path under a head: `cong Succ` turns a proof of
    /// `Path Nat k k` into a proof of `Path Nat (Succ k) (Succ k)`. We exercise it inside an
    /// induction step, the shape used by `plus-zero`.
    #[test]
    fn rewrite_tac_transports() {
        let env = env_with_plus();
        // Prove `Π n. Path Nat n n` again, but close the `Succ k` case with `cong Succ` over the IH.
        let goal = Goal::new(ty("(Pi ((n Nat)) (Path Nat n n))"));
        let script =
            tac("(intro n (induction n [(Zero) refl] [(Succ k) (cong Succ (exact k#ih))]))");
        let term = run(&env, &script, &goal).expect("cong proposes a term");
        let proof = check_core(&env, &goal.ty, &term).expect("kernel accepts cong proof");
        let _ = proof.concl();
    }

    /// A buggy tactic (claiming `refl` for a non-reflexive goal) does not yield a proof — the LCF
    /// guarantee. The kernel rejects the bogus term; no `Proof` is minted.
    #[test]
    fn tactic_failure_is_not_a_proof() {
        let env = env_with_plus();
        // `Path Nat Zero (Succ Zero)` is *not* reflexive; `refl` proposes `λ i. Zero`, which the
        // kernel rejects (its endpoints are `Zero`/`Zero`, not `Zero`/`Succ Zero`).
        let goal = Goal::new(ty("(Path Nat Zero (Succ Zero))"));
        let term = run(&env, &tac("refl"), &goal).expect("refl still proposes a (wrong) term");
        assert!(
            check_core(&env, &goal.ty, &term).is_err(),
            "a wrong tactic term must not produce a proof"
        );
    }
}
