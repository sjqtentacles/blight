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
use crate::surface::{Binder, Cofibration, Pattern, Surface};
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
    /// `(trans p q)` — path transitivity (Track M2a): from `p : Path A x y` and `q : Path A y z`
    /// conclude the outer goal `Path A x z`, built as a genuine `hcomp`-backed composition (§2.6,
    /// CCHM): `λ i. hcomp A (i=1) (λ j. q@j) (p@i)`. At the two boundaries this is a fast-path
    /// `hcomp` reduction (`i=0` ⇒ the empty face, floor `p@0`; `i=1` ⇒ the total face, lid `q@1`), so
    /// the kernel's boundary check for `PLam` against `PathP` accepts it without needing the
    /// (unimplemented) general varying-tube composition at a closed type — the LCF door still
    /// re-derives and rejects a bogus `p`/`q` chain (mismatched midpoint `y`), never minting a false
    /// proof.
    ///
    /// `p`/`q` are themselves *sub-tactics*, not bare surface terms: a chain of ≥ 3 paths needs
    /// `(trans (trans p q) r)`, and a rewrite step is often itself a `(cong f t)`. A bare surface
    /// expression (a hypothesis name, application, or `the`-ascribed proof) still parses here too —
    /// [`parse_tactic_or_exact`] falls back to wrapping it as `(exact e)` — so existing `(trans p
    /// q)` scripts over plain hypotheses are unaffected.
    Trans(Box<Tactic>, Box<Tactic>),
    /// `(ascribe T t)` — run sub-tactic `t`, then wrap its result term in an explicit type
    /// ascription `(the T result)`. Needed whenever a tactic-built term (a nested `trans`'s or
    /// `cong`'s bare `PLam`) is used somewhere that requires *inferring* its type rather than
    /// checking it against a known target — e.g. the operand of an outer `trans`, which applies its
    /// argument via `PApp` and must first infer that operand's own `PathP` family. A bare `PLam`
    /// (like a bare `Lam`) cannot be inferred without a target type; `ascribe` supplies one
    /// explicitly so a chain like `(trans (ascribe T (trans p q)) r)` elaborates.
    Ascribe(Surface, Box<Tactic>),
    /// `(then t u)` — run `t`, then `u`; here sequencing threads the goal that `t` leaves.
    Then(Box<Tactic>, Box<Tactic>),
    /// `(orelse t u)` — try `t`; if it fails, run `u` (LCF alternation).
    OrElse(Box<Tactic>, Box<Tactic>),
    /// `(repeat t)` — run `t` until it no longer makes progress (bounded; see [`run`]).
    Repeat(Box<Tactic>),
    /// `compute` — Wave 5/N4: close a `Path A x y` goal by *deciding* `x ~ y` up front through
    /// the kernel's (metered) evaluator, rather than blindly proposing `refl`'s witness `λ i. x`
    /// and letting the unmetered LCF door discover non-equality or divergence on its own. See
    /// [`compute`] for the exact contract.
    Compute,
    /// `decide` — Wave 5/N4: close the "is this decidable proposition true" idiom
    /// `Path Bool e true` by normalizing `e` (metered, like `compute`) and checking it reduces to
    /// the literal `true` constructor. See [`decide`] for the exact contract and how it differs
    /// from `compute`'s general definitional-equality check.
    Decide,
}

/// Parse a `(by <tactic>)` form's body s-expression into a [`Tactic`].
pub fn parse_tactic(s: &Sexpr) -> Result<Tactic, TacticError> {
    use crate::parse_surface;
    let bad = |m: &str| TacticError::BadScript(m.to_string());
    match s {
        Sexpr::Atom(a) => match a.as_str() {
            "refl" => Ok(Tactic::Refl),
            "assumption" => Ok(Tactic::Assumption),
            "compute" => Ok(Tactic::Compute),
            "decide" => Ok(Tactic::Decide),
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
                "trans" => {
                    let p = items.get(1).ok_or_else(|| bad("(trans p q)"))?;
                    let q = items.get(2).ok_or_else(|| bad("(trans p q)"))?;
                    Ok(Tactic::Trans(
                        Box::new(parse_tactic_or_exact(p)?),
                        Box::new(parse_tactic_or_exact(q)?),
                    ))
                }
                "ascribe" => {
                    let ty = items.get(1).ok_or_else(|| bad("(ascribe T t)"))?;
                    let t = items.get(2).ok_or_else(|| bad("(ascribe T t)"))?;
                    let tysur = parse_surface(ty).map_err(|e| bad(&format!("ascribe T: {e:?}")))?;
                    Ok(Tactic::Ascribe(tysur, Box::new(parse_tactic_or_exact(t)?)))
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

/// Parse a `trans` argument as a sub-tactic, falling back to treating it as a bare surface *term*
/// (an implicit `(exact e)`) when it is not a recognized tactic form. This is what lets `(trans p
/// q)` accept both genuine sub-tactics (`(cong f t)`, a nested `(trans p q)`) and plain proof
/// terms (a hypothesis name, an application like `(n#ih b c)`, or a `the`-ascribed term) in the
/// same position, so existing scripts over bare hypotheses keep working unchanged.
fn parse_tactic_or_exact(s: &Sexpr) -> Result<Tactic, TacticError> {
    use crate::parse_surface;
    if let Ok(t) = parse_tactic(s) {
        return Ok(t);
    }
    let sur = parse_surface(s).map_err(|e| TacticError::BadScript(format!("trans arg: {e:?}")))?;
    Ok(Tactic::Exact(sur))
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
        Tactic::Trans(p, q) => trans(env, p, q, goal),
        Tactic::Ascribe(ty, t) => {
            let term = run(env, t, goal)?;
            Ok(Surface::The(Box::new(ty.clone()), Box::new(term)))
        }
        Tactic::Then(t, u) => {
            // Sequencing: the only goal-transforming primitives (`intro`, `induction`) embed their
            // continuation directly, so a top-level `then` simply prefers `t` and falls through to
            // `u` only if `t` made no progress (a conservative reading sufficient for the prelude).
            run(env, t, goal).or_else(|_| run(env, u, goal))
        }
        Tactic::OrElse(t, u) => run(env, t, goal).or_else(|_| run(env, u, goal)),
        Tactic::Repeat(t) => run(env, t, goal),
        Tactic::Compute => compute(env, goal),
        Tactic::Decide => decide(env, goal),
    }
}

/// The evaluation budget used by [`compute`]/[`decide`] (Wave 5/N4): generous enough for any
/// closed, terminating stdlib-scale computation (unary `Nat` arithmetic well into the hundreds of
/// reduction steps), but bounded so a goal that would diverge or blow up under NbE fails fast with
/// a clean [`TacticError`] instead of hanging the caller (REPL/LSP) — the entire point of reusing
/// Wave 5/N2's metered evaluator here rather than eval'ing unmetered.
const COMPUTE_BUDGET: u64 = 2_000_000;

/// `compute`: close a `Path A x y` goal by normalizing both `x` and `y` through the kernel's
/// (metered) evaluator and checking definitional equality *before* proposing a term. This differs
/// from plain `refl` (which blindly emits `λ i. x` and lets the kernel's own, unmetered `conv`
/// discover whether `x`/`y` actually agree) in two ways: a genuinely non-equal goal is rejected
/// immediately by the tactic itself with a legible message, and a goal whose normalization would
/// diverge (or just run very long) is rejected via the budget rather than hanging the caller.
///
/// `x` and `y` must be *closed* surface terms: `compute` elaborates them itself, from scratch,
/// with no knowledge of the ambient [`Goal::hyps`] (that bookkeeping exists only for tactics like
/// `assumption`/`induction` that build a term the *outer* `check_core` call — which does see the
/// real binders, once `intro`/`induction` have wrapped the term in the corresponding `Lam`/`match`
/// — elaborates). A `compute` goal mentioning a hypothesis introduced by an enclosing `intro`
/// therefore fails to elaborate (an unbound-name error) and is reported as ordinary `NoProgress`,
/// the same as any other inapplicable tactic; `compute` is for ground, decidable computation
/// (arithmetic lemmas and the like), not for equations depending on an abstract variable.
fn compute(env: &ElabEnv, goal: &Goal) -> TacResult {
    let (a, x, y) = match &goal.ty {
        Surface::Path(a, x, y) => (a, x, y),
        other => {
            return Err(TacticError::NoProgress(format!(
                "compute expects a Path goal, found {other:?}"
            )))
        }
    };
    use crate::{elaborate, elaborate_against};
    let a_core = elaborate(env, a)
        .map_err(|e| TacticError::NoProgress(format!("compute: carrier type: {e:?}")))?;
    let x_core = elaborate_against(env, x, &a_core)
        .map_err(|e| TacticError::NoProgress(format!("compute: lhs: {e:?}")))?;
    let y_core = elaborate_against(env, y, &a_core)
        .map_err(|e| TacticError::NoProgress(format!("compute: rhs: {e:?}")))?;
    let sig = std::rc::Rc::new(env.signature().clone());
    let equal = blight_kernel::normalize::run_metered(COMPUTE_BUDGET, move || {
        let kenv = blight_kernel::value::Env::with_sig(sig);
        let vx = blight_kernel::normalize::eval(&kenv, &x_core);
        let vy = blight_kernel::normalize::eval(&kenv, &y_core);
        blight_kernel::normalize::conv(0, &vx, &vy)
    })
    .map_err(|()| TacticError::NoProgress("compute: normalization budget exceeded".to_string()))?;
    if equal {
        Ok(Surface::PLam("%i".into(), x.clone()))
    } else {
        Err(TacticError::NoProgress(
            "compute: lhs and rhs are not definitionally equal".to_string(),
        ))
    }
}

/// `decide`: close the "is this decidable proposition true" idiom `Path Bool e true` by
/// normalizing `e` (metered, exactly as [`compute`] does) and checking it reduces to the literal
/// `true` constructor. This is deliberately *narrower* than `compute`'s general definitional
/// equality: `decide` only ever certifies the *true* case — a `Path Bool e false` goal is out of
/// scope here even when `e` genuinely computes to `false` (a refuted decidable proposition is not
/// "decided true"; `compute` is the right tactic for a general boolean-equality goal, since it
/// does not care which side is `true`/`false`). Same closed-term restriction as `compute` applies.
fn decide(env: &ElabEnv, goal: &Goal) -> TacResult {
    let (a, x, y) = match &goal.ty {
        Surface::Path(a, x, y) => (a, x, y),
        other => {
            return Err(TacticError::NoProgress(format!(
                "decide expects a Path goal, found {other:?}"
            )))
        }
    };
    if !matches!(a.as_ref(), Surface::Var(n) if n == "Bool") {
        return Err(TacticError::NoProgress(format!(
            "decide expects a Path over Bool, found carrier {a:?}"
        )));
    }
    if !matches!(y.as_ref(), Surface::Var(n) if n == "true") {
        return Err(TacticError::NoProgress(
            "decide only certifies a `true` target; use compute for a general boolean equality"
                .to_string(),
        ));
    }
    use crate::{elaborate, elaborate_against};
    let a_core = elaborate(env, a)
        .map_err(|e| TacticError::NoProgress(format!("decide: carrier type: {e:?}")))?;
    let x_core = elaborate_against(env, x, &a_core)
        .map_err(|e| TacticError::NoProgress(format!("decide: scrutinee: {e:?}")))?;
    let sig = std::rc::Rc::new(env.signature().clone());
    let is_true = blight_kernel::normalize::run_metered(COMPUTE_BUDGET, move || {
        let kenv = blight_kernel::value::Env::with_sig(sig);
        let vx = blight_kernel::normalize::eval(&kenv, &x_core);
        matches!(vx, blight_kernel::value::Value::Con(name, args) if name.0 == "true" && args.is_empty())
    })
    .map_err(|()| TacticError::NoProgress("decide: normalization budget exceeded".to_string()))?;
    if is_true {
        Ok(Surface::PLam("%i".into(), x.clone()))
    } else {
        Err(TacticError::NoProgress(
            "decide: scrutinee did not compute to `true`".to_string(),
        ))
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

/// `trans p q`: run the sub-tactics `p`/`q` (expected to produce proofs of `Path A x y` and
/// `Path A y z` respectively — the kernel re-derives and rejects any mismatch) against the *same*
/// outer goal (as `cong` does: neither sub-tactic needs a goal reflecting the inner path here,
/// since both are typically `exact`/`cong` terms that don't inspect it) and close `Path A x z` by
/// the one-sided `hcomp` composition `λ i. hcomp A (i=1) (λ j. q@j) (p@i)`. Only the carrier `A` is
/// read off the outer goal; `p`/`q`'s actual types are never inspected here — the LCF door
/// (`check_core`) is what verifies they truly chain.
fn trans(env: &ElabEnv, p: &Tactic, q: &Tactic, goal: &Goal) -> TacResult {
    match &goal.ty {
        Surface::Path(a, _x, _z) => {
            let psur = run(env, p, goal)?;
            let qsur = run(env, q, goal)?;
            let i = "%i".to_string();
            let j = "%j".to_string();
            let tube_body = Surface::PApp(Box::new(qsur), Box::new(Surface::Var(j.clone())));
            let tube_line = Surface::PLam(j, Box::new(tube_body));
            let base = Surface::PApp(Box::new(psur), Box::new(Surface::Var(i.clone())));
            let cofib = Cofibration::Eq1(Box::new(Surface::Var(i.clone())));
            let hc = Surface::HComp(
                a.clone(),
                Box::new(cofib),
                Box::new(tube_line),
                Box::new(base),
            );
            Ok(Surface::PLam(i, Box::new(hc)))
        }
        other => Err(TacticError::NoProgress(format!(
            "trans expects a Path goal, found {other:?}"
        ))),
    }
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
///
/// Must recurse into binder-carrying nodes (`Pi`/`Sigma`/`Lam`/`The`/…), not just `App`/`Path`. A
/// goal like `Π a b c. Path Nat (plus (plus a b) c) …` reaches `induction`'s substitution while `b`
/// and `c` are still a *nested, un-introduced* `Pi` inside the goal type (the sub-tactic `intro`s
/// them one at a time inside each arm); an earlier version of this function only handled `Var`,
/// `App`, `Path`, `PApp` and silently left every other node (crucially `Pi`) untouched, so the
/// scrutinee's occurrences *inside* that trailing `Pi` were never actually replaced by the
/// constructor case — each arm's `refl`/`cong` then closed the goal against the *original*,
/// unspecialized statement rather than the per-case one, producing confusing kernel rejections that
/// looked like an elaborator bug but were this substitution silently doing nothing. Respects
/// shadowing: substitution stops under a binder that reuses `from`'s name.
fn substitute_term(s: &Surface, from: &str, to: &Surface) -> Surface {
    let r = |x: &Surface| substitute_term(x, from, to);
    let rb = |x: &Surface| Box::new(r(x));
    match s {
        Surface::Var(n) if n == from => to.clone(),
        Surface::Var(n) => Surface::Var(n.clone()),
        Surface::The(ty, e) => Surface::The(rb(ty), rb(e)),
        Surface::Lam(names, body) => {
            if names.iter().any(|n| n == from) {
                s.clone()
            } else {
                Surface::Lam(names.clone(), rb(body))
            }
        }
        Surface::App(h, args) => Surface::App(rb(h), args.iter().map(r).collect()),
        Surface::Pi(binders, cod) => {
            let new_binders: Vec<Binder> = binders
                .iter()
                .map(|b| Binder {
                    name: b.name.clone(),
                    ty: r(&b.ty),
                    grade: b.grade.as_ref().map(r),
                    implicit: b.implicit,
                })
                .collect();
            if binders.iter().any(|b| b.name == from) {
                Surface::Pi(new_binders, cod.clone())
            } else {
                Surface::Pi(new_binders, rb(cod))
            }
        }
        Surface::Sigma(binders, cod) => {
            let new_binders: Vec<Binder> = binders
                .iter()
                .map(|b| Binder {
                    name: b.name.clone(),
                    ty: r(&b.ty),
                    grade: b.grade.as_ref().map(r),
                    implicit: b.implicit,
                })
                .collect();
            if binders.iter().any(|b| b.name == from) {
                Surface::Sigma(new_binders, cod.clone())
            } else {
                Surface::Sigma(new_binders, rb(cod))
            }
        }
        Surface::Path(a, x, y) => Surface::Path(rb(a), rb(x), rb(y)),
        Surface::PLam(i, body) => {
            if i == from {
                s.clone()
            } else {
                Surface::PLam(i.clone(), rb(body))
            }
        }
        Surface::PApp(p, i) => Surface::PApp(rb(p), rb(i)),
        Surface::Pair(a, b) => Surface::Pair(rb(a), rb(b)),
        Surface::Fst(p) => Surface::Fst(rb(p)),
        Surface::Snd(p) => Surface::Snd(rb(p)),
        Surface::Let(name, e, body) => {
            let e2 = rb(e);
            if name == from {
                Surface::Let(name.clone(), e2, body.clone())
            } else {
                Surface::Let(name.clone(), e2, rb(body))
            }
        }
        Surface::Bang(row, a) => Surface::Bang(rb(row), rb(a)),
        Surface::Delay(a) => Surface::Delay(rb(a)),
        Surface::Now(a) => Surface::Now(rb(a)),
        Surface::Later(a) => Surface::Later(rb(a)),
        Surface::Force(a) => Surface::Force(rb(a)),
        Surface::Perform(op, type_args, arg) => {
            Surface::Perform(op.clone(), type_args.iter().map(&r).collect(), rb(arg))
        }
        Surface::Unglue(g) => Surface::Unglue(rb(g)),
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

    /// An env with `Nat`/`plus` (as [`env_with_plus`]) plus a `Bool` with a couple of small
    /// `deftotal`s over it, for [`decide`]'s tests.
    fn env_with_plus_and_bool() -> ElabEnv {
        let mut env = env_with_plus();
        {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Bool () (false) (true))\n\
                 (deftotal is-zero (Pi ((n Nat)) Bool) \
                    (lam (n) (match n [(Zero) true] [(Succ k) false])))",
            )
            .expect("Bool/is-zero define");
        }
        env
    }

    /// Wave 5/N4: `(by compute)` closes `Path Nat (plus 2 3) 5` (spelled out in unary) — a goal
    /// `refl` alone would also happen to close (the kernel's own `conv` inside `check_core` would
    /// discover the same equality), but `compute` *decides* it itself first, up front, via the
    /// metered evaluator, which is the property this test pins.
    #[test]
    fn compute_closes_definitional_equality() {
        let env = env_with_plus();
        let two = "(Succ (Succ Zero))";
        let three = "(Succ (Succ (Succ Zero)))";
        let five = "(Succ (Succ (Succ (Succ (Succ Zero)))))";
        let goal = Goal::new(ty(&format!("(Path Nat (plus {two} {three}) {five})")));
        let term = run(&env, &tac("compute"), &goal).expect("compute decides the goal true");
        let proof = check_core(&env, &goal.ty, &term).expect("kernel accepts the compute witness");
        let _ = proof.concl();
    }

    /// Twin: `compute` must *fail to propose a term at all* (not merely fail at the kernel door)
    /// when the two sides are not definitionally equal — the tactic decides this itself.
    #[test]
    fn compute_rejects_non_definitional_goal() {
        let env = env_with_plus();
        let two = "(Succ (Succ Zero))";
        let three = "(Succ (Succ (Succ Zero)))";
        let four = "(Succ (Succ (Succ (Succ Zero))))";
        let goal = Goal::new(ty(&format!("(Path Nat (plus {two} {three}) {four})")));
        assert!(
            run(&env, &tac("compute"), &goal).is_err(),
            "compute must not propose a term for a false equation"
        );
    }

    /// Wave 5/N4: `(by decide)` closes the "is this decidable proposition true" idiom
    /// `Path Bool (is-zero Zero) true` by computing `is-zero Zero` down to `true`.
    #[test]
    fn decide_closes_true_decidable_prop() {
        let env = env_with_plus_and_bool();
        let goal = Goal::new(ty("(Path Bool (is-zero Zero) true)"));
        let term = run(&env, &tac("decide"), &goal).expect("decide computes the prop true");
        let proof = check_core(&env, &goal.ty, &term).expect("kernel accepts the decide witness");
        let _ = proof.concl();
    }

    /// Twin: `decide` must fail to propose a term when the decidable proposition computes to
    /// `false` — it never tries to certify a refuted proposition, unlike `compute`.
    #[test]
    fn decide_rejects_false_prop() {
        let env = env_with_plus_and_bool();
        let goal = Goal::new(ty("(Path Bool (is-zero (Succ Zero)) true)"));
        assert!(
            run(&env, &tac("decide"), &goal).is_err(),
            "decide must not propose a term for a false decidable proposition"
        );
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
