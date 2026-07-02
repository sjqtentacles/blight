//! `:step` (Wave 9 / T4): an evaluator-backed reduction trace for one REPL/proof-debugging
//! expression. UNTRUSTED tooling — purely a *display* aid, built entirely out of the already
//! trusted, metered [`blight_kernel::normalize::eval`]/[`blight_kernel::normalize::quote`] (Wave
//! 5/N1's cheap NbE conv path + N2's metered evaluation). It never re-implements substitution or
//! any reduction rule of its own, so a trace can never show anything a from-scratch reducer could
//! get subtly wrong: every "reduces to" printed here is the literal output of the kernel's own
//! evaluator run on that (closed) subterm.
//!
//! # Scope
//!
//! A trace decomposes exactly *one level* of an expression's immediate argument-like positions —
//! the operands of a top-level application spine, an `Elim`'s scrutinee, a `Fst`/`Snd`'s operand,
//! or an `IntPrim`'s two operands — showing each one's own reduction, before a final step gives the
//! *whole* expression's true normal form. It deliberately does not recurse into each operand's own
//! sub-structure: doing that faithfully would need either genuine small-step operational semantics
//! (foreign to this NbE-based kernel, which jumps straight from a term to its fully-reduced
//! semantic value) or hand-rolled capture-avoiding substitution across the full ~25-variant cubical
//! term grammar — both real correctness risks for what is ultimately a teaching aid. This shallow
//! decomposition is still real, meaningful progress on the common case (arithmetic and structural
//! recursion over `Nat`/`List`/`Int`/user data), and — crucially — the reported normal form always
//! comes straight from the trusted evaluator, so a shallow trace can only ever be *less detailed*,
//! never wrong.
//!
//! Metered throughout (N2): a `(by compute)`-style budget bounds every `eval`/`quote` call this
//! module makes, so a divergent-under-naive-reduction expression reports
//! [`StepOutcome::BudgetExceeded`] instead of hanging the REPL.

use crate::elab::{elaborate, parse_surface};
use crate::pretty::pretty_term;
use crate::sexpr::read_one;
use crate::ElabEnv;
use blight_kernel::normalize::{eval, quote, run_metered};
use blight_kernel::value::Env;
use blight_kernel::Term;

/// The default step budget for `:step` (same order of magnitude as `tactic.rs`'s `(by compute)` —
/// generous for any genuinely terminating expression a REPL user would type, small enough that a
/// divergent one fails fast rather than hanging).
pub const DEFAULT_STEP_BUDGET: u64 = 2_000_000;

/// One decomposed operand's own reduction, shown as part of a [`StepTrace`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Step {
    /// A human-facing description of which position this is (`"argument 1"`, `"the scrutinee"`, …).
    pub label: String,
    pub before: String,
    pub after: String,
}

/// The outcome of stepping the whole (reassembled) expression to its true normal form, after any
/// per-operand [`Step`]s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepOutcome {
    /// The expression's normal form, pretty-printed — always computed by the trusted evaluator
    /// directly on the *original* expression (never reconstructed from the shown steps), so it is
    /// correct even when the shallow per-operand decomposition above skipped some structure.
    NormalForm(String),
    /// The metering budget was exhausted before a normal form was reached: a usability report, not
    /// a soundness one (mirrors N2 exactly) — this never claims a wrong answer, it declines to
    /// finish.
    BudgetExceeded,
}

/// A full `:step` result: zero or more per-operand reduction [`Step`]s (empty for an expression
/// with no top-level argument-like structure, e.g. a bare literal) followed by the whole
/// expression's [`StepOutcome`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StepTrace {
    pub steps: Vec<Step>,
    pub outcome: StepOutcome,
}

/// Elaborates `expr_src` against `env` (exactly like `:type`/[`crate::infer::infer_type_str`]) and
/// builds its [`StepTrace`], metering every evaluator call at `budget` steps.
pub fn trace(env: &ElabEnv, expr_src: &str, budget: u64) -> Result<StepTrace, String> {
    let (sexpr, _rest) = read_one(expr_src).map_err(|e| format!("{e:?}"))?;
    let surface = parse_surface(&sexpr).map_err(|e| format!("{e}"))?;
    let term = elaborate(env, &surface).map_err(|e| format!("{e}"))?;
    let sig = std::rc::Rc::new(env.signature().clone());

    let mut steps = Vec::new();
    for (label, operand) in immediate_operands(&term) {
        match reduce(&sig, &operand, budget) {
            Ok(reduced) if reduced != operand => steps.push(Step {
                label,
                before: pretty_folding_globals(env, &operand),
                after: pretty_folding_globals(env, &reduced),
            }),
            Ok(_) => {} // already a value at this position: no step worth showing
            Err(()) => {
                return Ok(StepTrace {
                    steps,
                    outcome: StepOutcome::BudgetExceeded,
                })
            }
        }
    }

    let outcome = match reduce(&sig, &term, budget) {
        Ok(nf) => StepOutcome::NormalForm(pretty_folding_globals(env, &nf)),
        Err(()) => StepOutcome::BudgetExceeded,
    };
    Ok(StepTrace { steps, outcome })
}

/// Pretty-prints `term`, folding back any sub-*term* that is exactly a known global's elaborated
/// body (as spliced in verbatim by the elaborator's "a global definition: inline it" rule,
/// `elab.rs`'s `Surface::Var` case 5) to that global's bare name — recursing structurally (rather
/// than substring-replacing the rendered text) so a folded head still composes correctly with its
/// arguments, e.g. `(plus Zero (Succ Zero))` rather than `((plus Zero) (Succ Zero))`. Only
/// application spines, non-empty constructors, and pairs are recursed into here — every other
/// former (binders, cubical constructs, effects, ...) falls back to the ordinary [`pretty_term`],
/// so a global buried inside one of those stays inlined rather than risking a mis-rendering; that
/// is a cosmetic limitation only. This is purely a display transform: `trace`'s traced *values*
/// above are always the real, fully inlined terms the kernel evaluator actually sees, so a bug here
/// could at worst make output confusing, never incorrect.
fn pretty_folding_globals(env: &ElabEnv, term: &Term) -> String {
    if let Some(name) = fold_whole_term(env, term) {
        return name;
    }
    match term {
        Term::App(..) => {
            // Flatten the spine so a folded head composes as `(name a1 a2 ...)`, matching
            // `pretty_term`'s own curried `(f a)` nesting once re-applied argument by argument.
            let mut spine = Vec::new();
            let mut cur = term;
            while let Term::App(f, a) = cur {
                spine.push(&**a);
                cur = f;
            }
            spine.reverse();
            let head = pretty_folding_globals(env, cur);
            let args: Vec<String> = spine
                .into_iter()
                .map(|a| pretty_folding_globals(env, a))
                .collect();
            format!("({head} {})", args.join(" "))
        }
        Term::Con(name, args) if !args.is_empty() => {
            let mut parts = vec![name.0.clone()];
            parts.extend(args.iter().map(|a| pretty_folding_globals(env, a)));
            format!("({})", parts.join(" "))
        }
        Term::Pair(a, b) => format!(
            "(pair {} {})",
            pretty_folding_globals(env, a),
            pretty_folding_globals(env, b)
        ),
        _ => pretty_term(term),
    }
}

/// `term` folds to a bare global name if it is exactly that global's stored body, or the
/// `Ann(body, ty)` wrapper the elaborator splices in when the global has a declared type (the two
/// shapes `elab.rs`'s inlining rule can produce).
fn fold_whole_term(env: &ElabEnv, term: &Term) -> Option<String> {
    for (name, body, ty) in env.typed_globals() {
        if body == *term || Term::Ann(Box::new(body.clone()), Box::new(ty)) == *term {
            return Some(name);
        }
    }
    None
}

/// Evaluate `term` to its normal form under `sig`'s global signature, metered at `budget` steps.
fn reduce(
    sig: &std::rc::Rc<blight_kernel::Signature>,
    term: &Term,
    budget: u64,
) -> Result<Term, ()> {
    let sig = sig.clone();
    let term = term.clone();
    run_metered(budget, move || {
        let kenv = Env::with_sig(sig);
        let v = eval(&kenv, &term);
        quote(0, &v)
    })
}

/// The immediate argument-like positions of `term`'s outermost former, in left-to-right source
/// order — see the module doc's "Scope" section for exactly how far this decomposition goes (one
/// level, never under a binder, never recursing into an operand's own structure).
fn immediate_operands(term: &Term) -> Vec<(String, Term)> {
    match term {
        Term::App(..) => {
            // Flatten the application spine `(...(head a1) a2...) an` — the head itself is folded
            // into the final whole-expression step below, only the applied arguments are shown.
            let mut spine = Vec::new();
            let mut cur = term;
            while let Term::App(f, a) = cur {
                spine.push((**a).clone());
                cur = f;
            }
            spine.reverse();
            spine
                .into_iter()
                .enumerate()
                .map(|(i, a)| (format!("argument {}", i + 1), a))
                .collect()
        }
        Term::Elim { scrutinee, .. } => vec![("the scrutinee".to_string(), (**scrutinee).clone())],
        Term::Fst(p) | Term::Snd(p) => vec![("the pair".to_string(), (**p).clone())],
        Term::IntPrim { lhs, rhs, .. } => vec![
            ("the left operand".to_string(), (**lhs).clone()),
            ("the right operand".to_string(), (**rhs).clone()),
        ],
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Program;

    fn env_with_nat() -> ElabEnv {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::new(&mut env);
            prog.run(
                "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                 (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n  \
                   (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))\n",
            )
            .expect("setup");
        }
        env
    }

    #[test]
    fn stepper_shows_reduction_sequence() {
        let env = env_with_nat();
        // `(plus (plus Zero (Succ Zero)) (Succ (Succ Zero)))`: argument 1 is itself a call that
        // reduces to `(Succ Zero)`; argument 2 is already a value (no step shown for it); the whole
        // expression's normal form is `(Succ (Succ (Succ Zero)))`.
        let t = trace(
            &env,
            "(plus (plus Zero (Succ Zero)) (Succ (Succ Zero)))",
            DEFAULT_STEP_BUDGET,
        )
        .expect("traces");
        assert_eq!(
            t.steps.len(),
            1,
            "only argument 1 has a visible reduction: {t:?}"
        );
        assert_eq!(t.steps[0].label, "argument 1");
        assert_eq!(t.steps[0].before, "(plus Zero (Succ Zero))");
        assert_eq!(t.steps[0].after, "(Succ Zero)");
        assert_eq!(
            t.outcome,
            StepOutcome::NormalForm("(Succ (Succ (Succ Zero)))".to_string())
        );
    }

    #[test]
    fn stepper_on_a_bare_value_has_no_steps() {
        let env = env_with_nat();
        let t = trace(&env, "(Succ Zero)", DEFAULT_STEP_BUDGET).expect("traces");
        assert!(t.steps.is_empty());
        assert_eq!(
            t.outcome,
            StepOutcome::NormalForm("(Succ Zero)".to_string())
        );
    }

    #[test]
    fn stepper_metered_reports_budget_on_divergence() {
        let env = env_with_nat();
        // A budget of `1` cannot possibly finish evaluating even this small a call (many `tick()`s
        // deep through `eval`+`do_elim`); this stands in for genuine divergence to exercise the
        // *plumbing* — the point (matching N2) is that the stepper reports budget-exceeded instead
        // of ever hanging, not that this particular expression is non-terminating.
        let t = trace(&env, "(plus (Succ Zero) (Succ Zero))", 1).expect("traces (does not panic)");
        assert_eq!(t.outcome, StepOutcome::BudgetExceeded);
    }

    #[test]
    fn stepper_reports_an_error_for_an_unbound_expression() {
        let env = ElabEnv::new();
        assert!(trace(&env, "nope", DEFAULT_STEP_BUDGET).is_err());
    }
}
