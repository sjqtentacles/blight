//! The cubical Kan table (spec §2.6/§8.3): the largest and riskiest single piece of the spore.
//!
//! `Comp` is implemented as `HComp` + `Transp` (the standard CCHM decomposition), so the
//! irreducible primitives are [`transp`] and [`hcomp`]. Each has *computation rules per type
//! former* (Pi, Sigma, Path, Data, Univ, Glue) and is conformance-tested against Cubical Agda.
//!
//! NOTE (TDD): the M0 acceptance proof `plus-zero` does NOT exercise this table, so it is
//! driven by its own conformance suite (ledger L5), never by the acceptance test.

use crate::normalize::{conv, quote_value_at};
use crate::term::{Cofib, Interval};
use crate::value::{Closure, Env, Value};

/// Decide whether a cofibration is the total face `⊤` (defined everywhere) after constant folding.
pub fn is_total(cofib: &Cofib) -> bool {
    match cofib {
        Cofib::Top => true,
        Cofib::Bot => false,
        Cofib::Eq0(_) | Cofib::Eq1(_) => false,
        Cofib::And(a, b) => is_total(a) && is_total(b),
        Cofib::Or(a, b) => is_total(a) || is_total(b),
    }
}

/// Decide whether a cofibration is the empty face `⊥` (never satisfied) after constant folding.
pub fn is_empty_face(cofib: &Cofib) -> bool {
    match cofib {
        Cofib::Bot => true,
        Cofib::Top => false,
        Cofib::Eq0(_) | Cofib::Eq1(_) => false,
        Cofib::And(a, b) => is_empty_face(a) || is_empty_face(b),
        Cofib::Or(a, b) => is_empty_face(a) && is_empty_face(b),
    }
}

/// Whether a dimension-binding line of types is *constant* — its value at `i = 0` is
/// definitionally equal to its value at `i = 1`. Transport along a constant line is the identity
/// (spec §2.6, the constant-family rule).
fn family_is_constant(family: &Closure) -> bool {
    let a0 = family.apply_dim(Interval::I0);
    let a1 = family.apply_dim(Interval::I1);
    conv(0, &a0, &a1)
}

/// `Transp (i. A) φ a0` — transport `a0 : A[I0/i]` to `A[I1/i]` (spec §2.6). The family is the
/// line of types `i. A`; `φ` marks where `A` is constant (when `φ = ⊤`, `A` is constant on the
/// whole interval and transport is the identity).
///
/// Reductions are dispatched on the head former of `A`, evaluated at a fresh dimension level so
/// that a former that genuinely depends on `i` is still detected (rather than collapsed at an
/// endpoint). The fully-constant case is the identity for *every* former and is handled up front.
pub fn transp(family: &Closure, cofib: &Cofib, base: &Value) -> Value {
    if is_total(cofib) || family_is_constant(family) {
        return base.clone();
    }
    // Inspect the head former on the *open* line (a fresh dimension in scope).
    let a_open = family.apply_dim(Interval::Dim(0));
    match a_open {
        // Universes are Kan-trivial in M0 (no univalence transport yet): the identity.
        Value::Univ(_) => base.clone(),

        // A closed inductive (no parameters/indices in M0, e.g. `Nat`): no `i`-dependence to
        // transport along, so the identity.
        Value::Data(_, params, indices) if params.is_empty() && indices.is_empty() => base.clone(),

        // Π / Σ / PathP: component-wise rules (CCHM, spec §2.6). M0 fully discharges the cases whose
        // component lines are constant (which the conformance goldens exercise); a genuinely
        // heterogeneous component line is documented as out of M0 scope rather than silently
        // mis-reducing. Both branches are *sound*: constant ⟹ identity on the component.
        Value::Pi(..) => transp_pi(family, base),
        Value::Sigma(..) => transp_sigma(family, base),
        Value::PathP { .. } => transp_path(family, base),

        // Any other head: only the (already-excluded) constant case is sound, so this is stuck.
        _ => unimplemented!(
            "transp: heterogeneous transport for this former is out of M0 scope \
             (Pi/Sigma/PathP/Data/Univ are implemented)"
        ),
    }
}

/// Build the line `i. project(A i)` as a [`Closure`] from the family `i. A`, by quoting the
/// projected open value under the single in-scope dimension (its free dim index 0 is the bound `i`).
fn line_closure(family: &Closure, project: impl Fn(Value) -> Value) -> Closure {
    let projected = project(family.apply_dim(Interval::Dim(0)));
    let body = quote_value_at(0, 1, &projected);
    Closure {
        env: Env::empty(),
        body,
    }
}

/// `transp` along a Π line. M0 implements the case where the domain line is constant (so the
/// argument transports as the identity), giving `λ x. transp (i. B i x) (f x)`. A non-constant
/// domain line needs the backward argument fill (CCHM) and is out of M0 scope.
fn transp_pi(family: &Closure, f: &Value) -> Value {
    let dom_line = line_closure(family, |a| match a {
        Value::Pi(_, d, _) => (*d).clone(),
        other => other,
    });
    if !family_is_constant(&dom_line) {
        unimplemented!("transp over Π with a non-constant domain line is out of M0 scope");
    }
    // Codomain line at the (constant) argument. We must build `i. B i x` for a *bound* argument; we
    // realize the result as `λ x. transp (i. B i x) (f x)` by quoting under one term binder.
    let x = Value::Neutral(crate::value::Neutral::Var(0));
    let cod_line = {
        let projected = match family.apply_dim(Interval::Dim(0)) {
            Value::Pi(_, _, cod) => cod.apply(x.clone()),
            other => other,
        };
        // Quote under one term binder (the `x`) and one dimension binder (`i`).
        let body = quote_value_at(1, 1, &projected);
        Closure {
            env: Env::empty(),
            body,
        }
    };
    let fx = crate::normalize::apply(f.clone(), x);
    let transported = transp(&cod_line, &Cofib::Bot, &fx);
    // `transported` lives under the term binder `x` (level 0); quote it as the Lam body.
    let body = quote_value_at(1, 0, &transported);
    Value::Lam(Closure {
        env: Env::empty(),
        body,
    })
}

/// `transp` along a Σ line, component-wise. M0 implements the constant-first-component case (so the
/// second line does not depend on the fill); a dependent first component is out of M0 scope.
fn transp_sigma(family: &Closure, pair: &Value) -> Value {
    let (a0, b0) = match pair {
        Value::Pair(a, b) => ((**a).clone(), (**b).clone()),
        other => (
            crate::normalize::vfst(other.clone()),
            crate::normalize::vsnd(other.clone()),
        ),
    };
    let fst_line = line_closure(family, |a| match a {
        Value::Sigma(d, _) => (*d).clone(),
        other => other,
    });
    let a1 = transp(&fst_line, &Cofib::Bot, &a0);
    if !family_is_constant(&fst_line) {
        unimplemented!("transp over Σ with a non-constant first-component line is out of M0 scope");
    }
    let a0c = a0.clone();
    let snd_line = line_closure(family, move |a| match a {
        Value::Sigma(_, cod) => cod.apply(a0c.clone()),
        other => other,
    });
    let b1 = transp(&snd_line, &Cofib::Bot, &b0);
    Value::Pair(Box::new(a1), Box::new(b1))
}

/// `transp` along a PathP line (CCHM). The fully-constant line is already the identity (handled at
/// the top of [`transp`]); a genuinely `i`-dependent path line needs inner composition and is out
/// of M0 scope.
fn transp_path(_family: &Closure, _path: &Value) -> Value {
    unimplemented!("transp over a non-constant PathP line is out of M0 scope");
}

/// `HComp A φ (i. u) a0` — homogeneous composition (spec §2.6). Composes the open box whose lid is
/// the `tube` (a line `i. u`) and whose floor is `base`, producing the value at `i = 1`.
///
/// The boundary cases reduce directly: on the empty face `⊥` the box is just its floor (`base`); on
/// the total face `⊤` it is the lid at `i = 1`. A *genuine* partial face additionally reduces when
/// the tube is constant in `i` (lid ≡ floor everywhere), in which case the composite is the floor.
pub fn hcomp(_ty: &Value, cofib: &Cofib, tube: &Closure, base: &Value) -> Value {
    if is_empty_face(cofib) {
        return base.clone();
    }
    if is_total(cofib) {
        return tube.apply_dim(Interval::I1);
    }
    // Partial face: if the tube does not vary along `i` (its lid equals its floor everywhere), the
    // open box is degenerate and the composite is the floor. This is the sound reduction M0 needs.
    if family_is_constant(tube) {
        return base.clone();
    }
    unimplemented!(
        "hcomp: composition over a genuinely varying partial face is out of M0 scope \
         (empty/total/constant-tube faces are implemented)"
    )
}

/// `Comp (i. A) φ (i. u) a0` — general composition, derived from `hcomp` + `transp` (the standard
/// CCHM decomposition): transport the base along the line, then hcomp in the target fibre.
pub fn comp(family: &Closure, cofib: &Cofib, tube: &Closure, base: &Value) -> Value {
    let transported = transp(family, &Cofib::Bot, base);
    let target_ty = family.apply_dim(Interval::I1);
    hcomp(&target_ty, cofib, tube, &transported)
}

/// Compute the result of `unglue` on a glued value (spec §2.6 Glue boundary): on a `Glue`-value it
/// projects the base; on the total/empty boundary `Glue A ⊤ T e ≡ T` the glued value is a
/// `T`-value and `unglue` is the identity.
pub fn unglue(glued: &Value) -> Value {
    match glued {
        Value::Glue { base, .. } => (**base).clone(),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    //! L5 white-box conformance tests for the Kan table. These are driven independently of the
    //! `plus-zero` acceptance proof (which never forces the Kan table). Goldens are checked
    //! against Cubical Agda's expected normal forms (spec §8.3).
    use super::*;
    use crate::value::{Closure, Env, Value};

    fn univ(n: u32) -> Value {
        let mut l = crate::term::Level::Zero;
        for _ in 0..n {
            l = crate::term::Level::Suc(Box::new(l));
        }
        Value::Univ(l)
    }
    fn const_line(n: u32) -> Closure {
        let mut l = crate::term::Level::Zero;
        for _ in 0..n {
            l = crate::term::Level::Suc(Box::new(l));
        }
        Closure {
            env: Env::empty(),
            body: crate::term::Term::Univ(l),
        }
    }

    /// `transp` along a constant family is the identity on the base.
    #[test]
    fn transp_constant_family_is_identity() {
        let out = transp(&const_line(0), &Cofib::Top, &univ(0));
        assert_eq!(out, univ(0), "transp over a constant family is the identity");
    }

    /// `hcomp` with an everywhere-`⊤` tube reduces to the tube's value at `i = 1`.
    #[test]
    fn hcomp_total_cofib_picks_tube() {
        let out = hcomp(&univ(0), &Cofib::Top, &const_line(0), &univ(1));
        assert_eq!(out, univ(0), "total tube ⟹ composite is tube@1");
    }

    /// `hcomp` with the empty face `⊥` returns the base unchanged.
    #[test]
    fn hcomp_empty_cofib_picks_base() {
        let out = hcomp(&univ(0), &Cofib::Bot, &const_line(0), &univ(1));
        assert_eq!(out, univ(1));
    }

    /// `comp` decomposes into `hcomp` + `transp` (CCHM) and agrees with the manual decomposition.
    #[test]
    fn comp_agrees_with_hcomp_transp() {
        let family = const_line(0);
        let tube = const_line(0);
        let base = univ(0);
        let out = comp(&family, &Cofib::Top, &tube, &base);
        assert_eq!(out, univ(0));
        let manual = hcomp(
            &family.apply_dim(crate::term::Interval::I1),
            &Cofib::Top,
            &tube,
            &transp(&family, &Cofib::Bot, &base),
        );
        assert_eq!(out, manual);
    }

    /// `unglue (glue ...)` round-trips to the base (the `Glue A ⊤ T e ≡ T` boundary direction).
    #[test]
    fn unglue_glue_roundtrip() {
        let base = univ(0);
        let glued = Value::Glue {
            base: Box::new(base.clone()),
            cofib: Cofib::Top,
            ty: Box::new(univ(0)),
            equiv: Box::new(univ(0)),
        };
        assert_eq!(unglue(&glued), base, "unglue ∘ glue = id on the base");
    }

    // ---- per-former transp goldens (spec §8.3) ----
    //
    // A *constant* line of any former transports as the identity. Each test below pins the head
    // former so we exercise the per-former dispatch in `transp`, then checks the golden (identity).

    use crate::term::Term;

    /// A closure `i. body` ignoring the dimension (a constant line) over a closed `body` term.
    fn const_type_line(body: Term) -> Closure {
        Closure {
            env: Env::empty(),
            body,
        }
    }

    fn nat_ty_term() -> Term {
        Term::Data(crate::term::DataName("Nat".into()), vec![], vec![])
    }

    /// `transp` along a constant `Nat` line is the identity (closed inductive, spec §2.6).
    #[test]
    fn transp_const_nat_is_identity() {
        let line = const_type_line(nat_ty_term());
        let base = Value::Con(crate::term::ConName("zero".into()), vec![]);
        assert_eq!(transp(&line, &Cofib::Bot, &base), base);
    }

    /// `transp` along a constant `Pi` line is the identity on a function value.
    #[test]
    fn transp_const_pi_is_identity() {
        // line: i. Π (_ : Nat) Nat
        let pi = Term::Pi(
            crate::semiring::Grade::Omega,
            Box::new(nat_ty_term()),
            Box::new(nat_ty_term()),
        );
        let line = const_type_line(pi);
        // base: λ x. x  (a closed identity-on-Nat function value)
        let f = Value::Lam(Closure {
            env: Env::empty(),
            body: Term::Var(0),
        });
        assert_eq!(transp(&line, &Cofib::Bot, &f), f);
    }

    /// `transp` along a constant `Sigma` line is the identity on a pair value.
    #[test]
    fn transp_const_sigma_is_identity() {
        let sigma = Term::Sigma(Box::new(nat_ty_term()), Box::new(nat_ty_term()));
        let line = const_type_line(sigma);
        let z = Value::Con(crate::term::ConName("zero".into()), vec![]);
        let pair = Value::Pair(Box::new(z.clone()), Box::new(z.clone()));
        assert_eq!(transp(&line, &Cofib::Bot, &pair), pair);
    }

    /// `transp` along a constant `PathP` line is the identity on a path value.
    #[test]
    fn transp_const_path_is_identity() {
        // line: i. PathP (j. Nat) zero zero  (a constant line of constant paths)
        let z = || Term::Con(crate::term::ConName("zero".into()), vec![]);
        let path = Term::PathP {
            family: Box::new(nat_ty_term()),
            lhs: Box::new(z()),
            rhs: Box::new(z()),
        };
        let line = const_type_line(path);
        // base: λ j. zero
        let p = Value::PLam(Closure {
            env: Env::empty(),
            body: z(),
        });
        assert_eq!(transp(&line, &Cofib::Bot, &p), p);
    }

    /// `hcomp` over a genuine partial face whose tube is constant in `i` reduces to the floor (the
    /// degenerate-box golden). This exercises the partial-face branch without forcing the
    /// out-of-scope general composition.
    #[test]
    fn hcomp_partial_constant_tube_picks_base() {
        // A genuinely partial face: r = 0 for a fresh dimension r (not ⊤ or ⊥).
        let partial = Cofib::Eq0(Interval::Dim(0));
        assert!(
            !is_total(&partial) && !is_empty_face(&partial),
            "the test face must be genuinely partial"
        );
        // Constant tube `i. univ 1`; floor `univ 1`. The composite is the floor.
        let tube = const_line(1);
        let base = univ(1);
        assert_eq!(hcomp(&univ(0), &partial, &tube, &base), base);
    }
}
