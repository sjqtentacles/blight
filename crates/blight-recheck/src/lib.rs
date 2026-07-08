//! # blight-recheck — an independent, untrusted minimal re-checker (spec §8.3)
//!
//! This crate is **not** part of the trusted base. It re-implements a *second, smaller* checker
//! for Blight's core fragment — its own normalizer (`eval`/`quote`/`conv`) and its own
//! bidirectional `infer`/`check` — and uses it to **re-verify** what the kernel already
//! concluded. The only thing it consumes from the kernel is the public observation
//! [`blight_kernel::Proof::concl`] (a [`blight_kernel::Judgement`] carrying a core `Term` + its
//! type) together with the public [`blight_kernel::Signature`]. It does **not** call any of the
//! kernel's checking internals (`Checker`, `normalize`, `check_g`, …); it re-derives the
//! judgement from scratch.
//!
//! Two independent checkers agreeing is a stronger soundness story than trusting one (spec
//! §8.3): a false `Proof` would have to fool *both* the kernel's level-based closure NbE and
//! this crate's substitution-based normalizer, which were written separately.
//!
//! ## Coverage
//! Supported: the sound *core fragment* — the dependent layer (`Var`, `Univ`, `Pi`, `Lam`,
//! `App`, `Sigma`, `Pair`, `Fst`, `Snd`, `Ann`), inductive data (`Data`, `Con`, `Elim`) —
//! including **indexed and parameterized** families up to full N-parameter / M-index telescopes
//! (the earlier ≤1/≤1 cap is lifted): the eliminator's motive threads all indices
//! (`λ i… . λ (_:D ps i…). T`) and the per-constructor method types reconstruct the indexed
//! conclusion and indexed induction hypotheses, a direct independent port of the kernel's
//! `infer_elim`/`method_type`. Also the grade discipline on binders, and the *constant* path layer
//! (`PathP`/`PLam`/`PApp` with the De Morgan interval and β/η). Everything the prelude + M0–M5
//! acceptance corpus need lives here.
//!
//! The univalence **`Glue`** layer (`Glue`/`GlueTerm`/`Unglue`) is now *modeled* (F1): the re-checker
//! independently re-derives Glue **formation** — its own contractible-fibres `equiv_type`, checking
//! the `equiv` slot against `Equiv T A` at grade 0 (the kernel-audit K3 soundness point — an
//! arbitrary term there is *Rejected*, not laundered) — and the CCHM **boundary reductions**
//! (`Glue A ⊤ T e ≡ T`, `Glue A ⊥ T e ≡ A`). So `std/path.bl`'s `ua : Equiv A B -> Path (Type 0) A B`,
//! a single-face `Glue` line, is now **Checked** by both checkers, not declined. Transporting *along*
//! a Glue line — the univalence `transp`-over-`Glue` (`ua`) computation rule — is likewise
//! **independently re-derived** (`transp_glue`, F1), so the re-checker genuinely re-computes the ua
//! transport (forward `fst e` / inverse `invEq e`) instead of trusting the kernel. (`hcomp` over a
//! Glue line is not corpus-reachable and stays fail-safe.) Re-deriving it *independently* is what
//! closed a shared **soundness bug**: both checkers' `family_is_constant` compared a Kan line only at
//! its endpoints, so the univalence loop `i. Glue B (i=0) A e` with `A ≡ B` (equal endpoints, varying
//! interior) was judged constant and `transp` short-circuited to the identity — the kernel proved
//! `∀ e. transp (ua e) a ≡ a`, false for any non-identity self-equivalence. Fixed by probing the
//! interior (see `kan::family_is_constant`).
//!
//! Declined (never silently accepted): cubical partial elements/systems (`Partial`/`System`), a
//! higher-inductive path constructor (`PCon`), and the `foreign` FFI hatch. The re-checker's own
//! normalizer does not model these, so reaching one yields [`RecheckError::Declined`] — an *honest
//! refusal* to re-verify, never a pass.
//!
//! The intensional **partiality** layer (`Delay`/`now`/`later`/`force`) *is* modeled (a second,
//! independent NbE over `Delay`/`Now`/`Later`/`Force` values with `force (now a) ⇝ a` and guarded
//! `later`), so forced/partial programs are genuinely **Checked** by both checkers.
//!
//! The **effects/handlers** layer (`Op`/`Handle`/`EffTy`) is likewise modeled and Checked.
//!
//! ## Independent effect-row + grade discipline (B2)
//! The re-checker now tracks its *own* graded effect [`RRow`] alongside the type and usage vector
//! — a second opinion on effect discipline, not just on types. Threaded through `infer`/`check`
//! exactly as the kernel threads [`blight_kernel::Row`] (`check.rs`): a `perform op a` contributes
//! its effect label at the ambient demand; `later`/`force` contribute the built-in `Partial` label
//! (so divergence is tracked); subterms' rows are unioned; a `handle` **discharges** the labels it
//! interprets and independently enforces each clause's **continuation-multiplicity grade**
//! (resuming `k` more often than the operation's `cont_grade` allows is now *Rejected*, not
//! ignored). The top-level [`recheck_judgement`] then re-derives the kernel's
//! [`blight_kernel::check_top_with`] purity invariant: **a proof's inferred effect row must be
//! empty** (pure + total, in particular `Partial` at grade 0). An impure/partial term claimed as a
//! proof is therefore independently *Rejected* — previously it was silently accepted because rows
//! were dropped. This strengthens "a false `Proof` must fool both checkers" to cover effectful and
//! partial programs, not just their types.

mod conv;
mod kan;
mod normalize;
mod term;
mod typecheck;
mod value;

/// Arc N / N5 instrumentation (this engine's IH counter) — see the doc on the definition.
pub use normalize::{take_ih_computed, take_ih_discarded};

pub use term::{RGrade, RRow, RTerm};

use blight_kernel::{Judgement, Proof, Signature};

/// Why a re-check did not succeed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecheckError {
    /// The judgement is outside the supported core fragment (a cubical partial-element/system, a
    /// higher-inductive path constructor, or a `foreign` postulate was reached). The univalence
    /// `Glue` layer (formation + boundary reductions), effects/handlers, `Int`, partiality-via-`Delay`,
    /// and symbolic universe levels (T2.3 — including prenex level variables, re-verified under the
    /// leveled door's told `n_levels`) are modeled and checked, not declined. This is an honest
    /// refusal, **not** a rejection of the proof.
    Declined(String),
    /// The independent checker genuinely *rejected* the term: it does not have the claimed type
    /// under this crate's own rules. If the kernel accepted it, the two checkers disagree — a
    /// soundness alarm worth investigating.
    Rejected(String),
}

impl std::fmt::Display for RecheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RecheckError::Declined(m) => write!(f, "re-check declined (unsupported): {m}"),
            RecheckError::Rejected(m) => write!(f, "re-check REJECTED: {m}"),
        }
    }
}

impl std::error::Error for RecheckError {}

/// The result of an independent re-check.
pub type RecheckResult = Result<(), RecheckError>;

/// Re-verify a kernel [`Judgement`] from scratch against the given [`Signature`].
///
/// Returns `Ok(())` when this crate's *own* independent checker agrees the term has the claimed
/// type; [`RecheckError::Declined`] when the judgement uses a variant outside the supported core
/// fragment; and [`RecheckError::Rejected`] when the independent checker disagrees with the
/// kernel (a soundness alarm).
pub fn recheck_judgement(sig: &Signature, judgement: &Judgement) -> RecheckResult {
    recheck_judgement_leveled(sig, judgement, 0)
}

/// Like [`recheck_judgement`], but re-verified under `n_levels` prenex universe-level variables
/// (T2.3) — the re-checker's twin of the kernel's `check_top_leveled` door for a level-polymorphic
/// definition. `n_levels` must be *told* by the caller (the elaborator records each
/// `define-level`'s binder count): a faithful independent re-checker cannot re-derive it from the
/// term, because scanning for the largest `Level::Var` would make the well-formedness gate
/// vacuous. `n_levels == 0` is exactly [`recheck_judgement`].
pub fn recheck_judgement_leveled(
    sig: &Signature,
    judgement: &Judgement,
    n_levels: usize,
) -> RecheckResult {
    let Judgement::HasType { term, ty } = judgement;
    // Translate both the term and its claimed type into this crate's own `RTerm`, declining if
    // either touches an unsupported variant. Universe levels translate totally (level variables
    // are modeled, T2.3); their scope is gated by the checker below against `n_levels`.
    let rterm = term::from_kernel(term)?;
    let rty = term::from_kernel(ty)?;
    // The general typing door: re-derive the effect-row + grade discipline (so a mis-graded handler
    // is Rejected), but do *not* demand top-level purity — a buildable definition may legitimately
    // be partial/effectful (the kernel's `Checker` allows it; only a `Proof` must be pure).
    typecheck::Recheck::new(sig).check_top_leveled(&rterm, &rty, false, n_levels)
}

/// Re-verify a kernel [`Judgement`] *as a proof obligation*: like [`recheck_judgement`] but
/// additionally re-derives the kernel's top-level **purity** invariant
/// ([`blight_kernel::check_top_with`], spec §4.1/§4.5) — the term's independently inferred effect
/// row must be empty (pure + total). This is the proof-strength door used by [`recheck_proof`]; it
/// is exposed so the purity re-derivation can be exercised on a hand-built `Judgement` (a `Proof`
/// itself can never be forged with an impure conclusion, by construction).
pub fn recheck_judgement_as_proof(sig: &Signature, judgement: &Judgement) -> RecheckResult {
    recheck_judgement_as_proof_leveled(sig, judgement, 0)
}

/// The proof-strength door under `n_levels` prenex level variables (T2.3): purity is re-derived
/// *and* every universe level is re-verified in scope — the second opinion on the kernel's
/// `check_top_leveled`.
pub fn recheck_judgement_as_proof_leveled(
    sig: &Signature,
    judgement: &Judgement,
    n_levels: usize,
) -> RecheckResult {
    let Judgement::HasType { term, ty } = judgement;
    let rterm = term::from_kernel(term)?;
    let rty = term::from_kernel(ty)?;
    typecheck::Recheck::new(sig).check_top_leveled(&rterm, &rty, true, n_levels)
}

/// Re-verify the conclusion of a kernel [`Proof`]. A `Proof` is the kernel's certified
/// pure/total top-level (spec §2.1), so the re-checker re-derives that purity too (via
/// [`recheck_judgement_as_proof`]) — a genuinely independent second opinion on the proof boundary.
pub fn recheck_proof(sig: &Signature, proof: &Proof) -> RecheckResult {
    recheck_judgement_as_proof(sig, proof.concl())
}

// =================================================================================================
// White-box unit tests (Track D hardening). These reach *inside* the crate — `term::from_kernel`
// and `typecheck::Recheck::check_top` — to pin behaviour the public surface only exercises
// indirectly: which kernel variants are honestly declined (vs rejected), and how the `require_pure`
// flag at the proof boundary turns a *buildable* partial term into a *rejected* one. The generative
// soundness / fragment-completeness *properties* live in `tests/properties.rs`.
// =================================================================================================
#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::term::{Cofib, SystemBranch};
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Interval, Level, Term};
    use std::rc::Rc;

    fn nat_sig() -> Signature {
        let mut sig = Signature::new();
        sig.declare(DataDecl {
            name: DataName("Nat".into()),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![
                Constructor {
                    name: ConName("Zero".into()),
                    args: vec![],
                    result_indices: vec![],
                },
                Constructor {
                    name: ConName("Succ".into()),
                    args: vec![Arg::Rec(vec![])],
                    result_indices: vec![],
                },
            ],
            path_constructors: vec![],
        });
        sig
    }
    fn nat() -> Term {
        Term::Data(DataName("Nat".into()), vec![], vec![])
    }
    fn zero() -> Term {
        Term::Con(ConName("Zero".into()), vec![])
    }

    /// T2.3 headline: the re-checker **agrees** (Ok — not Declined, not Rejected) on the
    /// level-polymorphic identity, the exact judgement the kernel pin
    /// `level_polymorphic_identity_checks` certifies through `check_top_leveled`:
    /// `λA.λx.x : Π^ω(A : Univ u). Π^ω(x : A). A` under one prenex level variable. This is the
    /// two-checker guarantee extended to the level-polymorphic fragment — and the same judgement is
    /// (a) *kernel*-verified here first, so the pin re-checks a genuinely kernel-accepted
    /// judgement, and (b) Rejected by the recheck with **no** level context, so the agreement is
    /// not vacuous.
    #[test]
    fn recheck_agrees_on_level_poly_identity() {
        use blight_kernel::Grade;
        let ty = || {
            Term::Pi(
                Grade::Omega,
                Rc::new(Term::Univ(Level::Var(0))),
                Rc::new(Term::Pi(
                    Grade::Omega,
                    Rc::new(Term::Var(0)),
                    Rc::new(Term::Var(1)),
                )),
            )
        };
        let id = || Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Var(0)))));
        assert!(
            blight_kernel::check_top_leveled(Signature::empty(), id(), ty(), 1).is_ok(),
            "the kernel accepts the level-polymorphic identity (premise of the parity pin)"
        );
        let j = Judgement::HasType {
            term: id(),
            ty: ty(),
        };
        let sig = Signature::empty();
        assert_eq!(
            recheck_judgement_leveled(&sig, &j, 1),
            Ok(()),
            "the independent re-checker agrees under u : Level"
        );
        assert!(
            matches!(recheck_judgement(&sig, &j), Err(RecheckError::Rejected(_))),
            "with no level context the same judgement is Rejected (gate is real)"
        );
    }

    /// F1: `from_kernel` *translates* the Glue univalence layer — it is modeled (typed, boundary-
    /// reduced, and Kan-transported via `transp_glue`), not declined. This test pins the translation.
    #[test]
    fn from_kernel_translates_glue() {
        let u0 = || Term::Univ(Level::Zero);
        let glue = Term::Glue {
            base: Rc::new(u0()),
            cofib: Cofib::Eq0(Interval::I0),
            ty: Rc::new(u0()),
            equiv: Rc::new(u0()),
        };
        assert!(matches!(term::from_kernel(&glue), Ok(RTerm::Glue { .. })));
        let unglue = Term::Unglue(Rc::new(glue));
        assert!(matches!(term::from_kernel(&unglue), Ok(RTerm::Unglue(_))));
    }

    /// `from_kernel` declines cubical partial elements and systems.
    #[test]
    fn from_kernel_declines_partial_and_system() {
        let partial = Term::Partial(Cofib::Top, Rc::new(nat()));
        assert!(matches!(
            term::from_kernel(&partial),
            Err(RecheckError::Declined(_))
        ));
        let system = Term::System(Vec::<SystemBranch>::new());
        assert!(matches!(
            term::from_kernel(&system),
            Err(RecheckError::Declined(_))
        ));
    }

    /// `from_kernel` declines a higher inductive type's path constructor (Wave 7/E4): the
    /// re-checker has no independent model of a HIT's `PathConstructor` boundary equations (those
    /// live only in the kernel's own `Signature`), so — exactly like `Partial`/`System` above — it
    /// honestly declines rather than silently pass a construct it cannot re-verify.
    #[test]
    fn from_kernel_declines_pcon() {
        let pcon = Term::PCon {
            data: DataName("S1".into()),
            name: ConName("loop".into()),
            args: vec![],
            dim: Interval::I0,
        };
        match term::from_kernel(&pcon) {
            Err(RecheckError::Declined(m)) => assert!(m.contains("path constructor")),
            other => panic!("expected Declined, got {other:?}"),
        }
    }

    /// `from_kernel` declines the trusted `foreign` FFI hatch (it cannot re-verify an opaque symbol).
    #[test]
    fn from_kernel_declines_foreign() {
        let f = Term::Foreign {
            symbol: "bl_x".into(),
            ty: Rc::new(nat()),
        };
        match term::from_kernel(&f) {
            Err(RecheckError::Declined(m)) => assert!(m.contains("foreign")),
            other => panic!("expected Declined, got {other:?}"),
        }
    }

    /// `from_kernel` *rejects* (not declines) an `Erased` sentinel — it must never appear in a
    /// checked term, so reaching one is a hard error, not an honest refusal.
    #[test]
    fn from_kernel_rejects_erased() {
        assert!(matches!(
            term::from_kernel(&Term::Erased),
            Err(RecheckError::Rejected(_))
        ));
    }

    /// T2.3: universe level variables are **modeled**, no longer declined at translation — the
    /// trio that replaces the pre-T2.3 `from_kernel_declines_level_variable` pin:
    /// 1. `from_kernel` translates `Univ (Var 0)` totally;
    /// 2. the **unleveled** door *Rejects* it (out-of-scope level variable — mirroring the kernel's
    ///    `check_top_with`, which errors on a var-level with no level context; an honest Decline
    ///    would be wrong now that levels are modeled);
    /// 3. the **leveled** door with `n_levels = 1` re-verifies `Univ u : Univ (suc u)` — Ok.
    #[test]
    fn level_variable_modeled_rejected_unleveled_ok_leveled() {
        let t = Term::Univ(Level::Var(0));
        assert!(
            term::from_kernel(&t).is_ok(),
            "level variables translate totally (modeled, not declined)"
        );
        let j = Judgement::HasType {
            term: Term::Univ(Level::Var(0)),
            ty: Term::Univ(Level::Suc(Box::new(Level::Var(0)))),
        };
        let sig = Signature::empty();
        assert!(
            matches!(recheck_judgement(&sig, &j), Err(RecheckError::Rejected(_))),
            "an out-of-scope level variable is Rejected through the unleveled door"
        );
        assert_eq!(
            recheck_judgement_leveled(&sig, &j, 1),
            Ok(()),
            "Univ u : Univ (suc u) re-verifies under one prenex level variable"
        );
    }

    /// T2.3 twin negative: the level well-formedness gate is exact — `Var(1)` under `n_levels = 1`
    /// is out of scope and Rejected (the gate is `u < n_levels`, not merely "some level context
    /// exists"). The kernel agrees (parity on the boundary).
    #[test]
    fn recheck_rejects_level_var_beyond_n_levels() {
        let j = Judgement::HasType {
            term: Term::Univ(Level::Var(1)),
            ty: Term::Univ(Level::Suc(Box::new(Level::Var(1)))),
        };
        let sig = Signature::empty();
        assert!(
            matches!(
                recheck_judgement_leveled(&sig, &j, 1),
                Err(RecheckError::Rejected(_))
            ),
            "Var(1) under n_levels = 1 must be Rejected"
        );
        assert!(
            blight_kernel::check_top_leveled(
                Signature::empty(),
                Term::Univ(Level::Var(1)),
                Term::Univ(Level::Suc(Box::new(Level::Var(1)))),
                1,
            )
            .is_err(),
            "the kernel rejects the same out-of-scope level (boundary parity)"
        );
    }

    /// The `require_pure` flag *is* the proof boundary: a partial `later (now Zero) : Delay Nat`
    /// type-checks as a *buildable* judgement (`require_pure = false`) but is *Rejected* for impurity
    /// at the proof boundary (`require_pure = true`). This is the in-crate white-box of the
    /// `recheck_judgement` vs `recheck_judgement_as_proof` split.
    #[test]
    fn require_pure_flag_rejects_partial_at_proof_boundary() {
        let sig = nat_sig();
        let delay_nat = Term::Delay(Rc::new(nat()));
        let later = Term::Later(Rc::new(Term::Now(Rc::new(zero()))));
        let rterm = term::from_kernel(&later).expect("partial term is in-fragment");
        let rty = term::from_kernel(&delay_nat).expect("Delay Nat is in-fragment");

        // Buildable door: accepted.
        assert!(typecheck::Recheck::new(&sig)
            .check_top(&rterm, &rty, false)
            .is_ok());
        // Proof door: rejected for impurity.
        match typecheck::Recheck::new(&sig).check_top(&rterm, &rty, true) {
            Err(RecheckError::Rejected(m)) => assert!(m.contains("pure")),
            other => panic!("proof door must reject a partial term, got {other:?}"),
        }
    }

    /// A pure `now Zero : Delay Nat` passes *both* the buildable and the proof door — purity does not
    /// over-reject well-behaved total terms.
    #[test]
    fn require_pure_flag_accepts_pure_term() {
        let sig = nat_sig();
        let delay_nat = Term::Delay(Rc::new(nat()));
        let now = Term::Now(Rc::new(zero()));
        let rterm = term::from_kernel(&now).unwrap();
        let rty = term::from_kernel(&delay_nat).unwrap();
        assert!(typecheck::Recheck::new(&sig)
            .check_top(&rterm, &rty, false)
            .is_ok());
        assert!(typecheck::Recheck::new(&sig)
            .check_top(&rterm, &rty, true)
            .is_ok());
    }
}
