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
//! Declined (never silently accepted): the cubical `Glue` operations (`Glue`/`GlueTerm`/`Unglue`)
//! and cubical partial elements/systems (`Partial`/`System`). The re-checker's own normalizer does
//! not model these layers, so reaching one yields [`RecheckError::Declined`] — an *honest refusal*
//! to re-verify, never a pass. In particular `std/path.bl`'s `ua : Equiv A B -> Path (Type 0) A B`
//! builds a `Glue` type, so re-checking `ua` (and anything that transports along it) is *declined*,
//! not rejected — the univalence layer is trusted to the seed kernel, whose `transp`-over-`Glue`
//! computation rule is exercised by a kernel white-box test and the closed `examples/ua_compute.bl`
//! (the independent re-checker deliberately does not duplicate the Glue Kan engine).
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

pub use term::{RGrade, RRow, RTerm};

use blight_kernel::{Judgement, Proof, Signature};

/// Why a re-check did not succeed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecheckError {
    /// The judgement is outside the supported core fragment (cubical `Glue`/partial-element/system,
    /// a `foreign` postulate, or a universe-level variable was reached). Effects/handlers, `Int`,
    /// and partiality-via-`Delay` are modeled and checked, not declined. This is an honest refusal,
    /// **not** a rejection of the proof.
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
    let Judgement::HasType { term, ty } = judgement;
    // Translate both the term and its claimed type into this crate's own `RTerm`, declining if
    // either touches an unsupported variant.
    let rterm = term::from_kernel(term)?;
    let rty = term::from_kernel(ty)?;
    // The general typing door: re-derive the effect-row + grade discipline (so a mis-graded handler
    // is Rejected), but do *not* demand top-level purity — a buildable definition may legitimately
    // be partial/effectful (the kernel's `Checker` allows it; only a `Proof` must be pure).
    typecheck::Recheck::new(sig).check_top(&rterm, &rty, false)
}

/// Re-verify a kernel [`Judgement`] *as a proof obligation*: like [`recheck_judgement`] but
/// additionally re-derives the kernel's top-level **purity** invariant
/// ([`blight_kernel::check_top_with`], spec §4.1/§4.5) — the term's independently inferred effect
/// row must be empty (pure + total). This is the proof-strength door used by [`recheck_proof`]; it
/// is exposed so the purity re-derivation can be exercised on a hand-built `Judgement` (a `Proof`
/// itself can never be forged with an impure conclusion, by construction).
pub fn recheck_judgement_as_proof(sig: &Signature, judgement: &Judgement) -> RecheckResult {
    let Judgement::HasType { term, ty } = judgement;
    let rterm = term::from_kernel(term)?;
    let rty = term::from_kernel(ty)?;
    typecheck::Recheck::new(sig).check_top(&rterm, &rty, true)
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
    use std::rc::Rc;
    use super::*;
    use blight_kernel::term::{Cofib, SystemBranch};
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Interval, Level, Term};

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

    /// `from_kernel` declines (never rejects, never silently passes) the Glue univalence layer.
    #[test]
    fn from_kernel_declines_glue() {
        let u0 = || Term::Univ(Level::Zero);
        let glue = Term::Glue {
            base: Rc::new(u0()),
            cofib: Cofib::Eq0(Interval::I0),
            ty: Rc::new(u0()),
            equiv: Rc::new(u0()),
        };
        assert!(matches!(
            term::from_kernel(&glue),
            Err(RecheckError::Declined(_))
        ));
        let unglue = Term::Unglue(Rc::new(glue));
        assert!(matches!(
            term::from_kernel(&unglue),
            Err(RecheckError::Declined(_))
        ));
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
    /// live only in the kernel's own `Signature`), so — exactly like `Glue`/`Partial`/`System`
    /// above — it honestly declines rather than silently pass a construct it cannot re-verify.
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

    /// `from_kernel` declines a universe *level variable* (the supported fragment uses concrete
    /// levels only).
    #[test]
    fn from_kernel_declines_level_variable() {
        let t = Term::Univ(Level::Var(0));
        assert!(matches!(
            term::from_kernel(&t),
            Err(RecheckError::Declined(_))
        ));
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
