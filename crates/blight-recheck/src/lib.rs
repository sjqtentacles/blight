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
//! `later`), so forced/partial programs are genuinely **Checked** by both checkers. The re-checker
//! re-derives only the *types* of the delay layer; the proof-boundary `Partial` discipline (a
//! `later`/`force` may not inhabit a proof) remains the trusted kernel's responsibility.
//!
//! The **effects/handlers** layer (`Op`/`Handle`/`EffTy`) is likewise modeled at the *type level
//! only* (the same honest precedent): the re-checker re-derives the types of `perform op a`
//! (`result_ty[a/x]`), `handle …` (the return clause's result type `C`), and `! E A` (a type),
//! consulting the [`blight_kernel::Signature`]'s operation signatures — but it does **not** track
//! effect rows or continuation-multiplicity grades (those remain the kernel's soundness job). So
//! effect/handler programs are now **Checked**, not declined.

mod conv;
mod kan;
mod normalize;
mod term;
mod typecheck;
mod value;

pub use term::{RGrade, RTerm};

use blight_kernel::{Judgement, Proof, Signature};

/// Why a re-check did not succeed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecheckError {
    /// The judgement is outside the supported core fragment (a Kan/effect/partiality variant was
    /// reached). This is an honest refusal, **not** a rejection of the proof.
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
    typecheck::Recheck::new(sig).check_top(&rterm, &rty)
}

/// Re-verify the conclusion of a kernel [`Proof`]. Convenience wrapper over
/// [`recheck_judgement`].
pub fn recheck_proof(sig: &Signature, proof: &Proof) -> RecheckResult {
    recheck_judgement(sig, proof.concl())
}
