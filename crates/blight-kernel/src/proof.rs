//! The abstract `Proof` and the only door (spec §2.1).
//!
//! A [`Proof`] can be constructed *only* by the kernel's own checking routines (via the
//! crate-private [`Proof::trusted_new`]). There is no public constructor, no `unsafe` escape
//! hatch. External crates obtain a `Proof` solely by handing the kernel a term and a type and
//! having it check (see [`crate::check`]). [`Proof::concl`] is the one safe observation.

use crate::term::Term;

/// A kernel judgement that a [`Proof`] may conclude (spec §2.3). For M0 we expose the central
/// typing judgement; the other forms (`A type`, `A ≡ B`, the effectful `! E`, etc.) are added
/// in later milestones.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Judgement {
    /// `Γ ⊢ t : A` — `term` has type `ty` in the (closed, for M0 top-level) context.
    HasType { term: Term, ty: Term },
}

/// An opaque proof: a guarantee that the kernel rules, and only those rules, were followed
/// (spec §2.1). The single field is private to this crate, so no value can be built outside
/// the kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof {
    conclusion: Judgement,
}

impl Proof {
    /// The *only* constructor, visible only inside `blight-kernel`. Checking routines call this
    /// after they have actually verified the judgement. This is the private door of spec §2.1.
    pub(crate) fn trusted_new(conclusion: Judgement) -> Self {
        Proof { conclusion }
    }

    /// Read what this proof concludes — the one safe observation (spec §2.1). You can never go
    /// the other way and build a `Proof` from a `Judgement`.
    pub fn concl(&self) -> &Judgement {
        &self.conclusion
    }
}
