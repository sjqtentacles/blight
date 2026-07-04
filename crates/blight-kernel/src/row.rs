//! Graded effect rows (spec §4.1): the producer-side reading of the §3 semiring.
//!
//! An effect row `E` records, for each effect label in scope, a [`Grade`] describing how the
//! surrounding computation may use that effect — in particular *continuation multiplicity*:
//! `0` = the handler must not resume (abort/exception), `1` = it must resume at most once
//! (state, reader), `ω` = it may resume freely (nondeterminism, generators). This is the exact
//! same `{0,1,ω}` semiring M1 uses for consumer coeffects (usage); effects and coeffects are
//! "one graded modality read in two polarities" (spec §4.6).
//!
//! Rows are *unordered* graded multisets of labels, optionally open with a trailing row variable
//! `ε` for effect polymorphism (spec §4.1). Two rows combine by **graded union** (per-label
//! [`Grade::add`]); the empty row `⟨⟩` is the unit and denotes a *pure* computation.

use crate::semiring::{Grade, Semiring};
use std::collections::BTreeMap;

/// The name of an effect (e.g. `State`, `IO`, or the built-in [`EffName::PARTIAL`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EffName(pub String);

impl EffName {
    /// The reserved built-in *partiality* effect (spec §4.5). Its presence in a row at a nonzero
    /// grade means "this computation may diverge"; a proof is demanded at `Partial = 0`.
    pub const PARTIAL_STR: &'static str = "Partial";

    /// Construct a user effect label from its name.
    pub fn new(name: impl Into<String>) -> Self {
        EffName(name.into())
    }

    /// Construct the built-in `Partial` label.
    pub fn partial() -> Self {
        EffName(Self::PARTIAL_STR.to_string())
    }

    /// Whether this is the built-in `Partial` label.
    pub fn is_partial(&self) -> bool {
        self.0 == Self::PARTIAL_STR
    }
}

/// A row variable `ε` (spec §4.1), as a de Bruijn-free unique tag. M2 supports at most one open
/// tail; richer Koka-style row unification is deferred to the tower (M3).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RowVar(pub usize);

/// A graded effect row `E ::= ⟨⟩ | ⟨ ℓ :^ρ ; E ⟩ | ε` (spec §4.1).
///
/// Represented as a sorted map from label to grade (so equality and conversion are canonical and
/// order-insensitive), plus an optional open tail. `labels` never stores a [`Grade::Zero`] entry:
/// a label graded `0` is *absent* (it contributes nothing), which keeps `is_empty`/equality clean.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    labels: BTreeMap<EffName, Grade>,
    tail: Option<RowVar>,
}

impl Row {
    /// The empty (pure) row `⟨⟩`.
    pub fn empty() -> Self {
        Row {
            labels: BTreeMap::new(),
            tail: None,
        }
    }

    /// A row carrying a single label at the given grade. A `Zero` grade yields the empty row
    /// (an absent effect).
    pub fn single(label: EffName, grade: Grade) -> Self {
        let mut r = Row::empty();
        r.insert(label, grade);
        r
    }

    /// Insert/accumulate a label at `grade` (grade-`add` with any existing entry). Inserting at
    /// `Zero` is a no-op; if accumulation reaches `Zero` the label is removed.
    fn insert(&mut self, label: EffName, grade: Grade) {
        if grade == Grade::Zero {
            return;
        }
        let entry = self.labels.entry(label).or_insert(Grade::Zero);
        *entry = entry.add(grade);
        // (add never yields Zero from a nonzero operand, so no removal needed here.)
    }

    /// Whether this row is empty *and closed* — i.e. denotes a pure computation.
    pub fn is_empty(&self) -> bool {
        self.labels.is_empty() && self.tail.is_none()
    }

    /// The grade at which `label` appears (Zero if absent).
    pub fn grade_of(&self, label: &EffName) -> Grade {
        self.labels.get(label).copied().unwrap_or(Grade::Zero)
    }

    /// Whether `label` appears at a nonzero grade.
    pub fn contains(&self, label: &EffName) -> bool {
        self.labels.contains_key(label)
    }

    /// The open tail row variable, if any.
    pub fn tail(&self) -> Option<&RowVar> {
        self.tail.as_ref()
    }

    /// Iterate over `(label, grade)` pairs (sorted by label).
    pub fn iter(&self) -> impl Iterator<Item = (&EffName, Grade)> {
        self.labels.iter().map(|(l, g)| (l, *g))
    }

    /// Graded union `E₁ ⊔ E₂` (spec §4.1): per-label [`Grade::add`]. Tails must agree (at most one
    /// open tail in M2); two distinct tails is a row-unification obligation deferred to M3, so we
    /// conservatively keep the left tail and require them equal at call sites that care.
    pub fn union(&self, other: &Row) -> Row {
        let mut out = self.clone();
        for (label, grade) in other.labels.iter() {
            out.insert(label.clone(), *grade);
        }
        // Tail handling: prefer an existing tail; if both present and distinct we still keep one
        // (M2 only ever unions against closed rows in practice — the checker demands closed rows
        // at the top — so this is a forward-compatible stub, not a correctness hazard here).
        if out.tail.is_none() {
            out.tail = other.tail.clone();
        }
        out
    }

    /// Discharge a label (spec §4.3): remove it from the row entirely. This is what a `Handle`
    /// does — it interprets `ℓ`, so the result row no longer mentions it.
    pub fn discharge(&self, label: &EffName) -> Row {
        let mut out = self.clone();
        out.labels.remove(label);
        out
    }

    /// Row order: `self ≤ other` iff every label of `self` appears in `other` at a `≥` grade and
    /// `self` is closed when `other` is closed. Used to check "a computation's row fits the
    /// ambient allowed row". (Reflexive; partial.)
    pub fn leq(&self, other: &Row) -> bool {
        // self has no tail beyond other's, and every label is dominated.
        if self.tail.is_some() && self.tail != other.tail {
            return false;
        }
        self.labels
            .iter()
            .all(|(label, g)| g.leq(other.grade_of(label)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Grade::{Omega, One, Zero};

    fn st() -> EffName {
        EffName("State".into())
    }
    fn io() -> EffName {
        EffName("IO".into())
    }

    #[test]
    fn empty_is_unit_of_union() {
        let e = Row::single(st(), One);
        assert_eq!(e.union(&Row::empty()), e);
        assert_eq!(Row::empty().union(&e), e);
        assert!(Row::empty().is_empty());
        assert!(!e.is_empty());
    }

    #[test]
    fn single_zero_is_empty() {
        assert!(Row::single(st(), Zero).is_empty());
    }

    #[test]
    fn union_is_commutative_and_associative() {
        let a = Row::single(st(), One);
        let b = Row::single(io(), One);
        let c = Row::single(st(), One);
        assert_eq!(a.union(&b), b.union(&a));
        assert_eq!(a.union(&b).union(&c), a.union(&b.union(&c)));
    }

    #[test]
    fn union_grade_adds_per_label() {
        // State at 1, unioned with State at 1, becomes State at ω (1+1=ω).
        let r = Row::single(st(), One).union(&Row::single(st(), One));
        assert_eq!(r.grade_of(&st()), Omega);
        // A distinct label keeps its own grade.
        let r2 = Row::single(st(), One).union(&Row::single(io(), One));
        assert_eq!(r2.grade_of(&st()), One);
        assert_eq!(r2.grade_of(&io()), One);
    }

    #[test]
    fn discharge_removes_label() {
        let r = Row::single(st(), One).union(&Row::single(io(), One));
        let d = r.discharge(&st());
        assert!(!d.contains(&st()));
        assert!(d.contains(&io()));
        // Discharging the last label yields the empty (pure) row.
        assert!(d.discharge(&io()).is_empty());
    }

    #[test]
    fn leq_is_reflexive_and_grade_monotone() {
        let r = Row::single(st(), One);
        assert!(r.leq(&r));
        // 1 ≤ ω, so State:1 fits inside State:ω.
        assert!(Row::single(st(), One).leq(&Row::single(st(), Omega)));
        // ω does not fit inside 1.
        assert!(!Row::single(st(), Omega).leq(&Row::single(st(), One)));
        // A label absent on the right (grade 0) cannot dominate a nonzero left.
        assert!(!Row::single(st(), One).leq(&Row::empty()));
        // Empty fits everywhere.
        assert!(Row::empty().leq(&r));
    }

    #[test]
    fn partial_label_helpers() {
        let p = EffName::partial();
        assert!(p.is_partial());
        assert!(!st().is_partial());
        assert_eq!(Row::single(p.clone(), One).grade_of(&p), One);
    }

    #[test]
    fn grade_of_absent_is_zero() {
        assert_eq!(Row::empty().grade_of(&st()), Zero);
    }
}
