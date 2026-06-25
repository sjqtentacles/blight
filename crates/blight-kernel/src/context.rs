//! Graded typing contexts (spec §2.3 / §3.2): each entry carries a type and a grade, and the
//! rules perform resource arithmetic (`scale`, `add`, `zero`) over the grade vector.

use crate::semiring::{Grade, Semiring};
use crate::term::Term;

/// One context entry `x :^ρ A` (spec §2.3): a type and the grade at which `x` is used.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    pub ty: Term,
    pub grade: Grade,
}

/// A graded context `Γ ::= · | Γ, x :^ρ A`. Index 0 is the most recently bound variable
/// (de Bruijn convention).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Context {
    entries: Vec<Entry>,
    /// Number of dimension (interval) variables in scope. Dimensions are not graded and have no
    /// type, so we only track their count to manage their de Bruijn space (spec §2.6).
    dims: usize,
}

impl Context {
    /// The empty context `·`.
    pub fn empty() -> Self {
        Context {
            entries: Vec::new(),
            dims: 0,
        }
    }

    /// Extend with a new binding `x :^ρ A` (becomes de Bruijn index 0).
    pub fn extend(&self, ty: Term, grade: Grade) -> Self {
        // Index 0 is the most recently bound variable, so new entries go at the front.
        let mut entries = Vec::with_capacity(self.entries.len() + 1);
        entries.push(Entry { ty, grade });
        entries.extend(self.entries.iter().cloned());
        Context {
            entries,
            dims: self.dims,
        }
    }

    /// Extend with a fresh dimension variable (interval). Returns a context with one more dim.
    pub fn extend_dim(&self) -> Self {
        Context {
            entries: self.entries.clone(),
            dims: self.dims + 1,
        }
    }

    /// Number of dimension variables in scope.
    pub fn dim_len(&self) -> usize {
        self.dims
    }

    /// Look up the entry at de Bruijn index `i`.
    pub fn lookup(&self, index: usize) -> Option<&Entry> {
        self.entries.get(index)
    }

    /// Number of bound variables.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the context is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// `ρ · Γ` — scale every entry's grade by `ρ` (spec §3.2).
    pub fn scale(&self, by: Grade) -> Self {
        Context {
            entries: self
                .entries
                .iter()
                .map(|e| Entry {
                    ty: e.ty.clone(),
                    grade: by.mul(e.grade),
                })
                .collect(),
            dims: self.dims,
        }
    }

    /// `Γ₁ + Γ₂` — add grade vectors entrywise; requires matching variables/types (spec §3.2).
    pub fn add(&self, other: &Self) -> Self {
        assert_eq!(
            self.entries.len(),
            other.entries.len(),
            "graded-context addition requires the same variables"
        );
        Context {
            entries: self
                .entries
                .iter()
                .zip(other.entries.iter())
                .map(|(a, b)| {
                    debug_assert_eq!(a.ty, b.ty, "context addition: mismatched types");
                    Entry {
                        ty: a.ty.clone(),
                        grade: a.grade.add(b.grade),
                    }
                })
                .collect(),
            dims: self.dims,
        }
    }

    /// `0 · Γ` — the zero context: everything erased (spec §3.2).
    pub fn zero(&self) -> Self {
        self.scale(Grade::zero())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{Level, Term};

    fn univ() -> Term {
        Term::Univ(Level::Zero)
    }

    #[test]
    fn extend_then_lookup() {
        let ctx = Context::empty().extend(univ(), Grade::Omega);
        assert_eq!(ctx.len(), 1);
        let e = ctx.lookup(0).expect("index 0 should be the just-bound var");
        assert_eq!(e.grade, Grade::Omega);
        assert_eq!(e.ty, univ());
    }

    #[test]
    fn lookup_out_of_range_is_none() {
        let ctx = Context::empty().extend(univ(), Grade::One);
        assert!(ctx.lookup(5).is_none());
    }

    #[test]
    fn scale_multiplies_each_grade() {
        let ctx = Context::empty()
            .extend(univ(), Grade::One)
            .extend(univ(), Grade::One);
        let scaled = ctx.scale(Grade::Omega);
        assert_eq!(scaled.lookup(0).unwrap().grade, Grade::Omega);
        assert_eq!(scaled.lookup(1).unwrap().grade, Grade::Omega);
    }

    #[test]
    fn zero_context_erases_all() {
        let ctx = Context::empty()
            .extend(univ(), Grade::One)
            .extend(univ(), Grade::Omega);
        let z = ctx.zero();
        assert_eq!(z.lookup(0).unwrap().grade, Grade::Zero);
        assert_eq!(z.lookup(1).unwrap().grade, Grade::Zero);
    }

    #[test]
    fn add_is_entrywise() {
        // extend puts the most-recent binding at index 0:
        //   a: index 0 = Zero, index 1 = One
        //   b: index 0 = One,  index 1 = One
        let a = Context::empty()
            .extend(univ(), Grade::One)
            .extend(univ(), Grade::Zero);
        let b = Context::empty()
            .extend(univ(), Grade::One)
            .extend(univ(), Grade::One);
        let sum = a.add(&b);
        // index 0: 0+1 = 1; index 1: 1+1 = ω
        assert_eq!(sum.lookup(0).unwrap().grade, Grade::One);
        assert_eq!(sum.lookup(1).unwrap().grade, Grade::Omega);
    }
}
