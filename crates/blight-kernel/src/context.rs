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
    /// Number of **universe-level** variables in scope (T2, universe polymorphism). Like dimensions,
    /// level variables are untyped and ungraded — they inhabit their own de Bruijn space (`Level::Var`
    /// is an index into it) — so we track only the count. A `Level::Var(u)` is well-formed exactly
    /// when `u < levels`. Non-zero only while checking a level-polymorphic definition's body (the
    /// prenex `∀u.` binders are introduced at the checking boundary; see `check_top_leveled`).
    levels: usize,
    /// Per-branch *value overrides* for dependent pattern-match refinement (spec §2.7, kernel item
    /// 1b): a list of `(de-Bruijn-level, value-term)` pairs that specialize an ambient variable to a
    /// concrete value within a refined match branch (e.g. the scrutinee index `n ↦ Succ m` in the
    /// `vcons` branch of `vec-map`). The evaluation environment built by the checker consults these
    /// so the motive/conclusion reflect the branch's solved index equations. Empty in the ordinary
    /// (non-refining) path, so behavior is unchanged everywhere else.
    overrides: Vec<(usize, Term)>,
}

impl Context {
    /// The empty context `·`.
    pub fn empty() -> Self {
        Context {
            entries: Vec::new(),
            dims: 0,
            levels: 0,
            overrides: Vec::new(),
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
            levels: self.levels,
            overrides: self.overrides.clone(),
        }
    }

    /// Extend with a fresh dimension variable (interval). Returns a context with one more dim.
    pub fn extend_dim(&self) -> Self {
        Context {
            entries: self.entries.clone(),
            dims: self.dims + 1,
            levels: self.levels,
            overrides: self.overrides.clone(),
        }
    }

    /// Number of dimension variables in scope.
    pub fn dim_len(&self) -> usize {
        self.dims
    }

    /// Extend with a fresh universe-level variable (T2). Returns a context with one more level var
    /// in scope (the new `Level::Var(levels)` becoming valid); mirrors [`Self::extend_dim`].
    pub fn extend_level(&self) -> Self {
        Context {
            entries: self.entries.clone(),
            dims: self.dims,
            levels: self.levels + 1,
            overrides: self.overrides.clone(),
        }
    }

    /// Number of universe-level variables in scope.
    pub fn level_len(&self) -> usize {
        self.levels
    }

    /// The per-branch value overrides (de-Bruijn-level → value-term) for dependent-match refinement.
    pub fn overrides(&self) -> &[(usize, Term)] {
        &self.overrides
    }

    /// Add (or replace) value overrides for dependent-match refinement, returning a new context.
    /// Existing overrides at the same level are replaced; others are kept. Used by the eliminator's
    /// refinement to specialize ambient scrutinee-index variables within a branch.
    pub fn with_overrides(&self, extra: &[(usize, Term)]) -> Self {
        let mut overrides = self.overrides.clone();
        for (lvl, t) in extra {
            if let Some(slot) = overrides.iter_mut().find(|(l, _)| l == lvl) {
                slot.1 = t.clone();
            } else {
                overrides.push((*lvl, t.clone()));
            }
        }
        Context {
            entries: self.entries.clone(),
            dims: self.dims,
            levels: self.levels,
            overrides,
        }
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
            levels: self.levels,
            overrides: self.overrides.clone(),
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
            levels: self.levels,
            overrides: self.overrides.clone(),
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
