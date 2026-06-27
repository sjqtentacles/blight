//! Usage vectors for the graded judgement (spec §3.2).
//!
//! The graded judgement `Γ ⊢ t :^σ A` produces, as *output*, a vector recording how much each
//! variable in scope was demanded by `t` (the QTT / Atkey / Idris-2 "usage" reading). This is
//! the dual of splitting the input context: rather than thread a budget *in*, we compute the
//! demand *out* and check it against each binder's declared grade at the binder rule.
//!
//! A [`Usage`] is indexed exactly like a [`crate::context::Context`]: slot `0` is the most
//! recently bound variable (innermost), and the vector's length equals the number of term
//! variables in scope.

use crate::semiring::{Grade, Semiring};

/// A usage vector: the demand placed on each in-scope term variable, innermost-first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Usage(Vec<Grade>);

impl Usage {
    /// The all-`0` vector of length `n`: nothing is used (the demand of a closed/typing subterm).
    pub fn zero(n: usize) -> Self {
        Usage(vec![Grade::zero(); n])
    }

    /// The unit vector `e_i` of length `n`: variable `i` demanded at `grade`, all others `0`.
    /// This is the demand produced by the `Var` rule for the variable it names.
    pub fn unit(i: usize, n: usize, grade: Grade) -> Self {
        let mut v = vec![Grade::zero(); n];
        v[i] = grade;
        Usage(v)
    }

    /// True iff every entry is `0` — the structural invariant of a 0-fragment (type-formation)
    /// subgoal, which may not charge any runtime usage.
    pub fn is_all_zero(&self) -> bool {
        self.0.iter().all(|g| *g == Grade::zero())
    }

    /// Entrywise sum `Γ₁ + Γ₂` (spec §3.2): combine two subterms' demands. Both must have equal
    /// length (they range over the same context).
    pub fn add(&self, other: &Usage) -> Usage {
        debug_assert_eq!(
            self.0.len(),
            other.0.len(),
            "usage addition requires equal-length vectors (same context)"
        );
        Usage(
            self.0
                .iter()
                .zip(other.0.iter())
                .map(|(a, b)| a.add(*b))
                .collect(),
        )
    }

    /// Scale `ρ · Γ` (spec §3.2): multiply every slot by `by`. `scale(0)` annihilates to all-`0`
    /// (the typing-fragment move) and `scale(1)` is the identity.
    pub fn scale(&self, by: Grade) -> Usage {
        Usage(self.0.iter().map(|g| by.mul(*g)).collect())
    }

    /// The demand on variable `i`, or `0` if out of range.
    pub fn get(&self, i: usize) -> Grade {
        self.0.get(i).copied().unwrap_or_else(Grade::zero)
    }

    /// Extend with a fresh innermost binder demanded at `grade` (becomes slot `0`).
    pub fn extend(&self, grade: Grade) -> Usage {
        let mut v = Vec::with_capacity(self.0.len() + 1);
        v.push(grade);
        v.extend(self.0.iter().copied());
        Usage(v)
    }

    /// Remove the innermost binder (slot `0`), returning its demand and the rest. Used by the
    /// `Lam` rule after it has checked `ρ ≥ demand(x)`.
    pub fn pop(&self) -> (Grade, Usage) {
        debug_assert!(!self.0.is_empty(), "pop on an empty usage vector");
        let head = self.0[0];
        (head, Usage(self.0[1..].to_vec()))
    }

    /// The number of variables this vector ranges over.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Grade::{Omega, One, Zero};

    #[test]
    fn zero_is_additive_unit() {
        let u = Usage(vec![One, Zero, Omega, One]);
        assert_eq!(u.add(&Usage::zero(4)), u, "u + 0 = u");
        assert_eq!(Usage::zero(4).add(&u), u, "0 + u = u");
    }

    #[test]
    fn add_is_entrywise_semiring() {
        // index 0: 0+1 = 1; index 1: 1+1 = ω; index 2: ω+0 = ω
        let a = Usage(vec![Zero, One, Omega]);
        let b = Usage(vec![One, One, Zero]);
        assert_eq!(a.add(&b), Usage(vec![One, Omega, Omega]));
    }

    #[test]
    fn scale_zero_annihilates() {
        let u = Usage(vec![One, Omega, One]);
        assert_eq!(u.scale(Zero), Usage::zero(3), "0·Γ is all-zero");
    }

    #[test]
    fn scale_one_identity() {
        let u = Usage(vec![One, Omega, Zero]);
        assert_eq!(u.scale(One), u, "1·Γ = Γ");
    }

    #[test]
    fn scale_omega() {
        // ω·0 = 0, ω·1 = ω, ω·ω = ω
        let u = Usage(vec![Zero, One, Omega]);
        assert_eq!(u.scale(Omega), Usage(vec![Zero, Omega, Omega]));
    }

    #[test]
    fn unit_is_basis_vector() {
        assert_eq!(Usage::unit(1, 3, One), Usage(vec![Zero, One, Zero]));
        assert_eq!(Usage::unit(0, 2, Omega), Usage(vec![Omega, Zero]));
    }

    #[test]
    fn unit_then_pop() {
        // unit at the innermost slot, then pop it: head is the demand, tail preserves the rest.
        let u = Usage(vec![One, Zero, Omega]); // some context demand
        let extended = u.extend(One); // push a fresh innermost binder demanded at 1
        let (head, rest) = extended.pop();
        assert_eq!(head, One);
        assert_eq!(rest, u, "pop restores the pre-extension vector");
    }

    #[test]
    fn get_in_and_out_of_range() {
        let u = Usage(vec![One, Omega]);
        assert_eq!(u.get(0), One);
        assert_eq!(u.get(1), Omega);
        assert_eq!(u.get(5), Zero, "out-of-range demand is 0");
    }

    #[test]
    #[should_panic(expected = "equal-length")]
    fn add_requires_equal_len() {
        let a = Usage(vec![One, Zero]);
        let b = Usage(vec![One]);
        let _ = a.add(&b);
    }
}
