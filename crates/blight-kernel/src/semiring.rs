//! The grading spine (spec §3.1): the `{0, 1, ω}` zero–one–many semiring used for erasure,
//! linearity, regions, effects, and partiality. Wired into the kernel from day one because
//! substitution depends on it (spec §2.9).

/// A resource grade drawn from the default `{0, 1, ω}` semiring (spec §3.1).
///
/// `0` = erased (no runtime use), `1` = linear (exactly once), `ω` = unrestricted.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Grade {
    Zero,
    One,
    Omega,
}

/// The semiring interface (spec §3.1). Any instantiation must satisfy *positivity*
/// (`ρ + π = 0 ⟹ ρ = 0 ∧ π = 0`) and *zero-product* (`ρ · π = 0 ⟹ ρ = 0 ∨ π = 0`), which
/// is what makes resource accounting sound under substitution.
pub trait Semiring: Copy + PartialEq {
    /// The additive unit `0`.
    fn zero() -> Self;
    /// The multiplicative unit `1`.
    fn one() -> Self;
    /// Resource demands combine (e.g. two uses).
    fn add(self, other: Self) -> Self;
    /// Application scales the argument's demand by the function's demand.
    fn mul(self, other: Self) -> Self;
    /// The order `≤` on grades; the graded `Var` rule needs available `ρ ≥ σ` demanded.
    fn leq(self, other: Self) -> bool;
}

impl Semiring for Grade {
    fn zero() -> Self {
        Grade::Zero
    }

    fn one() -> Self {
        Grade::One
    }

    fn add(self, other: Self) -> Self {
        use Grade::{Omega, Zero};
        match (self, other) {
            (Zero, g) | (g, Zero) => g,
            // 1+1 = ω; anything else involving 1 or ω is ω.
            _ => Omega,
        }
    }

    fn mul(self, other: Self) -> Self {
        use Grade::{Omega, One, Zero};
        match (self, other) {
            (Zero, _) | (_, Zero) => Zero,
            (One, g) | (g, One) => g,
            (Omega, Omega) => Omega,
        }
    }

    fn leq(self, other: Self) -> bool {
        self.rank() <= other.rank()
    }
}

impl Grade {
    /// A numeric rank realizing the order `0 < 1 < ω`.
    fn rank(self) -> u8 {
        match self {
            Grade::Zero => 0,
            Grade::One => 1,
            Grade::Omega => 2,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Grade::{Omega, One, Zero};

    /// Addition table (spec §3.1):
    /// ```text
    ///  + | 0 1 ω
    /// ---+-------
    ///  0 | 0 1 ω
    ///  1 | 1 ω ω
    ///  ω | ω ω ω
    /// ```
    #[test]
    fn addition_table() {
        assert_eq!(Zero.add(Zero), Zero);
        assert_eq!(Zero.add(One), One);
        assert_eq!(Zero.add(Omega), Omega);
        assert_eq!(One.add(Zero), One);
        assert_eq!(One.add(One), Omega);
        assert_eq!(One.add(Omega), Omega);
        assert_eq!(Omega.add(Zero), Omega);
        assert_eq!(Omega.add(One), Omega);
        assert_eq!(Omega.add(Omega), Omega);
    }

    /// Multiplication table (spec §3.1):
    /// ```text
    ///  · | 0 1 ω
    /// ---+-------
    ///  0 | 0 0 0
    ///  1 | 0 1 ω
    ///  ω | 0 ω ω
    /// ```
    #[test]
    fn multiplication_table() {
        assert_eq!(Zero.mul(Zero), Zero);
        assert_eq!(Zero.mul(One), Zero);
        assert_eq!(Zero.mul(Omega), Zero);
        assert_eq!(One.mul(Zero), Zero);
        assert_eq!(One.mul(One), One);
        assert_eq!(One.mul(Omega), Omega);
        assert_eq!(Omega.mul(Zero), Zero);
        assert_eq!(Omega.mul(One), Omega);
        assert_eq!(Omega.mul(Omega), Omega);
    }

    /// Units: `0` is additive, `1` is multiplicative.
    #[test]
    fn units() {
        for g in [Zero, One, Omega] {
            assert_eq!(Grade::zero().add(g), g);
            assert_eq!(g.add(Grade::zero()), g);
            assert_eq!(Grade::one().mul(g), g);
            assert_eq!(g.mul(Grade::one()), g);
        }
    }

    /// Positivity: `ρ + π = 0 ⟹ ρ = 0 ∧ π = 0` (spec §3.1).
    #[test]
    fn positivity_law() {
        for r in [Zero, One, Omega] {
            for p in [Zero, One, Omega] {
                if r.add(p) == Zero {
                    assert_eq!(r, Zero);
                    assert_eq!(p, Zero);
                }
            }
        }
    }

    /// Zero-product: `ρ · π = 0 ⟹ ρ = 0 ∨ π = 0` (spec §3.1).
    #[test]
    fn zero_product_law() {
        for r in [Zero, One, Omega] {
            for p in [Zero, One, Omega] {
                if r.mul(p) == Zero {
                    assert!(r == Zero || p == Zero);
                }
            }
        }
    }

    /// The order `0 < 1 < ω`, reflexive (spec §3.1). `leq(a, b)` reads "available `a` covers
    /// demand `b`"? No — `leq` is the lattice order with `0 ≤ 1 ≤ ω`.
    #[test]
    fn order() {
        assert!(Zero.leq(Zero));
        assert!(Zero.leq(One));
        assert!(Zero.leq(Omega));
        assert!(One.leq(One));
        assert!(One.leq(Omega));
        assert!(Omega.leq(Omega));
        assert!(!One.leq(Zero));
        assert!(!Omega.leq(One));
        assert!(!Omega.leq(Zero));
    }
}
