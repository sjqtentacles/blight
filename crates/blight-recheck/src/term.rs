//! This crate's *own* core term representation (`RTerm`), independent of
//! [`blight_kernel::Term`], plus the translation that reads a kernel term into it — declining on
//! any variant outside the supported core fragment.
//!
//! Keeping a separate datatype (rather than re-using `blight_kernel::Term`) is deliberate: it
//! forces the translation to enumerate exactly which variants the re-checker supports, so an
//! unsupported construct can never slip through as a silent pass.

use crate::RecheckError;
use blight_kernel::{ConName, DataName, IntPrimOp, Interval, Level, Term};

/// A grade in the `{0, 1, ω}` semiring (mirrors [`blight_kernel::Grade`] but is this crate's own
/// type, so the re-checker's accounting is independent).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RGrade {
    Zero,
    One,
    Omega,
}

impl RGrade {
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: RGrade) -> RGrade {
        use RGrade::*;
        match (self, other) {
            (Zero, g) | (g, Zero) => g,
            _ => Omega,
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, other: RGrade) -> RGrade {
        use RGrade::*;
        match (self, other) {
            (Zero, _) | (_, Zero) => Zero,
            (One, g) | (g, One) => g,
            (Omega, Omega) => Omega,
        }
    }

    /// The lattice order `0 ≤ 1 ≤ ω`.
    pub fn leq(self, other: RGrade) -> bool {
        self.rank() <= other.rank()
    }

    fn rank(self) -> u8 {
        match self {
            RGrade::Zero => 0,
            RGrade::One => 1,
            RGrade::Omega => 2,
        }
    }
}

impl From<blight_kernel::Grade> for RGrade {
    fn from(g: blight_kernel::Grade) -> Self {
        match g {
            blight_kernel::Grade::Zero => RGrade::Zero,
            blight_kernel::Grade::One => RGrade::One,
            blight_kernel::Grade::Omega => RGrade::Omega,
        }
    }
}

/// A De Morgan interval term, mirrored from the kernel (the interval theory is small and shared).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RInterval {
    I0,
    I1,
    Dim(usize),
    Min(Box<RInterval>, Box<RInterval>),
    Max(Box<RInterval>, Box<RInterval>),
    Neg(Box<RInterval>),
}

/// A cofibration, mirrored from the kernel (`crate::term::Cofib`). The re-checker models the Kan
/// table independently, so it needs its own cofibration algebra to decide total/empty faces.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RCofib {
    Top,
    Bot,
    Eq0(RInterval),
    Eq1(RInterval),
    And(Box<RCofib>, Box<RCofib>),
    Or(Box<RCofib>, Box<RCofib>),
}

/// This crate's independent core grammar. A strict subset of [`blight_kernel::Term`]: only the
/// supported core fragment is representable, which is what makes "declined" impossible to confuse
/// with "accepted".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RTerm {
    Var(usize),
    /// A universe at a *concrete* level (the only levels the core fragment needs). Level variables
    /// are declined at translation time.
    Univ(u32),
    Pi(RGrade, Box<RTerm>, Box<RTerm>),
    Lam(Box<RTerm>),
    App(Box<RTerm>, Box<RTerm>),
    Sigma(Box<RTerm>, Box<RTerm>),
    Pair(Box<RTerm>, Box<RTerm>),
    Fst(Box<RTerm>),
    Snd(Box<RTerm>),
    Ann(Box<RTerm>, Box<RTerm>),

    Data(DataName, Vec<RTerm>, Vec<RTerm>),
    Con(ConName, Vec<RTerm>),
    Elim {
        data: DataName,
        motive: Box<RTerm>,
        methods: Vec<RTerm>,
        scrutinee: Box<RTerm>,
    },

    /// `PathP (i. A) x y`. The family binds one dimension variable.
    PathP {
        family: Box<RTerm>,
        lhs: Box<RTerm>,
        rhs: Box<RTerm>,
    },
    PLam(Box<RTerm>),
    PApp(Box<RTerm>, RInterval),
    /// An interval lifted into term position (only valid in dimension argument position).
    Interval(RInterval),

    // ---- cubical Kan operations (spec §2.6): modeled independently so they are Checked, not
    // Declined. `Comp` is kept primitive (decomposed in the Kan engine, mirroring the kernel). ----
    /// `Transp (i. A) φ a0` — transport. `family` binds one dimension.
    Transp {
        family: Box<RTerm>,
        cofib: RCofib,
        base: Box<RTerm>,
    },
    /// `HComp A φ (i. u) a0` — homogeneous composition. `tube` binds one dimension.
    HComp {
        ty: Box<RTerm>,
        cofib: RCofib,
        tube: Box<RTerm>,
        base: Box<RTerm>,
    },
    /// `Comp (i. A) φ (i. u) a0` — general composition (derived from `HComp` + `Transp`).
    Comp {
        family: Box<RTerm>,
        cofib: RCofib,
        tube: Box<RTerm>,
        base: Box<RTerm>,
    },

    // ---- partiality (spec §4.5): the intensional Capretta delay, modeled independently so it is
    // Checked, not Declined. The re-checker does not track effect rows, so it re-derives only the
    // *types* (`Delay A : Univ`, `now a : Delay A`, `later d : Delay A`, `force d : A`); the
    // proof-boundary `Partial` discipline is the kernel's job. ----
    /// `Delay A` — the delay type former.
    Delay(Box<RTerm>),
    /// `now a : Delay A`.
    Now(Box<RTerm>),
    /// `later d : Delay A` — a guarded step (intensional: never auto-unfolded by NbE).
    Later(Box<RTerm>),
    /// `force d : A` when `d : Delay A` — the delay eliminator. `force (now a) ⇝ a`; over a
    /// `later`/neutral it stays stuck.
    Force(Box<RTerm>),

    // ---- effects and handlers (spec §4), modeled at the TYPE LEVEL ONLY so effect programs are
    // ACCEPTED (re-verified), not Declined. The re-checker re-derives the *types* via the
    // signature's operation signatures (param/result types), but does NOT track effect rows or
    // continuation grades — those remain the kernel's soundness responsibility (the same honest
    // precedent as the delay layer above). ----
    /// `perform op a` — invoke effect operation `op` of `effect` with argument `a`. The re-checker
    /// re-derives its type as `result_ty[a/x]` from the op's signature; the row is ignored.
    Op {
        effect: blight_kernel::row::EffName,
        op: blight_kernel::signature::OpName,
        arg: Box<RTerm>,
    },
    /// `handle body { return x. r ; (op x k. e)... }`. Binders mirror the kernel: `return_clause`
    /// binds the result value `x` (1 binder); each op clause binds the op argument `x` then the
    /// continuation `k` (2 binders, `k` innermost = de Bruijn 0). The re-checker re-derives the
    /// result type `C` from the return clause; rows and continuation grades are ignored.
    Handle {
        body: Box<RTerm>,
        return_clause: Box<RTerm>,
        op_clauses: Vec<(blight_kernel::signature::OpName, Box<RTerm>)>,
    },
    /// `! E A` — the effectful computation *type*. The re-checker drops the row `E` (it does not
    /// track rows), storing only the payload type `A`; `! E A` and `! E' A` are convertible.
    EffTy(Box<RTerm>),

    // ---- primitive machine integers (M11), modeled independently so Int programs are ACCEPTED
    // (re-verified), not Declined. The re-checker re-derives the Int types and re-runs the same
    // definitional arithmetic, an independent witness of the kernel's Int reduction. ----
    /// `Int` — the primitive integer type (`IntTy : Univ 0`).
    IntTy,
    /// An integer literal `n : Int`.
    IntLit(i64),
    /// A primitive `Int` operation; arithmetic and comparison alike conclude `Int`.
    IntPrim {
        op: IntPrimOp,
        lhs: Box<RTerm>,
        rhs: Box<RTerm>,
    },
}

/// Translate a kernel [`Term`] into this crate's [`RTerm`], **declining** on any variant outside
/// the supported core fragment. The decline carries the offending variant's name so a maintainer
/// can see exactly what coverage is missing.
pub fn from_kernel(t: &Term) -> Result<RTerm, RecheckError> {
    Ok(match t {
        Term::Var(i) => RTerm::Var(*i),
        Term::Univ(l) => RTerm::Univ(level_to_nat(l)?),
        Term::Pi(g, a, b) => RTerm::Pi(
            (*g).into(),
            Box::new(from_kernel(a)?),
            Box::new(from_kernel(b)?),
        ),
        Term::Lam(b) => RTerm::Lam(Box::new(from_kernel(b)?)),
        Term::App(f, a) => RTerm::App(Box::new(from_kernel(f)?), Box::new(from_kernel(a)?)),
        Term::Sigma(a, b) => RTerm::Sigma(Box::new(from_kernel(a)?), Box::new(from_kernel(b)?)),
        Term::Pair(a, b) => RTerm::Pair(Box::new(from_kernel(a)?), Box::new(from_kernel(b)?)),
        Term::Fst(p) => RTerm::Fst(Box::new(from_kernel(p)?)),
        Term::Snd(p) => RTerm::Snd(Box::new(from_kernel(p)?)),
        Term::Ann(e, ty) => RTerm::Ann(Box::new(from_kernel(e)?), Box::new(from_kernel(ty)?)),

        Term::Data(d, ps, is) => RTerm::Data(
            d.clone(),
            ps.iter().map(from_kernel).collect::<Result<_, _>>()?,
            is.iter().map(from_kernel).collect::<Result<_, _>>()?,
        ),
        Term::Con(c, args) => RTerm::Con(
            c.clone(),
            args.iter().map(from_kernel).collect::<Result<_, _>>()?,
        ),
        Term::Elim {
            data,
            motive,
            methods,
            scrutinee,
        } => RTerm::Elim {
            data: data.clone(),
            motive: Box::new(from_kernel(motive)?),
            methods: methods.iter().map(from_kernel).collect::<Result<_, _>>()?,
            scrutinee: Box::new(from_kernel(scrutinee)?),
        },

        Term::PathP { family, lhs, rhs } => RTerm::PathP {
            family: Box::new(from_kernel(family)?),
            lhs: Box::new(from_kernel(lhs)?),
            rhs: Box::new(from_kernel(rhs)?),
        },
        Term::PLam(b) => RTerm::PLam(Box::new(from_kernel(b)?)),
        Term::PApp(p, r) => RTerm::PApp(Box::new(from_kernel(p)?), interval_from_kernel(r)),
        Term::Interval(r) => RTerm::Interval(interval_from_kernel(r)),

        Term::Transp {
            family,
            cofib,
            base,
        } => RTerm::Transp {
            family: Box::new(from_kernel(family)?),
            cofib: cofib_from_kernel(cofib),
            base: Box::new(from_kernel(base)?),
        },
        Term::HComp {
            ty,
            cofib,
            tube,
            base,
        } => RTerm::HComp {
            ty: Box::new(from_kernel(ty)?),
            cofib: cofib_from_kernel(cofib),
            tube: Box::new(from_kernel(tube)?),
            base: Box::new(from_kernel(base)?),
        },
        Term::Comp {
            family,
            cofib,
            tube,
            base,
        } => RTerm::Comp {
            family: Box::new(from_kernel(family)?),
            cofib: cofib_from_kernel(cofib),
            tube: Box::new(from_kernel(tube)?),
            base: Box::new(from_kernel(base)?),
        },

        // ---- partiality: now MODELED (Checked), not declined ----
        Term::Delay(a) => RTerm::Delay(Box::new(from_kernel(a)?)),
        Term::Now(a) => RTerm::Now(Box::new(from_kernel(a)?)),
        Term::Later(d) => RTerm::Later(Box::new(from_kernel(d)?)),
        Term::Force(d) => RTerm::Force(Box::new(from_kernel(d)?)),

        // ---- primitive machine integers: MODELED (Checked), not declined ----
        Term::IntTy => RTerm::IntTy,
        Term::IntLit(n) => RTerm::IntLit(*n),
        Term::IntPrim { op, lhs, rhs } => RTerm::IntPrim {
            op: *op,
            lhs: Box::new(from_kernel(lhs)?),
            rhs: Box::new(from_kernel(rhs)?),
        },

        // ---- effects and handlers: now MODELED at the type level (Checked), not declined ----
        Term::Op { effect, op, arg } => RTerm::Op {
            effect: effect.clone(),
            op: op.clone(),
            arg: Box::new(from_kernel(arg)?),
        },
        Term::Handle {
            body,
            return_clause,
            op_clauses,
        } => RTerm::Handle {
            body: Box::new(from_kernel(body)?),
            return_clause: Box::new(from_kernel(return_clause)?),
            op_clauses: op_clauses
                .iter()
                .map(|(op, clause)| Ok((op.clone(), Box::new(from_kernel(clause)?))))
                .collect::<Result<_, RecheckError>>()?,
        },
        // `! E A`: drop the row, keep only the payload type `A`.
        Term::EffTy(_row, a) => RTerm::EffTy(Box::new(from_kernel(a)?)),

        // ---- declined: outside the core fragment (honest refusal, never a pass) ----
        Term::Partial(..) | Term::System(..) => {
            return Err(RecheckError::Declined(
                "cubical partial element/system".into(),
            ))
        }
        Term::Glue { .. } | Term::GlueTerm { .. } | Term::Unglue(..) => {
            return Err(RecheckError::Declined("Glue type".into()))
        }
        // A `foreign` postulate is trusted, kernel-only code (spec §7.6): the independent re-checker
        // cannot re-verify an opaque external symbol, so any judgement mentioning one is *declined*
        // (an honest "I won't certify this", not a soundness rejection).
        Term::Foreign { symbol, .. } => {
            return Err(RecheckError::Declined(format!(
                "foreign postulate `{symbol}` (trusted FFI; not independently re-checkable)"
            )))
        }
        Term::Erased => {
            return Err(RecheckError::Rejected(
                "an `Erased` sentinel reached the re-checker (must never appear in a checked term)"
                    .into(),
            ))
        }
    })
}

fn interval_from_kernel(r: &Interval) -> RInterval {
    match r {
        Interval::I0 => RInterval::I0,
        Interval::I1 => RInterval::I1,
        Interval::Dim(i) => RInterval::Dim(*i),
        Interval::Min(a, b) => RInterval::Min(
            Box::new(interval_from_kernel(a)),
            Box::new(interval_from_kernel(b)),
        ),
        Interval::Max(a, b) => RInterval::Max(
            Box::new(interval_from_kernel(a)),
            Box::new(interval_from_kernel(b)),
        ),
        Interval::Neg(a) => RInterval::Neg(Box::new(interval_from_kernel(a))),
    }
}

fn cofib_from_kernel(c: &blight_kernel::term::Cofib) -> RCofib {
    use blight_kernel::term::Cofib;
    match c {
        Cofib::Top => RCofib::Top,
        Cofib::Bot => RCofib::Bot,
        Cofib::Eq0(r) => RCofib::Eq0(interval_from_kernel(r)),
        Cofib::Eq1(r) => RCofib::Eq1(interval_from_kernel(r)),
        Cofib::And(a, b) => RCofib::And(
            Box::new(cofib_from_kernel(a)),
            Box::new(cofib_from_kernel(b)),
        ),
        Cofib::Or(a, b) => RCofib::Or(
            Box::new(cofib_from_kernel(a)),
            Box::new(cofib_from_kernel(b)),
        ),
    }
}

/// Collapse a concrete kernel [`Level`] to a natural number, declining on level *variables* (the
/// core fragment the prelude needs uses only concrete levels).
fn level_to_nat(l: &Level) -> Result<u32, RecheckError> {
    match l {
        Level::Zero => Ok(0),
        Level::Suc(inner) => Ok(level_to_nat(inner)? + 1),
        Level::Max(a, b) => Ok(level_to_nat(a)?.max(level_to_nat(b)?)),
        Level::Var(_) => Err(RecheckError::Declined("universe level variable".into())),
    }
}
