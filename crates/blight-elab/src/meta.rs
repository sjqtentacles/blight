//! Elaboration-time metavariables and first-order unification (spec §6.4). UNTRUSTED.
//!
//! Implicit arguments are solved here, never by the kernel: the elaborator inserts a fresh
//! metavariable for each leading implicit `Pi` binder of a used definition, unifies the
//! definition's explicit domains and result against the known argument/expected types, then
//! *zonks* the solutions back in. The kernel only ever sees a fully-solved closed core term;
//! a leftover (unsolved) meta is an elaboration error, never unsoundness.
//!
//! ## Representation trick
//! A core [`Term`] has no meta node (the trusted grammar must not grow one). We encode a meta as
//! `Term::Var(META_BASE + id)`: a reserved high de Bruijn range that cannot collide with a real
//! bound variable (contexts are tiny). [`MetaCtx::zonk`] removes every meta before the term leaves
//! the elaborator, so this encoding never escapes into the kernel.

use blight_kernel::Term;
use std::rc::Rc;

/// Reserved de Bruijn base for metavariables. Real contexts never reach this depth.
pub const META_BASE: usize = 1 << 40;

/// Whether `i` is a metavariable index (vs. a genuine de Bruijn variable).
pub fn is_meta(i: usize) -> bool {
    i >= META_BASE
}

/// The metavariable term `?id`.
pub fn meta_term(id: usize) -> Term {
    Term::Var(META_BASE + id)
}

/// A metavariable solution store. Solutions are recorded as (already-zonked) core terms in the
/// *global* (empty) de Bruijn scope; implicit arguments are solved to closed types/values.
#[derive(Debug, Default)]
pub struct MetaCtx {
    solutions: Vec<Option<Term>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnifyError {
    /// The two terms have incompatible rigid heads.
    Mismatch,
    /// A meta would be solved two incompatible ways: `(existing solution, conflicting candidate)`,
    /// both already zonked — a caller can pretty-print both for a "here are the two types I saw"
    /// diagnostic (E2), rather than the generic [`Mismatch`](Self::Mismatch). Boxed to keep the
    /// enum (and every `Result<_, UnifyError>` on the hot unify path) small.
    Ambiguous(Box<(Term, Term)>),
}

impl MetaCtx {
    pub fn new() -> Self {
        MetaCtx::default()
    }

    /// Allocate a fresh, unsolved metavariable, returning its id.
    pub fn fresh(&mut self) -> usize {
        let id = self.solutions.len();
        self.solutions.push(None);
        id
    }

    /// The current solution of meta `id`, if solved.
    pub fn solution(&self, id: usize) -> Option<&Term> {
        self.solutions.get(id).and_then(|o| o.as_ref())
    }

    /// Force a term's top meta head to its solution (shallow), repeatedly.
    fn force(&self, t: &Term) -> Term {
        let mut cur = t.clone();
        while let Term::Var(i) = cur {
            if is_meta(i) {
                if let Some(s) = self.solution(i - META_BASE) {
                    cur = s.clone();
                    continue;
                }
            }
            break;
        }
        cur
    }

    /// First-order unification: solve metas so that `a ≡ b` (syntactically, up to recorded
    /// solutions). This is deliberately *not* full higher-order unification — it covers the
    /// implicit-insertion patterns the tower needs (a meta standing for a type appearing rigidly in
    /// a domain or the result). A meta on either side that is unsolved is assigned the other side.
    pub fn unify(&mut self, a: &Term, b: &Term) -> Result<(), UnifyError> {
        let a = self.force(a);
        let b = self.force(b);
        match (&a, &b) {
            (Term::Var(i), _) if is_meta(*i) => self.assign(i - META_BASE, &b),
            (_, Term::Var(j)) if is_meta(*j) => self.assign(j - META_BASE, &a),
            (Term::Var(i), Term::Var(j)) => {
                if i == j {
                    Ok(())
                } else {
                    Err(UnifyError::Mismatch)
                }
            }
            (Term::Univ(_), Term::Univ(_)) => Ok(()),
            (Term::Erased, Term::Erased) => Ok(()),
            (Term::Pi(_, da, ca), Term::Pi(_, db, cb))
            | (Term::Sigma(da, ca), Term::Sigma(db, cb)) => {
                self.unify(da, db)?;
                self.unify(ca, cb)
            }
            (Term::Lam(ba), Term::Lam(bb)) | (Term::PLam(ba), Term::PLam(bb)) => self.unify(ba, bb),
            (Term::App(fa, xa), Term::App(fb, xb)) => {
                self.unify(fa, fb)?;
                self.unify(xa, xb)
            }
            (Term::Pair(la, ra), Term::Pair(lb, rb)) => {
                self.unify(la, lb)?;
                self.unify(ra, rb)
            }
            (Term::Fst(pa), Term::Fst(pb)) | (Term::Snd(pa), Term::Snd(pb)) => self.unify(pa, pb),
            (Term::Ann(ta, _), _) => self.unify(ta, &b),
            (_, Term::Ann(tb, _)) => self.unify(&a, tb),
            (Term::Data(na, pa, ia), Term::Data(nb, pb, ib)) => {
                if na != nb || pa.len() != pb.len() || ia.len() != ib.len() {
                    return Err(UnifyError::Mismatch);
                }
                for (x, y) in pa.iter().zip(pb) {
                    self.unify(x, y)?;
                }
                for (x, y) in ia.iter().zip(ib) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Term::Con(na, aa), Term::Con(nb, ab)) => {
                if na != nb || aa.len() != ab.len() {
                    return Err(UnifyError::Mismatch);
                }
                for (x, y) in aa.iter().zip(ab) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Term::Delay(x), Term::Delay(y))
            | (Term::Now(x), Term::Now(y))
            | (Term::Later(x), Term::Later(y)) => self.unify(x, y),
            // Effect subsumption at the elaborator level: when solving an implicit type argument
            // from an *effectful* computation's type `(! E T)`, unify against the underlying value
            // type `T`. This mirrors the kernel's subsumption (a value-typed slot accepts an
            // effectful argument — the empty row is ≤ any row), which is exactly what let the old
            // explicit-type-argument form work; without it, implicitizing e.g. `append`'s element
            // type breaks at a call site whose argument is an effectful `(! Bytes (List Token))`.
            // Only unsoundness-free: a wrong strip yields a term the kernel rejects, never accepts.
            (Term::EffTy(_, ta), Term::EffTy(_, tb)) => self.unify(ta, tb),
            (Term::EffTy(_, ta), _) => self.unify(ta, &b),
            (_, Term::EffTy(_, tb)) => self.unify(&a, tb),
            // Anything else: require syntactic equality (covers cubical/effect nodes we do not
            // descend into for unification — a meta is never introduced under them in M3).
            _ if a == b => Ok(()),
            _ => Err(UnifyError::Mismatch),
        }
    }

    /// Assign meta `id := t` (occurs-check elided: M3 implicit args are non-recursive types).
    fn assign(&mut self, id: usize, t: &Term) -> Result<(), UnifyError> {
        // If already solved, the new candidate must unify with the existing solution. On conflict,
        // report *both* zonked candidates (E2) rather than whatever `Mismatch` the recursive
        // unification bottomed out on internally — accurate even when the true clash is a few
        // levels deeper inside a compound type, since it is still true that this meta's two
        // proposed solutions disagree.
        if let Some(existing) = self.solution(id).cloned() {
            let candidate = self.zonk(t);
            return self
                .unify(&existing, &candidate)
                .map_err(|_| UnifyError::Ambiguous(Box::new((existing, candidate))));
        }
        self.solutions[id] = Some(self.zonk(t));
        Ok(())
    }

    /// Replace every solved meta in `t` by its (recursively zonked) solution. Used after
    /// elaboration to produce a meta-free core term for the kernel.
    pub fn zonk(&self, t: &Term) -> Term {
        match t {
            Term::Var(i) if is_meta(*i) => match self.solution(i - META_BASE) {
                Some(s) => self.zonk(&s.clone()),
                None => t.clone(),
            },
            Term::Var(_) | Term::Univ(_) | Term::Interval(_) | Term::Erased | Term::System(_) => {
                t.clone()
            }
            Term::Pi(g, a, b) => Term::Pi(*g, Rc::new(self.zonk(a)), Rc::new(self.zonk(b))),
            Term::Sigma(a, b) => Term::Sigma(Rc::new(self.zonk(a)), Rc::new(self.zonk(b))),
            Term::Lam(b) => Term::Lam(Rc::new(self.zonk(b))),
            Term::PLam(b) => Term::PLam(Rc::new(self.zonk(b))),
            Term::App(f, x) => Term::App(Rc::new(self.zonk(f)), Rc::new(self.zonk(x))),
            Term::Pair(a, b) => Term::Pair(Rc::new(self.zonk(a)), Rc::new(self.zonk(b))),
            Term::Fst(p) => Term::Fst(Rc::new(self.zonk(p))),
            Term::Snd(p) => Term::Snd(Rc::new(self.zonk(p))),
            Term::Ann(a, b) => Term::Ann(Rc::new(self.zonk(a)), Rc::new(self.zonk(b))),
            Term::Data(n, ps, is) => Term::Data(
                n.clone(),
                ps.iter().map(|x| self.zonk(x)).collect(),
                is.iter().map(|x| self.zonk(x)).collect(),
            ),
            Term::Con(n, args) => Term::Con(n.clone(), args.iter().map(|x| self.zonk(x)).collect()),
            Term::Delay(a) => Term::Delay(Rc::new(self.zonk(a))),
            Term::Now(a) => Term::Now(Rc::new(self.zonk(a))),
            Term::Later(a) => Term::Later(Rc::new(self.zonk(a))),
            // Other nodes carry no metas in M3 elaboration; clone structurally.
            other => other.clone(),
        }
    }

    /// Whether `t` still contains an unsolved meta after zonking.
    pub fn has_unsolved(&self, t: &Term) -> bool {
        match t {
            Term::Var(i) if is_meta(*i) => self.solution(i - META_BASE).is_none(),
            Term::Var(_) | Term::Univ(_) | Term::Interval(_) | Term::Erased | Term::System(_) => {
                false
            }
            Term::Pi(_, a, b) | Term::Sigma(a, b) => self.has_unsolved(a) || self.has_unsolved(b),
            Term::Lam(b) | Term::PLam(b) => self.has_unsolved(b),
            Term::App(f, x) => self.has_unsolved(f) || self.has_unsolved(x),
            Term::Pair(a, b) | Term::Ann(a, b) => self.has_unsolved(a) || self.has_unsolved(b),
            Term::Fst(p) | Term::Snd(p) => self.has_unsolved(p),
            Term::Data(_, ps, is) => {
                ps.iter().any(|x| self.has_unsolved(x)) || is.iter().any(|x| self.has_unsolved(x))
            }
            Term::Con(_, args) => args.iter().any(|x| self.has_unsolved(x)),
            Term::Delay(a) | Term::Now(a) | Term::Later(a) => self.has_unsolved(a),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blight_kernel::DataName;

    fn nat() -> Term {
        Term::Data(DataName("Nat".into()), vec![], vec![])
    }

    #[test]
    fn meta_solves_against_rigid() {
        let mut mc = MetaCtx::new();
        let m = mc.fresh();
        mc.unify(&meta_term(m), &nat()).unwrap();
        assert_eq!(mc.solution(m), Some(&nat()));
        // Zonk replaces the meta.
        assert_eq!(mc.zonk(&meta_term(m)), nat());
    }

    #[test]
    fn ambiguous_double_solution_unifies_or_errors() {
        let mut mc = MetaCtx::new();
        let m = mc.fresh();
        mc.unify(&meta_term(m), &nat()).unwrap();
        // Solving the same meta to a *different* rigid type is a mismatch.
        let other = Term::Univ(blight_kernel::Level::Zero);
        assert!(mc.unify(&meta_term(m), &other).is_err());
    }

    /// E2: solving an implicit type argument from an *effectful* computation type `(! E T)` strips
    /// the effect row and unifies against the value type `T` — the elaborator-level mirror of the
    /// kernel's effect subsumption, without which implicitizing a function used at an effectful
    /// call site would spuriously fail.
    #[test]
    fn effectful_argument_type_strips_row_for_unification() {
        use blight_kernel::row::Row;
        let list = |a: Term| Term::Data(DataName("List".into()), vec![a], vec![]);
        let mut mc = MetaCtx::new();
        let m = mc.fresh();
        // Domain `List ?m`; argument's synthesized type `(! E (List Nat))`.
        let eff = Term::EffTy(Row::empty(), Rc::new(list(nat())));
        mc.unify(&list(meta_term(m)), &eff).unwrap();
        assert_eq!(mc.solution(m), Some(&nat()));
    }

    #[test]
    fn unsolved_meta_detected() {
        let mut mc = MetaCtx::new();
        let m = mc.fresh();
        assert!(mc.has_unsolved(&meta_term(m)));
    }
}
