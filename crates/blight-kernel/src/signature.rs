//! Inductive signatures (spec §2.7): the declared shape of (higher) inductive types — their
//! parameters, the constructors, each constructor's argument telescope (marking recursive
//! occurrences), and any path constructors (for HITs). The kernel consults the signature when
//! typing `Data`/`Con`/`Elim` and when computing ι reductions.
//!
//! For M0 we support parameterized, non-indexed inductives (enough for `Nat`, `List`, and a
//! HIT with point + path constructors). Full indexed families are an M1 refinement.

use crate::term::{ConName, DataName, Term};
use std::collections::HashMap;

/// The name of an effect operation (e.g. `get`, `put`). Unique across all declared effects (M2).
pub type OpName = String;

/// One argument of a constructor. We distinguish *recursive* arguments (whose type is the data
/// type being defined) because the eliminator must supply an induction hypothesis for them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Arg {
    /// A non-recursive argument with the given type (which may mention earlier args/params).
    NonRec(Term),
    /// A recursive argument: a value of the inductive type itself (strictly positive). For an
    /// *indexed* family the recursive occurrence carries its own index expressions (over the
    /// parameter and the preceding constructor arguments); empty for a non-indexed family.
    Rec(Vec<Term>),
}

/// A point constructor: a name and its argument telescope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: ConName,
    pub args: Vec<Arg>,
    /// For an *indexed* family (spec §2.7, M1), the index expressions appearing in this
    /// constructor's conclusion `D params (result_indices...)`, as terms over the parameter and
    /// argument telescope (de Bruijn, innermost = last constructor arg). Empty for a
    /// non-indexed type. M1 supports a single index.
    pub result_indices: Vec<Term>,
}

/// A path constructor (HIT, spec §2.7): like a point constructor, but it produces a *path* in
/// the inductive type between two point expressions, binding one dimension variable. For M0 we
/// record it structurally; the eliminator's method for it must produce a path in the motive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathConstructor {
    pub name: ConName,
    pub args: Vec<Arg>,
    /// The two endpoints (as terms over the constructor's args and the bound dimension).
    pub lhs: Term,
    pub rhs: Term,
}

/// A declared inductive type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataDecl {
    pub name: DataName,
    /// Parameter telescope (each a type; later params may mention earlier ones). M1 supports a
    /// single parameter.
    pub params: Vec<Term>,
    /// Index telescope (spec §2.7): the types of the family's indices, over the parameters. M1
    /// supports a single index. Empty for a non-indexed type.
    pub indices: Vec<Term>,
    /// The universe level the type lives in.
    pub level: u32,
    pub constructors: Vec<Constructor>,
    pub path_constructors: Vec<PathConstructor>,
}

impl DataDecl {
    /// Find a point constructor by name and its index (the index is used to pick the matching
    /// eliminator method).
    pub fn constructor(&self, name: &ConName) -> Option<(usize, &Constructor)> {
        self.constructors
            .iter()
            .enumerate()
            .find(|(_, c)| &c.name == name)
    }

    /// Find a path constructor by name and its index *within the path-constructor list* (Wave
    /// 7/E4). An eliminator's methods vector is `[point methods...][path methods...]`, in
    /// declaration order within each group, so the method for path constructor index `i` lives at
    /// `self.constructors.len() + i`.
    pub fn path_constructor(&self, name: &ConName) -> Option<(usize, &PathConstructor)> {
        self.path_constructors
            .iter()
            .enumerate()
            .find(|(_, c)| &c.name == name)
    }
}

/// The signature of one effect operation (spec §4.1): `op : Π(x:A). B`, where `A` is the
/// parameter type and `B` is the result type (the type the continuation receives). Dependency of
/// `B` on the parameter `x` is allowed (de Bruijn 0 in `result_ty` refers to the parameter).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpSig {
    pub name: OpName,
    /// The operation's parameter type `A` (a type over the ambient context).
    pub param_ty: Term,
    /// The operation's result type `B` (a type over the ambient context extended with `x:A`).
    pub result_ty: Term,
    /// The **continuation multiplicity** (spec §4.6, M2): the grade at which a handler's `k`
    /// continuation for this operation may be invoked. `Grade::Zero` = *abort* (the handler must
    /// not resume — e.g. exceptions); `Grade::One` = *linear* (resume at most once — e.g. state);
    /// `Grade::Omega` = *multi-shot* (resume any number of times — e.g. nondeterminism). The
    /// handler's `k` binder is bound at this grade, so misuse is caught by the same [`crate::usage`]
    /// linearity accounting that governs `λ`-binders.
    pub cont_grade: crate::semiring::Grade,
}

/// A declared effect (spec §4.1): a name and a set of operations. Stored in the [`Signature`]
/// alongside inductive types — ops are kernel-checked declarations exactly like constructors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffDecl {
    pub name: crate::row::EffName,
    /// Parameter telescope (Wave 7/E2), like `DataDecl::params`: each a type, later params may
    /// mention earlier ones. Every `OpSig` of this effect has its `param_ty`/`result_ty` as terms
    /// over the ambient context extended with this telescope (outermost-first), then (for
    /// `result_ty`) the operation's own value parameter `x` innermost. Empty for a
    /// non-parameterized effect (every effect declared before E2).
    pub params: Vec<Term>,
    pub ops: Vec<OpSig>,
}

impl EffDecl {
    /// Find an operation of this effect by name.
    pub fn op(&self, name: &str) -> Option<&OpSig> {
        self.ops.iter().find(|o| o.name == name)
    }
}

/// The global signature: all declared inductive types, keyed by name.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Signature {
    datas: HashMap<DataName, DataDecl>,
    effects: HashMap<crate::row::EffName, EffDecl>,
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            datas: HashMap::new(),
            effects: HashMap::new(),
        }
    }

    /// Alias for [`Signature::new`]: the empty signature.
    pub fn empty() -> Self {
        Signature::new()
    }

    /// Register a declaration after it has passed well-formedness (incl. strict positivity).
    pub fn declare(&mut self, decl: DataDecl) {
        self.datas.insert(decl.name.clone(), decl);
    }

    pub fn get(&self, name: &DataName) -> Option<&DataDecl> {
        self.datas.get(name)
    }

    /// Iterate every registered inductive declaration (order is unspecified). Used by the backend to
    /// derive a stable per-data constructor tag (the constructor's index within its `DataDecl`).
    pub fn data_decls(&self) -> impl Iterator<Item = &DataDecl> {
        self.datas.values()
    }

    /// Find the inductive type (and the constructor's index + shape) that declares a constructor
    /// named `con`. For M0 constructor names are unique across the signature.
    pub fn data_of_con(&self, con: &ConName) -> Option<(&DataDecl, usize, &Constructor)> {
        for decl in self.datas.values() {
            if let Some((idx, ctor)) = decl.constructor(con) {
                return Some((decl, idx, ctor));
            }
        }
        None
    }

    /// Register an effect declaration after well-formedness (see [`Signature::check_effect`]).
    pub fn declare_effect(&mut self, decl: EffDecl) {
        self.effects.insert(decl.name.clone(), decl);
    }

    /// Look up an effect by name.
    pub fn get_effect(&self, name: &crate::row::EffName) -> Option<&EffDecl> {
        self.effects.get(name)
    }

    /// Find the effect (and the op's signature) that declares an operation named `op`. Operation
    /// names are unique across all effects (M2), so the lookup is unambiguous.
    pub fn op_of(&self, op: &str) -> Option<(&EffDecl, &OpSig)> {
        for eff in self.effects.values() {
            if let Some(sig) = eff.op(op) {
                return Some((eff, sig));
            }
        }
        None
    }

    /// Well-formedness for an effect declaration (spec §4.1): operation names are unique within
    /// the effect *and* across all already-declared effects, and the effect name is fresh and not
    /// the reserved built-in `Partial` label. (Type-checking that each `param_ty`/`result_ty` is a
    /// type happens at declaration time in the checker, which has the typing context.)
    pub fn check_effect(&self, decl: &EffDecl) -> Result<(), String> {
        if decl.name.is_partial() {
            return Err(format!(
                "{:?} is the reserved built-in partiality effect and cannot be declared",
                decl.name
            ));
        }
        if self.effects.contains_key(&decl.name) {
            return Err(format!("effect {:?} is already declared", decl.name));
        }
        // Unique op names within this effect.
        let mut seen = std::collections::HashSet::new();
        for op in &decl.ops {
            if !seen.insert(op.name.clone()) {
                return Err(format!(
                    "operation {:?} declared twice in effect {:?}",
                    op.name, decl.name
                ));
            }
            // Unique across already-declared effects.
            if self.op_of(&op.name).is_some() {
                return Err(format!(
                    "operation {:?} is already declared by another effect",
                    op.name
                ));
            }
        }
        Ok(())
    }

    /// Strict-positivity / well-formedness check (spec §2.7): every recursive argument must be
    /// the data type applied to the parameters, never to the left of an arrow inside another
    /// argument's type. For M0 the [`Arg::Rec`] marker already enforces this structurally; this
    /// method additionally rejects a non-recursive argument whose type *mentions* the data type
    /// in a negative position.
    pub fn check_positivity(&self, decl: &DataDecl) -> Result<(), String> {
        for c in &decl.constructors {
            for a in &c.args {
                if let Arg::NonRec(ty) = a {
                    if mentions_data(ty, &decl.name) {
                        return Err(format!(
                            "constructor {:?} has a non-strictly-positive occurrence of {:?}",
                            c.name, decl.name
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

/// Whether a term mentions a given data type by name — a conservative negative-occurrence check
/// (for M0: *any* mention inside a non-`Rec` argument is rejected as potentially non-positive; the
/// legitimate strictly-positive recursive occurrences are carried structurally by [`Arg::Rec`] and
/// never reach here). Guarded self-references (under `Later`/`Delay`) are also rejected — sound but
/// conservative; refining to position-awareness (allowing guarded/codata occurrences) is future
/// work.
///
/// **Exhaustive by design.** The match has no `_` wildcard arm: a newly-added [`Term`] variant will
/// fail to compile until its positivity handling is decided explicitly. The previous draft used a
/// `_ => false` catch-all that silently skipped `EffTy`/`Delay`/`PathP`/`Transp`/… — so a negative
/// self-occurrence hidden under any of those passed the check, admitting a non-strictly-positive
/// datatype and hence a fixpoint (soundness audit 2026-07-03, K4a).
fn mentions_data(term: &Term, name: &DataName) -> bool {
    match term {
        Term::Data(d, params, indices) => {
            d == name
                || params.iter().any(|t| mentions_data(t, name))
                || indices.iter().any(|t| mentions_data(t, name))
        }
        Term::Pi(_, a, b) | Term::Sigma(a, b) | Term::App(a, b) | Term::Ann(a, b) => {
            mentions_data(a, name) || mentions_data(b, name)
        }
        Term::Pair(a, b) => mentions_data(a, name) || mentions_data(b, name),
        // Single-`Term`-child formers (the child sits at various positions; the `Interval`/`Cofib`/
        // `Row`/symbol siblings carry no `Term`).
        Term::Lam(b)
        | Term::Fst(b)
        | Term::Snd(b)
        | Term::PLam(b)
        | Term::PApp(b, _)
        | Term::Partial(_, b)
        | Term::Unglue(b)
        | Term::EffTy(_, b)
        | Term::Delay(b)
        | Term::Now(b)
        | Term::Later(b)
        | Term::Force(b)
        | Term::Foreign { ty: b, .. } => mentions_data(b, name),
        Term::Con(_, args) | Term::PCon { args, .. } => args.iter().any(|t| mentions_data(t, name)),
        Term::Elim {
            motive,
            methods,
            scrutinee,
            ..
        } => {
            mentions_data(motive, name)
                || methods.iter().any(|t| mentions_data(t, name))
                || mentions_data(scrutinee, name)
        }
        Term::PathP { family, lhs, rhs } => {
            mentions_data(family, name) || mentions_data(lhs, name) || mentions_data(rhs, name)
        }
        Term::System(branches) => branches.iter().any(|b| mentions_data(&b.term, name)),
        Term::Transp { family, base, .. } => {
            mentions_data(family, name) || mentions_data(base, name)
        }
        Term::HComp { ty, tube, base, .. } => {
            mentions_data(ty, name) || mentions_data(tube, name) || mentions_data(base, name)
        }
        Term::Comp {
            family, tube, base, ..
        } => mentions_data(family, name) || mentions_data(tube, name) || mentions_data(base, name),
        Term::Glue {
            base, ty, equiv, ..
        } => mentions_data(base, name) || mentions_data(ty, name) || mentions_data(equiv, name),
        Term::GlueTerm { partial, base, .. } => {
            mentions_data(partial, name) || mentions_data(base, name)
        }
        Term::Op { type_args, arg, .. } => {
            type_args.iter().any(|t| mentions_data(t, name)) || mentions_data(arg, name)
        }
        Term::Handle {
            body,
            return_clause,
            op_clauses,
        } => {
            mentions_data(body, name)
                || mentions_data(return_clause, name)
                || op_clauses.iter().any(|(_, e)| mentions_data(e, name))
        }
        Term::IntPrim { lhs, rhs, .. } => mentions_data(lhs, name) || mentions_data(rhs, name),
        Term::IfZero {
            scrut,
            then_,
            else_,
            ..
        } => mentions_data(scrut, name) || mentions_data(then_, name) || mentions_data(else_, name),
        // Leaves with no `Term` child: cannot mention a data type.
        Term::Var(_)
        | Term::Univ(_)
        | Term::Interval(_)
        | Term::IntTy
        | Term::IntLit(_)
        | Term::Erased => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::row::EffName;
    use crate::term::Level;

    fn unit_ty() -> Term {
        Term::Univ(Level::Zero)
    }

    fn state_eff() -> EffDecl {
        EffDecl {
            name: EffName("State".into()),
            params: vec![],
            ops: vec![
                OpSig {
                    name: "get".into(),
                    param_ty: unit_ty(),
                    result_ty: unit_ty(),
                    cont_grade: crate::semiring::Grade::Omega,
                },
                OpSig {
                    name: "put".into(),
                    param_ty: unit_ty(),
                    result_ty: unit_ty(),
                    cont_grade: crate::semiring::Grade::Omega,
                },
            ],
        }
    }

    #[test]
    fn declare_and_lookup_effect() {
        let mut sig = Signature::new();
        let eff = state_eff();
        assert!(sig.check_effect(&eff).is_ok());
        sig.declare_effect(eff);
        let found = sig.get_effect(&EffName("State".into())).expect("declared");
        assert_eq!(found.ops.len(), 2);
        let (e, op) = sig.op_of("get").expect("op get");
        assert_eq!(e.name, EffName("State".into()));
        assert_eq!(op.name, "get");
    }

    #[test]
    fn duplicate_op_within_effect_rejected() {
        let sig = Signature::new();
        let bad = EffDecl {
            name: EffName("Bad".into()),
            params: vec![],
            ops: vec![
                OpSig {
                    name: "op".into(),
                    param_ty: unit_ty(),
                    result_ty: unit_ty(),
                    cont_grade: crate::semiring::Grade::Omega,
                },
                OpSig {
                    name: "op".into(),
                    param_ty: unit_ty(),
                    result_ty: unit_ty(),
                    cont_grade: crate::semiring::Grade::Omega,
                },
            ],
        };
        assert!(sig.check_effect(&bad).is_err());
    }

    #[test]
    fn duplicate_op_across_effects_rejected() {
        let mut sig = Signature::new();
        sig.declare_effect(state_eff());
        let clash = EffDecl {
            name: EffName("Other".into()),
            params: vec![],
            ops: vec![OpSig {
                name: "get".into(),
                param_ty: unit_ty(),
                result_ty: unit_ty(),
                cont_grade: crate::semiring::Grade::Omega,
            }],
        };
        assert!(sig.check_effect(&clash).is_err());
    }

    #[test]
    fn redeclaring_effect_rejected() {
        let mut sig = Signature::new();
        sig.declare_effect(state_eff());
        assert!(sig.check_effect(&state_eff()).is_err());
    }

    #[test]
    fn partial_label_cannot_be_declared() {
        let sig = Signature::new();
        let p = EffDecl {
            name: EffName::partial(),
            params: vec![],
            ops: vec![],
        };
        assert!(sig.check_effect(&p).is_err());
    }

    /// A parameterized effect (Wave 7/E2) declares a non-empty `params` telescope; well-formedness
    /// (name/op uniqueness) is unaffected by parameterization.
    #[test]
    fn parameterized_effect_declares_and_looks_up() {
        let mut sig = Signature::new();
        // `Ref` with one type parameter `A` (de Bruijn 0 inside `param_ty`/`result_ty`):
        // `get : Unit -> A`, `put : A -> Unit`.
        let a_ty = Term::Univ(Level::Zero); // A : Type 0
        let decl = EffDecl {
            name: EffName("Ref".into()),
            params: vec![a_ty],
            ops: vec![
                OpSig {
                    name: "get".into(),
                    param_ty: unit_ty(),
                    // scope `[A, x:Unit]` (x innermost = index 0), so `A` is index 1.
                    result_ty: Term::Var(1),
                    cont_grade: crate::semiring::Grade::Omega,
                },
                OpSig {
                    name: "put".into(),
                    param_ty: Term::Var(0), // scope `[A]`: A is index 0
                    result_ty: unit_ty(),
                    cont_grade: crate::semiring::Grade::Omega,
                },
            ],
        };
        assert!(sig.check_effect(&decl).is_ok());
        sig.declare_effect(decl);
        let found = sig.get_effect(&EffName("Ref".into())).expect("declared");
        assert_eq!(found.params.len(), 1, "Ref has one type parameter");
        let (e, op) = sig.op_of("get").expect("op get");
        assert_eq!(e.name, EffName("Ref".into()));
        assert_eq!(op.name, "get");
    }

    /// Pins [`mentions_data`]'s exhaustive traversal (soundness audit K4a): it must find the data
    /// type in *every* child position of *every* subterm-bearing former. Each probe places the
    /// data (`hit`) in exactly one position and a non-mentioning term (`no`) in every other, so a
    /// dropped recursion arm, a weakened `||`→`&&`, or a nullified `.any()` fails on at least one
    /// probe. Leaves must never report a mention, and a *different* data name must not match.
    #[test]
    fn mentions_data_recurses_through_every_term_former() {
        use crate::row::{EffName, Row};
        use crate::semiring::Grade;
        use crate::term::{Cofib, IntPrimOp, Interval, Level, SystemBranch};
        use std::rc::Rc;

        let d = DataName("D".into());
        let other = || DataName("Other".into());
        let hit = || Term::Data(d.clone(), vec![], vec![]); // mentions D
        let no = || Term::IntTy; // does not mention D
        let r = |t: Term| Rc::new(t);

        let probes: Vec<(&str, Term)> = vec![
            ("Data head", hit()),
            ("Data param", Term::Data(other(), vec![hit()], vec![])),
            ("Data index", Term::Data(other(), vec![], vec![hit()])),
            ("Pi dom", Term::Pi(Grade::Omega, r(hit()), r(no()))),
            ("Pi cod", Term::Pi(Grade::Omega, r(no()), r(hit()))),
            ("Sigma fst", Term::Sigma(r(hit()), r(no()))),
            ("Sigma snd", Term::Sigma(r(no()), r(hit()))),
            ("App fn", Term::App(r(hit()), r(no()))),
            ("App arg", Term::App(r(no()), r(hit()))),
            ("Ann tm", Term::Ann(r(hit()), r(no()))),
            ("Ann ty", Term::Ann(r(no()), r(hit()))),
            ("Pair fst", Term::Pair(r(hit()), r(no()))),
            ("Pair snd", Term::Pair(r(no()), r(hit()))),
            ("Lam", Term::Lam(r(hit()))),
            ("Fst", Term::Fst(r(hit()))),
            ("Snd", Term::Snd(r(hit()))),
            ("PLam", Term::PLam(r(hit()))),
            ("PApp", Term::PApp(r(hit()), Interval::I0)),
            ("Partial", Term::Partial(Cofib::Top, r(hit()))),
            ("Unglue", Term::Unglue(r(hit()))),
            ("EffTy", Term::EffTy(Row::empty(), r(hit()))),
            ("Delay", Term::Delay(r(hit()))),
            ("Now", Term::Now(r(hit()))),
            ("Later", Term::Later(r(hit()))),
            ("Force", Term::Force(r(hit()))),
            (
                "Foreign ty",
                Term::Foreign {
                    symbol: "s".into(),
                    ty: r(hit()),
                },
            ),
            ("Con arg", Term::Con(ConName("c".into()), vec![hit()])),
            (
                "PCon arg",
                Term::PCon {
                    data: d.clone(),
                    name: ConName("c".into()),
                    args: vec![hit()],
                    dim: Interval::I0,
                },
            ),
            (
                "Elim motive",
                Term::Elim {
                    data: d.clone(),
                    motive: r(hit()),
                    methods: vec![],
                    scrutinee: r(no()),
                },
            ),
            (
                "Elim method",
                Term::Elim {
                    data: d.clone(),
                    motive: r(no()),
                    methods: vec![hit()],
                    scrutinee: r(no()),
                },
            ),
            (
                "Elim scrutinee",
                Term::Elim {
                    data: d.clone(),
                    motive: r(no()),
                    methods: vec![],
                    scrutinee: r(hit()),
                },
            ),
            (
                "PathP family",
                Term::PathP {
                    family: r(hit()),
                    lhs: r(no()),
                    rhs: r(no()),
                },
            ),
            (
                "PathP lhs",
                Term::PathP {
                    family: r(no()),
                    lhs: r(hit()),
                    rhs: r(no()),
                },
            ),
            (
                "PathP rhs",
                Term::PathP {
                    family: r(no()),
                    lhs: r(no()),
                    rhs: r(hit()),
                },
            ),
            (
                "System",
                Term::System(vec![SystemBranch {
                    face: Cofib::Top,
                    term: hit(),
                }]),
            ),
            (
                "Transp family",
                Term::Transp {
                    family: r(hit()),
                    cofib: Cofib::Top,
                    base: r(no()),
                },
            ),
            (
                "Transp base",
                Term::Transp {
                    family: r(no()),
                    cofib: Cofib::Top,
                    base: r(hit()),
                },
            ),
            (
                "HComp ty",
                Term::HComp {
                    ty: r(hit()),
                    cofib: Cofib::Top,
                    tube: r(no()),
                    base: r(no()),
                },
            ),
            (
                "HComp tube",
                Term::HComp {
                    ty: r(no()),
                    cofib: Cofib::Top,
                    tube: r(hit()),
                    base: r(no()),
                },
            ),
            (
                "HComp base",
                Term::HComp {
                    ty: r(no()),
                    cofib: Cofib::Top,
                    tube: r(no()),
                    base: r(hit()),
                },
            ),
            (
                "Comp family",
                Term::Comp {
                    family: r(hit()),
                    cofib: Cofib::Top,
                    tube: r(no()),
                    base: r(no()),
                },
            ),
            (
                "Comp tube",
                Term::Comp {
                    family: r(no()),
                    cofib: Cofib::Top,
                    tube: r(hit()),
                    base: r(no()),
                },
            ),
            (
                "Comp base",
                Term::Comp {
                    family: r(no()),
                    cofib: Cofib::Top,
                    tube: r(no()),
                    base: r(hit()),
                },
            ),
            (
                "Glue base",
                Term::Glue {
                    base: r(hit()),
                    cofib: Cofib::Top,
                    ty: r(no()),
                    equiv: r(no()),
                },
            ),
            (
                "Glue ty",
                Term::Glue {
                    base: r(no()),
                    cofib: Cofib::Top,
                    ty: r(hit()),
                    equiv: r(no()),
                },
            ),
            (
                "Glue equiv",
                Term::Glue {
                    base: r(no()),
                    cofib: Cofib::Top,
                    ty: r(no()),
                    equiv: r(hit()),
                },
            ),
            (
                "GlueTerm partial",
                Term::GlueTerm {
                    cofib: Cofib::Top,
                    partial: r(hit()),
                    base: r(no()),
                },
            ),
            (
                "GlueTerm base",
                Term::GlueTerm {
                    cofib: Cofib::Top,
                    partial: r(no()),
                    base: r(hit()),
                },
            ),
            (
                "Op type_arg",
                Term::Op {
                    effect: EffName("E".into()),
                    op: "o".into(),
                    type_args: vec![hit()],
                    arg: r(no()),
                },
            ),
            (
                "Op arg",
                Term::Op {
                    effect: EffName("E".into()),
                    op: "o".into(),
                    type_args: vec![],
                    arg: r(hit()),
                },
            ),
            (
                "Handle body",
                Term::Handle {
                    body: r(hit()),
                    return_clause: r(no()),
                    op_clauses: vec![],
                },
            ),
            (
                "Handle return",
                Term::Handle {
                    body: r(no()),
                    return_clause: r(hit()),
                    op_clauses: vec![],
                },
            ),
            (
                "Handle clause",
                Term::Handle {
                    body: r(no()),
                    return_clause: r(no()),
                    op_clauses: vec![("o".into(), r(hit()))],
                },
            ),
            (
                "IntPrim lhs",
                Term::IntPrim {
                    op: IntPrimOp::Add,
                    lhs: r(hit()),
                    rhs: r(no()),
                },
            ),
            (
                "IntPrim rhs",
                Term::IntPrim {
                    op: IntPrimOp::Add,
                    lhs: r(no()),
                    rhs: r(hit()),
                },
            ),
        ];
        for (label, t) in &probes {
            assert!(
                mentions_data(t, &d),
                "{label}: the single occurrence of D must be found"
            );
        }

        // Leaves carry no `Term` child, so they mention no data type.
        let leaves = [
            ("Var", Term::Var(0)),
            ("Univ", Term::Univ(Level::Zero)),
            ("Interval", Term::Interval(Interval::I0)),
            ("IntTy", Term::IntTy),
            ("IntLit", Term::IntLit(3)),
            ("Erased", Term::Erased),
        ];
        for (label, t) in &leaves {
            assert!(
                !mentions_data(t, &d),
                "{label}: a leaf mentions no data type"
            );
        }
        // A different data name under a former is not a match (guards the `d == name` check).
        assert!(
            !mentions_data(
                &Term::Delay(Rc::new(Term::Data(other(), vec![], vec![]))),
                &d
            ),
            "a *different* data type is not a mention of D"
        );
    }
}
