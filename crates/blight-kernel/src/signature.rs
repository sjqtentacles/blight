//! Inductive signatures (spec §2.7): the declared shape of (higher) inductive types — their
//! parameters, the constructors, each constructor's argument telescope (marking recursive
//! occurrences), and any path constructors (for HITs). The kernel consults the signature when
//! typing `Data`/`Con`/`Elim` and when computing ι reductions.
//!
//! For M0 we support parameterized, non-indexed inductives (enough for `Nat`, `List`, and a
//! HIT with point + path constructors). Full indexed families are an M1 refinement.

use crate::term::{ConName, DataName, Term};
use std::collections::HashMap;

/// One argument of a constructor. We distinguish *recursive* arguments (whose type is the data
/// type being defined) because the eliminator must supply an induction hypothesis for them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Arg {
    /// A non-recursive argument with the given type (which may mention earlier args/params).
    NonRec(Term),
    /// A recursive argument: a value of the inductive type itself (strictly positive).
    Rec,
}

/// A point constructor: a name and its argument telescope.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: ConName,
    pub args: Vec<Arg>,
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
    /// Parameter telescope (each a type; later params may mention earlier ones).
    pub params: Vec<Term>,
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
}

/// The global signature: all declared inductive types, keyed by name.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Signature {
    datas: HashMap<DataName, DataDecl>,
}

impl Signature {
    pub fn new() -> Self {
        Signature {
            datas: HashMap::new(),
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

/// Whether a term mentions a given data type by name (a conservative negative-occurrence check
/// for M0: any non-`Rec` mention is rejected as potentially non-positive).
fn mentions_data(term: &Term, name: &DataName) -> bool {
    match term {
        Term::Data(d, params, indices) => {
            d == name
                || params.iter().any(|t| mentions_data(t, name))
                || indices.iter().any(|t| mentions_data(t, name))
        }
        Term::Pi(_, a, b) | Term::Sigma(a, b) | Term::App(a, b) => {
            mentions_data(a, name) || mentions_data(b, name)
        }
        Term::Lam(b) | Term::Fst(b) | Term::Snd(b) => mentions_data(b, name),
        Term::Ann(t, ty) => mentions_data(t, name) || mentions_data(ty, name),
        _ => false,
    }
}
