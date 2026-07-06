//! E4 (v0.1 roadmap): named-field records — `(defrecord Name ((f1 T1) … (fn Tn)))` — as pure
//! sexpr→sexpr sugar over a **single-constructor `defdata`** (the design re-verified against the
//! codebase on 2026-07-03; see the roadmap's E4 section for why not Sigma: dependent-index
//! refinement, nominal typing, codegen unboxing, linear consumption, and free match/E3/E5
//! integration).
//!
//! One `defrecord` emits, in order:
//! 1. `(defdata Name () (mk-Name (f1 T1) … (fn Tn)))` — the nominal record type;
//! 2. per projectable field, `(deftotal Name-fi (Pi ((r Name)) Ti) (lam (r) (match r
//!    [(mk-Name f1 … fn) fi])))` — a real global, so E2's synthesis reads its result type and
//!    bare `(Name-fi r)` needs no ascription. A field is *projectable* iff its type does not
//!    mention an earlier field name (a dependent later field is accessed via `match`; generating
//!    its projection would need a dependent motive — documented v1 limitation).
//!
//! The functional update `(Name-with r (f v) …)` is not a definition but an expression-position
//! rewrite ([`rewrite_updates`], applied by `Program::run_form` before macro expansion):
//! `(Name-with r (y v))` ⇒ `(mk-Name (Name-x r) v)`. The record expression `r` is duplicated
//! once per kept field — sound in a pure language; the duplication is a documented v1 cost.
//! Unknown fields get a dedicated diagnostic naming the field, never a generic no-rule error.

use crate::elab::ElabError;
use crate::sexpr::Sexpr;

fn bad(msg: impl Into<String>) -> ElabError {
    ElabError::BadForm(msg.into())
}

fn atom(s: &Sexpr) -> Option<&str> {
    match s {
        Sexpr::Atom(a) => Some(a.as_str()),
        Sexpr::List(_) => None,
    }
}

/// A parsed `defrecord`: the record name and its `(field, type)` telescope in declaration order.
pub struct RecordDecl {
    pub name: String,
    pub fields: Vec<(String, Sexpr)>,
}

/// Names this record generates (constructor, projections, the update head) — the hygiene set the
/// dispatcher checks against existing globals/constructors/datatypes before anything is emitted.
impl RecordDecl {
    pub fn ctor_name(&self) -> String {
        format!("mk-{}", self.name)
    }
    pub fn update_head(&self) -> String {
        format!("{}-with", self.name)
    }
    pub fn projection_name(&self, field: &str) -> String {
        format!("{}-{}", self.name, field)
    }
    /// Field names in declaration order.
    pub fn field_names(&self) -> Vec<String> {
        self.fields.iter().map(|(f, _)| f.clone()).collect()
    }
    /// Whether `field` is projectable: its type mentions no earlier field name.
    pub fn projectable(&self, idx: usize) -> bool {
        let earlier: Vec<&str> = self.fields[..idx].iter().map(|(f, _)| f.as_str()).collect();
        !mentions_any(&self.fields[idx].1, &earlier)
    }
}

fn mentions_any(t: &Sexpr, names: &[&str]) -> bool {
    match t {
        Sexpr::Atom(a) => names.contains(&a.as_str()),
        Sexpr::List(xs) => xs.iter().any(|x| mentions_any(x, names)),
    }
}

/// Parse and shape-check `(defrecord Name ((f1 T1) …))`. Exactly three items; a non-empty
/// binder-list of `(name Ty)` pairs; duplicate field names rejected. (A parameterized
/// `(defrecord (Name params…) …)` form is reserved for v2 — the field list is binder-list-shaped
/// and would be ambiguous with a parameter telescope.)
pub fn parse_defrecord(items: &[Sexpr]) -> Result<RecordDecl, ElabError> {
    if items.len() != 3 {
        return Err(bad(
            "defrecord: `(defrecord Name ((field Ty) …))` — exactly a name and a field list",
        ));
    }
    let name = atom(&items[1])
        .ok_or_else(|| bad("defrecord: the record name must be a symbol"))?
        .to_string();
    let Sexpr::List(field_items) = &items[2] else {
        return Err(bad("defrecord: the field list must be `((field Ty) …)`"));
    };
    if field_items.is_empty() {
        return Err(bad("defrecord: at least one `(field Ty)` is required"));
    }
    let mut fields = Vec::new();
    for fi in field_items {
        let Sexpr::List(pair) = fi else {
            return Err(bad(format!(
                "defrecord: each field must be a `(name Ty)` pair, got `{fi:?}`"
            )));
        };
        let [fname, fty] = pair.as_slice() else {
            return Err(bad(format!(
                "defrecord: each field must be a `(name Ty)` pair, got `{fi:?}`"
            )));
        };
        let fname = atom(fname)
            .ok_or_else(|| bad("defrecord: field names must be symbols"))?
            .to_string();
        if fields.iter().any(|(f, _)| *f == fname) {
            return Err(bad(format!(
                "defrecord: duplicate field name `{fname}` in record `{name}`"
            )));
        }
        fields.push((fname, fty.clone()));
    }
    Ok(RecordDecl { name, fields })
}

/// Emit the lowered forms for a parsed record: the single-constructor `defdata` followed by one
/// projection `deftotal` per projectable field.
pub fn emit_forms(decl: &RecordDecl) -> Vec<Sexpr> {
    let a = |s: &str| Sexpr::Atom(s.to_string());
    let mut forms = Vec::new();

    // (defdata Name () (mk-Name (f1 T1) … (fn Tn)))
    let mut ctor = vec![a(&decl.ctor_name())];
    for (f, t) in &decl.fields {
        ctor.push(Sexpr::List(vec![a(f), t.clone()]));
    }
    forms.push(Sexpr::List(vec![
        a("defdata"),
        a(&decl.name),
        Sexpr::List(vec![]),
        Sexpr::List(ctor),
    ]));

    // Projections: (deftotal Name-fi (Pi ((r Name)) Ti) (lam (r) (match r [(mk-Name f1 … fn) fi])))
    // `r` is fixed and cannot collide with field names in a harmful way: the match arm rebinds
    // every field name, and the projection body is exactly one such binder.
    let pat = {
        let mut p = vec![a(&decl.ctor_name())];
        for (f, _) in &decl.fields {
            p.push(a(f));
        }
        Sexpr::List(p)
    };
    for (i, (f, t)) in decl.fields.iter().enumerate() {
        if !decl.projectable(i) {
            continue; // dependent later field: access via match (documented v1 limitation)
        }
        let proj = Sexpr::List(vec![
            a("deftotal"),
            a(&decl.projection_name(f)),
            Sexpr::List(vec![
                a("Pi"),
                Sexpr::List(vec![Sexpr::List(vec![a("r"), a(&decl.name)])]),
                t.clone(),
            ]),
            Sexpr::List(vec![
                a("lam"),
                Sexpr::List(vec![a("r")]),
                Sexpr::List(vec![
                    a("match"),
                    a("r"),
                    Sexpr::List(vec![pat.clone(), a(f)]),
                ]),
            ]),
        ]);
        forms.push(proj);
    }
    forms
}

/// The registry the `Program` driver keeps (alongside its macro table, same lifetime and
/// snapshot discipline): record name → field names in declaration order, plus which are
/// projectable (needed to rebuild in `-with`).
#[derive(Clone, Default)]
pub struct RecordEnv {
    records: std::collections::HashMap<String, RecordInfo>,
}

#[derive(Clone)]
pub struct RecordInfo {
    pub fields: Vec<String>,
    pub projectable: Vec<bool>,
}

impl RecordEnv {
    pub fn register(&mut self, decl: &RecordDecl) {
        let projectable = (0..decl.fields.len())
            .map(|i| decl.projectable(i))
            .collect();
        self.records.insert(
            decl.name.clone(),
            RecordInfo {
                fields: decl.field_names(),
                projectable,
            },
        );
    }
    pub fn get(&self, name: &str) -> Option<&RecordInfo> {
        self.records.get(name)
    }
}

/// Rewrite every `(Name-with r (field v) …)` in `form` (any expression position, innermost
/// first) into the rebuilt constructor application `(mk-Name arg1 … argn)`, where the argument
/// for an updated field is its new value and every other argument is the projection
/// `(Name-field r)`. Errors name the offending field — the dedicated diagnostics the milestone
/// requires.
pub fn rewrite_updates(form: &Sexpr, records: &RecordEnv) -> Result<Sexpr, ElabError> {
    match form {
        Sexpr::Atom(_) => Ok(form.clone()),
        Sexpr::List(xs) => {
            // Rewrite children first (innermost updates, and the record expression itself).
            let xs: Vec<Sexpr> = xs
                .iter()
                .map(|x| rewrite_updates(x, records))
                .collect::<Result<_, _>>()?;
            let Some(head) = xs.first().and_then(atom) else {
                return Ok(Sexpr::List(xs));
            };
            let Some(rec_name) = head.strip_suffix("-with") else {
                return Ok(Sexpr::List(xs));
            };
            let Some(info) = records.get(rec_name) else {
                return Ok(Sexpr::List(xs)); // not a registered record; leave the form alone
            };
            if xs.len() < 3 {
                return Err(bad(format!(
                    "{head}: `({head} record (field value) …)` needs a record and at least one \
                     field update"
                )));
            }
            let rec_expr = xs[1].clone();
            // Collect the updates, validating field names as we go.
            let mut updates: Vec<(usize, Sexpr)> = Vec::new();
            for u in &xs[2..] {
                let Sexpr::List(pair) = u else {
                    return Err(bad(format!(
                        "{head}: each update must be a `(field value)` pair, got `{u:?}`"
                    )));
                };
                let [f, v] = pair.as_slice() else {
                    return Err(bad(format!(
                        "{head}: each update must be a `(field value)` pair, got `{u:?}`"
                    )));
                };
                let fname = atom(f).ok_or_else(|| {
                    bad(format!(
                        "{head}: update field names must be symbols, got `{f:?}`"
                    ))
                })?;
                let Some(idx) = info.fields.iter().position(|x| x == fname) else {
                    return Err(bad(format!(
                        "{head}: unknown field `{fname}` — record `{rec_name}` has fields ({})",
                        info.fields.join(" ")
                    )));
                };
                if updates.iter().any(|(i, _)| *i == idx) {
                    return Err(bad(format!(
                        "{head}: field `{fname}` updated twice in one `{head}`"
                    )));
                }
                updates.push((idx, v.clone()));
            }
            // Rebuild: updated fields take their new value; kept fields project from `rec_expr`.
            let mut app = vec![Sexpr::Atom(format!("mk-{rec_name}"))];
            for (i, f) in info.fields.iter().enumerate() {
                if let Some((_, v)) = updates.iter().find(|(j, _)| *j == i) {
                    app.push(v.clone());
                } else {
                    if !info.projectable[i] {
                        return Err(bad(format!(
                            "{head}: field `{f}` has a dependent type and no projection — \
                             rebuild this record with `match` instead"
                        )));
                    }
                    app.push(Sexpr::List(vec![
                        Sexpr::Atom(format!("{rec_name}-{f}")),
                        rec_expr.clone(),
                    ]));
                }
            }
            Ok(Sexpr::List(app))
        }
    }
}
