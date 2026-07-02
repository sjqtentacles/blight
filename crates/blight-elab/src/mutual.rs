//! `mutual.rs` — surface desugaring of mutual recursion (UNTRUSTED tower, zero kernel growth).
//!
//! A `(mutual M1 M2 …)` binding group is lowered, entirely at the s-expression level, into three
//! ordinary forms the existing elaborator already understands:
//!
//!   1. a generated tag datatype `(defdata MtlTag_<f1> () (mtl_tag_<f1>_0) …)` — one nullary
//!      constructor per group member;
//!   2. ONE merged recursive function `mtl_merged_<f1>` that matches the shared structural scrutinee
//!      (the members' common first parameter) and, in each constructor arm, dispatches on the tag to
//!      the corresponding member's arm body — with every cross/self call `(fj e0 e…)` rewritten to
//!      `(mtl_merged_<f1> e0 <tag_fj> e…)`;
//!   3. one projection `(define fi TYi (lam (params) (mtl_merged_<f1> p0 <tag_fi> p…)))` per member.
//!
//! The merged function then flows through the *unchanged* `elaborate_rec`: if every cross/self call
//! lands on the structural predecessor of the shared scrutinee it compiles to a single kernel `Elim`
//! (total, kernel-certified, re-checked `Ok`); otherwise (a `Delay`/effectful conclusion) it takes
//! the existing partial `Lam`+`Later` path. No kernel primitive is added.
//!
//! Supported shape (v1): every member is
//!     (deftotal|define-rec  NAME  (Pi (BINDERS) R)  (lam (P0 P… ) (match P0 ARMS)))
//! all members share an identical parameter list and an identical `(Pi (BINDERS) R)` type, recurse on
//! their common first parameter `P0`, and match it against the same set of constructor patterns.
//! Cross-calls must be *saturated* applications headed by a member name. Heterogeneous groups should
//! be uniformised first (see the plan); unsupported shapes produce a clear error.

use crate::elab::ElabError;
use crate::sexpr::Sexpr;
use std::collections::HashMap;

fn atom(s: impl Into<String>) -> Sexpr {
    Sexpr::Atom(s.into())
}
fn list(items: Vec<Sexpr>) -> Sexpr {
    Sexpr::List(items)
}

fn bad(msg: impl Into<String>) -> ElabError {
    ElabError::BadForm(msg.into())
}

/// Map every non-alphanumeric character of a member name to `_` so it is safe to splice into a
/// generated type/constructor identifier (member names may contain `?`, `-`, …).
fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| if c.is_alphanumeric() { c } else { '_' })
        .collect()
}

/// One `match` arm: `(constructor name, field binder names, arm body)`, in source order.
type MatchArm = (String, Vec<String>, Sexpr);

/// One parsed group member.
struct Member {
    kw: String,
    name: String,
    ty: Sexpr,
    params: Vec<String>,
    scrut: String,
    /// constructor name -> (field binder names, arm body) in source order.
    arms: Vec<MatchArm>,
}

fn as_atom(s: &Sexpr) -> Option<&str> {
    match s {
        Sexpr::Atom(a) => Some(a.as_str()),
        _ => None,
    }
}

/// Parse `(lam (P…) (match P0 ARMS))` into (params, scrut, arms).
fn parse_member_body(body: &Sexpr) -> Result<(Vec<String>, String, Vec<MatchArm>), ElabError> {
    let items = match body {
        Sexpr::List(items) => items,
        _ => {
            return Err(bad(
                "mutual member body must be (lam (params) (match p0 arms))",
            ))
        }
    };
    if items.len() != 3 || as_atom(&items[0]) != Some("lam") {
        return Err(bad(
            "mutual member body must be (lam (params) (match p0 arms))",
        ));
    }
    let params: Vec<String> = match &items[1] {
        Sexpr::List(ps) => ps
            .iter()
            .map(|p| {
                as_atom(p)
                    .map(str::to_string)
                    .ok_or_else(|| bad("mutual member params must be plain names"))
            })
            .collect::<Result<_, _>>()?,
        _ => return Err(bad("mutual member params must be a list of names")),
    };
    if params.is_empty() {
        return Err(bad(
            "mutual member must take at least the recursion parameter",
        ));
    }
    let m = match &items[2] {
        Sexpr::List(m) => m,
        _ => return Err(bad("mutual member body must end in (match p0 arms)")),
    };
    if m.is_empty() || as_atom(&m[0]) != Some("match") {
        return Err(bad(
            "mutual member body must be (lam (params) (match p0 arms)) — only this shape is supported in v1",
        ));
    }
    let scrut = as_atom(&m[1])
        .ok_or_else(|| bad("mutual member must match on a parameter"))?
        .to_string();
    if scrut != params[0] {
        return Err(bad(format!(
            "mutual member must recurse on its FIRST parameter `{}` (matched `{scrut}`)",
            params[0]
        )));
    }
    let mut arms = Vec::new();
    for arm in &m[2..] {
        let pair = match arm {
            Sexpr::List(p) if p.len() == 2 => p,
            _ => return Err(bad("each mutual member arm must be [pattern body]")),
        };
        let pat = match &pair[0] {
            Sexpr::List(p) if !p.is_empty() => p,
            _ => return Err(bad("mutual member arm pattern must be (Con fields…)")),
        };
        let con = as_atom(&pat[0])
            .ok_or_else(|| bad("constructor pattern must start with a constructor name"))?
            .to_string();
        let fields: Vec<String> = pat[1..]
            .iter()
            .map(|f| {
                as_atom(f)
                    .map(str::to_string)
                    .ok_or_else(|| bad("constructor pattern fields must be plain names"))
            })
            .collect::<Result<_, _>>()?;
        arms.push((con, fields, pair[1].clone()));
    }
    Ok((params, scrut, arms))
}

fn parse_member(form: &Sexpr) -> Result<Member, ElabError> {
    let items = match form {
        Sexpr::List(items) => items,
        _ => {
            return Err(bad(
                "a mutual member must be a (deftotal|define-rec …) form",
            ))
        }
    };
    if items.len() != 4 {
        return Err(bad(
            "a mutual member must be (deftotal|define-rec name (Pi (binders) R) body)",
        ));
    }
    let kw = as_atom(&items[0])
        .filter(|k| *k == "deftotal" || *k == "define-rec")
        .ok_or_else(|| bad("a mutual member must be a `deftotal` or `define-rec` form"))?
        .to_string();
    let name = as_atom(&items[1])
        .ok_or_else(|| bad("mutual member needs a name"))?
        .to_string();
    let ty = items[2].clone();
    let (params, scrut, arms) = parse_member_body(&items[3])?;
    Ok(Member {
        kw,
        name,
        ty,
        params,
        scrut,
        arms,
    })
}

/// Split `(Pi (BINDERS) R)` into its binder list and the return type.
fn split_pi(ty: &Sexpr) -> Result<(Vec<Sexpr>, Sexpr), ElabError> {
    let items = match ty {
        Sexpr::List(items) => items,
        _ => return Err(bad("mutual member type must be (Pi (binders) R)")),
    };
    if items.len() != 3 || as_atom(&items[0]) != Some("Pi") {
        return Err(bad(
            "mutual member type must be a single (Pi (binders) R) form in v1",
        ));
    }
    let binders = match &items[1] {
        Sexpr::List(b) => b.clone(),
        _ => return Err(bad("mutual member type binders must be a list")),
    };
    if binders.is_empty() {
        return Err(bad("mutual member type needs at least one binder"));
    }
    Ok((binders, items[2].clone()))
}

/// Replace every atom occurring as a key of `map` with its value (naive; v1 assumes member arm
/// bodies do not shadow their own field/param names).
fn subst_atoms(s: &Sexpr, map: &HashMap<String, String>) -> Sexpr {
    match s {
        Sexpr::Atom(a) => match map.get(a) {
            Some(r) => atom(r.clone()),
            None => atom(a.clone()),
        },
        Sexpr::List(items) => list(items.iter().map(|i| subst_atoms(i, map)).collect()),
    }
}

/// Rewrite saturated cross/self calls `(fj e0 e…)` to `(merged e0 <tag_fj> e…)`. A *bare* reference
/// to a member name (used as a value, not the head of an application) is unsupported in v1.
fn rewrite_calls(
    s: &Sexpr,
    tag_of: &HashMap<String, String>,
    merged: &str,
) -> Result<Sexpr, ElabError> {
    match s {
        Sexpr::Atom(a) => {
            if tag_of.contains_key(a) {
                return Err(bad(format!(
                    "mutual member `{a}` used as a bare value; only saturated calls `({a} arg …)` are supported in v1"
                )));
            }
            Ok(atom(a.clone()))
        }
        Sexpr::List(items) => {
            if let Some(h) = items.first().and_then(as_atom) {
                if let Some(tag) = tag_of.get(h) {
                    if items.len() < 2 {
                        return Err(bad(format!(
                            "call to mutual member `{h}` needs its recursion argument"
                        )));
                    }
                    let mut out = vec![
                        atom(merged.to_string()),
                        rewrite_calls(&items[1], tag_of, merged)?,
                        atom(tag.clone()),
                    ];
                    for a in &items[2..] {
                        out.push(rewrite_calls(a, tag_of, merged)?);
                    }
                    return Ok(list(out));
                }
            }
            Ok(list(
                items
                    .iter()
                    .map(|i| rewrite_calls(i, tag_of, merged))
                    .collect::<Result<_, _>>()?,
            ))
        }
    }
}

/// Desugar a `(mutual M1 M2 …)` group into ordinary forms. Also used (via [`desugar_block`]) for the
/// `(define-recs …)` / `(deftotals …)` shorthands.
pub fn desugar_mutual(items: &[Sexpr]) -> Result<Vec<Sexpr>, ElabError> {
    // items[0] == "mutual"; the rest are member forms.
    let members: Vec<Member> = items[1..]
        .iter()
        .map(parse_member)
        .collect::<Result<_, _>>()?;
    if members.is_empty() {
        return Err(bad("(mutual …) needs at least one member"));
    }
    // A single member is just that definition.
    if members.len() == 1 {
        return Ok(vec![items[1].clone()]);
    }

    // Uniformity checks: identical parameter list and identical type across members.
    let params = members[0].params.clone();
    let ty = members[0].ty.clone();
    let scrut = members[0].scrut.clone();
    for m in &members[1..] {
        if m.params != params {
            return Err(bad(
                "all mutual members must share an identical parameter list (uniformise the group first)",
            ));
        }
        if m.ty != ty {
            return Err(bad(
                "all mutual members must share an identical type (uniformise the group first)",
            ));
        }
    }

    // Canonical constructor list (name, arity, canonical field names) from the first member.
    let canon_cons: Vec<(String, Vec<String>)> = members[0]
        .arms
        .iter()
        .map(|(c, fields, _)| (c.clone(), fields.clone()))
        .collect();

    // Generated names (group-unique via the sanitized first member name).
    let s1 = sanitize(&members[0].name);
    let tag_ty = format!("MtlTag_{s1}");
    let merged = format!("mtl_merged_{s1}");
    let tag_of: HashMap<String, String> = members
        .iter()
        .enumerate()
        .map(|(i, m)| (m.name.clone(), format!("mtl_tag_{s1}_{i}")))
        .collect();

    // The merged keyword: total only if every member is total.
    let merged_kw = if members.iter().all(|m| m.kw == "deftotal") {
        "deftotal"
    } else {
        "define-rec"
    };
    // For each member, index its arms by constructor for quick lookup, validating the set matches.
    let mut per_member: Vec<HashMap<String, (Vec<String>, Sexpr)>> = Vec::new();
    for m in &members {
        let mut map = HashMap::new();
        for (c, fields, body) in &m.arms {
            map.insert(c.clone(), (fields.clone(), body.clone()));
        }
        if map.len() != canon_cons.len() || canon_cons.iter().any(|(c, _)| !map.contains_key(c)) {
            return Err(bad(
                "all mutual members must match the same set of constructors",
            ));
        }
        per_member.push(map);
    }

    // Build the merged body: (lam (scrut) (match scrut <outer arms>)).
    let mut outer_arms: Vec<Sexpr> = Vec::new();
    for (con, canon_fields) in &canon_cons {
        // Inner: (lam (tag p1 … pk) (match tag [tag_i arm_i'] …)).
        let mut inner_tag_arms: Vec<Sexpr> = Vec::new();
        for (i, m) in members.iter().enumerate() {
            let (fields_i, body_i) = &per_member[i][con];
            if fields_i.len() != canon_fields.len() {
                return Err(bad(format!(
                    "member `{}` arm for `{con}` has a different arity",
                    m.name
                )));
            }
            // Rename this member's field binders to the canonical ones, then rewrite cross-calls.
            let mut fmap: HashMap<String, String> = HashMap::new();
            for (from, to) in fields_i.iter().zip(canon_fields.iter()) {
                if from != to {
                    fmap.insert(from.clone(), to.clone());
                }
            }
            let renamed = subst_atoms(body_i, &fmap);
            let rewritten = rewrite_calls(&renamed, &tag_of, &merged)?;
            inner_tag_arms.push(list(vec![
                list(vec![atom(tag_of[&m.name].clone())]),
                rewritten,
            ]));
        }
        let mut inner_match = vec![atom("match"), atom("mtl_tag")];
        inner_match.extend(inner_tag_arms);
        // Inner lambda binds the tag then the non-scrutinee parameters (kept by name).
        let mut inner_lam_params = vec![atom("mtl_tag")];
        for p in &params[1..] {
            inner_lam_params.push(atom(p.clone()));
        }
        let inner = list(vec![atom("lam"), list(inner_lam_params), list(inner_match)]);
        // Outer arm: [(Con canon_fields…) inner].
        let mut pat = vec![atom(con.clone())];
        for f in canon_fields {
            pat.push(atom(f.clone()));
        }
        outer_arms.push(list(vec![list(pat), inner]));
    }
    let mut outer_match = vec![atom("match"), atom(scrut.clone())];
    outer_match.extend(outer_arms);
    let merged_body = list(vec![
        atom("lam"),
        list(vec![atom(scrut.clone())]),
        list(outer_match),
    ]);

    // The merged type: insert the tag binder right after the scrutinee binder.
    let (binders, ret) = split_pi(&ty)?;
    let mut merged_binders = vec![
        binders[0].clone(),
        list(vec![atom("mtl_tag"), atom(tag_ty.clone())]),
    ];
    merged_binders.extend(binders[1..].iter().cloned());
    let merged_ty = list(vec![atom("Pi"), list(merged_binders), ret]);

    // Assemble the output forms.
    let mut out: Vec<Sexpr> = Vec::new();

    // 1. (defdata MtlTag_<s1> () (mtl_tag_<s1>_0) …)
    let mut tag_decl = vec![atom("defdata"), atom(tag_ty.clone()), list(vec![])];
    for i in 0..members.len() {
        tag_decl.push(list(vec![atom(format!("mtl_tag_{s1}_{i}"))]));
    }
    out.push(list(tag_decl));

    // 2. (deftotal|define-rec mtl_merged_<s1> merged_ty merged_body)
    out.push(list(vec![
        atom(merged_kw),
        atom(merged.clone()),
        merged_ty,
        merged_body,
    ]));

    // 3. projections: (define fi TYi (lam (params) (merged p0 tag_fi p1 …)))
    for m in &members {
        let mut call = vec![
            atom(merged.clone()),
            atom(params[0].clone()),
            atom(tag_of[&m.name].clone()),
        ];
        for p in &params[1..] {
            call.push(atom(p.clone()));
        }
        let lam = list(vec![
            atom("lam"),
            list(params.iter().map(|p| atom(p.clone())).collect()),
            list(call),
        ]);
        out.push(list(vec![
            atom("define"),
            atom(m.name.clone()),
            m.ty.clone(),
            lam,
        ]));
    }

    Ok(out)
}

/// `(define-recs ((name ty body) …))` / `(deftotals ((name ty body) …))` — a shorthand whose members
/// are bare `(name ty body)` triples; expand to a `(mutual (kw name ty body) …)` then desugar.
pub fn desugar_block(kw: &str, items: &[Sexpr]) -> Result<Vec<Sexpr>, ElabError> {
    if items.len() != 2 {
        return Err(bad(format!("({kw} ((name ty body) …))")));
    }
    let triples = match &items[1] {
        Sexpr::List(t) => t,
        _ => {
            return Err(bad(format!(
                "({kw} ((name ty body) …)): expected a list of members"
            )))
        }
    };
    let member_kw = if kw == "deftotals" {
        "deftotal"
    } else {
        "define-rec"
    };
    let mut mutual = vec![atom("mutual")];
    for t in triples {
        let parts = match t {
            Sexpr::List(p) if p.len() == 3 => p,
            _ => return Err(bad(format!("({kw} …): each member must be (name ty body)"))),
        };
        mutual.push(list(vec![
            atom(member_kw),
            parts[0].clone(),
            parts[1].clone(),
            parts[2].clone(),
        ]));
    }
    desugar_mutual(&mutual[..])
}
