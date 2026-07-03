//! Lexical scope analysis over the *spanned* s-expression tree (Wave 9 / T1: LSP v2). UNTRUSTED
//! tooling; purely advisory (diagnostics/rename quality), never consulted by the trusted kernel.
//!
//! `Surface`/`ElabError`/kernel `TypeError` carry no spans (see `crates/blight-lsp/src/main.rs`'s
//! module doc for the ledger of why a full span-threading refactor is out of scope here). Rather
//! than thread spans through the ~6k-line elaborator, this module re-derives just enough lexical
//! structure by walking the pre-elaboration [`SpannedSexpr`] tree directly, mirroring the surface
//! grammar's binder-introducing forms one-for-one with `elab.rs`'s `parse_list`/`parse_binders`/
//! `parse_pattern`/`parse_clause_*` (kept in sync by hand; a form new to one is meant to be added
//! to the other — see the exhaustive keyword match below).
//!
//! This gives two things without any elaborator change:
//! - [`narrow_span`]: given a top-level form and the [`ElabError`] it produced, look for a
//!   tighter sub-expression span to underline (currently: the first free — i.e. genuinely
//!   unbound, accounting for local shadowing — occurrence of an unbound name).
//! - [`rename_local_binder`]: given the cursor position on a local binder's *declaration*, collect
//!   every occurrence (its own declaration plus every unshadowed use in its scope) so an editor
//!   can rename them all atomically, refusing (rather than silently mis-renaming) if the new name
//!   would be captured by an intervening binder.
//!
//! Known limitations (documented, not silently dropped): binder *grade* annotations (the optional
//! third element of a `(x A ρ)` binder) are not scanned, since grades are almost always the
//! constants `zero`/`one`/`omega` rather than variable references; macro-introduced (hygiene
//! mark, `name%N`) unbound references cannot be found in pre-expansion source text, so `narrow_span`
//! degrades gracefully to the whole-form span for those. Lambda-bound variables are covered (unlike
//! the LSP hover MVP, which only supports globals); `defdata`/`effect` field telescopes are a
//! separate (already-indexed) global namespace, not lexical scope, and are out of scope here.

use crate::elab::ElabError;
use crate::sexpr::{Span, Spanned, SpannedSexpr};

/// Head keywords that introduce **no** new binding but whose own head atom (`"the"`, `"Path"`,
/// ...) must not itself be mistaken for a variable reference or rename/unbound target. Every
/// other element is an ordinary sub-expression, walked generically. Kept in 1:1 correspondence
/// with `elab.rs::parse_list`'s keyword arms, minus the binder-introducing forms (handled
/// specially in [`walk_uses`]/[`find_binder_at`]) and the pure-application fallback.
const NON_BINDING_KEYWORDS: &[&str] = &[
    "the", "Path", "Type", "Delay", "now", "later", "force", "Partial", "system", "Glue", "glue",
    "unglue", "transp", "hcomp", "comp", "int", "int+", "int-", "int*", "int/", "int=", "int<",
    "perform", "!", "pair", "fst", "snd", "ieq0", "ieq1", "cand", "cor",
];

/// Bare atoms that are never a variable reference even outside a recognized list form (cofibration
/// constants and the match wildcard).
fn is_reserved_atom(a: &str) -> bool {
    matches!(a, "ctop" | "cbot" | "_")
}

fn atom_text(s: &Spanned<SpannedSexpr>) -> Option<&str> {
    match &s.node {
        SpannedSexpr::Atom(a) => Some(a.as_str()),
        _ => None,
    }
}

fn contains(offset: usize, span: Span) -> bool {
    offset >= span.start && offset < span.end
}

/// Parse `(x y z)` as a flat list of binder names (mirrors `elab.rs::parse_name_list`, used by
/// `lam`/`plam`), tolerating malformed input by simply yielding fewer/no names.
fn flat_name_list(s: &Spanned<SpannedSexpr>) -> Vec<String> {
    match &s.node {
        SpannedSexpr::List(items) => items
            .iter()
            .filter_map(atom_text)
            .map(String::from)
            .collect(),
        _ => Vec::new(),
    }
}

/// The `(x A)` / `(x A ρ)` / `{x A}` / `{x A ρ}` / `(x A implicit)` binder parts, stripped of the
/// `brace`/`implicit` markers (mirrors `elab.rs::parse_one_binder`).
fn binder_core(b: &Spanned<SpannedSexpr>) -> Option<&[Spanned<SpannedSexpr>]> {
    let parts = match &b.node {
        SpannedSexpr::List(parts) if !parts.is_empty() => parts,
        _ => return None,
    };
    if atom_text(&parts[0]) == Some("brace") {
        return Some(&parts[1..]);
    }
    if parts.len() > 1 && atom_text(&parts[parts.len() - 1]) == Some("implicit") {
        return Some(&parts[..parts.len() - 1]);
    }
    Some(&parts[..])
}

fn binder_name_span(b: &Spanned<SpannedSexpr>) -> Option<(String, Span)> {
    let core = binder_core(b)?;
    let name_node = core.first()?;
    let name = atom_text(name_node)?;
    Some((name.to_string(), name_node.span))
}

fn binder_type_subtree(b: &Spanned<SpannedSexpr>) -> Option<&Spanned<SpannedSexpr>> {
    binder_core(b)?.get(1)
}

/// Every variable bound by a single-scrutinee pattern (`_`, a bare var, or `(Con p...)`
/// recursively), mirroring `elab.rs::parse_pattern`. The head of a list pattern is the constructor
/// name, never itself a bound variable.
fn pattern_vars_single(pat: &Spanned<SpannedSexpr>) -> Vec<(String, Span)> {
    match &pat.node {
        SpannedSexpr::Atom(a) if a == "_" => Vec::new(),
        SpannedSexpr::Atom(a) => vec![(a.clone(), pat.span)],
        SpannedSexpr::List(items) if !items.is_empty() => {
            items[1..].iter().flat_map(pattern_vars_single).collect()
        }
        SpannedSexpr::List(_) => Vec::new(),
    }
}

/// Every variable bound by a multi-scrutinee pattern tuple `(p1 p2 ...)` (`matchx`'s clause
/// pattern position), mirroring `elab.rs::parse_clause_multi`: unlike a single pattern, the tuple
/// itself has no constructor head — each element is independently a full pattern.
fn pattern_vars_tuple(tuple: &Spanned<SpannedSexpr>) -> Vec<(String, Span)> {
    match &tuple.node {
        SpannedSexpr::List(items) => items.iter().flat_map(pattern_vars_single).collect(),
        _ => Vec::new(),
    }
}

/// Walk every *use-position* atom under `node` — skipping syntax keywords and binder-declaration
/// name tokens themselves — calling `f(text, span, bound)` for each, where `bound` is the stack of
/// lexically-in-scope local names at that point (innermost last; grows/shrinks exactly as
/// elaboration's scope would). Each entry also carries, when the binding is a `let` (the only
/// local-binder kind whose type is cheaply recoverable — see [`resolve_let_rhs_at`]), the span of
/// its right-hand-side expression; every other binder kind (`lam`/`Pi`/`Sigma`/`plam`/pattern/
/// `handle`/`region`) carries `None`. `f` returns `Some(t)` to stop the whole walk early
/// (propagated out), or `None` to keep going.
fn walk_uses<T>(
    node: &Spanned<SpannedSexpr>,
    bound: &mut Vec<(String, Option<Span>)>,
    f: &mut impl FnMut(&str, Span, &[(String, Option<Span>)]) -> Option<T>,
) -> Option<T> {
    match &node.node {
        SpannedSexpr::Atom(a) => {
            if is_reserved_atom(a) {
                None
            } else {
                f(a, node.span, bound)
            }
        }
        SpannedSexpr::List(items) => {
            if items.is_empty() {
                return None;
            }
            let head = atom_text(&items[0]);
            match head {
                Some("lam") if items.len() == 3 => {
                    let names = flat_name_list(&items[1]);
                    let pushed = names.len();
                    bound.extend(names.into_iter().map(|n| (n, None)));
                    let r = walk_uses(&items[2], bound, f);
                    bound.truncate(bound.len() - pushed);
                    return r;
                }
                Some("plam") if items.len() == 3 => {
                    let names = flat_name_list(&items[1]);
                    let pushed = names
                        .into_iter()
                        .take(1)
                        .map(|n| bound.push((n, None)))
                        .count();
                    let r = walk_uses(&items[2], bound, f);
                    bound.truncate(bound.len() - pushed);
                    return r;
                }
                Some("let") if items.len() == 3 => {
                    if let SpannedSexpr::List(bindings) = &items[1].node {
                        if let Some(Spanned {
                            node: SpannedSexpr::List(pair),
                            ..
                        }) = bindings.first()
                        {
                            if pair.len() == 2 {
                                if let Some(t) = walk_uses(&pair[1], bound, f) {
                                    return Some(t);
                                }
                                if let Some(x) = atom_text(&pair[0]) {
                                    bound.push((x.to_string(), Some(pair[1].span)));
                                    let r = walk_uses(&items[2], bound, f);
                                    bound.pop();
                                    return r;
                                }
                            }
                        }
                    }
                }
                Some("Pi") | Some("Sigma") if items.len() == 3 => {
                    if let SpannedSexpr::List(binders) = &items[1].node {
                        let mut pushed = 0usize;
                        for b in binders {
                            if let Some(ty) = binder_type_subtree(b) {
                                if let Some(t) = walk_uses(ty, bound, f) {
                                    bound.truncate(bound.len() - pushed);
                                    return Some(t);
                                }
                            }
                            if let Some((name, _)) = binder_name_span(b) {
                                bound.push((name, None));
                                pushed += 1;
                            }
                        }
                        let r = walk_uses(&items[2], bound, f);
                        bound.truncate(bound.len() - pushed);
                        return r;
                    }
                }
                Some("match") if items.len() >= 2 => {
                    if let Some(t) = walk_uses(&items[1], bound, f) {
                        return Some(t);
                    }
                    for clause in &items[2..] {
                        if let SpannedSexpr::List(cparts) = &clause.node {
                            if cparts.len() == 2 {
                                let names: Vec<String> = pattern_vars_single(&cparts[0])
                                    .into_iter()
                                    .map(|(n, _)| n)
                                    .collect();
                                let pushed = names.len();
                                bound.extend(names.into_iter().map(|n| (n, None)));
                                let r = walk_uses(&cparts[1], bound, f);
                                bound.truncate(bound.len() - pushed);
                                if let Some(t) = r {
                                    return Some(t);
                                }
                            }
                        }
                    }
                    return None;
                }
                Some("matchx") if items.len() >= 2 => {
                    if let Some(t) = walk_uses(&items[1], bound, f) {
                        return Some(t);
                    }
                    for clause in &items[2..] {
                        if let SpannedSexpr::List(cparts) = &clause.node {
                            if cparts.len() == 2 {
                                let names: Vec<String> = pattern_vars_tuple(&cparts[0])
                                    .into_iter()
                                    .map(|(n, _)| n)
                                    .collect();
                                let pushed = names.len();
                                bound.extend(names.into_iter().map(|n| (n, None)));
                                let r = walk_uses(&cparts[1], bound, f);
                                bound.truncate(bound.len() - pushed);
                                if let Some(t) = r {
                                    return Some(t);
                                }
                            }
                        }
                    }
                    return None;
                }
                Some("handle") if items.len() >= 3 => {
                    if let Some(t) = walk_uses(&items[1], bound, f) {
                        return Some(t);
                    }
                    for clause in &items[2..] {
                        if let SpannedSexpr::List(parts) = &clause.node {
                            let h = parts.first().and_then(atom_text);
                            if h == Some("return") && parts.len() == 3 {
                                if let Some(x) = atom_text(&parts[1]) {
                                    bound.push((x.to_string(), None));
                                    let r = walk_uses(&parts[2], bound, f);
                                    bound.pop();
                                    if let Some(t) = r {
                                        return Some(t);
                                    }
                                }
                            } else if parts.len() == 4 {
                                if let (Some(x), Some(k)) =
                                    (atom_text(&parts[1]), atom_text(&parts[2]))
                                {
                                    bound.push((x.to_string(), None));
                                    bound.push((k.to_string(), None));
                                    let r = walk_uses(&parts[3], bound, f);
                                    bound.pop();
                                    bound.pop();
                                    if let Some(t) = r {
                                        return Some(t);
                                    }
                                }
                            }
                        }
                    }
                    return None;
                }
                Some("region") if items.len() == 3 => {
                    if let Some(r) = atom_text(&items[1]) {
                        bound.push((r.to_string(), None));
                        let res = walk_uses(&items[2], bound, f);
                        bound.pop();
                        return res;
                    }
                }
                Some(kw) if NON_BINDING_KEYWORDS.contains(&kw) => {
                    for it in &items[1..] {
                        if let Some(t) = walk_uses(it, bound, f) {
                            return Some(t);
                        }
                    }
                    return None;
                }
                _ => {
                    for it in items {
                        if let Some(t) = walk_uses(it, bound, f) {
                            return Some(t);
                        }
                    }
                    return None;
                }
            }
            None
        }
    }
}

/// The byte span of the first genuinely-free (not locally shadowed) occurrence of `name` in
/// `form`, if any. Used to narrow an [`ElabError::Unbound`] diagnostic from the whole top-level
/// form down to the specific offending sub-expression.
pub fn find_unbound_span(form: &Spanned<SpannedSexpr>, name: &str) -> Option<Span> {
    let mut bound = Vec::new();
    walk_uses(form, &mut bound, &mut |text, span, bound| {
        if text == name && !bound.iter().any(|(n, _)| n == name) {
            Some(span)
        } else {
            None
        }
    })
}

/// If the identifier at `offset` resolves, by ordinary lexical scoping, to a `let`-bound local
/// variable, return that binding's right-hand-side expression span — a caller (`blight-lsp`'s
/// hover) can elaborate that span standalone to recover the local's type, which is otherwise
/// unavailable since elaboration has no local-variable-typed-context entry point of its own.
/// Returns `None` for globals, for non-`let` locals (`lam`/pattern/`Pi`/`Sigma`/`plam`/`handle`/
/// `region` — recovering *their* types needs more than a spanless re-elaboration of one
/// subexpression, so they are out of scope for this MVP), and if `offset` isn't inside any atom.
pub fn resolve_let_rhs_at(form: &Spanned<SpannedSexpr>, offset: usize) -> Option<Span> {
    let mut bound = Vec::new();
    walk_uses(form, &mut bound, &mut |text, span, bound| {
        if !contains(offset, span) {
            return None;
        }
        // The unique atom containing `offset` has been found; resolve its innermost binding
        // (`Some(Some(rhs))` = a let-binding, `Some(None)` = bound but not a let / not a local at
        // all) and stop the walk either way, since there is nothing else to find for this offset.
        Some(
            bound
                .iter()
                .rev()
                .find(|(n, _)| n == text)
                .and_then(|(_, rhs)| *rhs),
        )
    })
    .flatten()
}

/// The byte span of the first occurrence of `name` as a plain atom anywhere in `form`, regardless
/// of binding status. Unlike [`find_unbound_span`] (which specifically wants a *free* occurrence
/// of an undefined name), this is for narrowing diagnostics about a name that legitimately
/// resolves — a definition or binder an error message names in backticks (E2: "could not infer
/// implicit argument `n` of `g`") — down to that name's use site.
fn find_ident_span(form: &Spanned<SpannedSexpr>, name: &str) -> Option<Span> {
    let mut bound = Vec::new();
    walk_uses(form, &mut bound, &mut |text, span, _bound| {
        if text == name {
            Some(span)
        } else {
            None
        }
    })
}

/// Every backtick-quoted identifier in an error message, in order, e.g. "could not infer implicit
/// argument `n` of `g`" yields `["n", "g"]`. A multi-token backtick span (e.g. `` "no instance
/// `Show Bool` in scope" `` ) contributes only its leading token, the part most likely to be a
/// single source atom.
fn backtick_idents(msg: &str) -> impl Iterator<Item = &str> {
    let mut rest = msg;
    std::iter::from_fn(move || loop {
        let start = rest.find('`')? + 1;
        rest = &rest[start..];
        let end = rest.find('`')?;
        let quoted = &rest[..end];
        rest = &rest[end + 1..];
        if let Some(tok) = quoted.split_whitespace().next() {
            return Some(tok);
        }
    })
}

/// Narrow a top-level form's span down to the sub-expression an [`ElabError`] actually concerns,
/// falling back to the whole form's span when no tighter span can be found (unrecognized error
/// kind, or a macro-hygiene-mangled name that no longer matches source text).
pub fn narrow_span(form: &Spanned<SpannedSexpr>, err: &ElabError) -> Span {
    if let ElabError::Unbound(name) = err {
        // E7: the payload may carry a "did you mean" suffix after the bare identifier;
        // identifiers cannot contain spaces, so the first token is always the name itself.
        let name = name.split_whitespace().next().unwrap_or(name);
        if let Some(span) = find_unbound_span(form, name) {
            return span;
        }
    }
    if let ElabError::BadForm(msg) = err {
        // Try each backtick-quoted identifier in message order; the first that actually resolves
        // to a source occurrence wins (an invisible definition-side name like a binder's own
        // parameter name legitimately resolves to nothing here, so this falls through to the
        // next — typically the applied global's own name, which does appear at the call site).
        for name in backtick_idents(msg) {
            if let Some(span) = find_ident_span(form, name) {
                return span;
            }
        }
    }
    form.span
}

/// Why [`rename_local_binder`] refused to produce a rename.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RenameError {
    /// The cursor was not on a local binder's declaration occurrence (`lam`/`let`/`Pi`/`Sigma`/
    /// `plam`/`match`/`matchx`/`handle`/`region`). Globals are renamed by a different mechanism
    /// (not yet implemented — see the T1 roadmap entry).
    NotABinder,
    /// Renaming would let an intervening (nested) binder capture at least one occurrence: some
    /// currently-unshadowed use of the old name sits inside a nested scope that already binds the
    /// new name, so after renaming it would silently refer to that inner binding instead.
    WouldCapture,
}

/// Locate the local binder whose *declaration* name-token contains `offset`, returning its name,
/// declaration span, and the sub-expression(s) that constitute its lexical scope (searched
/// depth-first across `form`; the first-found declaration wins, matching a cursor click resolving
/// to the innermost enclosing binder).
fn find_binder_at(
    form: &Spanned<SpannedSexpr>,
    offset: usize,
) -> Option<(String, Span, Vec<&Spanned<SpannedSexpr>>)> {
    let items = match &form.node {
        SpannedSexpr::List(items) if !items.is_empty() => items,
        _ => return None,
    };
    let head = atom_text(&items[0]);
    match head {
        Some("lam") if items.len() == 3 => {
            if let SpannedSexpr::List(names) = &items[1].node {
                for n in names {
                    if let Some(a) = atom_text(n) {
                        if contains(offset, n.span) {
                            return Some((a.to_string(), n.span, vec![&items[2]]));
                        }
                    }
                }
            }
        }
        Some("plam") if items.len() == 3 => {
            if let SpannedSexpr::List(names) = &items[1].node {
                if let Some(n) = names.first() {
                    if let Some(a) = atom_text(n) {
                        if contains(offset, n.span) {
                            return Some((a.to_string(), n.span, vec![&items[2]]));
                        }
                    }
                }
            }
        }
        Some("let") if items.len() == 3 => {
            if let SpannedSexpr::List(bindings) = &items[1].node {
                if let Some(Spanned {
                    node: SpannedSexpr::List(pair),
                    ..
                }) = bindings.first()
                {
                    if pair.len() == 2 {
                        if let Some(a) = atom_text(&pair[0]) {
                            if contains(offset, pair[0].span) {
                                return Some((a.to_string(), pair[0].span, vec![&items[2]]));
                            }
                        }
                    }
                }
            }
        }
        Some("Pi") | Some("Sigma") if items.len() == 3 => {
            if let SpannedSexpr::List(binders) = &items[1].node {
                for (i, b) in binders.iter().enumerate() {
                    if let Some((name, name_span)) = binder_name_span(b) {
                        if contains(offset, name_span) {
                            let mut scope: Vec<&Spanned<SpannedSexpr>> = binders[i + 1..]
                                .iter()
                                .filter_map(binder_type_subtree)
                                .collect();
                            scope.push(&items[2]);
                            return Some((name, name_span, scope));
                        }
                    }
                }
            }
        }
        Some("match") if items.len() >= 2 => {
            for clause in &items[2..] {
                if let SpannedSexpr::List(cparts) = &clause.node {
                    if cparts.len() == 2 {
                        for (vname, vspan) in pattern_vars_single(&cparts[0]) {
                            if contains(offset, vspan) {
                                return Some((vname, vspan, vec![&cparts[1]]));
                            }
                        }
                    }
                }
            }
        }
        Some("matchx") if items.len() >= 2 => {
            for clause in &items[2..] {
                if let SpannedSexpr::List(cparts) = &clause.node {
                    if cparts.len() == 2 {
                        for (vname, vspan) in pattern_vars_tuple(&cparts[0]) {
                            if contains(offset, vspan) {
                                return Some((vname, vspan, vec![&cparts[1]]));
                            }
                        }
                    }
                }
            }
        }
        Some("handle") if items.len() >= 3 => {
            for clause in &items[2..] {
                if let SpannedSexpr::List(parts) = &clause.node {
                    let h = parts.first().and_then(atom_text);
                    if h == Some("return") && parts.len() == 3 {
                        if let Some(a) = atom_text(&parts[1]) {
                            if contains(offset, parts[1].span) {
                                return Some((a.to_string(), parts[1].span, vec![&parts[2]]));
                            }
                        }
                    } else if parts.len() == 4 {
                        if let Some(a) = atom_text(&parts[1]) {
                            if contains(offset, parts[1].span) {
                                return Some((a.to_string(), parts[1].span, vec![&parts[3]]));
                            }
                        }
                        if let Some(k) = atom_text(&parts[2]) {
                            if contains(offset, parts[2].span) {
                                return Some((k.to_string(), parts[2].span, vec![&parts[3]]));
                            }
                        }
                    }
                }
            }
        }
        Some("region") if items.len() == 3 => {
            if let Some(a) = atom_text(&items[1]) {
                if contains(offset, items[1].span) {
                    return Some((a.to_string(), items[1].span, vec![&items[2]]));
                }
            }
        }
        _ => {}
    }
    // Not this node's own binder: search its children (the binder may be nested anywhere,
    // including inside another binder's own type annotation or body).
    for item in items {
        if let Some(found) = find_binder_at(item, offset) {
            return Some(found);
        }
    }
    None
}

/// Rename the local binder whose declaration-name token contains `decl_offset` to `new_name`,
/// searching every top-level form in `forms`. On success, returns every byte span to replace
/// (the declaration itself plus every unshadowed use in its scope), sorted by position. Refuses
/// (rather than silently mis-renaming) if `decl_offset` is not on a recognized local binder
/// declaration, or if the rename would let a nested binder capture an occurrence.
pub fn rename_local_binder(
    forms: &[Spanned<SpannedSexpr>],
    decl_offset: usize,
    new_name: &str,
) -> Result<Vec<Span>, RenameError> {
    let (name, decl_span, scope) = forms
        .iter()
        .find_map(|form| find_binder_at(form, decl_offset))
        .ok_or(RenameError::NotABinder)?;

    let mut out = vec![decl_span];
    for subtree in scope {
        let mut bound = vec![(name.clone(), None)];
        let capture = walk_uses(subtree, &mut bound, &mut |text, span, bound| {
            if text != name {
                return None;
            }
            // A nested rebinding of `name` shadows this occurrence — it refers to the inner
            // binder, not ours, so leave it untouched.
            if bound[1..].iter().any(|(n, _)| n == &name) {
                return None;
            }
            // A nested rebinding of `new_name` between our declaration and this occurrence would
            // capture it once renamed: refuse rather than silently changing its meaning.
            if bound[1..].iter().any(|(n, _)| n == new_name) {
                return Some(RenameError::WouldCapture);
            }
            out.push(span);
            None
        });
        if let Some(err) = capture {
            return Err(err);
        }
    }
    out.sort_by_key(|s| s.start);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::read_all_spanned;

    fn span_text(src: &str, span: Span) -> &str {
        &src[span.start..span.end]
    }

    // ---- find_unbound_span --------------------------------------------------------------------

    #[test]
    fn finds_the_free_occurrence_inside_a_lambda_body() {
        let src = "(the Nat (lam (x) (plus x undefined-thing)))";
        let forms = read_all_spanned(src).unwrap();
        let span = find_unbound_span(&forms[0], "undefined-thing").unwrap();
        assert_eq!(span_text(src, span), "undefined-thing");
    }

    #[test]
    fn does_not_confuse_a_shadowed_name_with_the_free_one() {
        // The inner `x` is bound by the nested `lam`; `x` is otherwise the (hypothetically)
        // unbound name at the outer level — the scanner must skip the shadowed inner use and
        // report the outer, truly-free occurrence instead.
        let src = "(lam (y) (app (lam (x) x) x))";
        let forms = read_all_spanned(src).unwrap();
        let span = find_unbound_span(&forms[0], "x").unwrap();
        // The *last* `x` (outside the inner lam) is the free one; the inner body's `x` is bound.
        let last_x = src.rfind('x').unwrap();
        assert_eq!(span.start, last_x);
    }

    #[test]
    fn let_rhs_is_scanned_in_the_outer_scope() {
        // `undefined` in the let-binding's RHS is free even though `v` is about to be bound —
        // `let` is non-recursive, so the RHS must not see `v`.
        let src = "(let ((v undefined)) v)";
        let forms = read_all_spanned(src).unwrap();
        let span = find_unbound_span(&forms[0], "undefined").unwrap();
        assert_eq!(span_text(src, span), "undefined");
    }

    #[test]
    fn no_free_occurrence_returns_none() {
        let src = "(lam (x) x)";
        let forms = read_all_spanned(src).unwrap();
        assert!(find_unbound_span(&forms[0], "x").is_none());
    }

    // ---- rename_local_binder --------------------------------------------------------------------

    #[test]
    fn renames_a_lambda_bound_variable_and_its_uses() {
        let src = "(lam (x) (plus x x))";
        let forms = read_all_spanned(src).unwrap();
        let decl_offset = src.find("(x)").unwrap() + 1;
        let spans = rename_local_binder(&forms, decl_offset, "y").unwrap();
        assert_eq!(spans.len(), 3, "the decl plus two uses");
        for s in &spans {
            assert_eq!(span_text(src, *s), "x");
        }
    }

    #[test]
    fn rename_skips_occurrences_shadowed_by_a_nested_binder() {
        // The outer `x`'s scope is `(app (lam (x) x) x)`; the inner `lam`'s own `x` shadows the
        // parameter's own `x` for its body, so only the *outer* trailing `x` should be renamed
        // alongside the declaration (2 occurrences total, not 3).
        let src = "(lam (x) (app (lam (x) x) x))";
        let forms = read_all_spanned(src).unwrap();
        let decl_offset = src.find("(x)").unwrap() + 1;
        let spans = rename_local_binder(&forms, decl_offset, "y").unwrap();
        assert_eq!(spans.len(), 2, "decl + the one truly-outer use: {spans:?}");
    }

    #[test]
    fn rename_refuses_when_the_new_name_would_be_captured() {
        // The outer `x`'s scope is the inner `(lam (y) x)`; the trailing `x` there is currently
        // free (referring to the outer binder), but renaming it to `y` would put it under the
        // inner `lam`'s own `y` binder — silently capturing it instead of renaming it.
        let src = "(lam (x) (lam (y) x))";
        let forms = read_all_spanned(src).unwrap();
        let decl_offset = src.find("(x)").unwrap() + 1;
        let err = rename_local_binder(&forms, decl_offset, "y").unwrap_err();
        assert_eq!(err, RenameError::WouldCapture);
    }

    #[test]
    fn rename_of_a_non_binder_offset_is_refused() {
        let src = "(lam (x) x)";
        let forms = read_all_spanned(src).unwrap();
        let offset = src.find("lam").unwrap();
        assert_eq!(
            rename_local_binder(&forms, offset, "y").unwrap_err(),
            RenameError::NotABinder
        );
    }

    #[test]
    fn renames_a_let_bound_variable_only_in_its_body() {
        let src = "(let ((v (plus 1 2))) (plus v v))";
        let forms = read_all_spanned(src).unwrap();
        let decl_offset = src.find("v (plus 1 2)").unwrap();
        let spans = rename_local_binder(&forms, decl_offset, "total").unwrap();
        // decl + two uses in the body; the `v` inside `(plus 1 2)`... there is none (no `v`
        // there), so exactly 3 spans.
        assert_eq!(spans.len(), 3);
    }

    #[test]
    fn renames_a_match_pattern_bound_variable() {
        let src = "(match n [(Succ k) (plus k k)] [(Zero) Zero])";
        let forms = read_all_spanned(src).unwrap();
        let decl_offset = src.find("k)").unwrap();
        let spans = rename_local_binder(&forms, decl_offset, "pred").unwrap();
        assert_eq!(
            spans.len(),
            3,
            "decl + two uses in the clause body: {spans:?}"
        );
    }

    // ---- resolve_let_rhs_at ------------------------------------------------------------------

    #[test]
    fn resolves_a_use_of_a_let_bound_variable_to_its_rhs() {
        let src = "(let ((v (Succ Zero))) (plus v v))";
        let forms = read_all_spanned(src).unwrap();
        let use_offset = src.rfind('v').unwrap();
        let span = resolve_let_rhs_at(&forms[0], use_offset).unwrap();
        assert_eq!(span_text(src, span), "(Succ Zero)");
    }

    #[test]
    fn does_not_resolve_a_lambda_bound_variable() {
        let src = "(lam (v) v)";
        let forms = read_all_spanned(src).unwrap();
        let use_offset = src.rfind('v').unwrap();
        assert!(resolve_let_rhs_at(&forms[0], use_offset).is_none());
    }

    #[test]
    fn does_not_resolve_a_use_shadowed_by_an_inner_lambda() {
        // Inside the inner `(lam (v) v)`, `v` refers to the lambda parameter, not the outer let.
        let src = "(let ((v (Succ Zero))) (lam (v) v))";
        let forms = read_all_spanned(src).unwrap();
        let use_offset = src.rfind('v').unwrap();
        assert!(resolve_let_rhs_at(&forms[0], use_offset).is_none());
    }

    // ---- narrow_span ----------------------------------------------------------------------------

    #[test]
    fn narrow_span_targets_the_unbound_name_not_the_whole_form() {
        let src = "(the Nat undefined-name)";
        let forms = read_all_spanned(src).unwrap();
        let err = ElabError::Unbound("undefined-name".to_string());
        let span = narrow_span(&forms[0], &err);
        assert_eq!(span_text(src, span), "undefined-name");
    }

    #[test]
    fn narrow_span_falls_back_to_the_whole_form_for_other_errors() {
        let src = "(bad form here)";
        let forms = read_all_spanned(src).unwrap();
        let err = ElabError::BadForm("whatever".to_string());
        let span = narrow_span(&forms[0], &err);
        assert_eq!(span, forms[0].span);
    }
}
