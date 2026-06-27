//! A pre-elaboration `Sexpr -> Sexpr` macro-expansion phase (spec §6.6). UNTRUSTED.
//!
//! This is a small `syntax-rules`-style rewriter with *marker-based hygiene*. It runs on raw
//! `Sexpr` before `parse_surface`, so it never touches the kernel: a buggy macro can only produce
//! an `Sexpr` that fails to elaborate, never an unsound term.
//!
//! ## Patterns and templates
//! A macro is a sequence of `(pattern template)` rules. In a pattern:
//! - the head position matches the macro keyword and is ignored;
//! - an atom listed in the rule's `literals` must appear verbatim;
//! - the atom `_` matches anything and binds nothing;
//! - a sub-pattern immediately followed by `...` matches zero or more forms (only one ellipsis per
//!   list, and it must be the last element) — the bound variable then expands once per match;
//! - any other atom is a pattern variable binding exactly one form.
//!
//! ## Hygiene (marker-based)
//! Each expansion gets a fresh integer *mark*. Template identifiers that are **not** pattern
//! variables are tagged `name%mark`. A later [`resolve_marks`] pass strips the mark from any
//! identifier that does not end up referring to a macro-local binding, so introduced references to
//! globals (`lam`, `Pi`, user functions) work, while introduced *binders* (`tmp%3`) stay distinct
//! from a user's own `tmp`. This is enough for the classic capture-avoidance oracle.

use crate::sexpr::Sexpr;
use std::collections::HashMap;

/// A single `(pattern template)` rewrite rule.
#[derive(Debug, Clone)]
pub struct Rule {
    pub pattern: Sexpr,
    pub template: Sexpr,
}

/// A `syntax-rules` macro: a set of literal keywords and an ordered list of rules.
#[derive(Debug, Clone)]
pub struct MacroDef {
    pub literals: Vec<String>,
    pub rules: Vec<Rule>,
}

/// The macro table plus a monotonically-increasing mark counter for hygiene.
#[derive(Debug, Default)]
pub struct MacroEnv {
    macros: HashMap<String, MacroDef>,
    next_mark: u64,
}

/// The hygiene mark separator. `%` cannot start a normal identifier in practice, so a marked name
/// is unambiguous and round-trips through the reader as a single atom.
const MARK_SEP: char = '%';

impl MacroEnv {
    pub fn new() -> Self {
        MacroEnv::default()
    }

    /// Register `(define-macro name (syntax-rules (lits...) (pat tmpl) ...))`. Returns the macro
    /// name on success.
    pub fn define(&mut self, form: &Sexpr) -> Result<String, String> {
        let items = match form {
            Sexpr::List(items) => items,
            _ => return Err("define-macro: expected a list".into()),
        };
        if items.len() != 3 || !atom_is(&items[0], "define-macro") {
            return Err("expected (define-macro name (syntax-rules ...))".into());
        }
        let name = atom(&items[1])
            .ok_or("macro name must be an atom")?
            .to_string();
        let def = parse_syntax_rules(&items[2])?;
        self.macros.insert(name.clone(), def);
        Ok(name)
    }

    /// Whether `name` names a registered macro.
    pub fn is_macro(&self, name: &str) -> bool {
        self.macros.contains_key(name)
    }

    fn fresh_mark(&mut self) -> u64 {
        self.next_mark += 1;
        self.next_mark
    }

    /// Fully expand `form`, repeatedly rewriting any list whose head is a macro keyword until a
    /// fixpoint (bounded to avoid runaway recursion). Hygiene marks are *retained* in the output:
    /// introduced binders carry a fresh mark so they never collide with the caller's identifiers.
    /// The elaborator strips a mark only as a fallback when resolving a *free* reference (to a
    /// global/constructor), so macro-introduced references to globals still work. See `elab`'s
    /// `Surface::Var` handling and [`strip_mark`].
    pub fn expand(&mut self, form: &Sexpr) -> Result<Sexpr, String> {
        self.expand_inner(form, 0)
    }

    fn expand_inner(&mut self, form: &Sexpr, depth: usize) -> Result<Sexpr, String> {
        if depth > 1000 {
            return Err("macro expansion did not terminate (depth limit)".into());
        }
        // First, try to expand this node if it is a macro call.
        if let Sexpr::List(items) = form {
            if let Some(head) = items.first().and_then(atom) {
                if let Some(def) = self.macros.get(head).cloned() {
                    let mark = self.fresh_mark();
                    let rewritten = apply_macro(head, &def, items, mark)?;
                    return self.expand_inner(&rewritten, depth + 1);
                }
            }
            // Not a macro call: recurse into children.
            let mut out = Vec::with_capacity(items.len());
            for it in items {
                out.push(self.expand_inner(it, depth + 1)?);
            }
            return Ok(Sexpr::List(out));
        }
        Ok(form.clone())
    }
}

/// A binding captured by a pattern variable: either a single form or an ellipsis sequence.
#[derive(Debug, Clone)]
enum Binding {
    One(Sexpr),
    Many(Vec<Sexpr>),
}

/// Try each rule in order; the first whose pattern matches is instantiated.
fn apply_macro(name: &str, def: &MacroDef, call: &[Sexpr], mark: u64) -> Result<Sexpr, String> {
    for rule in &def.rules {
        let mut binds = HashMap::new();
        if match_pattern(
            &rule.pattern,
            &Sexpr::List(call.to_vec()),
            &def.literals,
            &mut binds,
        ) {
            return Ok(instantiate(&rule.template, &binds, &def.literals, mark));
        }
    }
    Err(format!(
        "no matching `syntax-rules` clause for macro `{name}`"
    ))
}

/// Match `pat` against `inp`, recording pattern-variable bindings. Returns whether it matched.
fn match_pattern(
    pat: &Sexpr,
    inp: &Sexpr,
    literals: &[String],
    binds: &mut HashMap<String, Binding>,
) -> bool {
    match pat {
        Sexpr::Atom(a) => {
            if a == "_" {
                return true;
            }
            if literals.iter().any(|l| l == a) {
                // A literal must match the identical atom.
                return matches!(inp, Sexpr::Atom(b) if b == a);
            }
            // A pattern variable binds whatever is here.
            binds.insert(a.clone(), Binding::One(inp.clone()));
            true
        }
        Sexpr::List(pats) => {
            let ins = match inp {
                Sexpr::List(ins) => ins,
                _ => return false,
            };
            // The head of a top-level pattern is the macro keyword; treat it as a wildcard so the
            // call's head (the macro name) is ignored. We detect "ellipsis present" generally.
            match_seq(pats, ins, literals, binds)
        }
    }
}

/// Match a sequence of sub-patterns against input forms, supporting a single trailing `x ...`.
fn match_seq(
    pats: &[Sexpr],
    ins: &[Sexpr],
    literals: &[String],
    binds: &mut HashMap<String, Binding>,
) -> bool {
    // Locate an ellipsis: a `...` atom immediately following a sub-pattern.
    let ellipsis = pats.iter().position(|p| atom_is(p, "..."));
    match ellipsis {
        None => {
            if pats.len() != ins.len() {
                return false;
            }
            pats.iter()
                .zip(ins.iter())
                .all(|(p, i)| match_pattern(p, i, literals, binds))
        }
        Some(dots_at) => {
            // `dots_at` points at `...`; the repeated sub-pattern is at `dots_at - 1`.
            if dots_at == 0 {
                return false;
            }
            let rep = &pats[dots_at - 1];
            let before = &pats[..dots_at - 1];
            let after = &pats[dots_at + 1..];
            if ins.len() < before.len() + after.len() {
                return false;
            }
            // Fixed prefix.
            for (p, i) in before.iter().zip(ins.iter()) {
                if !match_pattern(p, i, literals, binds) {
                    return false;
                }
            }
            // Repeated middle.
            let mid_end = ins.len() - after.len();
            let mid = &ins[before.len()..mid_end];
            // Collect per-variable sequences for the repeated sub-pattern.
            let vars = pattern_vars(rep, literals);
            let mut seqs: HashMap<String, Vec<Sexpr>> =
                vars.iter().map(|v| (v.clone(), Vec::new())).collect();
            for item in mid {
                let mut sub = HashMap::new();
                if !match_pattern(rep, item, literals, &mut sub) {
                    return false;
                }
                for v in &vars {
                    if let Some(Binding::One(s)) = sub.get(v) {
                        seqs.get_mut(v).unwrap().push(s.clone());
                    }
                }
            }
            for (v, seq) in seqs {
                binds.insert(v, Binding::Many(seq));
            }
            // Fixed suffix.
            for (p, i) in after.iter().zip(ins[mid_end..].iter()) {
                if !match_pattern(p, i, literals, binds) {
                    return false;
                }
            }
            true
        }
    }
}

/// The pattern variables (non-literal, non-`_`, non-`...`) occurring in `pat`.
fn pattern_vars(pat: &Sexpr, literals: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    collect_vars(pat, literals, &mut out);
    out
}

fn collect_vars(pat: &Sexpr, literals: &[String], out: &mut Vec<String>) {
    match pat {
        Sexpr::Atom(a) => {
            if a != "_" && a != "..." && !literals.iter().any(|l| l == a) && !out.contains(a) {
                out.push(a.clone());
            }
        }
        Sexpr::List(ps) => {
            for p in ps {
                collect_vars(p, literals, out);
            }
        }
    }
}

/// Instantiate `tmpl`, substituting pattern variables and tagging template-introduced identifiers
/// with `mark` for hygiene. A `var ...` in the template splices the var's matched sequence.
fn instantiate(
    tmpl: &Sexpr,
    binds: &HashMap<String, Binding>,
    literals: &[String],
    mark: u64,
) -> Sexpr {
    match tmpl {
        Sexpr::Atom(a) => match binds.get(a) {
            Some(Binding::One(s)) => s.clone(),
            // A bare `var` that matched a sequence is an error in real syntax-rules; here we just
            // wrap it in a list so it is visibly malformed rather than silently dropped.
            Some(Binding::Many(seq)) => Sexpr::List(seq.clone()),
            None => {
                if a == "..." || literals.iter().any(|l| l == a) {
                    tmpl.clone()
                } else {
                    // Template-introduced identifier: tag with the hygiene mark.
                    Sexpr::Atom(format!("{a}{MARK_SEP}{mark}"))
                }
            }
        },
        Sexpr::List(ts) => {
            let mut out = Vec::with_capacity(ts.len());
            let mut i = 0;
            while i < ts.len() {
                // `sub ...` splices a sequence-bound variable.
                if i + 1 < ts.len() && atom_is(&ts[i + 1], "...") {
                    if let Some(v) = atom(&ts[i]) {
                        if let Some(Binding::Many(seq)) = binds.get(v) {
                            for s in seq {
                                out.push(s.clone());
                            }
                            i += 2;
                            continue;
                        }
                    }
                }
                out.push(instantiate(&ts[i], binds, literals, mark));
                i += 1;
            }
            Sexpr::List(out)
        }
    }
}

/// Strip a hygiene mark from an identifier: `name%m` becomes `name`, anything else is unchanged.
/// The elaborator calls this as a *fallback* when a (possibly macro-introduced) identifier is not a
/// bound local, so that introduced references to globals/constructors resolve while introduced
/// *binders* (matched by exact, still-marked name) stay distinct from the caller's identifiers.
pub fn strip_mark(name: &str) -> &str {
    match name.split_once(MARK_SEP) {
        Some((base, _)) if !base.is_empty() => base,
        _ => name,
    }
}

/// Parse `(syntax-rules (lit...) (pat tmpl) ...)`.
fn parse_syntax_rules(form: &Sexpr) -> Result<MacroDef, String> {
    let items = match form {
        Sexpr::List(items) => items,
        _ => return Err("expected (syntax-rules ...)".into()),
    };
    if items.is_empty() || !atom_is(&items[0], "syntax-rules") {
        return Err("expected (syntax-rules (lits...) rules...)".into());
    }
    let literals = match items.get(1) {
        Some(Sexpr::List(ls)) => ls
            .iter()
            .map(|l| {
                atom(l)
                    .map(str::to_string)
                    .ok_or("literal must be an atom".to_string())
            })
            .collect::<Result<Vec<_>, _>>()?,
        _ => return Err("syntax-rules: second element must be the literals list".into()),
    };
    let mut rules = Vec::new();
    for r in &items[2..] {
        let parts = match r {
            Sexpr::List(p) if p.len() == 2 => p,
            _ => return Err("each rule must be (pattern template)".into()),
        };
        rules.push(Rule {
            pattern: parts[0].clone(),
            template: parts[1].clone(),
        });
    }
    if rules.is_empty() {
        return Err("syntax-rules needs at least one rule".into());
    }
    Ok(MacroDef { literals, rules })
}

fn atom(s: &Sexpr) -> Option<&str> {
    match s {
        Sexpr::Atom(a) => Some(a.as_str()),
        _ => None,
    }
}

fn atom_is(s: &Sexpr, name: &str) -> bool {
    atom(s) == Some(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sexpr::read_one;

    fn read(src: &str) -> Sexpr {
        read_one(src).unwrap().0
    }

    fn expand_str(env: &mut MacroEnv, src: &str) -> Sexpr {
        env.expand(&read(src)).unwrap()
    }

    /// Recursively strip hygiene marks — for asserting *shape* in non-hygiene tests.
    fn unmark(s: &Sexpr) -> Sexpr {
        match s {
            Sexpr::Atom(a) => Sexpr::Atom(strip_mark(a).to_string()),
            Sexpr::List(items) => Sexpr::List(items.iter().map(unmark).collect()),
        }
    }

    #[test]
    fn macro_expands_simple() {
        let mut env = MacroEnv::new();
        env.define(&read(
            "(define-macro inc (syntax-rules () ((inc x) (Succ x))))",
        ))
        .unwrap();
        assert_eq!(
            unmark(&expand_str(&mut env, "(inc Zero)")),
            read("(Succ Zero)")
        );
        // Expansion is recursive: nested macro calls expand too.
        assert_eq!(
            unmark(&expand_str(&mut env, "(inc (inc Zero))")),
            read("(Succ (Succ Zero))")
        );
    }

    #[test]
    fn macro_ellipsis_splices() {
        let mut env = MacroEnv::new();
        env.define(&read(
            "(define-macro list* (syntax-rules () ((list* x ...) (mk x ...))))",
        ))
        .unwrap();
        assert_eq!(
            unmark(&expand_str(&mut env, "(list* a b c)")),
            read("(mk a b c)")
        );
        assert_eq!(unmark(&expand_str(&mut env, "(list*)")), read("(mk)"));
    }

    #[test]
    fn macro_hygiene_no_capture() {
        // The classic capture oracle: the macro introduces a temporary binder `tmp`. A caller who
        // *also* names something `tmp` must not be captured. With marker hygiene the introduced
        // `tmp` carries a fresh mark (`tmp%N`) and stays distinct from the caller's unmarked `tmp`.
        let mut env = MacroEnv::new();
        env.define(&read(
            "(define-macro swap (syntax-rules () \
               ((swap a b) (let ((tmp a)) (seq (set b tmp))))))",
        ))
        .unwrap();
        // `a`->`x`, `b`->`tmp` (the caller's). The template `tmp`, `let`, `seq`, `set` are
        // introduced and get the same fresh mark `N`.
        let out = env.expand(&read("(swap x tmp)")).unwrap();
        let marked = |s: &str| {
            // find the single mark used this expansion by inspecting the binder
            if let Sexpr::List(items) = &out {
                if let Sexpr::Atom(a) = &items[0] {
                    let n = a.split_once(MARK_SEP).unwrap().1;
                    return format!("{s}{MARK_SEP}{n}");
                }
            }
            unreachable!()
        };
        let expected = Sexpr::List(vec![
            Sexpr::Atom(marked("let")),
            Sexpr::List(vec![Sexpr::List(vec![
                Sexpr::Atom(marked("tmp")),
                Sexpr::Atom("x".into()),
            ])]),
            Sexpr::List(vec![
                Sexpr::Atom(marked("seq")),
                Sexpr::List(vec![
                    Sexpr::Atom(marked("set")),
                    Sexpr::Atom("tmp".into()), // the caller's `tmp` (from `b`) — unmarked
                    Sexpr::Atom(marked("tmp")), // the macro's introduced `tmp` — marked
                ]),
            ]),
        ]);
        assert_eq!(out, expected);
        // The decisive property: the macro-introduced binder is NOT the caller's `tmp`.
        assert_ne!(marked("tmp"), "tmp");
        // …yet `strip_mark` recovers the base name for free-reference resolution.
        assert_eq!(strip_mark(&marked("let")), "let");
    }

    #[test]
    fn unknown_macro_clause_errors() {
        let mut env = MacroEnv::new();
        env.define(&read("(define-macro one (syntax-rules () ((one a) a)))"))
            .unwrap();
        // Two args where the only clause expects one: no matching clause.
        let r = env.expand(&read("(one a b)"));
        assert!(r.is_err(), "no clause should match: {r:?}");
    }

    #[test]
    fn non_macro_passes_through() {
        let mut env = MacroEnv::new();
        let src = "(lam (x) (Succ x))";
        assert_eq!(expand_str(&mut env, src), read(src));
    }
}
