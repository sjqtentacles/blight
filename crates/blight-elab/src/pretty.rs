//! A pretty-printer for core kernel [`Term`]s (spec §5 surface). UNTRUSTED.
//!
//! The kernel stores terms nameless (de Bruijn) and only derives `Debug`, which is unreadable for
//! humans (`Pi(One, Data(DataName("Nat"), [], []), ...)`). This module re-sugars a core term back
//! into the surface s-expression syntax the reader accepts, inventing readable binder names and
//! resolving de Bruijn indices against the binder stack. It lives in the untrusted frontend (it has
//! no bearing on what the kernel accepts) and is reused by the REPL and by diagnostics so that types
//! in error messages are legible.

use blight_kernel::proof::Judgement;
use blight_kernel::semiring::Grade;
use blight_kernel::term::{ConName, DataName, Interval, Level, Term};
use blight_kernel::Proof;

/// Pretty-print a core term as a surface s-expression string.
pub fn pretty_term(term: &Term) -> String {
    let mut p = Printer { names: Vec::new() };
    p.term(term)
}

/// Recognize a canonical `Nat` term — a chain of `Succ` applications ending in `Zero` — and
/// return its decimal value (E1). Iterative (not recursive) so printing a large unary numeral
/// cannot add stack depth proportional to its value. Matches by constructor *name* only (core
/// `Term::Con` carries no data-type tag), the same heuristic the reader's char-literal desugaring
/// already relies on; a user-defined type that happens to name its constructors `Zero`/`Succ`
/// would print as a decimal too, which is the accepted trade-off for readable `Nat` output.
/// Returns `None` for anything else, which falls back to the general `Con` printer.
pub(crate) fn nat_value(t: &Term) -> Option<u64> {
    let mut cur = t;
    let mut n: u64 = 0;
    loop {
        match cur {
            Term::Con(c, args) if c.0 == "Zero" && args.is_empty() => return Some(n),
            Term::Con(c, args) if c.0 == "Succ" && args.len() == 1 => {
                n = n.checked_add(1)?;
                cur = &args[0];
            }
            _ => return None,
        }
    }
}

/// Pretty-print a proof's conclusion, e.g. `⊢ (lam (x) x) : (Pi ((x A)) A)`.
pub fn pretty_concl(proof: &Proof) -> String {
    match proof.concl() {
        Judgement::HasType { term, ty } => {
            format!("⊢ {} : {}", pretty_term(term), pretty_term(ty))
        }
    }
}

struct Printer {
    /// The binder stack: `names[len-1-i]` is the name of de Bruijn index `i`.
    names: Vec<String>,
}

impl Printer {
    /// Resolve de Bruijn index `i` to the name introduced by the enclosing binder, or a fallback
    /// `?i` if it escapes the known binder stack (should not happen for well-scoped terms).
    fn var(&self, i: usize) -> String {
        if i < self.names.len() {
            self.names[self.names.len() - 1 - i].clone()
        } else {
            format!("?{i}")
        }
    }

    /// Invent a fresh, readable binder name not currently shadowing anything on the stack.
    fn fresh(&self) -> String {
        const LETTERS: &[u8] = b"xyzabcdefghijklmnopqrstuvw";
        let depth = self.names.len();
        let letter = LETTERS[depth % LETTERS.len()] as char;
        let tick = depth / LETTERS.len();
        if tick == 0 {
            letter.to_string()
        } else {
            format!("{letter}{tick}")
        }
    }

    fn with_binder<R>(&mut self, name: String, f: impl FnOnce(&mut Self) -> R) -> R {
        self.names.push(name);
        let r = f(self);
        self.names.pop();
        r
    }

    fn grade(g: &Grade) -> &'static str {
        match g {
            Grade::Zero => "0",
            Grade::One => "1",
            Grade::Omega => "w",
        }
    }

    fn level(l: &Level) -> String {
        fn n(l: &Level) -> Option<u32> {
            match l {
                Level::Zero => Some(0),
                Level::Suc(i) => n(i).map(|k| k + 1),
                Level::Max(a, b) => match (n(a), n(b)) {
                    (Some(x), Some(y)) => Some(x.max(y)),
                    _ => None,
                },
                Level::Var(_) => None,
            }
        }
        match n(l) {
            Some(k) => k.to_string(),
            None => match l {
                Level::Var(i) => format!("u{i}"),
                _ => "?".to_string(),
            },
        }
    }

    fn interval(&self, r: &Interval) -> String {
        match r {
            Interval::I0 => "i0".to_string(),
            Interval::I1 => "i1".to_string(),
            Interval::Dim(i) => self.var(*i),
            Interval::Min(a, b) => format!("(and {} {})", self.interval(a), self.interval(b)),
            Interval::Max(a, b) => format!("(or {} {})", self.interval(a), self.interval(b)),
            Interval::Neg(a) => format!("(neg {})", self.interval(a)),
        }
    }

    fn data_name(d: &DataName) -> &str {
        &d.0
    }
    fn con_name(c: &ConName) -> &str {
        &c.0
    }

    fn term(&mut self, t: &Term) -> String {
        match t {
            Term::Var(i) => self.var(*i),
            Term::Univ(l) => format!("(Type {})", Self::level(l)),
            Term::Pi(g, dom, cod) => {
                let name = self.fresh();
                let dom_s = self.term(dom);
                let grade = Self::grade(g);
                let binder = if grade == "1" {
                    format!("({name} {dom_s})")
                } else {
                    format!("({name} {dom_s} {grade})")
                };
                let cod_s = self.with_binder(name, |p| p.term(cod));
                format!("(Pi ({binder}) {cod_s})")
            }
            Term::Lam(body) => {
                let name = self.fresh();
                let body_s = self.with_binder(name.clone(), |p| p.term(body));
                format!("(lam ({name}) {body_s})")
            }
            Term::App(f, a) => format!("({} {})", self.term(f), self.term(a)),
            Term::Sigma(dom, cod) => {
                let name = self.fresh();
                let dom_s = self.term(dom);
                let cod_s = self.with_binder(name.clone(), |p| p.term(cod));
                format!("(Sigma (({name} {dom_s})) {cod_s})")
            }
            Term::Pair(a, b) => format!("(pair {} {})", self.term(a), self.term(b)),
            Term::Fst(p) => format!("(fst {})", self.term(p)),
            Term::Snd(p) => format!("(snd {})", self.term(p)),
            Term::Ann(e, ty) => format!("(the {} {})", self.term(ty), self.term(e)),
            Term::Data(d, params, indices) => {
                let mut parts = vec![Self::data_name(d).to_string()];
                parts.extend(params.iter().map(|p| self.term(p)));
                parts.extend(indices.iter().map(|i| self.term(i)));
                if parts.len() == 1 {
                    parts.into_iter().next().unwrap()
                } else {
                    format!("({})", parts.join(" "))
                }
            }
            Term::Con(c, args) => {
                // E1: re-sugar a canonical `Nat` numeral (a `Succ`-chain ending in `Zero`) back to
                // decimal, so REPL/diagnostic output round-trips with the surface literal syntax.
                if let Some(n) = nat_value(t) {
                    n.to_string()
                } else if args.is_empty() {
                    Self::con_name(c).to_string()
                } else {
                    let mut parts = vec![Self::con_name(c).to_string()];
                    parts.extend(args.iter().map(|a| self.term(a)));
                    format!("({})", parts.join(" "))
                }
            }
            Term::PCon {
                name, args, dim, ..
            } => {
                let mut parts = vec![Self::con_name(name).to_string()];
                parts.extend(args.iter().map(|a| self.term(a)));
                parts.push(format!("@{}", self.interval(dim)));
                format!("({})", parts.join(" "))
            }
            Term::Elim {
                data,
                motive,
                methods,
                scrutinee,
            } => {
                let mut parts = vec![
                    "elim".to_string(),
                    Self::data_name(data).to_string(),
                    self.term(motive),
                ];
                parts.extend(methods.iter().map(|m| self.term(m)));
                parts.push(self.term(scrutinee));
                format!("({})", parts.join(" "))
            }
            Term::Interval(r) => self.interval(r),
            Term::PathP { family, lhs, rhs } => {
                format!(
                    "(PathP {} {} {})",
                    self.term(family),
                    self.term(lhs),
                    self.term(rhs)
                )
            }
            Term::PLam(body) => {
                let name = self.fresh();
                let body_s = self.with_binder(name.clone(), |p| p.term(body));
                format!("(plam ({name}) {body_s})")
            }
            Term::PApp(p, r) => format!("(@ {} {})", self.term(p), self.interval(r)),
            Term::Partial(_, ty) => format!("(Partial {})", self.term(ty)),
            Term::System(_) => "(system ...)".to_string(),
            Term::Transp { family, base, .. } => {
                format!("(transp {} {})", self.term(family), self.term(base))
            }
            Term::HComp { ty, base, .. } => {
                format!("(hcomp {} {})", self.term(ty), self.term(base))
            }
            Term::Comp { family, base, .. } => {
                format!("(comp {} {})", self.term(family), self.term(base))
            }
            Term::Glue { base, ty, .. } => {
                format!("(Glue {} {})", self.term(base), self.term(ty))
            }
            Term::GlueTerm { base, .. } => format!("(glue {})", self.term(base)),
            Term::Unglue(t) => format!("(unglue {})", self.term(t)),
            Term::Op {
                effect,
                op,
                type_args,
                arg,
            } => {
                if type_args.is_empty() {
                    format!("(perform {} {} {})", effect.0, op, self.term(arg))
                } else {
                    let tas: Vec<String> = type_args.iter().map(|t| self.term(t)).collect();
                    format!(
                        "(perform {} {} ({}) {})",
                        effect.0,
                        op,
                        tas.join(" "),
                        self.term(arg)
                    )
                }
            }
            Term::Handle { body, .. } => format!("(handle {} ...)", self.term(body)),
            Term::EffTy(_, a) => format!("(! E {})", self.term(a)),
            Term::Delay(a) => format!("(Delay {})", self.term(a)),
            Term::Now(a) => format!("(now {})", self.term(a)),
            Term::Later(a) => format!("(later {})", self.term(a)),
            Term::Force(a) => format!("(force {})", self.term(a)),
            Term::Foreign { symbol, ty } => format!("(foreign {:?} {})", symbol, self.term(ty)),
            // ---- primitive machine integers (M11) ----
            Term::IntTy => "Int".to_string(),
            Term::IntLit(n) => format!("(int {n})"),
            Term::IntPrim { op, lhs, rhs } => {
                let head = match op {
                    blight_kernel::IntPrimOp::Add => "int+",
                    blight_kernel::IntPrimOp::Sub => "int-",
                    blight_kernel::IntPrimOp::Mul => "int*",
                    blight_kernel::IntPrimOp::Div => "int/",
                    blight_kernel::IntPrimOp::Eq => "int=",
                    blight_kernel::IntPrimOp::Lt => "int<",
                };
                format!("({head} {} {})", self.term(lhs), self.term(rhs))
            }
            Term::IfZero {
                scrut,
                then_,
                else_,
            } => format!(
                "(if-zero {} {} {})",
                self.term(scrut),
                self.term(then_),
                self.term(else_)
            ),
            Term::Erased => "<erased>".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    #[test]
    fn prints_identity_lambda() {
        // λ. 0  ==>  (lam (x) x)
        let id = Term::Lam(Rc::new(Term::Var(0)));
        assert_eq!(pretty_term(&id), "(lam (x) x)");
    }

    #[test]
    fn prints_pi_with_binder_name() {
        // Pi (_ :^1 Type0) (Var 0) ==> (Pi ((x (Type 0))) x)
        let t = Term::Pi(
            Grade::One,
            Rc::new(Term::Univ(Level::Zero)),
            Rc::new(Term::Var(0)),
        );
        assert_eq!(pretty_term(&t), "(Pi ((x (Type 0))) x)");
    }

    #[test]
    fn prints_nested_binders_distinctly() {
        // λ. λ. (1 0) ==> (lam (x) (lam (y) (x y)))
        let t = Term::Lam(Rc::new(Term::Lam(Rc::new(Term::App(
            Rc::new(Term::Var(1)),
            Rc::new(Term::Var(0)),
        )))));
        assert_eq!(pretty_term(&t), "(lam (x) (lam (y) (x y)))");
    }

    #[test]
    fn prints_data_and_con() {
        let nat = Term::Data(DataName("Nat".into()), vec![], vec![]);
        assert_eq!(pretty_term(&nat), "Nat");
    }

    /// E1: a canonical `Nat` numeral re-sugars to decimal, not the raw `Succ`-chain — the
    /// pretty-printer half of the literal round-trip (parse `1` -> `Succ Zero` -> print `1`).
    #[test]
    fn prints_canonical_nat_as_decimal() {
        let zero = Term::Con(ConName("Zero".into()), vec![]);
        assert_eq!(pretty_term(&zero), "0");
        let one = Term::Con(ConName("Succ".into()), vec![zero.clone()]);
        assert_eq!(pretty_term(&one), "1");
        let three = Term::Con(
            ConName("Succ".into()),
            vec![Term::Con(ConName("Succ".into()), vec![one.clone()])],
        );
        assert_eq!(pretty_term(&three), "3");
    }

    /// A `Succ`/`Zero`-shaped `Con` that is *not* a canonical chain (wrong arity, or an
    /// unrelated constructor) still falls back to the general s-expression printer.
    #[test]
    fn non_canonical_con_falls_back_to_sexpr_printing() {
        let two_args = Term::Con(
            ConName("Succ".into()),
            vec![
                Term::Con(ConName("Zero".into()), vec![]),
                Term::Con(ConName("Zero".into()), vec![]),
            ],
        );
        assert_eq!(pretty_term(&two_args), "(Succ 0 0)");
        let cons = Term::Con(
            ConName("cons".into()),
            vec![
                Term::Con(ConName("Zero".into()), vec![]),
                Term::Con(ConName("nil".into()), vec![]),
            ],
        );
        assert_eq!(pretty_term(&cons), "(cons 0 nil)");
    }
}
