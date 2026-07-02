//! P10 — whole-program defunctionalization (untrusted backend, spec §7.1).
//!
//! A higher-order argument that survives `mono` + `inline` stays a runtime closure: each
//! [`crate::anf::Comp::Call`] / [`crate::anf::Tail::TailCall`] loads the lifted function pointer from
//! the closure header and makes an indirect `tailcc` call (`bl_app`). LTO cannot devirtualize a
//! function pointer loaded from a heap object, so the indirection — and the lost inlining of the
//! callee — is paid at every apply.
//!
//! This pass runs a flow-insensitive whole-program closure analysis (0-CFA) over the
//! closure-converted ANF: it builds the finite universe of first-class function values (every
//! [`crate::anf::Comp::MkClosure`] site) and, for each indirect apply, the set of lifted functions
//! that can reach its head. Closure values are propagated through every flow vector closure
//! conversion + the elim-loop transform produce: `let`-copies, function parameters, environment
//! slots (`MkClosure` captures ↔ `EnvRef`), **tuple fields** (the elim-loop packs a loop's live
//! variables — including a threaded continuation closure — into a state `Tuple`, read back with
//! `Proj`), call arguments → callee parameters, and callee returns → call results. Anything that
//! escapes to an unanalyzable consumer (a `Foreign`, an effect `Op`/`Handle`, an unknown-callee
//! apply, a delay, or a data constructor) is treated conservatively as **open**, and any function
//! whose closure escapes there has its parameter opened — so a head that could receive an
//! unanalyzable value is never devirtualized.
//!
//! When a head's reachable set is a **singleton** `{L}` with no open/struct component, the indirect
//! apply is rewritten to a direct [`crate::anf::Comp::CallKnown`] / [`crate::anf::Tail::TailCallKnown`]
//! of `L` with the closure object itself as the environment — statically binding `L` (so LTO can
//! inline it) and dropping the header function-pointer load. Captures are untouched: they already
//! live in the closure object's fields, and the env atom passed is exactly the original head.
//!
//! This is **value-preserving**: `CallKnown(L, head, arg)` computes exactly what `Call(head, arg)`
//! did when `head`'s only possible value is a closure over `L`. The safety net is the `BL_NO_DEFUNC`
//! differential A/B (DIFF_FLAGS) — a bug is a wrong number the harness catches, never a false proof
//! or a use-after-free. Zero kernel/re-checker surface is added.
//!
//! Pipeline position: an ANF→ANF pass run immediately after `anf::normalize` (and after `con_tags`
//! are attached), gated by `BL_NO_DEFUNC`.

use crate::anf::{AnfFunc, AnfProgram, Comp, Tail, TailArm};

/// Rewrite pass: replace the `i`-th rewritable indirect apply (in the same deterministic order the
/// analysis recorded heads) with a direct `CallKnown`/`TailCallKnown` when `decisions[i]` is set.
struct Rewriter {
    decisions: Vec<Option<String>>,
    idx: usize,
}

impl Rewriter {
    fn comp(&mut self, c: &Comp) -> Comp {
        match c {
            Comp::Call(f, a) => {
                let d = self.decisions[self.idx].clone();
                self.idx += 1;
                match d {
                    Some(l) => Comp::CallKnown(l, f.clone(), a.clone()),
                    None => c.clone(),
                }
            }
            _ => c.clone(),
        }
    }

    fn tail(&mut self, t: &Tail) -> Tail {
        match t {
            Tail::Let(comp, rest) => {
                let c = self.comp(comp);
                let r = self.tail(rest);
                Tail::Let(c, Box::new(r))
            }
            Tail::TailCall(f, a) => {
                let d = self.decisions[self.idx].clone();
                self.idx += 1;
                match d {
                    Some(l) => Tail::TailCallKnown(l, f.clone(), a.clone()),
                    None => t.clone(),
                }
            }
            Tail::Case(scrut, arms) => Tail::Case(
                scrut.clone(),
                arms.iter()
                    .map(|arm| TailArm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        body: self.tail(&arm.body),
                    })
                    .collect(),
            ),
            Tail::Region(body) => Tail::Region(Box::new(self.tail(body))),
            // Terminal / no embedded rewritable apply.
            Tail::Ret(_)
            | Tail::Jump(_)
            | Tail::TailCallGlobal(_, _)
            | Tail::TailCallKnown(_, _, _)
            | Tail::Trampoline(_)
            | Tail::Handle { .. } => t.clone(),
        }
    }
}

/// Defunctionalize `prog`: devirtualize every singleton-flow indirect apply to a direct `CallKnown`.
pub fn defunc(prog: &AnfProgram) -> AnfProgram {
    let (cfa, sol) = crate::cfa::build(prog);

    // Decide each recorded indirect apply: devirtualize iff its head is exactly one closure, with no
    // tuple-site or open component.
    let decisions: Vec<Option<String>> = cfa
        .call_heads
        .iter()
        .map(|&h| {
            let v = &sol[h];
            if !v.open && v.sites.is_empty() && v.fns.len() == 1 {
                Some(v.fns.iter().next().unwrap().clone())
            } else {
                None
            }
        })
        .collect();

    // Nothing to do? Return the program unchanged (cheap identity).
    if decisions.iter().all(Option::is_none) {
        return prog.clone();
    }

    let mut rw = Rewriter { decisions, idx: 0 };
    let funcs: Vec<AnfFunc> = prog
        .funcs
        .iter()
        .map(|f| AnfFunc {
            name: f.name.clone(),
            recursive: f.recursive,
            body: rw.tail(&f.body),
        })
        .collect();
    let entry = rw.tail(&prog.entry);
    debug_assert_eq!(
        rw.idx,
        rw.decisions.len(),
        "rewrite visited every recorded apply"
    );

    AnfProgram {
        funcs,
        entry,
        con_tags: prog.con_tags.clone(),
    }
}
