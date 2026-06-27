//! The backend compiler IR (`Cir`) — spec §7.1, the representation downstream of the spore.
//!
//! `Cir` is deliberately *distinct* from the kernel [`blight_kernel::Term`]: it carries only
//! runtime-relevant structure. By the time a term reaches the backend it has been **checked** by
//! the spore and **erased** ([`blight_kernel::erase::erase`]) of all grade-`0` content, so the
//! entire type layer (`Univ`, `Pi`/`Sigma`-as-types, the cubical Kan machinery) is gone or
//! degenerate. What remains is a small untyped functional core: variables, functions and calls,
//! tuples/projections, tagged sums with a constructor-index `case`, the delay monad, and effect
//! operations/handlers.
//!
//! ## Recursion (the load-bearing design point, verified against the elaborator)
//! The kernel core has **no general fixpoint**. Recursion arrives in exactly two shapes:
//! - *structural* recursion is an [`blight_kernel::Term::Elim`] fold (the recursion is the
//!   eliminator unrolling, with an induction hypothesis supplied per recursive field). Lowered to
//!   [`Cir::Case`] plus inserted recursive eliminations.
//! - *general / partial* recursion is a `later (self a…)` guarded self-reference of type
//!   `Delay A` (the Capretta delay monad, spec §4.5). Lowered to a [`Cir::Fix`] self-binding whose
//!   body produces a [`Cir::Later`]; the runtime *delay trampoline* forces the chain in a loop
//!   with bounded stack, which is how unbounded recursion runs without overflow.
//!
//! Nodes use de Bruijn indices for locals (matching the kernel), until closure conversion
//! ([`crate::closure`]) lifts lambdas to named top-level functions with explicit environments.

use blight_kernel::ConName;

/// Where an allocation is placed (spec §3.5 / §7.3). The default is the garbage-collected heap;
/// the untrusted region escape analysis ([`crate::region`]) flips an allocation to [`Alloc::Arena`]
/// when it provably does not outlive its enclosing [`Cir::Region`] scope, so the runtime can
/// bump-allocate it in the region's arena and reclaim it in O(1) at scope exit — bypassing the GC.
///
/// This tag is *behavior-irrelevant* for the term's value: a miscompile (wrongly choosing `Arena`)
/// is a memory-safety bug the analysis must prevent, never an unsoundness in the type theory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Alloc {
    /// The garbage-collected heap (the safe default; any value may live here).
    #[default]
    Gc,
    /// The enclosing region's bump arena: reclaimed in O(1) when the region scope exits.
    Arena,
}

/// The backend IR: an untyped functional core (spec §7.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cir {
    /// A local variable (de Bruijn index), or — after closure conversion — a reference into the
    /// current function's environment/parameters (see [`crate::closure`]).
    Var(usize),
    /// A reference to a lifted top-level function by name (produced by closure conversion).
    Global(String),
    /// `λ. body` — a single-argument function (multi-arg functions are curried, matching the
    /// kernel's `Lam`). Before closure conversion these may capture free variables.
    Lam(Box<Cir>),
    /// `f a` — application.
    App(Box<Cir>, Box<Cir>),
    /// `let x = e in body` — a (non-recursive) binding; `body` is under one new binder. Introduced
    /// by ANF and by lowering of `Now`/sequencing.
    Let(Box<Cir>, Box<Cir>),
    /// `fix self. body` — a recursive self-binding for `later`-guarded partial recursion. `self`
    /// (de Bruijn 0 in `body`) refers to the recursive function itself; `body` is expected to be a
    /// function whose recursive calls are wrapped in [`Cir::Later`]. The runtime delay trampoline
    /// drives this to a loop.
    Fix(Box<Cir>),

    /// A constructor value `Con c args` — a tagged record. The tag is the constructor's index in
    /// its data declaration (resolved during lowering / codegen via the signature). The [`Alloc`]
    /// tag records where the record is allocated (GC heap by default; arena if the region analysis
    /// proved it non-escaping).
    Con(ConName, Vec<Cir>, Alloc),
    /// `case scrut of [arm…]` — eliminate a constructor value by switching on its tag. Each arm
    /// binds the (kept, post-erasure) fields of its constructor as fresh innermost binders, plus —
    /// for each recursive field — the induction-hypothesis value (the recursive elimination over
    /// that field), mirroring `do_elim` (`normalize.rs`). Arms are positionally aligned with the
    /// data declaration's constructors.
    Case(Box<Cir>, Vec<Arm>),
    /// `Tuple [e…]` — an anonymous product (the runtime rep of `Pair`/records). N-ary for
    /// convenience; the lowering of kernel `Pair` produces binary tuples. The [`Alloc`] tag records
    /// where the tuple is allocated.
    Tuple(Vec<Cir>, Alloc),
    /// `Proj i e` — project the `i`-th component of a tuple (the rep of `Fst`/`Snd`).
    Proj(usize, Box<Cir>),

    // ---- the delay monad (spec §4.5), the partial-recursion runtime substrate ----
    /// `now e : Delay A` — an immediately-available value. The [`Alloc`] tag records where the
    /// delay node is allocated.
    Now(Box<Cir>, Alloc),
    /// `later e : Delay A` — a guarded step; the trampoline forces it on the next loop iteration.
    /// The [`Alloc`] tag records where the delay node is allocated.
    Later(Box<Cir>, Alloc),
    /// `force e` — drive a `Delay A` to its value by trampolining `Later` steps (bounded stack).
    Force(Box<Cir>),

    // ---- regions (spec §3.5) ----
    /// `region { body }` — a lexical arena scope. At runtime the backend brackets `body` with
    /// `bl_arena_enter()`/`bl_arena_leave(mark)`; allocations inside `body` that the escape analysis
    /// tagged [`Alloc::Arena`] are bump-allocated in this region's arena and reclaimed in O(1) on
    /// exit. Carries no binder of its own — the region capability was already consumed at the term
    /// level (the desugared grade-1 λ), so this node only marks the dynamic extent of the arena.
    Region(Box<Cir>),

    // ---- effects (spec §4), if not fully handled before codegen ----
    /// `perform op a` — invoke an effect operation; bubbles to the nearest enclosing `Handle`.
    Op {
        effect: String,
        op: String,
        arg: Box<Cir>,
    },
    /// `handle body { return x. r ; (op x k. e)… }` — a deep handler. `return_clause` binds 1
    /// var; each op clause binds `x` (de Bruijn 1) then continuation `k` (de Bruijn 0).
    Handle {
        body: Box<Cir>,
        return_clause: Box<Cir>,
        op_clauses: Vec<(String, Cir)>,
    },

    /// An opaque/erased placeholder. Should never be reached at runtime in a well-graded program
    /// (it only stands in for a dropped grade-`0` position that a later pass removes). Codegen
    /// treats it as an unreachable poison value.
    Erased,

    // ---- post-closure-conversion nodes (introduced by [`crate::closure`]) ----
    /// `mkclosure f [env…]` — allocate a closure capturing `env` for the lifted top-level function
    /// named `f`. The function's first parameter is the environment record. Produced by closure
    /// conversion; absent before it. The [`Alloc`] tag records where the closure record is placed.
    MkClosure(String, Vec<Cir>, Alloc),
    /// `envref i` — project the `i`-th captured value from the *current function's* environment
    /// record. Only valid inside a lifted function body.
    EnvRef(usize),
    /// `callclosure f a` — apply a closure value `f` to argument `a` (the runtime unpacks the
    /// environment and tail-calls the lifted code). Produced by closure conversion in place of
    /// `App` whose head is a closure.
    CallClosure(Box<Cir>, Box<Cir>),

    /// `foreign "sym"` — the value produced by calling the external C function `sym()` (an opaque
    /// trusted FFI postulate, spec §7.6). The C symbol takes no arguments and returns a `BlValue`
    /// (so a function-typed foreign is a C thunk returning a Blight closure). The kernel trusts it;
    /// the re-checker declines any term mentioning it. Has no de Bruijn content.
    Foreign(String),

    // ---- primitive machine integers (M11) ----
    /// An `Int` literal — a boxed `BL_INT` machine integer (`i64` in `header.aux`). Has no de
    /// Bruijn content. (`IntTy`, being a type, is erased before reaching the backend.)
    IntLit(i64),
    /// A primitive `Int` operation on two operands, lowered to a runtime helper call
    /// (`bl_int_add/sub/mul/div/eq/lt`). Comparisons produce a `BL_INT` `1`/`0`.
    IntPrim {
        op: blight_kernel::IntPrimOp,
        lhs: Box<Cir>,
        rhs: Box<Cir>,
    },
}

/// A lifted top-level function (the output of closure conversion). The body refers to its single
/// value parameter as de Bruijn 0 and to captured free variables via [`Cir::EnvRef`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Func {
    /// The generated unique name.
    pub name: String,
    /// `true` if this is a recursive (`Fix`-derived) function: the runtime binds the closure to
    /// its own name so the body can call itself.
    pub recursive: bool,
    /// The function body, under one parameter binder (de Bruijn 0 = the argument).
    pub body: Cir,
}

/// A whole closure-converted program: the lifted functions plus the entry expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub funcs: Vec<Func>,
    pub entry: Cir,
}

/// One arm of a [`Cir::Case`]: the constructor it matches and its body. The body is elaborated in
/// a scope extended with the constructor's kept fields and their induction hypotheses (innermost
/// last), so it refers to them by de Bruijn index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Arm {
    /// The constructor this arm matches.
    pub con: ConName,
    /// The number of binders this arm introduces (kept fields + one IH per recursive field). Kept
    /// for codegen to know how many values to bind before running `body`.
    pub binders: usize,
    /// The arm body, under `binders` new innermost binders.
    pub body: Cir,
}

impl Cir {
    /// Smart constructor for a GC-heap constructor value (the default allocation).
    pub fn con(name: ConName, args: Vec<Cir>) -> Cir {
        Cir::Con(name, args, Alloc::Gc)
    }

    /// Smart constructor for a GC-heap tuple (the default allocation).
    pub fn tuple(args: Vec<Cir>) -> Cir {
        Cir::Tuple(args, Alloc::Gc)
    }

    /// Smart constructor for a GC-heap `now` delay node (the default allocation).
    pub fn now(e: Cir) -> Cir {
        Cir::Now(Box::new(e), Alloc::Gc)
    }

    /// Smart constructor for a GC-heap `later` delay node (the default allocation).
    pub fn later(e: Cir) -> Cir {
        Cir::Later(Box::new(e), Alloc::Gc)
    }

    /// Smart constructor for a GC-heap closure record (the default allocation).
    pub fn mkclosure(name: String, env: Vec<Cir>) -> Cir {
        Cir::MkClosure(name, env, Alloc::Gc)
    }

    /// Smart constructor for an application spine `f a1 a2 …`.
    pub fn apply(head: Cir, args: impl IntoIterator<Item = Cir>) -> Cir {
        args.into_iter()
            .fold(head, |f, a| Cir::App(Box::new(f), Box::new(a)))
    }

    /// Collect an application spine `((f a1) a2) …` into `(f, [a1, a2, …])`.
    pub fn unapply(&self) -> (&Cir, Vec<&Cir>) {
        let mut args = Vec::new();
        let mut head = self;
        while let Cir::App(f, a) = head {
            args.push(a.as_ref());
            head = f.as_ref();
        }
        args.reverse();
        (head, args)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The IR composes: an application spine round-trips through `apply`/`unapply`.
    #[test]
    fn cir_ir_constructs() {
        let spine = Cir::apply(
            Cir::Global("f".into()),
            [Cir::Var(0), Cir::Var(1), Cir::now(Cir::Var(2))],
        );
        let (head, args) = spine.unapply();
        assert_eq!(head, &Cir::Global("f".into()));
        assert_eq!(args.len(), 3);
        assert_eq!(args[0], &Cir::Var(0));

        // A case with one arm binding two values.
        let case = Cir::Case(
            Box::new(Cir::Var(0)),
            vec![Arm {
                con: ConName("Succ".into()),
                binders: 2,
                body: Cir::Var(0),
            }],
        );
        match case {
            Cir::Case(_, arms) => assert_eq!(arms[0].binders, 2),
            _ => unreachable!(),
        }

        // The delay/effect nodes construct.
        let _ = Cir::Force(Box::new(Cir::later(Cir::now(Cir::Erased))));
        let _ = Cir::Fix(Box::new(Cir::Lam(Box::new(Cir::Var(0)))));
    }

    /// A `Cir::Region` scope wraps a body, and the allocating nodes default to GC allocation while
    /// also being constructible at `Arena`.
    #[test]
    fn cir_region_constructs() {
        let scope = Cir::Region(Box::new(Cir::tuple(vec![Cir::Var(0), Cir::Var(1)])));
        match &scope {
            Cir::Region(body) => match body.as_ref() {
                Cir::Tuple(elems, alloc) => {
                    assert_eq!(elems.len(), 2);
                    assert_eq!(*alloc, Alloc::Gc, "smart constructor defaults to GC");
                }
                other => panic!("expected a tuple body, got {other:?}"),
            },
            other => panic!("expected a region scope, got {other:?}"),
        }

        // Every allocating variant carries an Alloc tag, defaulting to Gc via its smart ctor and
        // settable to Arena explicitly.
        assert_eq!(
            Cir::con(ConName("Zero".into()), vec![]),
            Cir::Con(ConName("Zero".into()), vec![], Alloc::Gc)
        );
        let arena_con = Cir::Con(ConName("Zero".into()), vec![], Alloc::Arena);
        assert!(matches!(arena_con, Cir::Con(_, _, Alloc::Arena)));
        assert!(matches!(
            Cir::mkclosure("f".into(), vec![]),
            Cir::MkClosure(_, _, Alloc::Gc)
        ));
        assert!(matches!(Cir::now(Cir::Erased), Cir::Now(_, Alloc::Gc)));
        assert!(matches!(Cir::later(Cir::Erased), Cir::Later(_, Alloc::Gc)));
    }
}
