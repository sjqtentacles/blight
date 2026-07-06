//! ANF normalization, tail-call detection, and the delay-trampoline loop (spec 7.4 tier 1).
//!
//! A-Normal Form makes evaluation order explicit: every intermediate result is bound by a `let`,
//! operands of calls/constructors are **atoms** (variables or already-evaluated values), and the
//! **tail position** of a function is syntactically apparent. This is the representation LLVM
//! codegen consumes, and it is where we perform the spec 7.4 *tier-1* tail-call optimization:
//!
//! - **Self/mutual tail calls → jumps.** A call in tail position to the enclosing (recursive)
//!   function is rewritten to a [`Tail::Jump`], which codegen emits as a back-edge (a loop)
//!   instead of a call frame. This guarantees constant stack for self-recursive loops regardless
//!   of what the LLVM tail-call pass decides.
//! - **Delay trampoline.** A `Force(e)` over a `later`-guarded recursive computation is lowered to
//!   a [`Tail::Trampoline`] loop: repeatedly step the delay until a `now` is reached, with bounded
//!   stack. This is the realistic deep-recursion path (the core has no general fixpoint; unbounded
//!   recursion arrives as the Capretta delay monad, spec 4.5).

use crate::ir::{Cir, Program};

/// An ANF *atom*: a value that requires no further evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    /// A bound variable (de Bruijn index into the ANF let-scope).
    Var(usize),
    /// A reference to the environment record's `i`-th capture (inside a lifted function).
    EnvRef(usize),
    /// A top-level function name.
    Global(String),
    /// The erased poison value.
    Erased,
}

/// An ANF *computation*: the right-hand side of a `let`, evaluated for its value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Comp {
    /// An atom (already a value).
    Atom(Atom),
    /// Allocate a closure capturing the given atoms for top-level function `name`. The [`Alloc`]
    /// tag records whether the closure record goes on the GC heap or the enclosing region's arena.
    MkClosure(String, Vec<Atom>, crate::ir::Alloc),
    /// Call a closure atom with an argument atom (non-tail; the result is bound).
    Call(Atom, Atom),
    /// A non-tail call to a *named top-level function* whose closure captures nothing (A3
    /// spine-fusion): the callee reads no environment, so codegen calls its lifted code with a null
    /// env and **skips allocating** the per-call `MkClosure(f, [])`. The non-tail analog of
    /// [`Tail::TailCallGlobal`]; emitted in [`Anfer::atomize`] for a `CallClosure(MkClosure(f, []),
    /// a)` (the curried partial-application chains structural/effectful loops build every step).
    /// Lowers through the OpNode-aware `bl_app_global`, so effects bubble identically to `Call`.
    CallGlobal(String, Atom),
    /// A non-tail *devirtualized* closure apply (P10 defunctionalization): call the statically-known
    /// lifted function `name` directly with environment atom `env` (the closure object itself, which
    /// carries the captures in its fields) and argument `arg`, binding the result. Lowers exactly like
    /// [`Comp::Call`] minus the closure-header function-pointer load: a direct `tailcc` call
    /// `name(env, arg)`. Produced ONLY by [`crate::defunc`] (a whole-program ANF→ANF pass run after
    /// normalization), which rewrites a [`Comp::Call`] whose head provably reaches only the single
    /// closure over `name`. Observationally identical to the indirect `Call`; gated end-to-end by
    /// `BL_NO_DEFUNC`.
    CallKnown(String, Atom, Atom),
    /// Build a constructor value. The [`Alloc`] tag records its allocation site.
    Con(blight_kernel::ConName, Vec<Atom>, crate::ir::Alloc),
    /// Build a tuple. The [`Alloc`] tag records its allocation site.
    Tuple(Vec<Atom>, crate::ir::Alloc),
    /// Project a tuple component.
    Proj(usize, Atom),
    /// `now a` — an immediately-available delayed value. The [`Alloc`] tag records its allocation.
    Now(Atom, crate::ir::Alloc),
    /// `later a` — a guarded delay step (a thunk atom). The [`Alloc`] tag records its allocation.
    Later(Atom, crate::ir::Alloc),
    /// Perform an effect operation.
    Op {
        effect: String,
        op: String,
        arg: Atom,
    },
    /// Call a foreign (FFI) C symbol, optionally with one argument atom, yielding its `BlValue`
    /// result (spec §7.6; the argument was added for Wave 2 / L2's `F64` hatch — mirrors
    /// [`Comp::Op`]'s single atom `arg`, see [`crate::ir::Cir::Foreign`]'s doc comment for why one
    /// atom suffices for every arity the hatch supports).
    Foreign(String, Option<Atom>),
    /// A machine-integer literal (M11): allocates a `BL_INT` value carrying the i64 payload.
    IntLit(i64),
    /// A machine-word `Nat` literal (M20): emitted when the recognizer folds a fully-canonical
    /// `Succ (… (Succ Zero))` chain. Allocates a `BL_NAT` value carrying the count in `aux`,
    /// observationally identical to the inductive chain (materialized on demand by `bl_nat_to_con`).
    NatLit(u64),
    /// A packed `String` literal (A2): emitted when the recognizer folds a fully-canonical
    /// `push`/`empty` codepoint cons-list. Lowers to one `bl_string_from_codepoints` call building a
    /// single `BL_STRING` value over a program-lifetime side buffer, observationally identical to the
    /// inductive cons-list (materialized one layer at a time on demand by `bl_string_to_con`).
    /// Codepoints are in head-first (declaration) order.
    StrLit(Vec<u64>),
    /// A primitive `Int` operation over two atoms (M11): emitted as a call to the corresponding
    /// `prim.c` runtime helper (`bl_int_add`/`…`), which unboxes both `BL_INT` operands, computes,
    /// and boxes the `BL_INT` result.
    IntPrim {
        op: blight_kernel::IntPrimOp,
        lhs: Atom,
        rhs: Atom,
    },
    /// A primitive machine-word `Nat` operation (M20), emitted by the recognizer. Lowers to a call
    /// to the corresponding `numeric.c` helper (`bl_nat_add`/`bl_nat_mul`/`bl_nat_sub`/`bl_nat_pred`)
    /// on machine-word `Nat`s. Unary (`pred`) ops leave `rhs` `None`.
    NatPrim {
        op: crate::ir::NatPrimOp,
        lhs: Atom,
        rhs: Option<Atom>,
    },
    /// A primitive fixed-point `Float` operation (M23), emitted by the recognizer. Lowers to a call
    /// to the corresponding `numeric.c` helper (`bl_float_add`/`bl_float_sub`/`bl_float_mul`/
    /// `bl_float_div`/`bl_float_neg`) over the `(mkfloat (mantissa Int))` library representation.
    /// Unary (`neg`) ops leave `rhs` `None`.
    FloatPrim {
        op: crate::ir::FloatPrimOp,
        lhs: Atom,
        rhs: Option<Atom>,
    },
}

/// An ANF *tail expression*: what a block evaluates to. Tail position is explicit here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tail {
    /// Return an atom.
    Ret(Atom),
    /// `let x = comp in rest` — bind a computation, continue (x = innermost de Bruijn 0 in rest).
    Let(Comp, Box<Tail>),
    /// A tail call to a closure atom with an argument atom (an ordinary tail call; codegen uses
    /// `tailcc`/`musttail`).
    TailCall(Atom, Atom),
    /// A tail self-call rewritten to a back-edge jump (tier-1 TCO): re-enter the current function
    /// with a new argument atom, as a loop, using **no** new stack frame.
    Jump(Atom),
    /// A direct tail call to a *named top-level function* whose closure captures nothing (M26): the
    /// callee reads no environment, so codegen calls it via `tailcc`/`musttail` with a null env and
    /// skips allocating the per-step `MkClosure(f, [])`. Emitted by the [`peephole`] pass for the
    /// `Let(MkClosure(f, []), TailCall(Var0, arg))` shape that guarded (`define-rec`) recursion
    /// produces every step; observationally identical to building the closure and tail-calling it.
    TailCallGlobal(String, Atom),
    /// A tail *devirtualized* closure apply (P10 defunctionalization): the tail analog of
    /// [`Comp::CallKnown`]. Tail-call the statically-known lifted function `name` directly with
    /// environment atom `env` (the closure object, carrying the captures) and argument `arg`, via
    /// `tailcc`/`musttail` — identical to an indirect [`Tail::TailCall`] minus the closure-header
    /// function-pointer load. Produced ONLY by [`crate::defunc`] (rewriting a [`Tail::TailCall`] whose
    /// head provably reaches only the closure over `name`); observationally identical to `TailCall`,
    /// gated by `BL_NO_DEFUNC`.
    TailCallKnown(String, Atom, Atom),
    /// `case scrut of [arm…]` in tail position.
    Case(Atom, Vec<TailArm>),
    /// `if-zero scrut then else` in tail position (T1a): a native `i64` compare-and-branch. The
    /// scrutinee is an unboxed-`Int` atom; codegen emits `icmp eq i64 %scrut, 0` and branches to the
    /// `then`/`else` continuations. Unlike [`Tail::Case`], the branches bind no variables.
    IfZero(Atom, Box<Tail>, Box<Tail>),
    /// Force a delay value to its result, driving the trampoline loop (bounded stack).
    Trampoline(Atom),
    /// A region scope `region { body }` in tail position (spec §3.5): the codegen brackets `body`
    /// with arena enter/leave so `Alloc::Arena` allocations inside are bump-allocated and reclaimed
    /// in O(1) at scope exit. The arena leave is emitted at the lexical boundary, never after a tail
    /// call (preserving the `musttail` safepoint rule, spec §7.4).
    Region(Box<Tail>),
    /// A deep effect handler in tail position. After lowering wrapped each clause in a thunk/lambda
    /// and closure conversion lifted them, the three clauses arrive here as ordinary closure *atoms*:
    /// `body` is a thunk `λ_. <computation>` (run once to start the handled computation);
    /// `return_clause` is `λx. r`; and each op clause is a curried `λx. λk. e`. The backend installs
    /// them via `bl_handle_clo`, which drives the deep-handler semantics by applying these closures
    /// through the normal calling convention.
    Handle {
        body: Atom,
        return_clause: Atom,
        op_clauses: Vec<(String, Atom)>,
    },
}

/// One arm of an ANF tail [`Tail::Case`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TailArm {
    pub con: blight_kernel::ConName,
    pub binders: usize,
    pub body: Tail,
}

/// An ANF top-level function: a body in tail form, plus whether it is recursive (so self tail
/// calls become jumps).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnfFunc {
    pub name: String,
    pub recursive: bool,
    pub body: Tail,
}

/// A whole ANF program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnfProgram {
    pub funcs: Vec<AnfFunc>,
    pub entry: Tail,
    /// Per-constructor tag: the constructor's index within its `DataDecl.constructors`. This is the
    /// value stored in a `Con` object's aux word and switched on by `case` (which uses the
    /// constructor's *declaration order* as the arm index). Empty when normalized without a
    /// signature (tests fall back to a name-derived id).
    pub con_tags: std::collections::HashMap<blight_kernel::ConName, u64>,
}

/// Build the per-constructor tag map from a signature: each constructor maps to its 0-based index
/// within its data declaration's `constructors` list (matching the `case` arm order).
pub fn con_tags_from_sig(
    sig: &blight_kernel::Signature,
) -> std::collections::HashMap<blight_kernel::ConName, u64> {
    let mut tags = std::collections::HashMap::new();
    for decl in sig.data_decls() {
        for (idx, ctor) in decl.constructors.iter().enumerate() {
            tags.insert(ctor.name.clone(), idx as u64);
        }
    }
    tags
}

/// Normalize a closure-converted [`Program`] to ANF, performing tier-1 TCO and the delay
/// trampoline transform. The A3 captureless-call spine fusion is on (see [`normalize_opts`]).
pub fn normalize(prog: &Program) -> AnfProgram {
    normalize_opts(prog, true)
}

/// Like [`normalize`], but `fuse` selects whether the A3 **captureless-call spine fusion** runs: a
/// `CallClosure(MkClosure(f, []), a)` (a captureless closure built only to be called once — the
/// per-step shape curried structural/effectful loops emit) is lowered to a direct [`Comp::CallGlobal`]
/// with **no** `MkClosure` allocation, instead of `MkClosure` + [`Comp::Call`]. Observationally
/// identical (the callee reads no env; effects still bubble through `bl_app_global`), so it is a pure
/// fast path gated by `BL_NO_SPINEFUSE` for the differential A/B bit-identity safety net. When `fuse`
/// is false the un-fused `MkClosure` + `Call` is emitted (the slow reference).
pub fn normalize_opts(prog: &Program, fuse: bool) -> AnfProgram {
    normalize_opts_raise(prog, fuse, true)
}

/// Like [`normalize_opts`] but also selects whether the **self-recursion arity-raise** runs (P2): a
/// tail self-call that rebuilds the function's *own full environment unchanged*
/// (`Let(MkClosure(self, [EnvRef(0)…EnvRef(n-1)]), TailCall(Var0, arg))` — the exact shape
/// [`crate::closure::rebind_recursive`] emits for a structural self-reference whose captured leading
/// parameters ride verbatim) is collapsed to a [`Tail::Jump`] that *reuses* the current env, instead
/// of allocating an identical closure each step. Observationally identical (the rebuilt env is a
/// byte-for-byte copy of the current one, and closures are immutable), so it is a pure fast path
/// gated by `BL_NO_ARITYRAISE` for the differential A/B bit-identity safety net. When `raise` is
/// false the un-raised `MkClosure` + `TailCall` is emitted (the slow reference).
pub fn normalize_opts_raise(prog: &Program, fuse: bool, raise: bool) -> AnfProgram {
    let funcs = prog
        .funcs
        .iter()
        .map(|f| AnfFunc {
            name: f.name.clone(),
            recursive: f.recursive,
            // Inside a function, `self` is the function itself; a tail call to `self` becomes a
            // jump. We mark the current function name so `to_tail` can recognize it.
            body: peephole(
                to_tail(&f.body, Some(&f.name), f.recursive, fuse),
                Some(&f.name),
                f.recursive,
                raise,
            ),
        })
        .collect();
    let entry = peephole(to_tail(&prog.entry, None, false, fuse), None, false, raise);
    AnfProgram {
        funcs,
        entry,
        con_tags: std::collections::HashMap::new(),
    }
}

/// Peephole over ANF tails (M26): collapse the per-step `Let(MkClosure(f, []), TailCall(Var0, arg))`
/// that guarded (`define-rec`) recursion emits — a zero-capture closure built only to be immediately
/// tail-called — into a closure-free tail. A self-call becomes a `Jump` (tier-1 TCO loop, reusing the
/// current env); a call to a different captureless function becomes a direct `TailCallGlobal` (null
/// env, the callee reads none). This removes one `bl_alloc` per recursion step. It is observationally
/// identical: the eliminated closure captures nothing, so the only thing lost is the allocation.
fn peephole(t: Tail, self_name: Option<&str>, is_rec: bool, raise: bool) -> Tail {
    match t {
        Tail::Let(Comp::MkClosure(name, caps, alloc), rest) => {
            // Fuse `Let(MkClosure(f, caps), TailCall(Var0, arg))` — a closure built only to be
            // immediately tail-called — into a closure-free tail when sound. The callee must be
            // exactly the just-built closure (de Bruijn 0) and the argument must not be that same
            // closure (so dropping the binder is sound); we shift the argument down past it.
            if let Tail::TailCall(Atom::Var(0), arg) = rest.as_ref() {
                if !matches!(arg, Atom::Var(0)) {
                    let is_self = is_rec && self_name == Some(name.as_str());
                    let arg = shift_atom_down(arg);
                    if caps.is_empty() {
                        // Captureless (M26): self → `Jump` (reuse the empty env as a loop back-edge);
                        // a different captureless function → direct `TailCallGlobal` (null env).
                        if is_self {
                            return Tail::Jump(arg);
                        }
                        return Tail::TailCallGlobal(name, arg);
                    }
                    // P2 arity-raise: a self-call rebuilding the function's *own* full environment
                    // unchanged (`caps == [EnvRef(0), …, EnvRef(n-1)]`, the identity capture that
                    // `rebind_recursive` emits for a structural self-reference) is a `Jump` that
                    // reuses the current env — no per-step closure alloc. The rebuilt env is a
                    // byte-identical copy of the current one, so reusing it is observationally
                    // identical. Anything else (a permuted/changed capture, or a non-self target)
                    // keeps the explicit `MkClosure`.
                    if raise
                        && is_self
                        && caps
                            .iter()
                            .enumerate()
                            .all(|(i, c)| matches!(c, Atom::EnvRef(k) if *k == i))
                    {
                        return Tail::Jump(arg);
                    }
                }
            }
            Tail::Let(
                Comp::MkClosure(name, caps, alloc),
                Box::new(peephole(*rest, self_name, is_rec, raise)),
            )
        }
        Tail::Let(comp, rest) => {
            Tail::Let(comp, Box::new(peephole(*rest, self_name, is_rec, raise)))
        }
        Tail::Case(scrut, arms) => Tail::Case(
            scrut,
            arms.into_iter()
                .map(|a| TailArm {
                    con: a.con,
                    binders: a.binders,
                    body: peephole(a.body, self_name, is_rec, raise),
                })
                .collect(),
        ),
        Tail::IfZero(scrut, then_, else_) => Tail::IfZero(
            scrut,
            Box::new(peephole(*then_, self_name, is_rec, raise)),
            Box::new(peephole(*else_, self_name, is_rec, raise)),
        ),
        Tail::Region(body) => Tail::Region(Box::new(peephole(*body, self_name, is_rec, raise))),
        // Other tails contain no nested `Tail` to rewrite.
        other => other,
    }
}

/// Shift a free atom variable down by one (used when [`peephole`] removes a `let` binder). The atom
/// here is the argument of a `TailCall(Var0, arg)`; it was elaborated under the removed binder, so a
/// `Var(i)` for `i >= 1` refers one binder out. `Var(0)` is the removed closure itself and is
/// excluded by the caller, so we never underflow.
fn shift_atom_down(a: &Atom) -> Atom {
    match a {
        Atom::Var(i) if *i >= 1 => Atom::Var(i - 1),
        _ => a.clone(),
    }
}

/// A fresh-binder counter encoded purely through the de Bruijn discipline: when we `let`-bind a
/// computation, the continuation runs under one extra binder, so existing atoms must be shifted.
/// We avoid global gensym by building bottom-up.
///
/// Convert a `Cir` expression into a tail expression. `self_name` is the enclosing recursive
/// function's name (for self-tail-call→jump); `is_rec` says whether the function is recursive
/// (a `Fix`-derived function calling itself).
fn to_tail(c: &Cir, self_name: Option<&str>, is_rec: bool, fuse: bool) -> Tail {
    // Build by ANF-ing into a sequence of lets ending in a tail.
    let mut binder = Anfer::new(self_name, is_rec, fuse);
    binder.tail(c, &Shift::default())
}

struct Anfer<'a> {
    self_name: Option<&'a str>,
    is_rec: bool,
    /// A3: fuse a `CallClosure(MkClosure(f, []), a)` to a direct [`Comp::CallGlobal`] (no closure
    /// alloc). Off → emit the un-fused `MkClosure` + `Call` (the `BL_NO_SPINEFUSE` slow reference).
    fuse: bool,
}

/// A deferred de Bruijn shift, threaded lazily through [`Anfer::atomize`]/[`Anfer::seq`] instead of
/// eagerly rewriting whole subtrees (M29). Conceptually it is a composition of frames, each a
/// `(cutoff, by)` step: a free variable `i` is mapped to `i + Σ{ by_k : i >= cutoff_k }`. We only
/// ever materialize the shift at `Cir::Var` leaves, so a chain of `n` nested `let`s costs Θ(n)
/// O(1) frame-pushes (a shared persistent cons cell — no `Vec` copy, no structural tree clone) plus
/// one resolution per variable occurrence. The old code instead rebuilt the entire body subtree at
/// every `let` level (`shift_cir_under`), which is what made normalization O(n²).
///
/// **Coordinates.** `lift` counts the binders entered since the function root. A frame stores its
/// threshold `thresh0` and the `base` lift at which it was created; because entering a binder pushes
/// every previously-free variable one index deeper, the frame's *current* effective cutoff is
/// `thresh0 + (lift - base)`. This lets [`Shift::under_binders`] be O(1) (just bump `lift`, share the
/// frame list) and [`Shift::pushed`] be O(1) (cons one frame), so a deep `let` chain does no
/// per-level allocation beyond the single new frame.
#[derive(Clone, Default)]
struct Shift {
    head: Option<std::rc::Rc<ShiftFrame>>,
    lift: usize,
}

struct ShiftFrame {
    /// Threshold in the coordinate system current when this frame was pushed.
    thresh0: usize,
    /// The `lift` value when this frame was pushed (frames created later have a larger base).
    base: usize,
    by: usize,
    next: Option<std::rc::Rc<ShiftFrame>>,
}

impl Shift {
    /// Resolve a free variable index under this deferred shift. The frame list is kept sorted by
    /// effective cutoff ascending from the head (see [`Self::pushed`]), so once a frame's effective
    /// cutoff exceeds `i` every older frame does too and we can stop — making the common shallow
    /// variables (e.g. `Var(0)` in a deep `let` chain) O(1) and the whole normalization ~linear.
    fn apply(&self, i: usize) -> usize {
        let mut total = 0usize;
        let mut cur = self.head.as_deref();
        while let Some(f) = cur {
            // Effective cutoff now = thresh0 + (lift - base) (the variable has sunk `lift - base`
            // indices deeper since the frame was recorded).
            let eff_cutoff = f.thresh0 + (self.lift - f.base);
            if i < eff_cutoff {
                break;
            }
            total += f.by;
            cur = f.next.as_deref();
        }
        i + total
    }

    /// Compute a frame's current effective cutoff.
    fn eff(&self, f: &ShiftFrame) -> usize {
        f.thresh0 + (self.lift - f.base)
    }

    /// Compose an additional `(out_cutoff, by)` step applied *after* the existing shift: variables
    /// whose already-shifted index is `>= out_cutoff` gain a further `+by`. Functional composition
    /// requires translating `out_cutoff` back into this shift's *input* coordinate, i.e. the
    /// smallest input index whose output reaches `out_cutoff`. Because [`Self::apply`] is monotone
    /// non-decreasing, that threshold is well-defined; `out_cutoff` is tiny in practice (1 for a let
    /// body, the arm's binder count for a case), so the search is O(out_cutoff). The new frame is
    /// spliced into the list at its sorted (effective-cutoff) position, preserving the ascending
    /// invariant `apply` relies on; for a `let` chain the new frame's cutoff is the smallest so it
    /// lands at the head in O(1).
    fn pushed(&self, out_cutoff: usize, by: usize) -> Shift {
        if by == 0 {
            return self.clone();
        }
        let mut t = 0usize;
        while self.apply(t) < out_cutoff {
            t += 1;
        }
        let new_eff = t; // base == lift, so effective cutoff == thresh0 == t right now.
                         // Walk to the sorted insertion point: collect the (shorter) prefix of frames whose effective
                         // cutoff is strictly below `new_eff`, then cons the new frame, then keep the shared tail.
        let mut prefix: Vec<&ShiftFrame> = Vec::new();
        let mut cur = self.head.as_deref();
        while let Some(f) = cur {
            if self.eff(f) < new_eff {
                prefix.push(f);
                cur = f.next.as_deref();
            } else {
                break;
            }
        }
        // Rebuild from the unchanged shared tail (`cur`'s cell, still in `self`'s list) outward.
        // The frames that follow the new one are exactly the original frames whose effective cutoff
        // is `>= new_eff` — i.e. the ones *not* in `prefix` — so the shared tail starts at index
        // `prefix.len()`. (Using `prefix.len() + 1` dropped the first such frame, silently losing a
        // shift step when composing two `pushed`s — e.g. `s.pushed(0,a).pushed(0,b)` collapsed to
        // `+max(a,b)`-ish instead of `+a+b`.)
        let mut tail: Option<std::rc::Rc<ShiftFrame>> = Self::rc_at(&self.head, prefix.len());
        // Cons the new frame onto the shared tail, then the prefix frames back on top.
        tail = Some(std::rc::Rc::new(ShiftFrame {
            thresh0: t,
            base: self.lift,
            by,
            next: tail,
        }));
        for f in prefix.iter().rev() {
            tail = Some(std::rc::Rc::new(ShiftFrame {
                thresh0: f.thresh0,
                base: f.base,
                by: f.by,
                next: tail,
            }));
        }
        Shift {
            head: tail,
            lift: self.lift,
        }
    }

    /// Return the shared `Rc` cons cell at position `n` (0 = head) in a list, cloning the `Rc`
    /// handle (cheap, ref-count bump) so the unchanged tail stays structurally shared.
    fn rc_at(head: &Option<std::rc::Rc<ShiftFrame>>, n: usize) -> Option<std::rc::Rc<ShiftFrame>> {
        let mut cur = head.clone();
        for _ in 0..n {
            cur = cur.and_then(|c| c.next.clone());
        }
        cur
    }

    /// Lift this shift under one freshly-introduced inner binder (e.g. entering a `let` body): the
    /// new binder is index 0 and must never be shifted, and every previously-free variable is now
    /// one index deeper. O(1): bump `lift` and share the frame list (effective cutoffs all rise by
    /// one via the `lift - base` term in [`Self::apply`], so index 0 stays protected). Adding the
    /// same delta to every frame preserves their relative order, so the sorted invariant holds.
    fn under_binder(&self) -> Shift {
        self.under_binders(1)
    }

    /// Lift this shift under `n` freshly-introduced inner binders at once (e.g. a `Case` arm's
    /// constructor-field binders). O(1) (shares the frame list).
    fn under_binders(&self, n: usize) -> Shift {
        Shift {
            head: self.head.clone(),
            lift: self.lift + n,
        }
    }
}

impl<'a> Anfer<'a> {
    fn new(self_name: Option<&'a str>, is_rec: bool, fuse: bool) -> Self {
        Anfer {
            self_name,
            is_rec,
            fuse,
        }
    }

    /// Emit `c` in tail position under deferred shift `s` (identity at a function/arm entry; M29).
    fn tail(&mut self, c: &Cir, s: &Shift) -> Tail {
        match c {
            // A tail force becomes the trampoline loop.
            Cir::Force(e) => {
                let mut binds = Vec::new();
                let atom = self.atomize(e, s, &mut binds);
                wrap(binds, Tail::Trampoline(atom))
            }
            // A tail call: detect self-call → jump.
            Cir::CallClosure(f, a) => {
                // Self tail-call → `Jump` (a bounded-stack loop back-edge). A *captureless* self
                // closure (`MkClosure(self, [])`, the shape closure conversion gives a self
                // reference) applied in tail position re-enters the current function as a loop. We
                // atomize ONLY the argument under the current shift — building no closure — which is
                // both the bounded-stack win the elim-loop transform needs and the *correct* de
                // Bruijn handling: sequencing the closure head first (below) pushes a `let` that the
                // argument's variable references must skip, and for a *computed* argument (e.g. the
                // elim-loop's state tuple) that shift was being dropped. Observationally identical to
                // building the closure and tail-calling it (it captures nothing).
                if let (Some(sn), true) = (self.self_name, self.is_rec) {
                    if let Cir::MkClosure(name, caps, _) = f.as_ref() {
                        if name == sn && caps.is_empty() {
                            let mut binds = Vec::new();
                            let aa = self.atomize(a, s, &mut binds);
                            return wrap(binds, Tail::Jump(aa));
                        }
                    }
                }
                // Sequence the callee then the argument, keeping the de Bruijn discipline straight
                // (each `let` introduced for `f` shifts the vars seen by `a`, and vice versa).
                let mut binds = Vec::new();
                let mut atoms = self.seq(&[(**f).clone(), (**a).clone()], s, &mut binds);
                let aa = atoms.pop().unwrap();
                let fa = atoms.pop().unwrap();
                // Is the callee a self-reference closure? After CC, a self call is `MkClosure(self
                // name)` or the recursive function's own closure. We recognize a direct global to
                // the current function.
                if let (Some(sn), true) = (self.self_name, self.is_rec) {
                    if is_self_closure(&fa, sn) {
                        return wrap(binds, Tail::Jump(aa));
                    }
                }
                wrap(binds, Tail::TailCall(fa, aa))
            }
            Cir::App(f, a) => {
                // App should have become CallClosure after CC; handle defensively as a call.
                self.tail(&Cir::CallClosure(f.clone(), a.clone()), s)
            }
            Cir::Case(scrut, arms) => {
                let mut binds = Vec::new();
                let satom = self.atomize(scrut, s, &mut binds);
                let pushed = binds.len();
                let arms2 = arms
                    .iter()
                    .map(|arm| TailArm {
                        con: arm.con.clone(),
                        binders: arm.binders,
                        // Codegen evaluates the scrutinee (emitting `binds` as `pushed` slots), then
                        // pushes this arm's `arm.binders` field slots on top before running the
                        // body. So the body's references to the *outer* scope must skip those
                        // `pushed` scrutinee slots — shift them up. The arm's own field binders stay
                        // below the cutoff and are untouched. (M29) We thread this as a deferred
                        // shift rather than rebuilding the arm body (old `shift_cir_under`): lift the
                        // incoming shift under the field binders, then compose the `+pushed` skip.
                        body: {
                            let arm_shift =
                                s.under_binders(arm.binders).pushed(arm.binders, pushed);
                            let mut inner = Anfer::new(self.self_name, self.is_rec, self.fuse);
                            inner.tail(&arm.body, &arm_shift)
                        },
                    })
                    .collect();
                wrap(binds, Tail::Case(satom, arms2))
            }
            Cir::IfZero {
                scrut,
                then_,
                else_,
            } => {
                // Evaluate the scrutinee (emitting `binds` as `pushed` slots), then branch. The
                // branches bind NO variables (unlike a `Case` arm), so — exactly like `Case` with
                // `arm.binders == 0` — their bodies must skip the `pushed` scrutinee slots that sit
                // between them and the outer scope. Each branch is a fresh control-flow path, so it
                // gets its own `Anfer` (fresh-var counter), mirroring the per-arm `Case` handling.
                let mut binds = Vec::new();
                let satom = self.atomize(scrut, s, &mut binds);
                let pushed = binds.len();
                let branch_shift = s.pushed(0, pushed);
                let then_t = {
                    let mut inner = Anfer::new(self.self_name, self.is_rec, self.fuse);
                    inner.tail(then_, &branch_shift)
                };
                let else_t = {
                    let mut inner = Anfer::new(self.self_name, self.is_rec, self.fuse);
                    inner.tail(else_, &branch_shift)
                };
                wrap(
                    binds,
                    Tail::IfZero(satom, Box::new(then_t), Box::new(else_t)),
                )
            }
            Cir::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                // After lowering + closure conversion each clause is a closure value (MkClosure).
                // Sequence all of them through `seq` so the de Bruijn indices stay correct as each
                // closure-construction `let` shifts the ones bound before it, then install via
                // `bl_handle_clo`.
                let mut subs = Vec::with_capacity(2 + op_clauses.len());
                subs.push((**body).clone());
                subs.push((**return_clause).clone());
                for (_, e) in op_clauses {
                    subs.push(e.clone());
                }
                let mut binds = Vec::new();
                let atoms = self.seq(&subs, s, &mut binds);
                let body_a = atoms[0].clone();
                let ret_a = atoms[1].clone();
                let ops = op_clauses
                    .iter()
                    .enumerate()
                    .map(|(i, (n, _))| (n.clone(), atoms[2 + i].clone()))
                    .collect();
                wrap(
                    binds,
                    Tail::Handle {
                        body: body_a,
                        return_clause: ret_a,
                        op_clauses: ops,
                    },
                )
            }
            // A `let` in tail position: emit its binding(s) and keep the *body* in tail position, so
            // a tail call / case nested under the let still becomes a `Jump`/`Tail::Case` rather than
            // being atomized into a `Ret`. Mirrors the `atomize` `Cir::Let` de Bruijn discipline (M29):
            // ANF the value into `nv` slots, name it with one alias slot, then shift the body under the
            // new binder by `+nv`. (Without this arm a tail `let`—e.g. the elim-loop's `let s = state
            // in self (…)`—would fall through to the `_` atomize+`Ret` case and lose its tail call.)
            Cir::Let(v, b) => {
                let mut binds = Vec::new();
                let va = self.atomize(v, s, &mut binds);
                let nv = binds.len();
                binds.push(Comp::Atom(va));
                let body_shift = s.under_binder().pushed(1, nv);
                let body_tail = self.tail(b, &body_shift);
                wrap(binds, body_tail)
            }
            // A region scope in tail position: bracket its body with arena enter/leave. The body
            // is re-ANFed in tail position so its own tail call / case lands inside the scope.
            Cir::Region(body) => {
                let mut inner = Anfer::new(self.self_name, self.is_rec, self.fuse);
                Tail::Region(Box::new(inner.tail(body, s)))
            }
            // Otherwise, atomize to a value and return it.
            _ => {
                let mut binds = Vec::new();
                let atom = self.atomize(c, s, &mut binds);
                wrap(binds, Tail::Ret(atom))
            }
        }
    }

    /// ANF-normalize `c`, pushing its `let`-binding [`Comp`]s onto the shared `out` accumulator
    /// (innermost last) and returning the [`Atom`] that names its value.
    ///
    /// **De Bruijn discipline.** The result is understood relative to a scope `S` (the scope in
    /// which `c` lives). Each `Comp` pushed onto `out` extends `S` by one slot; the returned `atom`
    /// and every `Atom::Var` occurring inside the pushed `Comp`s are indices into that *extended
    /// innermost* scope. This is the exact model codegen uses (`Tail::Let` pushes one slot; `Var(0)`
    /// is the innermost). Honoring it is essential: when we sequence several sub-expressions
    /// (constructor fields, call operands), each new `let` shifts every variable that was already in
    /// scope, so we shift as we go via [`Self::seq`]. (M29) Streaming into a shared `out` makes the
    /// whole normalization Θ(total nodes) instead of re-copying a growing binds `Vec` per level.
    fn atomize(&mut self, c: &Cir, s: &Shift, out: &mut Vec<Comp>) -> Atom {
        match c {
            // A free variable resolves under the deferred shift (M29): instead of having rebuilt a
            // shifted copy of the whole enclosing subtree, we add the accumulated offset here.
            Cir::Var(i) => Atom::Var(s.apply(*i)),
            Cir::EnvRef(k) => Atom::EnvRef(*k),
            Cir::Global(g) => Atom::Global(g.clone()),
            Cir::Erased => Atom::Erased,

            Cir::MkClosure(name, caps, al) => {
                let atoms = self.seq(caps, s, out);
                out.push(Comp::MkClosure(name.clone(), atoms, *al));
                Atom::Var(0)
            }
            Cir::CallClosure(f, a) | Cir::App(f, a) => {
                // A3 spine fusion: if the callee is a *captureless* closure of a named global
                // (`MkClosure(name, [])`) — the per-step shape a curried structural/effectful loop
                // emits for each partial application — skip building that closure entirely and emit a
                // direct `CallGlobal`. The argument is atomized under the *unchanged* shift `s` (no
                // phantom closure binder is introduced), so no de Bruijn surgery is needed and the
                // result still binds `Var(0)` exactly as `Call` does. Observationally identical: the
                // callee reads no env, and effects still bubble (via `bl_app_global`).
                if self.fuse {
                    if let Cir::MkClosure(name, caps, _) = f.as_ref() {
                        if caps.is_empty() {
                            let aa = self.atomize(a, s, out);
                            out.push(Comp::CallGlobal(name.clone(), aa));
                            return Atom::Var(0);
                        }
                    }
                }
                let mut atoms = self.seq(&[(**f).clone(), (**a).clone()], s, out);
                let aa = atoms.pop().unwrap();
                let fa = atoms.pop().unwrap();
                out.push(Comp::Call(fa, aa));
                Atom::Var(0)
            }
            Cir::Con(name, args, al) => {
                let atoms = self.seq(args, s, out);
                out.push(Comp::Con(name.clone(), atoms, *al));
                Atom::Var(0)
            }
            Cir::Tuple(args, al) => {
                let atoms = self.seq(args, s, out);
                out.push(Comp::Tuple(atoms, *al));
                Atom::Var(0)
            }
            Cir::Proj(i, e) => {
                let a = self.atomize(e, s, out);
                out.push(Comp::Proj(*i, a));
                Atom::Var(0)
            }
            Cir::Now(e, al) => {
                let a = self.atomize(e, s, out);
                out.push(Comp::Now(a, *al));
                Atom::Var(0)
            }
            Cir::Later(e, al) => {
                let a = self.atomize(e, s, out);
                out.push(Comp::Later(a, *al));
                Atom::Var(0)
            }
            Cir::Force(e) => {
                // A non-tail force still trampolines; bind its result.
                let a = self.atomize(e, s, out);
                out.push(Comp::Now(a, crate::ir::Alloc::Gc));
                Atom::Var(0)
            }
            Cir::Op { effect, op, arg } => {
                let a = self.atomize(arg, s, out);
                out.push(Comp::Op {
                    effect: effect.clone(),
                    op: op.clone(),
                    arg: a,
                });
                Atom::Var(0)
            }
            Cir::Foreign(sym, arg) => {
                let a = arg.as_ref().map(|a| self.atomize(a, s, out));
                out.push(Comp::Foreign(sym.clone(), a));
                Atom::Var(0)
            }
            Cir::IntLit(n) => {
                out.push(Comp::IntLit(*n));
                Atom::Var(0)
            }
            Cir::NatLit(n) => {
                out.push(Comp::NatLit(*n));
                Atom::Var(0)
            }
            Cir::StrLit(cps) => {
                out.push(Comp::StrLit(cps.clone()));
                Atom::Var(0)
            }
            Cir::IntPrim { op, lhs, rhs } => {
                let mut atoms = self.seq(&[(**lhs).clone(), (**rhs).clone()], s, out);
                let ra = atoms.pop().unwrap();
                let la = atoms.pop().unwrap();
                out.push(Comp::IntPrim {
                    op: *op,
                    lhs: la,
                    rhs: ra,
                });
                Atom::Var(0)
            }
            Cir::NatPrim { op, lhs, rhs } => {
                // Sequence the operand(s) left-to-right (mirrors IntPrim). A unary `pred` has no rhs.
                match rhs {
                    Some(r) => {
                        let mut atoms = self.seq(&[(**lhs).clone(), (**r).clone()], s, out);
                        let ra = atoms.pop().unwrap();
                        let la = atoms.pop().unwrap();
                        out.push(Comp::NatPrim {
                            op: *op,
                            lhs: la,
                            rhs: Some(ra),
                        });
                        Atom::Var(0)
                    }
                    None => {
                        let mut atoms = self.seq(&[(**lhs).clone()], s, out);
                        let la = atoms.pop().unwrap();
                        out.push(Comp::NatPrim {
                            op: *op,
                            lhs: la,
                            rhs: None,
                        });
                        Atom::Var(0)
                    }
                }
            }
            Cir::FloatPrim { op, lhs, rhs } => {
                // Identical sequencing to NatPrim. A unary `neg` has no rhs.
                match rhs {
                    Some(r) => {
                        let mut atoms = self.seq(&[(**lhs).clone(), (**r).clone()], s, out);
                        let ra = atoms.pop().unwrap();
                        let la = atoms.pop().unwrap();
                        out.push(Comp::FloatPrim {
                            op: *op,
                            lhs: la,
                            rhs: Some(ra),
                        });
                        Atom::Var(0)
                    }
                    None => {
                        let mut atoms = self.seq(&[(**lhs).clone()], s, out);
                        let la = atoms.pop().unwrap();
                        out.push(Comp::FloatPrim {
                            op: *op,
                            lhs: la,
                            rhs: None,
                        });
                        Atom::Var(0)
                    }
                }
            }
            // A `Let` binds one variable that the body refers to as de Bruijn 0. We ANF the bound
            // value into `nv` slots, add one slot naming its result, then ANF the body. The body
            // already counts the let binder as index 0; its references to the *outer* scope (index
            // >= 1) must skip the `nv` value-slots we inserted between the binder and that scope.
            // (M29) Rather than rebuild a shifted copy of `b` (the old `shift_cir_under`, O(body) per
            // level → O(n²) over a let chain), we extend the deferred `Shift`: lift it under the new
            // binder (protecting index 0) and compose the `+nv` skip at cutoff 1. Binds stream
            // straight into the shared `out` accumulator, so the chain costs Θ(n) total (no
            // per-level `Vec` copy).
            Cir::Let(v, b) => {
                let before = out.len();
                let va = self.atomize(v, s, out);
                let nv = out.len() - before;
                out.push(Comp::Atom(va));
                let body_shift = s.under_binder().pushed(1, nv);
                self.atomize(b, &body_shift, out)
            }
            Cir::Lam(_)
            | Cir::Fix(_)
            | Cir::Case(_, _)
            | Cir::IfZero { .. }
            | Cir::Handle { .. } => {
                // Control-flow forms (and lambdas/fix) don't appear as sub-atoms post-CC for the
                // programs we compile — a branch reaches ANF in tail position (a function body or a
                // match/if-zero arm). Emit a poison atom rather than panicking so the pure-Rust
                // pipeline is total. (Same contract as `Cir::Case`; non-tail `if-zero` is unsupported,
                // exactly as non-tail `match` is.)
                Atom::Erased
            }
            // A flattened product (A1): a *single* allocation whose runtime slots are the
            // left-to-right concatenation of its logical fields' slots — a `Leaf` contributes its one
            // atomized pointer slot, a `Nested` sub-product contributes its own slots inline (no
            // separate allocation/indirection). We collect every embedded leaf `Cir` in slot order,
            // ANF them through `seq` (so the de Bruijn shifts compose exactly as for `Con`/`Tuple`
            // fields), and emit one wide `Comp::Con`/`Comp::Tuple`. Because every slot is a `BlValue`
            // pointer, the resulting object is traced by the GC's uniform `nfields`-pointer walk with
            // no tracer change (A1d). The constructor tag, when present, is the parent's — nested
            // tags are erased because their cells no longer exist as distinct objects (flatten.rs only
            // fires when each nested field is consumed purely by leaf projection, never matched on).
            Cir::Flat {
                tag,
                fields,
                total_slots,
                alloc,
            } => {
                let leaves = flatten_leaf_cirs(fields);
                debug_assert_eq!(
                    leaves.len(),
                    *total_slots,
                    "Flat total_slots must equal the flattened leaf count"
                );
                let atoms = self.seq(&leaves, s, out);
                match tag {
                    Some(con) => out.push(Comp::Con(con.clone(), atoms, *alloc)),
                    None => out.push(Comp::Tuple(atoms, *alloc)),
                }
                Atom::Var(0)
            }
            // A projection over a flattened product (A1): `index` is already the *physical* pointer
            // slot offset of the target leaf within the parent object (flatten.rs resolved the
            // logical projection chain — including drilling through inlined nested sub-products —
            // down to one slot via its layout walk). flatten.rs only emits a `FlatProj` whose target
            // is a `Leaf` (a single pointer slot); a whole nested sub-product is never projected out
            // (it has no standalone cell), so the offset names exactly one slot and lowers to the
            // ordinary `Comp::Proj` over the parent object.
            Cir::FlatProj {
                index,
                layout: _,
                scrut,
            } => {
                let a = self.atomize(scrut, s, out);
                out.push(Comp::Proj(*index, a));
                Atom::Var(0)
            }
            // A region scope in non-tail position: atomize the body for its value. Arena bracketing
            // only fires for tail-position regions (the common `(region r …)` shape, where the body
            // is the region's result); a non-tail region keeps its allocations on the GC heap, which
            // is always safe.
            Cir::Region(body) => self.atomize(body, s, out),
        }
    }

    /// ANF a left-to-right sequence of sub-expressions (constructor fields, call operands), keeping
    /// the de Bruijn discipline straight. Each sub-expression `cs[k]` is atomized in a scope already
    /// extended by all the `let`s emitted for `cs[0..k]`, so we defer its free-var shift by that
    /// running count. Symmetrically, every atom we have *already* produced is shifted up as later
    /// sub-expressions push more `let`s, so the returned `atoms` are all consistent in the final
    /// innermost scope. Binds stream into the shared `out` accumulator.
    fn seq(&mut self, cs: &[Cir], s: &Shift, out: &mut Vec<Comp>) -> Vec<Atom> {
        // `s` resolves each operand relative to the scope as it is *on entry* to this `seq` — i.e.
        // with the `out_start` comps already present in the shared accumulator (the caller calibrated
        // `s` to exactly that). So the extra binders a later operand must skip are only the ones
        // emitted *within this `seq`*, `out.len() - out_start`, NOT the absolute `out.len()`. Using
        // the absolute count double-skips any comps already in `out` when `seq` is entered with a
        // non-empty accumulator — which happens when a `Let` arm pushes its binding's comps and then
        // atomizes a body that is itself a constructor/operand (a `Let` directly inside a `Con`/
        // `Tuple`/`Op` argument), the shape CSE introduces.
        let out_start = out.len();
        let mut atoms: Vec<Atom> = Vec::with_capacity(cs.len());
        for c in cs {
            let pre = out.len();
            let before = pre - out_start;
            // Defer this sub-expression's free-var shift past the `let`s emitted *within this seq* so
            // far (cutoff 0, uniform +before) instead of eagerly rebuilding `c` (old `shift_cir`).
            let sub = s.pushed(0, before);
            let a = self.atomize(c, &sub, out);
            let added = out.len() - pre;
            // Everything produced so far becomes `added` slots further from the innermost scope.
            // These are already-resolved concrete atoms, so they shift directly.
            for atom in atoms.iter_mut() {
                *atom = shift_atom(atom, 0, added);
            }
            atoms.push(a);
        }
        atoms
    }
}

/// Wrap a tail expression in a sequence of `let` bindings (innermost last).
fn wrap(binds: Vec<Comp>, tail: Tail) -> Tail {
    binds
        .into_iter()
        .rev()
        .fold(tail, |acc, comp| Tail::Let(comp, Box::new(acc)))
}

/// Collect, in physical slot order, the leaf `Cir` values of a flattened product's logical fields
/// (A1). A `Leaf` contributes its own value; a `Nested` sub-product contributes its slots' leaves
/// recursively, inline. The returned `Vec` length equals the product's `total_slots`, and feeding it
/// through [`Anfer::seq`] yields one wide allocation with every slot a `BlValue` pointer.
fn flatten_leaf_cirs(fields: &[crate::ir::FlatField]) -> Vec<Cir> {
    let mut out = Vec::new();
    fn go(f: &crate::ir::FlatField, out: &mut Vec<Cir>) {
        match f {
            crate::ir::FlatField::Leaf(c) => out.push((**c).clone()),
            crate::ir::FlatField::Nested { slots, .. } => {
                for s in slots {
                    go(s, out);
                }
            }
        }
    }
    for f in fields {
        go(f, &mut out);
    }
    out
}

/// Is atom `a` a closure of the current self function `sn`? After CC, the recursive self-reference
/// is the function's own closure; we recognize a direct global to `sn`. (A `MkClosure(sn, …)` is
/// reduced to a global by the time it reaches here in the simple programs we target.)
fn is_self_closure(a: &Atom, sn: &str) -> bool {
    matches!(a, Atom::Global(g) if g == sn)
}

/// Shift a free atom var by `by` if at/above `depth` (used when an atom crosses introduced lets).
fn shift_atom(a: &Atom, depth: usize, by: usize) -> Atom {
    match a {
        Atom::Var(i) if *i >= depth => Atom::Var(i + by),
        _ => a.clone(),
    }
}

/// Does this tail expression name every call (i.e. is it in ANF)? A structural check used by tests:
/// every `Call`/`MkClosure`/`Con`/`Tuple`/`Proj`/`Op` appears as a `let`-bound [`Comp`], never
/// nested inside another computation's operand (operands are [`Atom`]s by construction).
pub fn is_anf(t: &Tail) -> bool {
    match t {
        Tail::Ret(_) | Tail::TailCall(_, _) | Tail::Jump(_) | Tail::Trampoline(_) => true,
        Tail::TailCallGlobal(_, _) | Tail::TailCallKnown(_, _, _) => true,
        Tail::Let(_comp, rest) => is_anf(rest),
        Tail::Case(_, arms) => arms.iter().all(|a| is_anf(&a.body)),
        Tail::IfZero(_, t, e) => is_anf(t) && is_anf(e),
        Tail::Region(body) => is_anf(body),
        Tail::Handle {
            body: _,
            return_clause: _,
            op_clauses: _,
        } => true,
    }
}

/// Does `t` contain a [`Tail::Jump`] (a self-tail-call turned into a loop)?
pub fn has_jump(t: &Tail) -> bool {
    match t {
        Tail::Jump(_) => true,
        Tail::Ret(_) | Tail::TailCall(_, _) | Tail::Trampoline(_) => false,
        Tail::TailCallGlobal(_, _) | Tail::TailCallKnown(_, _, _) => false,
        Tail::Let(_, rest) => has_jump(rest),
        Tail::Case(_, arms) => arms.iter().any(|a| has_jump(&a.body)),
        Tail::IfZero(_, t, e) => has_jump(t) || has_jump(e),
        Tail::Region(body) => has_jump(body),
        Tail::Handle {
            body: _,
            return_clause: _,
            op_clauses: _,
        } => false,
    }
}

/// Does `t` contain a [`Tail::Trampoline`]?
pub fn has_trampoline(t: &Tail) -> bool {
    match t {
        Tail::Trampoline(_) => true,
        Tail::Ret(_) | Tail::TailCall(_, _) | Tail::Jump(_) => false,
        Tail::TailCallGlobal(_, _) | Tail::TailCallKnown(_, _, _) => false,
        Tail::Let(_, rest) => has_trampoline(rest),
        Tail::Case(_, arms) => arms.iter().any(|a| has_trampoline(&a.body)),
        Tail::IfZero(_, t, e) => has_trampoline(t) || has_trampoline(e),
        Tail::Region(body) => has_trampoline(body),
        Tail::Handle {
            body: _,
            return_clause: _,
            op_clauses: _,
        } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Func;
    use blight_kernel::ConName;

    /// An `Alloc::Arena` tag on an allocation inside a `Cir::Region` survives ANF normalization: the
    /// region becomes a `Tail::Region` and the allocation's `Comp` carries the same tag (pass-through
    /// threading, spec §3.5).
    #[test]
    fn tags_survive_anf() {
        use crate::ir::Alloc;
        // entry = region { Con "Zero" [] @Arena }
        let entry = Cir::Region(Box::new(Cir::Con(
            ConName("Zero".into()),
            vec![],
            Alloc::Arena,
        )));
        let prog = Program {
            funcs: vec![],
            entry,
        };
        let anf = normalize(&prog);
        let Tail::Region(inner) = &anf.entry else {
            panic!("region scope must become a Tail::Region: {:?}", anf.entry);
        };
        // The body is `let x = Con Zero @Arena in Ret x`.
        let Tail::Let(Comp::Con(_, _, alloc), _) = inner.as_ref() else {
            panic!("region body must bind the constructor: {inner:?}");
        };
        assert_eq!(*alloc, Alloc::Arena, "the Arena tag must survive ANF");
    }

    /// Every call is named: ANF-ing a nested application produces only `let`-bound calls with atom
    /// operands.
    #[test]
    fn anf_names_all_calls() {
        // entry = f (g x)  -> after CC: CallClosure(f, CallClosure(g, x))
        let term = Cir::CallClosure(
            Box::new(Cir::Global("f".into())),
            Box::new(Cir::CallClosure(
                Box::new(Cir::Global("g".into())),
                Box::new(Cir::Var(0)),
            )),
        );
        let prog = Program {
            funcs: vec![],
            entry: term,
        };
        let anf = normalize(&prog);
        assert!(is_anf(&anf.entry), "entry is in ANF: {:?}", anf.entry);
        // The inner call (g x) is let-bound, and the outer is a tail call.
        match &anf.entry {
            Tail::Let(Comp::Call(g, _), rest) => {
                assert_eq!(*g, Atom::Global("g".into()));
                assert!(matches!(**rest, Tail::TailCall(Atom::Global(_), _)));
            }
            other => panic!("expected let-bound inner call, got {other:?}"),
        }
    }

    /// A self tail call in a recursive function becomes a `Jump` (a loop), not a call.
    #[test]
    fn self_tailcall_becomes_loop() {
        // function `loop`: body = CallClosure(Global "loop", Var 0)  (tail self-call)
        let func = Func {
            name: "loop".into(),
            recursive: true,
            body: Cir::CallClosure(Box::new(Cir::Global("loop".into())), Box::new(Cir::Var(0))),
        };
        let prog = Program {
            funcs: vec![func],
            entry: Cir::Erased,
        };
        let anf = normalize(&prog);
        let loopf = &anf.funcs[0];
        assert!(
            has_jump(&loopf.body),
            "self tail call became a jump: {:?}",
            loopf.body
        );
        assert!(!matches!(loopf.body, Tail::TailCall(_, _)));
    }

    /// M26: a zero-capture self-closure built only to be immediately tail-called collapses to a
    /// `Jump` (no per-step `MkClosure` alloc), reusing the current env as a loop back-edge.
    #[test]
    fn captureless_self_closure_call_becomes_jump() {
        use crate::ir::Alloc;
        // `let c = MkClosure("f", []) in TailCall(Var0=c, Var1=arg)` inside recursive `f`.
        let body = Tail::Let(
            Comp::MkClosure("f".into(), vec![], Alloc::Gc),
            Box::new(Tail::TailCall(Atom::Var(0), Atom::Var(1))),
        );
        let out = peephole(body, Some("f"), true, true);
        match out {
            // The argument `Var(1)` shifts down to `Var(0)` once the closure binder is removed.
            Tail::Jump(Atom::Var(0)) => {}
            other => panic!("expected Jump(Var0), got {other:?}"),
        }
    }

    /// P2 arity-raise: a self-call rebuilding the function's *own* full environment unchanged
    /// (`MkClosure(self, [EnvRef(0), EnvRef(1)])` — the identity capture a structural self-reference
    /// emits) collapses to a `Jump` that reuses the current env, eliminating the per-step alloc.
    #[test]
    fn identity_env_self_rebuild_becomes_jump() {
        use crate::ir::Alloc;
        // `let c = MkClosure("f", [EnvRef0, EnvRef1]) in TailCall(Var0=c, Var1=arg)` inside rec `f`.
        let body = Tail::Let(
            Comp::MkClosure(
                "f".into(),
                vec![Atom::EnvRef(0), Atom::EnvRef(1)],
                Alloc::Gc,
            ),
            Box::new(Tail::TailCall(Atom::Var(0), Atom::Var(1))),
        );
        match peephole(body.clone(), Some("f"), true, true) {
            Tail::Jump(Atom::Var(0)) => {}
            other => panic!("expected Jump(Var0), got {other:?}"),
        }
        // With the raise OFF (BL_NO_ARITYRAISE), the explicit closure rebuild is preserved.
        assert!(matches!(
            peephole(body, Some("f"), true, false),
            Tail::Let(Comp::MkClosure(_, _, _), _)
        ));
    }

    /// The arity-raise must NOT fire when the rebuilt env is not the *identity* of the current env
    /// (a permuted or partial capture would change the env the loop runs with), nor for a non-self
    /// target. Both keep the explicit `MkClosure`.
    #[test]
    fn non_identity_env_rebuild_is_not_raised() {
        use crate::ir::Alloc;
        // Permuted env: [EnvRef1, EnvRef0] is a *different* env than the current [EnvRef0, EnvRef1].
        let permuted = Tail::Let(
            Comp::MkClosure(
                "f".into(),
                vec![Atom::EnvRef(1), Atom::EnvRef(0)],
                Alloc::Gc,
            ),
            Box::new(Tail::TailCall(Atom::Var(0), Atom::Var(1))),
        );
        assert!(matches!(
            peephole(permuted, Some("f"), true, true),
            Tail::Let(Comp::MkClosure(_, _, _), _)
        ));
        // Identity env but a *different* function name: not a self-call, so no jump (and a non-empty
        // env can't become a `TailCallGlobal`, which passes a null env).
        let other = Tail::Let(
            Comp::MkClosure("g".into(), vec![Atom::EnvRef(0)], Alloc::Gc),
            Box::new(Tail::TailCall(Atom::Var(0), Atom::Var(1))),
        );
        assert!(matches!(
            peephole(other, Some("f"), true, true),
            Tail::Let(Comp::MkClosure(_, _, _), _)
        ));
    }

    /// M26: a zero-capture closure of a *different* captureless function, immediately tail-called,
    /// collapses to a direct `TailCallGlobal` (null env), not a `Jump`.
    #[test]
    fn captureless_other_closure_call_becomes_global() {
        use crate::ir::Alloc;
        let body = Tail::Let(
            Comp::MkClosure("g".into(), vec![], Alloc::Gc),
            Box::new(Tail::TailCall(Atom::Var(0), Atom::Var(2))),
        );
        let out = peephole(body, Some("f"), true, true);
        match out {
            Tail::TailCallGlobal(name, Atom::Var(1)) => assert_eq!(name, "g"),
            other => panic!("expected TailCallGlobal(g, Var1), got {other:?}"),
        }
    }

    /// The fuse must NOT fire when the closure captures something (the env is load-bearing) or when
    /// the argument is the closure itself (dropping the binder would be unsound).
    #[test]
    fn peephole_preserves_capturing_or_self_arg() {
        use crate::ir::Alloc;
        let capturing = Tail::Let(
            Comp::MkClosure("f".into(), vec![Atom::Var(3)], Alloc::Gc),
            Box::new(Tail::TailCall(Atom::Var(0), Atom::Var(1))),
        );
        assert!(matches!(
            peephole(capturing, Some("f"), true, true),
            Tail::Let(Comp::MkClosure(_, _, _), _)
        ));
        let self_arg = Tail::Let(
            Comp::MkClosure("f".into(), vec![], Alloc::Gc),
            Box::new(Tail::TailCall(Atom::Var(0), Atom::Var(0))),
        );
        assert!(matches!(
            peephole(self_arg, Some("f"), true, true),
            Tail::Let(Comp::MkClosure(_, _, _), _)
        ));
    }

    /// A `Let` nested directly inside a constructor operand, whose body references **both** the
    /// `let` binder and an outer binder, must thread de Bruijn indices through the binding's own
    /// emitted slots exactly once. Regression for the M29 deferred-shift double-skip: `seq` measured
    /// the binders to skip as the *absolute* accumulator length rather than the comps emitted within
    /// the `seq`, so a `Let`-bearing operand (the shape CSE introduces) double-counted the binding's
    /// slots and corrupted the inner indices.
    /// `pushed` must compose: shifting at cutoff 0 by `a` then by `b` adds `a+b` to every index,
    /// regardless of any pre-existing frames. A frame-dropping bug in `pushed`'s tail splice would
    /// silently lose the earlier `+a`.
    #[test]
    fn pushed_composes_at_cutoff_zero() {
        // Start from a non-trivial base shift with a frame (cutoff 2, +1) like an arm shift.
        let base = Shift::default().under_binders(2).pushed(2, 1);
        let body = base.under_binder(); // like a let body
        for i in 0..6 {
            let once = body.pushed(0, 1);
            let twice = body.pushed(0, 1).pushed(0, 1);
            assert_eq!(
                once.apply(i),
                body.apply(i) + 1,
                "single pushed(0,1) at i={i}"
            );
            assert_eq!(
                twice.apply(i),
                body.apply(i) + 2,
                "composed pushed(0,1).pushed(0,1) at i={i}"
            );
        }
    }

    #[test]
    fn let_inside_operand_threads_indices() {
        use crate::ir::Alloc;
        // entry = let x = 5 in ( (let y = 9 in (y, x)) , x )
        let inner = Cir::Let(
            Box::new(Cir::NatLit(9)),
            Box::new(Cir::Tuple(vec![Cir::Var(0), Cir::Var(1)], Alloc::Gc)),
        );
        let term = Cir::Let(
            Box::new(Cir::NatLit(5)),
            Box::new(Cir::Tuple(vec![inner, Cir::Var(0)], Alloc::Gc)),
        );
        let prog = Program {
            funcs: vec![],
            entry: term,
        };
        let anf = normalize(&prog);
        // Walk to the inner pair (the first of the two `Tuple` lets) and the outer pair.
        fn nth_tuple(t: &Tail, want: usize) -> Vec<Atom> {
            let mut seen = 0;
            let mut cur = t;
            loop {
                match cur {
                    Tail::Let(Comp::Tuple(atoms, _), rest) => {
                        if seen == want {
                            return atoms.clone();
                        }
                        seen += 1;
                        cur = rest;
                    }
                    Tail::Let(_, rest) => cur = rest,
                    _ => panic!("ran out of tuples at {want}: {t:?}"),
                }
            }
        }
        // Slots (innermost→outer at the inner pair): y(0), 9(1), x(2), 5(3). So inner pair = (y, x) =
        // (Var0, Var2). The outer pair, one slot deeper, is (innerpair, x) = (Var0, Var3).
        assert_eq!(nth_tuple(&anf.entry, 0), vec![Atom::Var(0), Atom::Var(2)]);
        assert_eq!(nth_tuple(&anf.entry, 1), vec![Atom::Var(0), Atom::Var(3)]);
    }

    /// Sequencing several non-trivial sub-expressions keeps the de Bruijn discipline straight: a
    /// constructor whose two fields each bind a computation must reference the *earlier* field's
    /// result at the correctly-shifted index (it sits one slot further from the innermost once the
    /// second field's `let` is introduced). Regression: the old `atomize` ignored shifting, so the
    /// first field pointed at the wrong slot.
    #[test]
    fn seq_shifts_earlier_atoms() {
        use crate::ir::Alloc;
        // entry = Pair( g x , h x )  → after CC: Tuple[ CallClosure(g,x), CallClosure(h,x) ]
        let term = Cir::Tuple(
            vec![
                Cir::CallClosure(Box::new(Cir::Global("g".into())), Box::new(Cir::Var(0))),
                Cir::CallClosure(Box::new(Cir::Global("h".into())), Box::new(Cir::Var(0))),
            ],
            Alloc::Gc,
        );
        let prog = Program {
            funcs: vec![],
            entry: term,
        };
        let anf = normalize(&prog);
        // entry = let a = g x ; let b = h x ; ret (Tuple [a, b]) — where the final Tuple names the
        // first call as Var(1) (now one slot deeper) and the second as Var(0).
        let Tail::Let(Comp::Call(_, _), rest1) = &anf.entry else {
            panic!("first call let: {:?}", anf.entry);
        };
        let Tail::Let(Comp::Call(_, _), rest2) = &**rest1 else {
            panic!("second call let: {rest1:?}");
        };
        let Tail::Let(Comp::Tuple(atoms, _), _) = &**rest2 else {
            panic!("tuple let: {rest2:?}");
        };
        assert_eq!(
            atoms,
            &vec![Atom::Var(1), Atom::Var(0)],
            "earlier field shifted past the later field's let"
        );
    }

    /// Build a right-nested `Cir::Let` chain of depth `n` whose innermost body refers to the
    /// outermost binder, so normalization must thread indices across the whole chain:
    /// `let x0 = Zero in let x1 = Succ[x0] in … in Succ[x_{n-1}]` (each value references the
    /// previous binder). This is the shape that exposes the O(n²) re-shifting: normalizing each
    /// outer `let` historically re-walked and copied the entire inner chain.
    fn deep_let_chain(n: usize) -> Cir {
        use crate::ir::Alloc;
        // Innermost body: `Succ[ Var(0) ]` (refers to the last-bound var).
        let mut body = Cir::Con(ConName("Succ".into()), vec![Cir::Var(0)], Alloc::Gc);
        for _ in 0..n {
            // each level: `let v = Con Succ [Var0] in <body>` — value refers to the enclosing binder,
            // body refers to this new one as Var0.
            let value = Cir::Con(ConName("Succ".into()), vec![Cir::Var(0)], Alloc::Gc);
            body = Cir::Let(Box::new(value), Box::new(body));
        }
        // Outermost binder names a base `Zero`.
        Cir::Let(
            Box::new(Cir::Con(ConName("Zero".into()), vec![], Alloc::Gc)),
            Box::new(body),
        )
    }

    /// Normalizing a deep `let` chain stays ~linear (M29). We assert a *scaling* invariant rather
    /// than an absolute time: doubling the depth must not anywhere near quadruple the work. We count
    /// the emitted `Tail::Let` nodes (which must be exactly linear in depth) and check the wall-time
    /// ratio is sub-quadratic, which fails loudly if the O(n²) re-shifting ever returns.
    #[test]
    fn deep_let_chain_normalizes_linearly() {
        use std::time::Instant;
        fn count_lets(t: &Tail) -> usize {
            match t {
                Tail::Let(_, rest) => 1 + count_lets(rest),
                Tail::Region(b) => count_lets(b),
                Tail::Case(_, arms) => arms.iter().map(|a| count_lets(&a.body)).sum(),
                Tail::IfZero(_, t, e) => count_lets(t) + count_lets(e),
                _ => 0,
            }
        }
        let time_depth = |n: usize| -> (u128, usize) {
            let prog = Program {
                funcs: vec![],
                entry: deep_let_chain(n),
            };
            let t0 = Instant::now();
            let anf = normalize(&prog);
            (t0.elapsed().as_micros().max(1), count_lets(&anf.entry))
        };
        // Linear in the structural count: a depth-n chain emits Θ(n) lets.
        let (_, c1) = time_depth(50);
        let (_, c2) = time_depth(100);
        assert!(
            c2 >= 2 * c1 - 10 && c2 <= 2 * c1 + 10,
            "let count must scale linearly with depth: {c1} → {c2}"
        );
        // Wall-time scaling guard (loose, to avoid CI flakiness): 8× the depth must cost far less
        // than the ~64× a quadratic pass would. We compare 30 vs 240 and require < 30× (a true
        // O(n²) is ≥ 64×; linear is ~8×; 30× leaves generous slack for noise and constant factors).
        let (t_small, _) = time_depth(30);
        let (t_big, _) = time_depth(240);
        assert!(
            t_big < t_small * 30,
            "deep-let normalization must be sub-quadratic: 30 took {t_small}µs, 240 took \
             {t_big}µs (ratio {:.1}×; quadratic would be ~64×)",
            t_big as f64 / t_small as f64
        );
    }

    /// Does some [`Comp`] in `t` match `pred`?
    fn any_comp(t: &Tail, pred: &dyn Fn(&Comp) -> bool) -> bool {
        match t {
            Tail::Let(c, rest) => pred(c) || any_comp(rest, pred),
            Tail::Case(_, arms) => arms.iter().any(|a| any_comp(&a.body, pred)),
            Tail::IfZero(_, t, e) => any_comp(t, pred) || any_comp(e, pred),
            Tail::Region(b) => any_comp(b, pred),
            _ => false,
        }
    }

    /// A3: a *non-tail* call whose callee is a captureless closure of a named global
    /// (`CallClosure(MkClosure(f, []), a)` — the per-step partial-application shape) fuses to a
    /// direct `Comp::CallGlobal(f, a)` with **no** `MkClosure` alloc when spine fusion is on.
    #[test]
    fn captureless_nontail_call_fuses_to_callglobal() {
        use crate::ir::Alloc;
        // entry = Tuple[ CallClosure(MkClosure("f", []), Var0) ]  — the call is a field, so it is
        // atomized in *non-tail* position (exercising `atomize`, not `tail`).
        let call = Cir::CallClosure(
            Box::new(Cir::MkClosure("f".into(), vec![], Alloc::Gc)),
            Box::new(Cir::Var(0)),
        );
        let prog = Program {
            funcs: vec![],
            entry: Cir::Tuple(vec![call], Alloc::Gc),
        };
        let on = normalize_opts(&prog, true);
        assert!(
            any_comp(
                &on.entry,
                &|c| matches!(c, Comp::CallGlobal(n, _) if n == "f")
            ),
            "fused build emits CallGlobal(f): {:?}",
            on.entry
        );
        assert!(
            !any_comp(
                &on.entry,
                &|c| matches!(c, Comp::MkClosure(_, caps, _) if caps.is_empty())
            ),
            "fused build builds no captureless MkClosure: {:?}",
            on.entry
        );
        assert!(
            !any_comp(&on.entry, &|c| matches!(c, Comp::Call(_, _))),
            "fused build emits no generic Call for the captureless callee: {:?}",
            on.entry
        );
    }

    /// A3: with spine fusion *off* (`BL_NO_SPINEFUSE`), the same program emits the un-fused
    /// `MkClosure(f, []) + Call` reference shape and **no** `CallGlobal` — the differential slow path.
    #[test]
    fn captureless_nontail_call_unfused_when_disabled() {
        use crate::ir::Alloc;
        let call = Cir::CallClosure(
            Box::new(Cir::MkClosure("f".into(), vec![], Alloc::Gc)),
            Box::new(Cir::Var(0)),
        );
        let prog = Program {
            funcs: vec![],
            entry: Cir::Tuple(vec![call], Alloc::Gc),
        };
        let off = normalize_opts(&prog, false);
        assert!(
            !any_comp(&off.entry, &|c| matches!(c, Comp::CallGlobal(_, _))),
            "unfused build emits no CallGlobal: {:?}",
            off.entry
        );
        assert!(
            any_comp(
                &off.entry,
                &|c| matches!(c, Comp::MkClosure(n, caps, _) if n == "f" && caps.is_empty())
            ),
            "unfused build builds the captureless MkClosure(f, []): {:?}",
            off.entry
        );
        assert!(
            any_comp(&off.entry, &|c| matches!(c, Comp::Call(_, _))),
            "unfused build emits a generic Call: {:?}",
            off.entry
        );
    }

    /// A3: the fusion must NOT fire when the closure *captures* something — its env is load-bearing,
    /// so the call cannot become a null-env `CallGlobal`. The capturing `MkClosure` + `Call` survives
    /// even with fusion on.
    #[test]
    fn capturing_nontail_call_not_fused() {
        use crate::ir::Alloc;
        // CallClosure(MkClosure("f", [Var1]), Var0) — non-empty captures.
        let call = Cir::CallClosure(
            Box::new(Cir::MkClosure("f".into(), vec![Cir::Var(1)], Alloc::Gc)),
            Box::new(Cir::Var(0)),
        );
        let prog = Program {
            funcs: vec![],
            entry: Cir::Tuple(vec![call], Alloc::Gc),
        };
        let on = normalize_opts(&prog, true);
        assert!(
            !any_comp(&on.entry, &|c| matches!(c, Comp::CallGlobal(_, _))),
            "a capturing closure call must not fuse to CallGlobal: {:?}",
            on.entry
        );
        assert!(
            any_comp(
                &on.entry,
                &|c| matches!(c, Comp::MkClosure(n, caps, _) if n == "f" && caps.len() == 1)
            ),
            "the capturing MkClosure(f, [Var1]) survives: {:?}",
            on.entry
        );
    }
}
