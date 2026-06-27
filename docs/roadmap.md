# Blight capabilities roadmap

A sourced, honest answer to the questions people actually ask: **can Blight do strings? be fast? do
I/O? build games?** And for each missing capability: **where would it live, and does it touch the
trusted kernel?**

The single organizing principle of Blight is a **tiny trusted kernel + an independent re-checker**.
Soundness rests on two small type-checkers agreeing, not on one large trusted compiler. So the only
question that really matters for any new feature is:

> Does it enlarge the **TCB** (the trusted kernel, [`crates/blight-kernel`](../crates/blight-kernel)),
> or can it be built as **untrusted tower** code (runtime C, codegen, elaborator sugar, `.bl`
> libraries) that the kernel still checks?

Anything in the tower can be wrong and at worst produce a wrong *answer*; it can never mint a false
`Proof`. Anything in the kernel is trusted forever. The roadmap below classifies each capability on
exactly that axis.

> The two unproven research corners (quantities × cubical; graded effects + normalization) now have
> evidence-backed notes in [docs/metatheory.md](metatheory.md), reporting the kernel's *measured*
> behavior at grade 0/1 rather than speculation.

## What the kernel already has (this surprises people)

Reading [`crates/blight-kernel/src/term.rs`](../crates/blight-kernel/src/term.rs), the core term
grammar **already includes**:

- **Algebraic effects + handlers** — `Op { effect, op, arg }`, `Handle { … }`, and the effectful
  computation type `EffTy(Row, A)` (spec §4). There is a working native runtime for them
  ([`runtime/effects.c`](../crates/blight-codegen/runtime/effects.c)): **full CPS deep handlers with
  multi-shot delimited continuations** (not merely tail-resumptive), via an effect trampoline. See
  [`examples/effects_demo.bl`](../examples/effects_demo.bl).
- **Partiality** — `Delay A`, `now`, `later` (spec §4.5), driven by the `bl_force` trampoline in
  bounded C stack (the 1,000,000-deep test).
- **Inductives, dependent types, a cubical layer, graded (quantitative) binders.**

What the kernel **deliberately does not have**: any *primitive base type*. There is no `Int`,
`Float`, `Char`, array, or string in `Term` — only `Data`/`Con`/`Elim` over user-declared
inductives. That is why `Nat` is unary and `String` is a cons-list of unary codepoints. This absence
is the whole point: the kernel stays small enough to audit.

## Capability table

| capability | status | lives in | touches TCB? |
|---|---|---|---|
| **String output** | ✅ done this pass | runtime + codegen + elaborator sugar | **No** |
| **Algebraic effects / handlers** | ✅ in kernel + runtime | kernel (type), runtime (handlers) | already in TCB |
| **Bounded-stack deep recursion** | ✅ done | kernel (`Delay`), runtime (`bl_force`) | already in TCB |
| **Console / file I/O** | ⏳ designable now | a `Console`/`IO` *effect* + runtime handler | **No** (handlers are untrusted) |
| **Unboxed `Int`/`Float` arithmetic** | ✖ not yet | kernel primitives **or** untrusted FFI escape hatch | **Yes** (kernel) *or* No (FFI, with cost) |
| **Mutable arrays** | ✖ not yet | effect + runtime, or linear/graded discipline | mostly No |
| **Growable heap** | ✖ fixed 64 MiB | runtime (`gc.c`) | **No** |
| **FFI to C** | ✖ not yet | codegen + an untrusted `foreign` decl | **No** (but unchecked) |
| **Frame loop / real-time games** | ✖ not yet | IO effect + a host driver loop | **No** |

## Strings — delivered (no TCB change)

Done in this pass, entirely in the tower:

- **Runtime** ([`runtime/prelude_rt.c`](../crates/blight-codegen/runtime/prelude_rt.c)): a
  `bl_print_string` that walks the `push`/`empty` spine and `putchar`s each decoded codepoint.
- **Codegen** ([`driver.rs`](../crates/blight-codegen/src/driver.rs)): `build_binary` authors a
  `main` that dispatches to `bl_print_string` when `main : String`, else `bl_print`.
- **Reader/elaborator sugar**: `"hi"` in term position desugars to the `push`/`empty` `Con` chain
  and `?A` to a codepoint `Nat`. The kernel still only ever sees `Con`s — no new term form.

The kernel is byte-for-byte unchanged; `git diff --stat crates/blight-kernel` is empty. See
[`examples/`](../examples/): `hello_string.bl`, `string_reverse.bl`, `string_length.bl`,
`palindrome.bl`, `caesar.bl`, and the ASCII-render `ascii_box.bl`.

**Caveat:** strings are still *unary-codepoint cons lists*, so they are O(n) heap and slow for big
text. Fast strings want unboxed bytes, which is the `Int`/array story below.

## Console / file I/O — the realistic next brick (no TCB change)

Because the **effect system is already in the kernel**, real I/O does **not** need a kernel change.
The design:

1. Declare a `Console` effect in a `.bl` library: `(effect Console (print String Unit) (read Unit String))`.
2. A program that does I/O has type `! ⟨Console⟩ A` — the effect row tracks it; this is fully
   kernel-checked today.
3. Provide an **untrusted runtime handler** in C (alongside `effects.c`) that interprets `print` by
   calling `bl_print_string` and `read` by reading stdin, re-installing itself (deep handler).
4. `build_binary` installs the top-level `Console` handler in the authored `main`.

Why the **re-checker declines** (rather than rejects) a *cubical or foreign* `main`, while it now
**checks effectful programs at the type level**: the independent re-checker re-derives the types of
`perform`/`handle`/`! E A` (consulting the kernel's operation signatures) but does not track effect
rows or continuation grades — so an effectful program is a genuine second opinion at the type level
(**Checked**), and only the truly out-of-fragment forms (cubical `Glue`/`ua`/partial elements,
`foreign` postulates, universe-level variables) are **Declined**. Declining ≠ accepting a falsehood, which is exactly what
`effects_demo.bl` documents. The headline: **I/O is a library + a runtime handler, not a kernel
feature.**

## Unboxed `Int` / `Float` — the one that forces a real choice

This is the only capability where "fast" genuinely collides with "tiny kernel." Two designs, with
their soundness cost stated plainly:

### Design A — primitive types in the kernel (TCB growth)

Add `Term::IntLit`, an `Int` type, and primitive reduction rules (`add`, `mul`, …) to
`blight-kernel`, plus matching cases in the **re-checker**. Pros: genuinely fast arithmetic, normal
literals. Cons: the TCB grows by every primitive type *and its definitional-equality rules*; the
re-checker must independently re-implement the same primitive semantics (or the "two checkers agree"
story weakens precisely where bugs hide — integer overflow, float NaN/rounding, `0.1+0.2`). This is
the standard proof-assistant compromise (Coq/Lean trust their kernels' primitive ints), but it is a
real, permanent enlargement of what you must trust.

### Design B — an untrusted primitive FFI escape hatch (no TCB growth)

Keep the kernel pure. Add a `foreign`/`primitive` declaration (untrusted) that the **elaborator
treats as an opaque postulate** and the **codegen lowers to a native `i64`/`f64` op**. The kernel
sees an abstract constant of a declared type and never reduces it; the re-checker *declines* anything
mentioning a primitive. Pros: zero TCB growth, real machine arithmetic where you opt in. Cons: those
operations are **unverified** — you get speed exactly by stepping outside the proof guarantee for
that code, and a wrong FFI declaration is a wrong answer (never a false proof, since the kernel never
believed anything about the primitive's *value*).

**Recommendation:** B as the default (preserves the thesis; lets numeric-heavy code opt out of
unary), with A available only if a future Blight wants verified primitive arithmetic and is willing
to pay the trust. Either way, today's unary `Nat` stays as the *verified* default.

## Mutable arrays, growable heap, FFI

- **Mutable arrays**: a `Array`/`Ref` effect with runtime-backed storage (untrusted handler), or a
  linear/graded-binder discipline (the kernel already has quantitative grades) to make in-place
  update sound. The *type* could be an inductive + effect; the *storage* is runtime. Mostly tower;
  no kernel change for the effect-handler route.
- **Growable heap**: today the GC heap is a fixed 64 MiB ([`runtime/gc.c`](../crates/blight-codegen/runtime/gc.c));
  exhaustion aborts. Growing it is a pure **runtime** change (resize semi-spaces / add a heap-growth
  policy). No TCB, no codegen, no kernel — just `gc.c`.
- **FFI to C**: a `foreign` declaration lowered by codegen to a direct C call; same untrusted-opaque
  treatment as Design B above. Enables linking real libraries (SDL, sockets) at the cost of trusting
  those declarations. No kernel change.

## "Can we build games?" — the honest answer

**Yes, as a tower — not as a kernel feature, and not today out of the box.** A game needs three
things Blight doesn't yet ship but each of which is reachable *without enlarging the trusted kernel*:

1. **Text/graphics output** — the first brick is laid (string rendering; `ascii_box.bl` renders an
   N×N grid as a printed `String`). Pixel output needs FFI to a graphics library.
2. **A frame loop with I/O** — an `IO`/`Console` effect (designable now, §"Console I/O") plus a host
   driver that calls the effectful `main` repeatedly, reads input, and renders each frame. The
   driver is untrusted runtime code.
3. **Fast arithmetic for physics/coordinates** — unary `Nat` is too slow; this wants the unboxed
   `Int`/`Float` escape hatch (Design B), opted into for the hot numeric paths.

So a **deterministic, turn-based, text-rendered game** (think a roguelike frame, a cellular
automaton, a board solver) is the realistic near-term target: it needs only the IO effect + the
string output already shipped. A **real-time graphical game** additionally needs FFI + unboxed
primitives, all of which live in the tower. None of it ever requires touching
`crates/blight-kernel`.

## Conclusion

Blight is a **correctness-first, proof-carrying language**. Its defining constraint — a tiny trusted
kernel with no primitive types — is exactly what makes "fast numerics" and "games" feel far away.
But the architecture's payoff is that **almost everything people want lives in the untrusted tower**:
strings (done), I/O (an effect + handler), arrays (an effect or graded discipline), a growable heap
(a `gc.c` change), FFI and unboxed primitives (an opt-in escape hatch). Only *verified* primitive
arithmetic would enlarge the kernel — and even that is optional. Games are reachable as a tower, and
this pass delivers the first brick: real text output.

## See also

- [performance.md](performance.md) — cost model and the unary-`Nat` / boxing trade-offs.
- [benchmarks-game.md](benchmarks-game.md) — scaling tables and the honest cross-language comparison.
- [blight-spec.md](blight-spec.md) §4 (effects), §4.5 (partiality), §7 (compilation/runtime).
