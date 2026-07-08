# Blight capabilities roadmap

> **Note — this is the pre-M6 capability-axis essay.** It frames each capability by *where it would
> live* and *whether it enlarges the TCB*, written before M7–M14 landed. Several items it discusses as
> future ("Console I/O," native `Int`, the `foreign` FFI hatch, a growable heap) have since **shipped**;
> they are marked done below. For the authoritative record of what actually landed after M6 — with
> acceptance tests and TCB accounting — see [roadmap-post-m6.md](roadmap-post-m6.md). The
> TCB-discipline reasoning here is still valid and is the rationale behind those milestones.

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

What the kernel **deliberately keeps minimal**: primitive base types. Originally there were *none* —
the pre-M6 design had no `Int`, `Float`, `Char`, array, or string in `Term`, only `Data`/`Con`/`Elim`
over user-declared inductives, which is why `Nat` is unary and `String` is a cons-list of unary
codepoints. **M10 added exactly one primitive — `Int` (`IntTy`/`IntLit`/`IntPrim`)** — as a single,
reviewed, documented exception for fast integer arithmetic (see the "Unboxed `Int`" section). There is
still no `Float`, `Char`, array, or string primitive. Keeping the primitive set this small is the
whole point: the kernel stays small enough to audit.

## Capability table

| capability | status | lives in | touches TCB? |
|---|---|---|---|
| **String output** | ✅ done this pass | runtime + codegen + elaborator sugar | **No** |
| **Algebraic effects / handlers** | ✅ in kernel + runtime | kernel (type), runtime (handlers) | already in TCB |
| **Bounded-stack deep recursion** | ✅ done | kernel (`Delay`), runtime (`bl_force`) | already in TCB |
| **Console I/O** | ✅ shipped (M7) | a `Console` *effect* + native runtime handler | **No** (handlers are untrusted) |
| **Native `Int` arithmetic** | ✅ shipped (M10) | kernel primitive (`IntTy`/`IntLit`/`IntPrim`) + re-checker | **Yes** (the one deliberate, documented growth) |
| **Unboxed `Float` arithmetic** | ✖ not yet | kernel primitive **or** untrusted FFI escape hatch | **Yes** (kernel) *or* No (FFI, with cost) |
| **Mutable arrays (scalar `Int`)** | ✅ shipped (A3a) | a `std/array.bl` `Arrays` effect + native runtime handler | **No** (mirrors the `Bytes` effect exactly) |
| **Mutable arrays (generic/boxed)** | ✅ shipped (A3b, Arc II Wave 10 / P1) | a `std/array.bl` `Array A` effect + `runtime/boxed_array.c` (rooted handle table + write barrier) | **No** (untrusted runtime; rides the already-shipped Wave 7/E2 parameterized-effects kernel feature) |
| **Growable heap** | ✅ shipped (M9) | runtime (`gc.c`) | **No** |
| **FFI to C** | ✅ shipped (M8) | codegen + an untrusted `foreign` decl | **No** (but unchecked) |
| **Frame loop / real-time games** | ✅ shipped (Arc II Wave 10 / P2) | a `std/graphics.bl` `Graphics` effect + `runtime/graphics.c` native handler (Design B, [`docs/design-wave4-gobars.md`](design-wave4-gobars.md) §5) linking SDL2 behind the `graphics` cargo feature | **No** (untrusted runtime; no raw pointer or SDL type ever crosses into Blight code) |
| **Code mobility (closures/continuations across a heap/process boundary)** | ✅ shipped, same-binary only (Arc II Wave 10 / P5) | `serialize.c`'s `bl_value_serialize_mobile`/`deserialize_mobile` + a codegen-emitted function-index table (`driver.rs`'s `code_table_source_for`); see [`docs/design-code-mobility.md`](design-code-mobility.md) | **No** (untrusted runtime; a mismatched-binary blob is rejected before any pointer is resolved) |
| **Auto-parallelism (divide-and-conquer → `worker.c`)** | ◐ detection shipped, rewrite deferred (Arc II Wave 10 / P4) | `crate::autopar` (a pure `Cir → Vec<AutoparCandidate>` analysis, `BL_NO_AUTOPAR`); the parallel rewrite is a documented sharpened negative — see `docs/roadmap-post-m6.md` P8 | **No** (untrusted codegen analysis; never mutates the `Cir`, so it cannot change any program's behavior) |
| **RC + in-place reuse (Perceus-style functional-update reuse)** | ✖ deferred, sharpened negative + committed red test (Arc II Wave 10 / P6) | none shipped; go-bar + finding + `rc_diff.c` (currently non-compiling by design) — see [`docs/design-rc-reuse.md`](design-rc-reuse.md) | n/a (no code shipped; a future consumer pass would be untrusted codegen, same TCB story as `autopar`) |

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

## Console I/O — shipped (M7), no TCB change

Because the **effect system is already in the kernel**, real I/O did **not** need a kernel change.
This shipped as **M7** (`std/io.bl` + a native top-level handler; `examples/game/guess.bl` builds and
runs). General *file* I/O beyond stdin/stdout is still future. The design that landed:

1. Declare a `Console` effect in a `.bl` library: `(effect Console (print String Unit) (read Unit String))`.
2. A program that does I/O has type `! ⟨Console⟩ A` — the effect row tracks it; this is fully
   kernel-checked today.
3. Provide an **untrusted runtime handler** in C (alongside `effects.c`) that interprets `print` by
   calling `bl_print_string` and `read` by reading stdin, re-installing itself (deep handler).
4. `build_binary` installs the top-level `Console` handler in the authored `main`.

Why the **re-checker declines** (rather than rejects) a *cubical or foreign* `main`, while it now
**checks effectful programs at the type level**: the independent re-checker re-derives the types of
`perform`/`handle`/`! E A` (consulting the kernel's operation signatures), independently re-derives
the effect row, and enforces the continuation multiplicity (resuming above the operation's
`cont_grade` is `Rejected`) — so an effectful program is a genuine second opinion at the type level
(**Checked**), and only the truly out-of-fragment forms (cubical partial elements, `foreign`
postulates) are **Declined**. Cubical `Glue`/`ua` (modeled since F1) and universe-level *variables*
(modeled since T2 — the re-checker re-verifies level-polymorphic judgements under its own symbolic
`RLevel` order through a leveled door) were formerly on that list. Declining ≠ accepting a
falsehood, which is exactly what
`effects_demo.bl` documents. The headline: **I/O is a library + a runtime handler, not a kernel
feature.**

## Unboxed `Int` / `Float` — the one that forces a real choice (Int now shipped)

This is the only capability where "fast" genuinely collides with "tiny kernel." Both designs below
**shipped** for integers — Design A as **M10**, Design B as **M8**. For `Float`, the A-vs-B tension
was **resolved by a third path (Design C, shipped as M23)** that needs neither: see "Design C" below.

### Design A — primitive types in the kernel (TCB growth) — shipped for `Int` as M10

Add `Term::IntLit`, an `Int` type, and primitive reduction rules (`add`, `mul`, …) to
`blight-kernel`, plus matching cases in the **re-checker**. Pros: genuinely fast arithmetic, normal
literals. Cons: the TCB grows by every primitive type *and its definitional-equality rules*; the
re-checker must independently re-implement the same primitive semantics (or the "two checkers agree"
story weakens precisely where bugs hide — integer overflow, float NaN/rounding, `0.1+0.2`). This is
the standard proof-assistant compromise (Coq/Lean trust their kernels' primitive ints), and it is a
real, permanent enlargement of what you must trust. **M10 paid exactly this cost for `Int`**: the
kernel gained `IntTy`/`IntLit`/`IntPrim` and the re-checker re-implements the same semantics, with
`--recheck` agreement as the acceptance test. It is the one deliberate, documented kernel growth (see
[roadmap-post-m6.md](roadmap-post-m6.md) M10). A future `Float` would pay this cost again — and is
where NaN/rounding make the "two checkers agree" story most delicate.

### Design B — an untrusted primitive FFI escape hatch (no TCB growth) — shipped as M8

Keep the kernel pure. Add a `foreign`/`primitive` declaration (untrusted) that the **elaborator
treats as an opaque postulate** and the **codegen lowers to a native `i64`/`f64` op**. The kernel
sees an abstract constant of a declared type and never reduces it; the re-checker *declines* anything
mentioning a primitive. Pros: zero TCB growth, real machine arithmetic where you opt in. Cons: those
operations are **unverified** — you get speed exactly by stepping outside the proof guarantee for
that code, and a wrong FFI declaration is a wrong answer (never a false proof, since the kernel never
believed anything about the primitive's *value*). **M8 shipped this** as the `foreign` hatch
(elaborator-only; re-checker declines honestly), so it is the no-TCB path available today for any
primitive `Float`/SIMD/etc. op you are willing to leave unverified.

### Design C — a library type built on the trusted base (no TCB growth, *and* verified) — shipped for `Float` as M23

The `Float` question turned out to have an answer that beats both A and B for the common case. Rather
than add a kernel `FloatTy` (A) or postulate an unverified `foreign` `f64` (B), **M23 defines `Float`
as an ordinary inductive `Data` built entirely from the already-trusted `Int` base** —
`(mkfloat (mantissa Int))`, a fixed-point rational scaled by 10^6 (`std/float.bl`). The kernel sees
only `Int` and `Data` it already understood, so there is **no new kernel surface and nothing new to
trust**, *and* — unlike the `foreign` hatch — the program is **fully checked**: the independent
re-checker *accepts* a `Float` program outright because it is plain `Int`/`Data`. Speed comes from the
untrusted backend recognizer rewriting each `float-*` wrapper to an O(1) `bl_float_*` helper computing
the *same* fixed-point semantics, gated by a fuzzed differential test (`float_diff.c`) so a wrong
recognizer yields a wrong number, never a false proof. The cost is the honest one of fixed-point: it
is **not IEEE-754** — no NaN/Inf, fixed precision (6 decimal places), and `0.1+0.2` is exact in the
scaled representation rather than reproducing IEEE rounding. So the open trade is no longer "A vs B"
but "is fixed-point `Float`-over-`Int` enough (C, shipped) or do you need genuine IEEE-754 — at which
point you pick B (unverified `foreign` `f64`, fast + real rounding) or A (kernel `FloatTy`, verified
but the TCB absorbs NaN/rounding definitional equality)."

**Where this leaves things:** for integers you have verified-but-unary `Nat`, verified-and-fast kernel
`Int` (A/M10), and the unverified `foreign` hatch (B/M8). For `Float`, the default is now **Design C**
(M23: a verified fixed-point library type, zero TCB) — it is what `std/float.bl` ships. **B** remains
the escape hatch when you need real IEEE-754 `f64` arithmetic and will accept that those ops are
unverified, and **A** is reserved for if/when verified primitive IEEE-754 `Float` is worth paying the
permanent trust in its NaN/rounding equality rules. The A-vs-B dilemma the older roadmap framed is
therefore *resolved for the common case* — fast `Float` without spending trust already exists.

**Design B for `Float`, shipped as L2 (`std/f64.bl`).** The "B remains the escape hatch" line above is
no longer hypothetical: `std/f64.bl` postulates an opaque `F64` (`(foreign F64 (Type 0) …)`) plus
conversion/arithmetic/comparison ops, each backed by a `bl_f64_*` C symbol (`runtime/numeric.c`) that
computes with a genuine hardware `double` — real NaN/Inf, real IEEE rounding, no fixed-precision
compromise. A boxed `F64` is bit-for-bit a `bl_int` box of the `double`'s raw bit pattern (no new GC
tag), and a binary op packs its two operands into one `(Pair F64 F64)` argument, exactly the
`std/bytes.bl` multi-arg convention. The honest cost is exactly Design B's: `F64` is a `foreign`
postulate the kernel trusts on faith, so **`--recheck` declines** any program mentioning it (never a
false accept), and — unlike `Float`'s `float_diff.c` — there is no differential gate, because there is
no independent reference to diff a hardware double against; a `f64_test.c` regression harness instead
pins `bl_f64_*` against literal C `double` arithmetic so a refactor cannot silently break it. See
`examples/f64_scratch.bl` for an end-to-end dogfooding program. **The tradeoff, spelled out:** reach
for `std/float.bl` by default (verified, but fixed-point); reach for `std/f64.bl` only when you
specifically need real IEEE-754 semantics and are willing to leave the checked fragment for that code
— the re-checker's decline is the honest, visible price tag, never a silently-accepted hole.

## Mutable arrays, growable heap, FFI

- **Mutable arrays**: a `Array`/`Ref` effect with runtime-backed storage (untrusted handler), or a
  linear/graded-binder discipline (the kernel already has quantitative grades) to make in-place
  update sound. The *type* could be an inductive + effect; the *storage* is runtime. Mostly tower;
  no kernel change for the effect-handler route. **Still future** — this is the one brick here that
  has not landed.
- **Growable heap**: **shipped (M9).** The GC heap ([`runtime/gc.c`](../crates/blight-codegen/runtime/gc.c))
  starts at 64 MiB and **grows** on pressure — `major_collect_grow` doubles the semi-space until the
  live set plus the request fit (amortized O(1)), so only a true host-OOM aborts. It was a pure
  **runtime** change: no TCB, no codegen, no kernel — just `gc.c`.
- **FFI to C**: **shipped (M8).** A `foreign` declaration lowered by codegen to a direct C call, with
  the same untrusted-opaque treatment as Design B above. It enables linking real libraries (SDL,
  sockets) at the cost of trusting those declarations. No kernel change; the re-checker declines a
  `foreign`-using `main` honestly (`examples/foreign_answer.bl`).

## "Can we build games?" — the honest answer

**Yes, as a tower — not as a kernel feature.** A game needs three things; all three have now shipped,
none of them enlarging the trusted kernel:

1. **Text/graphics output** — text output shipped (string rendering; `ascii_box.bl` renders an
   N×N grid as a printed `String`). **Pixel output** shipped too (Arc II Wave 10 / P2): rather than a
   raw `foreign` binding to SDL (Design A, rejected — see the go-bar's reasoning), a purpose-built
   `Graphics` **effect** (`std/graphics.bl`) + native `bl_run_graphics` handler
   (`runtime/graphics.c`, Design B) hides every SDL call behind five small ops, gated behind the
   `graphics` cargo feature so the ordinary build/CI stay SDL-free.
2. **A frame loop with I/O** — **shipped (M7)** for text (the `Console` effect) and **shipped (Wave
   10 / P2)** for real-time pixel output (the `Graphics` effect's native handler paces the loop with
   the same CPS deep-handler trampoline `Console` uses, vsync/`SDL_Delay` in place of blocking on
   `stdin`); the turn-based `examples/game/guess.bl` and the real-time `examples/graphics_scratch.bl`
   both build and run. Both drivers are untrusted runtime code.
3. **Fast arithmetic for physics/coordinates** — unary `Nat` is too slow, so this wanted unboxed
   primitives; **native `Int` shipped (M10)**, the fixed-point `std/float.bl` (verified) and the
   IEEE-754 `std/f64.bl` hatch (Wave 2 L2, unverified) both shipped for real-valued coordinates.

So both a **deterministic, turn-based, text-rendered game** (a roguelike frame, a cellular automaton,
a board solver) and a **real-time, pixel-rendered game** (a `snake`/`pong`-class frame loop) are now
buildable out of shipped bricks — the `Console`/`Graphics` effects, string output, fast `Int`, and
`Float`/`F64`. None of it ever required touching `crates/blight-kernel`: the `Graphics` effect is an
ordinary user effect the independent re-checker already type-checks with no decline, exactly like
`Console`/`Bytes`/`Arrays`/`Array` before it. See
[`docs/design-wave4-gobars.md`](design-wave4-gobars.md) §5 for the two candidate designs, the
acceptance checklist, and why Design B (the effect) won over Design A (raw `foreign` SDL bindings).

## Conclusion

Blight is a **correctness-first, proof-carrying language**. Its defining constraint — a tiny trusted
kernel with no primitive types — is exactly what once made "fast numerics" and "games" feel far away.
But the architecture's payoff is that **almost everything people want lives in the untrusted tower**:
strings (done), I/O (an effect + handler, shipped M7), a growable heap (a `gc.c` change, shipped M9),
FFI (the `foreign` hatch, shipped M8), generic/boxed arrays (A3a/A3b), real-valued arithmetic
(`Float`/`F64`), and now real-time graphics (`Graphics` effect, Wave 10 / P2). Native `Int` (M10)
remains the **one** deliberate, documented kernel growth, taken because verified-and-fast integer
arithmetic was worth the trust. Games — turn-based/text and real-time/pixel alike — are reachable
entirely as a tower on top of the bricks already shipped, with no further kernel growth required.

## See also

- [performance.md](performance.md) — cost model and the unary-`Nat` / boxing trade-offs.
- [benchmarks-game.md](benchmarks-game.md) — scaling tables and the honest cross-language comparison.
- [blight-spec.md](blight-spec.md) §4 (effects), §4.5 (partiality), §7 (compilation/runtime).
