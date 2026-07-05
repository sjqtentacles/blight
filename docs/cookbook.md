# The Blight cookbook

Task-oriented recipes. Every snippet is lifted from a program in [`examples/`](../examples) or
[`crates/blight-prelude/std`](../crates/blight-prelude/std) that the acceptance suite type-checks
on every CI run — if a recipe here rots, a test fails. Each recipe names its source file; open it
for the full, runnable version.

The [tutorial](tutorial.md) teaches the language bottom-up; this file answers "how do I …?"
top-down.

---

## Handle errors without exceptions (`Result`)

`Result a e` (std/result.bl) is the value-or-error type; `result-bind` chains checked steps and
short-circuits on the first `err` (the railway pattern). From
[`examples/result_chain.bl`](../examples/result_chain.bl):

```lisp
(load "std/nat.bl")
(load "std/result.bl")

; A "checked decrement": Zero has no predecessor, so it errs.
(deftotal checked-pred (Pi ((n Nat)) (Result Nat Nat))
  (lam (n) (match n [(Zero) (err 1)] [(Succ m) (ok m)])))

; 4 - 1 - 1 = 2 end-to-end; from 1, the second step errs and the chain carries it out.
(define twice-from-four
  (the (Result Nat Nat) (result-bind Nat Nat Nat (checked-pred 4) (lam (m) (checked-pred m)))))

; Extract with a default:
(define main (the Nat (result-unwrap-or Nat Nat twice-from-four 0)))
```

Also in the module: `result` (the case eliminator), `result-map`, `result-map-err`.

## Use a mutable hash map (and sequence effects generally)

`std/hashmap.bl` is an `Int`-keyed mutable hash map over the `Array` effect. Three rules govern
sequencing *any* effectful code:

1. **A `let` unwraps only a *bare* `perform`** — `(let ((x (perform op …))) …)` binds the
   operation's *result*.
2. **An application returning `(! E A)` binds the computation**, not the `A` — there is no
   implicit monadic bind. Use the CPS `*-then` combinators, which pass the result to an explicit
   continuation in tail position.
3. **A pure term checks against `(! E A)`** — the final continuation of a chain can just compute.

Abridged from [`examples/hashmap_lookup.bl`](../examples/hashmap_lookup.bl) (the full example
chains 3 puts — one negative key, one shadowing re-put — and 3 gets; result `11 + 20 + 0 = 31`):

```lisp
(load "std/hashmap.bl")

(define main (! Array Nat)
  (hm-new-then Nat Nat 8
    (lam (h)
      (hm-put-then Nat Nat h (int 1) 10
        (lam (u1)
          (hm-get-then Nat Nat h (int 1)
            (lam (a)
              (from-maybe 0 a))))))))
```

`hm-put` prepends (newest binding shadows older ones); `hm-get` returns `(Maybe V)`.

## Prove a function total when recursion is not structural

Three escalating tools, all `deftotal` (the kernel certifies totality unconditionally; an
inadequate measure yields the declared `default`, never unsoundness):

**Structural** (the common case — recurse on an immediate sub-term): plain `deftotal`.

**One measure** (`(measure e)`, E6) — any recursion whose *step count* a `Nat` of the inputs
bounds. Quicksort recurses on `filter`-ed partitions (not sub-terms); the list length bounds it.
From [`examples/quicksort.bl`](../examples/quicksort.bl) (see also `mergesort.bl`, `gcd.bl`):

```lisp
(deftotal quicksort (Pi ((xs (List Nat))) (List Nat))
  (measure (length xs))
  (default xs)
  (lam (xs) …sort the < p partition, the pivot, then the >= p partition…))
```

**Lexicographic** (`(measure e1 e2)`) — decrease `e1`, or keep it and decrease `e2`. This is
Ackermann's termination argument, and Ackermann computes *exactly* under it. From
[`examples/ackermann_total.bl`](../examples/ackermann_total.bl):

```lisp
(deftotal ack (Pi ((m Nat) (n Nat)) Nat)
  (measure m n)
  (default Zero)
  (lam (m n)
    (match m
      [(Zero) (Succ n)]
      [(Succ mm) (match n [(Zero) (ack mm 1)] [(Succ nn) (ack mm (ack m nn))])])))
```

For recursion the kernel cannot certify at all, `define-rec` compiles non-structural calls into
the `Delay` partiality monad instead (see [`examples/ackermann.bl`](../examples/ackermann.bl) —
the same function, honestly partial, driven by `force`).

## Write one definition for every universe level

`(define-level name (u …) T body)` declares a level-polymorphic definition (checked once, under
prenex level variables); `(inst name ℓ)` stamps a copy at a concrete level. From
[`examples/level_poly.bl`](../examples/level_poly.bl):

```lisp
(define-level id (u)
  (Pi ((A (Type u) omega)) (Pi ((x A omega)) A))
  (lam (A x) x))

(define id-at-nat  (the Nat ((inst id 0) Nat Zero)))          ; values (level 0)
(define id-at-type (the (Type 0) ((inst id 1) (Type 0) Nat))) ; types (level 1)
```

A bare reference to a level-polymorphic global is an error that names the fix (`inst`).

## Branch on machine integers

Kernel comparisons return `Int` flags (`1`/`0`), and `if-zero` is the branch primitive: the
then-branch fires on `0`, the else-branch on anything else. From `std/int.bl`:

```lisp
(deftotal int-abs (Pi ((a Int)) Int)
  (lam (a) (if-zero (int< a (int 0)) a (int- (int 0) a))))
```

`int-mod` (truncated remainder), `int-abs`, and friends are in `std/int.bl`; bridge an `Int` flag
to a real `Bool` as in [`examples/int_branch.bl`](../examples/int_branch.bl).

## Do I/O

Effects. `main : (! Console Unit)` reads and prints via the top-level native handler. The whole
of [`examples/echo.bl`](../examples/echo.bl):

```lisp
(load "std/io.bl")
(define main (! Console Unit) (let ((line (perform read tt))) (perform print line)))
```

Files: the `FileIO` effect (`std/io.bl`); bytes: `Bytes` (`std/bytes.bl`); mutable arrays:
`Arrays`/`Array` (`std/array.bl`); actors: `std/actor.bl` with
[`examples/actor_pingpong.bl`](../examples/actor_pingpong.bl).

## Prove an equation about your own function

`(define-by name (Path T lhs rhs) compute)` asks the kernel to close the goal by computation —
the proof is re-checked on every load, so it doubles as a pinned regression test. From
`std/int.bl`:

```lisp
(define-by int-mod-17-5-is-2 (Path Int (int-mod (int 17) (int 5)) (int 2)) compute)
```

`decide` closes decidable `Bool` goals the same way (`std/nat.bl`'s `four-is-even`). For
interactive proofs (`intro`/`induction`/`refl`/`exact`), see the [tutorial §7–8](tutorial.md) and
[`examples/plus_zero_proof.bl`](../examples/plus_zero_proof.bl).

## Build and run a native binary

```sh
LLVM_SYS_181_PREFIX=$(brew --prefix llvm@18) \
  cargo run -p blight-repl --features llvm -- build examples/hashmap_lookup.bl -o hm
./hm   # => 31
```

Type-check without LLVM by loading the file at the REPL (`cargo run -p blight-repl`), or pass
`--recheck` to `build` to re-verify every judgement through the independent second checker first.
Heavy computation belongs in the compiled binary: the check-time evaluator is a tree-walker with
native-stack recursion (fine for proofs and small grounds, not for deep unary-`Nat` towers).
