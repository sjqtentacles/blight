# Blight tutorial — from `Nat` to a tactic proof

This is a hands-on walk through Blight, the small dependently-typed language whose trusted kernel
(the *spore*) is re-checked by a second, independent checker. We start at the natural numbers and
end by *proving a theorem* and having the kernel re-verify it.

Everything below is real, tested syntax. Each `.bl` snippet loads through the `blight` REPL or
`blight build`; the standard-library modules live under `crates/blight-prelude/std/`.

## 0. Installing

Blight is a Rust workspace; there is no separate installer yet, so you build it from source with
[Cargo](https://rustup.rs/) (stable Rust; no nightly features are required for the checker/REPL):

```bash
git clone <this repo> && cd loonglang
cargo build -p blight-repl                       # checker + REPL, no native codegen
cargo build -p blight-repl --features llvm        # + `blight build` (needs a system LLVM matching
                                                   #   the `llvm-sys` crate's expected version)
```

The `llvm` feature is only needed to compile checked programs to a native binary or object file
(`blight build`); the REPL, type-checking, and proof-checking all work without it. If you don't
have LLVM installed, skip straight to §1 — everything through §7 (the first proof) runs in the
plain REPL.

An editor extension (`editors/vscode-blight`) adds diagnostics, hover, and go-to-definition for
`.bl` files via `blight-lsp`; see its `README.md` to build and load it.

## 1. Running the REPL

```bash
cargo run -p blight-repl            # the checker/REPL (no native backend)
cargo run -p blight-repl --features llvm -- build examples/hello_nat.bl -o hello && ./hello
```

In the REPL, enter forms (multi-line forms are read until the parentheses balance). REPL commands
start with `:` —

```
blight> :help
blight> :type (Succ Zero)
Nat
blight> :load examples/hello_nat.bl
blight> :quit
```

`:type <expr>` infers and pretty-prints a type; `:load <file>` checks a file of forms.

## 2. Data and functions: the natural numbers

A datatype is declared with `defdata`. `Nat` is the unary (Peano) encoding the kernel's
structural-recursion checker understands directly:

```
(defdata Nat () (Zero) (Succ (n Nat)))
```

`()` is the (empty) parameter telescope; `(Zero)` and `(Succ (n Nat))` are the constructors. A
recursive field is written with the type being defined (`(n Nat)`).

Total functions recurse structurally. `define-rec` allows a recursive self-call on a structurally
smaller argument; `deftotal` additionally *requires* the recursion to be structural (so it compiles
to a kernel eliminator):

```
(define-rec plus (Pi ((a Nat) (b Nat)) Nat)
  (lam (a b) (match a
    [(Zero) b]
    [(Succ n) (Succ (plus n b))])))
```

`(Pi ((a Nat) (b Nat)) Nat)` is the dependent function type (here non-dependent: `Nat → Nat → Nat`).
`(lam (a b) …)` is the lambda; `(match a …)` is sugar that elaborates to the kernel's `Elim`.

Try it:

```
blight> :type (plus (Succ Zero) (Succ Zero))
Nat
```

## 3. Parameters and indices

Datatypes can take **parameters** (uniform across all constructors) and **indices** (which vary per
constructor). Blight handles full telescopes of each.

A one-parameter container — the optional type:

```
(defdata Maybe ((a (Type 0)))
  (nothing)
  (just (x a)))
```

A *two-parameter* sum — `Either a b`:

```
(defdata Either ((a (Type 0)) (b (Type 0)))
  (left (x a))
  (right (y b)))
```

An *indexed* family — length-indexed vectors. Here `((n Nat))` is the index telescope, and each
constructor declares the index it targets with a trailing `(=> …)`:

```
(defdata Vec ((a (Type 0))) ((n Nat))
  (vnil (=> Zero))
  (vcons (m Nat) (x a) (xs (Vec a m)) (=> (Succ m))))
```

`vnil` builds a `Vec a Zero`; `vcons` takes a `Vec a m` and builds a `Vec a (Succ m)`. The recursive
field `(xs (Vec a m))` records its own index.

These all live in the standard library (`std/maybe.bl`, `std/either.bl`, `std/vec.bl`) and are
re-checked by the *independent* re-checker, not just the kernel.

## 4. Eliminating by `match`

A non-dependent fold over `Vec` that recovers its length as a plain `Nat`:

```
(define-rec vec-length (Pi ((A (Type 0)) (n Nat) (v (Vec A n))) Nat)
  (lam (A n v) (match v
    [(vnil) Zero]
    [(vcons m x xs) (Succ (vec-length A m xs))])))
```

Every `match` must cover its scrutinee's constructors. Leave one out and the elaborator lists the
gaps up front — `match` on a three-constructor `Ordering` with only two arms reports
`non-exhaustive `match` on `Ordering`: missing case `eq``. It also rejects a `duplicate `match`
arm` (the same constructor twice) and an `unreachable `match` arm` (a clause after a `_`/variable
catch-all). A trailing `_` arm makes any `match` exhaustive.

For a recursive function that matches on one argument, `defn` writes it as pattern **equations** —
one `[(patterns) body]` clause per case — instead of a `lam` + `match`:

```
(defn add (Pi ((a Nat) (b Nat)) Nat)
  [((Zero) b) b]
  [((Succ n) b) (Succ (add n b))])
```

`defn` reads the argument count from the `Pi` type, finds the single column that is pattern-matched
(here `a`; the other arguments must be plain variables), and desugars to a single-scrutinee `match`
on it — recursing through the same kernel `Elim` the hand-written form uses. The matched argument
need not be the first: `(defn len (Pi ((A (Type 0)) (xs (List A))) Nat) [(A (nil)) Zero] [(A (cons x
rest)) (Succ (len A rest))])` matches on `xs`. Nested patterns and the coverage check above both
apply.

## 5. Paths: equality in the cubical kernel

Blight's kernel is cubical: propositional equality is the **path** type `Path A x y` (a function out
of the interval). `refl` is the constant path; paths compute under the Kan operations
(`transp`/`hcomp`/`comp`), which the kernel implements for the full heterogeneous cases and the
re-checker mirrors.

You rarely write raw paths; you prove them. That is the next step (§7) — but first, a program that
actually talks to the outside world.

## 6. Effects: an interactive `Console` program

Everything so far is pure. Blight programs that do I/O use **algebraic effects with handlers**: a
`perform` suspends the computation and hands control to whichever `handle` (or, at the top level,
the native runtime) is running it, which decides how to resume. `Console` (`std/io.bl`) is the
`print`/`read` effect; a `main : (! Console Unit)` is a *computation*, not a value, and the native
top-level handler drives it against real stdio.

[`examples/game/guess.bl`](../examples/game/guess.bl) is a small turn-based guessing game built
this way — each turn prints a prompt, `perform read tt` blocks for a line of stdin, and the guess is
compared against a secret word, recursing on one less unit of fuel (a `Nat`) so the loop is
structurally total:

```
(load "std/io.bl")

(define secret String "dog")

; A Bool-selector kept non-recursive so the recursive `play` call stays outside `match`.
(deftotal console-if (Pi ((t (! Console Unit)) (e (! Console Unit)) (b Bool)) (! Console Unit))
  (lam (t e b) (match b [(true) t] [(false) e])))

(define-rec play (Pi ((attempts Nat)) (! Console Unit))
  (lam (attempts) (match attempts
    [(Zero) (perform print "out of guesses!\n")]
    [(Succ k)
      (let ((_ (perform print "guess: ")))
        (let ((g (perform read tt)))
          (console-if
            (perform print "you win!\n")
            (let ((_ (perform print "nope, try again.\n"))) (play k))
            (string-eq g secret))))])))

(define main (! Console Unit) (play (Succ (Succ (Succ Zero)))))
```

Build and run it, feeding it guesses on stdin:

```bash
cargo run -p blight-repl --features llvm -- build examples/game/guess.bl -o guess
printf 'cat\ndog\n' | ./guess
# guess: nope, try again.
# guess: you win!
```

Effects are modeled at the type level, so `--recheck` (§8) agrees with the seed kernel on this
program too — an interactive program is just as re-checkable as a pure one.

## 7. Proving a theorem by tactics

`plus n Zero` is *not* definitionally `n` (because `plus` recurses on its first argument, so with `n`
a variable it is stuck). Proving `plus n Zero = n` needs a genuine induction.

Blight's tactics only *propose* a proof term; the spore re-checks it (the LCF discipline), so a buggy
script can fail but can never mint a false proof. The right-unit law for addition:

```
(define-by plus-zero
  (Pi ((n Nat)) (Path Nat (plus n Zero) n))
  (intro n
    (induction n
      [(Zero)   refl]
      [(Succ k) (cong Succ (exact k#ih))])))
```

Reading the script:

- `(intro n …)` introduces the universally-quantified `n`.
- `(induction n …)` does structural induction, giving one arm per constructor.
- In the `Zero` arm the goal reduces to `Path Nat Zero Zero`, discharged by `refl`.
- In the `(Succ k)` arm the induction hypothesis is in scope as `k#ih : Path Nat (plus k Zero) k`,
  and `(cong Succ (exact k#ih))` lifts it under `Succ` to close the goal.

Run it through the example (which loads the tactic substrate and `std/nat`):

```bash
cargo test -p blight-repl --test examples plus_zero_proof_example_loads
```

The proof is recorded as the global `plus-zero`, re-checked by the kernel.

## 8. Building a binary

Any `main : Nat` is buildable:

```
(load "std/nat.bl")
(define main Nat (plus (mult (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))) (Succ Zero)))
```

```bash
cargo run -p blight-repl --features llvm -- build examples/hello_nat.bl -o hello
./hello        # prints 7
```

Add `--recheck` to have the independent re-checker re-verify every judgement before any code is
emitted; a rejection aborts the build as a soundness alarm. `--target=wasm32` emits a WebAssembly
module (a linked `.wasm` when a wasm toolchain is available, else the object).

## Where to go next

- `examples/` — small, tested programs: buildable ones (`hello_nat` → 7, `containers` → 2,
  `vec_head` → 3, `list_sum` → 6, `minmax` → 7, `fib` → 13, `either_compute` → 4,
  `region_scratch` → 2) and load-only ones (`plus_zero_proof`, `mult_one_proof`, `traits`,
  `show_dispatch`, `functor`, `redblacktree`, `effects_demo`), plus a `spores` package. See
  [`examples/README.md`](../examples/README.md).
- The standard library under [`crates/blight-prelude/std`](../crates/blight-prelude/std): `std/nat`
  (`plus`/`mult`/`sub`/`min`/`max`/`even`/`odd`), `std/list` (`map`/`filter`/`reverse`/`foldr`/
  `concat`), `std/maybe`, `std/either`, `std/pair`, `std/function`, `std/ordering`, `std/vec`,
  `std/string`, `std/tree`, and the `std/prelude` aggregator.
- [`docs/performance.md`](performance.md) — the cost model, benchmarks, and honest trade-offs.
- [`docs/implementation.md`](implementation.md) — how the kernel, re-checker, and backend are built
  and tested.
- [`docs/blight-spec.md`](blight-spec.md) — the language specification.
