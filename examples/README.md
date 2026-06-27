# Blight examples

Small, runnable programs that exercise the toolchain. Every example here is loaded and type-checked
by `crates/blight-repl/tests/examples.rs`, so they cannot silently rot.

Each `.bl` references the standard library exactly as the prelude does — `(load "std/nat.bl")`
resolves against `crates/blight-prelude/`. In the REPL, start from the repo root so relative loads
resolve, or run the example through the test harness.

| Example | What it shows | How to run |
|---|---|---|
| [hello_nat.bl](hello_nat.bl) | Smallest buildable program: `main : Nat` via `std/nat` (`(2*3)+1`). Prints **7**. | `cargo run -p blight-repl --features llvm -- build examples/hello_nat.bl -o hello && ./hello` |
| [containers.bl](containers.bl) | The containers `Maybe`, two-parameter `Either`, and length-indexed `Vec`; reads a `Vec`'s length back. Prints **2**. | `cargo run -p blight-repl --features llvm -- build examples/containers.bl -o containers && ./containers` |
| [vec_head.bl](vec_head.bl) | A `Vec Nat 3` whose statically-tracked index is recovered as a `Nat`. Prints **3**. | `cargo run -p blight-repl --features llvm -- build examples/vec_head.bl -o vec_head && ./vec_head` |
| [safe_head.bl](safe_head.bl) | A length-indexed `safe-head : (Vec A (Succ n)) -> Maybe A`: its **type** forbids the empty case, so calling it on `(vnil)` is a compile-time error caught by the kernel and the independent re-checker. The good call prints **1**. | `cargo run -p blight-repl --features llvm -- build examples/safe_head.bl -o safe_head --recheck && ./safe_head` |
| [safe_tail.bl](safe_tail.bl) | A **dependent indexed motive**: `safe-tail : (Vec A (Succ n)) -> Vec A n` drops the head and the result type *remembers* the length shrank to `n`. Certified by **both** checkers: the trusted kernel now performs dependent-match refinement itself (the `vnil` arm is unreachable, the `vcons` arm forces the tail length to `n`), and the **independent re-checker** agrees (`--recheck`, no soundness alarm). Prints **1**. | `cargo run -p blight-repl --features llvm -- build examples/safe_tail.bl -o safe_tail --recheck && ./safe_tail` |
| [vec_map.bl](vec_map.bl) | A **length-preserving** `vec-map : (A->B) -> Vec A n -> Vec B n`: the result type `Vec B n` shares the input's index. Certified by **both** the trusted kernel and the **independent re-checker** (`--recheck`), exercising per-branch index refinement (`vcons` ⇒ `n := Succ m`, induction hypothesis at the shorter length `m`). Prints the preserved length **2**. | `cargo run -p blight-repl --features llvm -- build examples/vec_map.bl -o vec_map --recheck && ./vec_map` |
| [zip_vec.bl](zip_vec.bl) | `zip-vec : Vec A n -> Vec B n -> Vec (Pair A B) n` zips two equally-long vectors. Matching the first while the second is in scope produces a **higher-order eliminator motive** (the inner `match`'s result type is itself a `Π`). This is now certified by **both** checkers: the trusted kernel lowers the nested match to a core term with a higher-order Π-conclusion motive it fully verifies, and the **independent re-checker** agrees (`--recheck`, no decline, no soundness alarm). Prints the shared length **2**. | `cargo run -p blight-repl --features llvm -- build examples/zip_vec.bl -o zip_vec --recheck && ./zip_vec` |
| [list_sum.bl](list_sum.bl) | Summing a `List Nat` with `foldr`/`plus`. Prints **6**. | `cargo run -p blight-repl --features llvm -- build examples/list_sum.bl -o list_sum && ./list_sum` |
| [minmax.bl](minmax.bl) | `min`/`max` on `Nat` (`min 2 5 + max 2 5`). Prints **7**. | `cargo run -p blight-repl --features llvm -- build examples/minmax.bl -o minmax && ./minmax` |
| [fib.bl](fib.bl) | Fibonacci as a single structural recursion via a pair accumulator (`fib 7`). Prints **13**. | `cargo run -p blight-repl --features llvm -- build examples/fib.bl -o fib && ./fib` |
| [factorial.bl](factorial.bl) | Factorial by a single structural recursion on `n` (`fact 4` = 1·2·3·4). Prints **24**. | `cargo run -p blight-repl --features llvm -- build examples/factorial.bl -o factorial && ./factorial` |
| [either_compute.bl](either_compute.bl) | An `Either`/`Maybe` computation folded to a `Nat`. Prints **4**. | `cargo run -p blight-repl --features llvm -- build examples/either_compute.bl -o either_compute && ./either_compute` |
| [region_scratch.bl](region_scratch.bl) | A `(region …)` arena scope that allocates scratch and bypasses the GC. Prints **2**. | `cargo run -p blight-repl --features llvm -- build examples/region_scratch.bl -o region_scratch && ./region_scratch` |
| [hello_string.bl](hello_string.bl) | Smallest program that prints **text**: `main : String = "hello"` (reader sugar → `push`/`empty` codepoints, runtime prints via `bl_print_string`). Prints **hello**. | `cargo run -p blight-repl --features llvm -- build examples/hello_string.bl -o hello_string && ./hello_string` |
| [string_length.bl](string_length.bl) | `string-length "hello"` over the codepoint spine. Prints **5**. | `cargo run -p blight-repl --features llvm -- build examples/string_length.bl -o sl && ./sl` |
| [string_reverse.bl](string_reverse.bl) | `string-reverse "abc"` rebuilt and printed as text. Prints **cba**. | `cargo run -p blight-repl --features llvm -- build examples/string_reverse.bl -o sr && ./sr` |
| [palindrome.bl](palindrome.bl) | `string-eq word (reverse word)` on `"level"` → `1`. Prints **1**. | `cargo run -p blight-repl --features llvm -- build examples/palindrome.bl -o pal && ./pal` |
| [caesar.bl](caesar.bl) | `string-shift 1 "abc"` (Caesar shift of each codepoint), printed as text. Prints **bcd**. | `cargo run -p blight-repl --features llvm -- build examples/caesar.bl -o caesar && ./caesar` |
| [gcd.bl](gcd.bl) | Subtractive Euclidean GCD over `Nat` (`gcd 12 8`), fuel-bounded so it stays structurally recursive. Prints **4**. | `cargo run -p blight-repl --features llvm -- build examples/gcd.bl -o gcd && ./gcd` |
| [collatz_steps.bl](collatz_steps.bl) | Collatz step count for `6` (6→3→10→5→16→8→4→2→1), fuel-bounded. Prints **8**. | `cargo run -p blight-repl --features llvm -- build examples/collatz_steps.bl -o collatz && ./collatz` |
| [list_sort.bl](list_sort.bl) | Insertion sort over `List Nat` (`[3,1,2]` → `[1,2,3]`), printing the head (smallest). Prints **1**. | `cargo run -p blight-repl --features llvm -- build examples/list_sort.bl -o list_sort && ./list_sort` |
| [fizzbuzz.bl](fizzbuzz.bl) | FizzBuzz classification of `15` as a `Nat` code (0=number, 1=Fizz, 2=Buzz, 3=FizzBuzz), via fuel-bounded `nat-mod`. Prints **3**. | `cargo run -p blight-repl --features llvm -- build examples/fizzbuzz.bl -o fizzbuzz && ./fizzbuzz` |
| [calculator.bl](calculator.bl) | A tiny `Expr` AST evaluator over native `Int` (`(2+3)*4-1`); structural `eval`, **re-checker-accepted** (Int primitives). Prints **19**. | `cargo run -p blight-repl --features llvm -- build examples/calculator.bl -o calc && ./calc` |
| [int_arith.bl](int_arith.bl) | Native machine `Int` (M11): `(int* (int 100000) (int 100000))` is a single hardware multiply on an unboxed 64-bit payload — the headline contrast with the O(unary) `Nat` tower. **Re-checker-accepted**. Prints **10000000000**. | `cargo run -p blight-repl --features llvm -- build examples/int_arith.bl -o int_arith --recheck && ./int_arith` |
| [int_sum.bl](int_sum.bl) | The machine-`Int` side of the sum benchmark: `foldr int-add` over 800 `Int`-ones (via `std/int.bl`), each add O(1) with no per-magnitude allocation. Pairs with `bench_sum.bl`; see [docs/benchmarks-game.md](../docs/benchmarks-game.md). Prints **800**. | `cargo run -p blight-repl --features llvm -- build examples/int_sum.bl -o int_sum --recheck && ./int_sum` |
| [bench_sum.bl](bench_sum.bl) | The unary-`Nat` side of the sum benchmark: `foldr plus` over 800 `Nat`-ones, so the result is `Succ^800 Zero` — every `+` walks a `Succ` chain (the honest unary cost the `Int` counterpart avoids). Prints **800**. | `cargo run -p blight-repl --features llvm -- build examples/bench_sum.bl -o bench_sum && ./bench_sum` |
| [rle.bl](rle.bl) | Run-length encoding of `[7,7,7,1,1]` → `[(7,3),(1,2)]` (structural on the spine); reads back the first run's count. Prints **3**. | `cargo run -p blight-repl --features llvm -- build examples/rle.bl -o rle && ./rle` |
| [mergesort.bl](mergesort.bl) | Merge sort over `List Nat` (`[5,3,8,1,2,7]`), made structural with a `Nat` fuel (merge/split are non-structural classically); prints the head (minimum). Prints **1**. | `cargo run -p blight-repl --features llvm -- build examples/mergesort.bl -o mergesort && ./mergesort` |
| [quicksort.bl](quicksort.bl) | Quicksort over `List Nat` (`[5,3,8,1,2,7]`), made structural with a `Nat` fuel (tail partitioning is non-structural); prints the head (minimum). Prints **1**. | `cargo run -p blight-repl --features llvm -- build examples/quicksort.bl -o quicksort && ./quicksort` |
| [tree_sum.bl](tree_sum.bl) | Sum of a binary search tree built by `tree-insert`. Prints **6**. | `cargo run -p blight-repl --features llvm -- build examples/tree_sum.bl -o tree_sum && ./tree_sum` |
| [ackermann.bl](ackermann.bl) | Ackermann via `define-rec` (general recursion): shows the **boundary** of structural totality — it elaborates and builds, but its result is a `later`-guarded delay, so it prints the delay constructor, not a numeral. (load/build only) | `cargo test -p blight-repl --test examples` |
| [ascii_box.bl](ascii_box.bl) | The honest "graphics" demo: builds a 3×3 `#` grid as a `String` at runtime (rows by recursion + `string-append`) and prints it. Single deterministic frame — interactive games still need I/O + a frame loop (see [docs/roadmap.md](../docs/roadmap.md)). Prints a **3×3 box of `#`**. | `cargo run -p blight-repl --features llvm -- build examples/ascii_box.bl -o ascii_box && ./ascii_box` |
| [plus_zero_proof.bl](plus_zero_proof.bl) | Proving `plus n Zero = n` by tactics, re-checked by the kernel. (load-only) | `cargo test -p blight-repl --test examples` |
| [mult_one_proof.bl](mult_one_proof.bl) | Proving `mult n 1 = n` by tactics. (load-only) | `cargo test -p blight-repl --test examples` |
| [traits.bl](traits.bl) | Dictionary-passing `Show`/`Ord` traits with instance search. (load-only) | open the REPL and paste, or `cargo test -p blight-repl --test examples` |
| [show_dispatch.bl](show_dispatch.bl) | `Show`/`Ord` trait dispatch over `Nat`/`Bool`. (load-only) | `cargo test -p blight-repl --test examples` |
| [functor.bl](functor.bl) | An ML-style functor deriving equality from an `ORD` module. (load-only) | `cargo test -p blight-repl --test examples` |
| [redblacktree.bl](redblacktree.bl) | The `RedBlackTree` functor applied to a `Nat` module. (load-only) | `cargo test -p blight-repl --test examples` |
| [effects_demo.bl](effects_demo.bl) | A `State` effect with `get`/`put` and a handler interpreting it. (load-only; the re-checker now checks effects at the type level) | `cargo test -p blight-repl --test examples` |
| [game/guess.bl](game/guess.bl) | The interactive turn-based **"guess the word"** game: a fuel-bounded `Console` frame loop (`define-rec play : Nat -> (! Console Unit)`) that reads a guess each turn, compares with `string-eq`, and branches (win+stop / hint+recurse). Recursion *over an effectful computation*, run through the native Console handler. (effects: re-checked at the type level; runs natively) | `printf 'cat\ndog\n' \| ./guess` after `cargo run -p blight-repl --features llvm -- build examples/game/guess.bl -o guess` |
| [package/](package) | A `spores` package: a `spore.toml` manifest plus a module that `(import "std/nat")`s a dependency. | `cargo test -p blight-repl --test examples` |

Buildable examples define a `main` (a `Nat`, a native `Int`, or a `String` printed as text) that `blight build`
compiles, runs, and prints; load-only examples typecheck through the REPL / test corpus (tactic
proofs, traits, functors, and effects — the latter now re-checked at the type level by the
independent re-checker, which declines only cubical `Glue`/`ua`/partial, `foreign`, and
universe-level-variable forms). Strings are
**untrusted tower code** — a `String` is a cons-list of `Nat` codepoints (`std/string.bl`), the
reader desugars quoted literals into that chain, and the runtime renders a `String`-typed result as
text. The kernel gains no primitive string type. For Blight's cost model and benchmarks, see
[docs/performance.md](../docs/performance.md).

Notes:

- `blight build` requires a binary built with the native backend (`--features llvm`, which needs
  LLVM 18 + clang). See the repo [README](../README.md#build).
- `blight build --target=wasm32` emits a WebAssembly module: a linked `.wasm` when a wasm-capable
  `clang` + `wasm-ld` are available, otherwise the object only.
- The `package/` example's `spore.toml` declares `std = { path = "../../crates/blight-prelude/std" }`;
  a module id `std/nat` therefore resolves to `crates/blight-prelude/std/nat.bl`.
