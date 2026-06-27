//! Examples acceptance: every program under `examples/` loads and type-checks through the public
//! `Program` driver, so the curated examples can never silently rot. Black-box: only the
//! `blight-elab` public API is used.

use blight_elab::{ElabEnv, Outcome, PackageManifest, Program};
use std::path::PathBuf;

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Absolute path to the repo's top-level `examples/` directory (this crate lives at
/// `crates/blight-repl`, so `examples/` is two levels up).
fn examples_dir() -> PathBuf {
    PathBuf::from(format!("{}/../../examples", env!("CARGO_MANIFEST_DIR")))
}

/// Read an example's source by file name (relative to `examples/`).
fn read_example(name: &str) -> String {
    let path = examples_dir().join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read example {path:?}: {e}"))
}

/// Run an example's source through the `Program` driver and assert every form is accepted (a
/// well-typed `Declared` declaration or a kernel-`Checked` ascription). The example's own
/// `(load "std/…")` forms resolve via the shared prelude resolver, exactly as the prelude does.
fn assert_example_loads(name: &str) {
    // Some examples (notably the string ones) desugar literals into deep unary-`Nat` codepoint
    // chains, so elaboration/type-checking recurses deeply. `cargo test` worker threads use a small
    // (~2 MiB) stack, so run the load on a thread with an 8 MiB stack to match the CLI's main thread.
    let name = name.to_string();
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || assert_example_loads_inner(&name))
        .expect("spawn load thread")
        .join()
        .expect("example load thread panicked (see message above)");
}

fn assert_example_loads_inner(name: &str) {
    let src = read_example(name);
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&src)
            .unwrap_or_else(|e| panic!("example {name} loads and type-checks, got: {e:?}"))
    };
    assert!(
        outcomes
            .iter()
            .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
        "every form in {name} is accepted (declared or kernel-checked); got {outcomes:?}"
    );
}

#[test]
fn hello_nat_example_loads() {
    assert_example_loads("hello_nat.bl");
    // `main` is the buildable global the native backend would compile.
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("hello_nat.bl")).expect("loads");
    }
    assert!(
        env.global_term("main").is_some(),
        "hello_nat defines a `main` to compile"
    );
}

#[test]
fn hello_string_example_loads() {
    // String-literal sugar makes `main : String` a buildable global; the load + global probe runs on
    // a larger stack since the literal desugars to a deep unary-`Nat` codepoint chain.
    assert_buildable_main("hello_string.bl");
}

#[test]
fn traits_example_loads() {
    assert_example_loads("traits.bl");
}

#[test]
fn redblacktree_example_loads() {
    assert_example_loads("redblacktree.bl");
}

#[test]
fn containers_example_loads() {
    assert_example_loads("containers.bl");
    // `main` is buildable and reads the indexed vector's length back as a `Nat`.
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("containers.bl")).expect("loads");
    }
    assert!(
        env.global_term("main").is_some(),
        "containers defines a buildable `main`"
    );
}

#[test]
fn plus_zero_proof_example_loads() {
    assert_example_loads("plus_zero_proof.bl");
    // The tactic proof is recorded as a global.
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("plus_zero_proof.bl"))
            .expect("loads");
    }
    assert!(
        env.global_term("plus-zero").is_some(),
        "plus-zero is proved"
    );
}

/// `ua_compute.bl` witnesses the univalence *computation* rule on a closed instance: transporting
/// `true` along `ua (id-equiv Bool)` reduces (definitionally, via the kernel's `transp`-over-`Glue`
/// rule) to `equiv-fun (id-equiv Bool) true = true`, so the reflexivity proof `ua-computes-bool`
/// type-checks. This is the end-to-end (`ua` + `Glue` formation + `transp`) counterpart to the
/// kernel white-box test `kan.rs::transp_ua_glue_line_applies_forward_map`.
#[test]
fn ua_compute_example_loads() {
    assert_example_loads("ua_compute.bl");
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("ua_compute.bl")).expect("loads");
    }
    assert!(
        env.global_term("ua-computes-bool").is_some(),
        "the univalence computation rule is witnessed on the closed Bool instance"
    );
}

/// Assert an example loads and defines a buildable `main` global.
fn assert_buildable_main(name: &str) {
    let name = name.to_string();
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            assert_example_loads_inner(&name);
            let mut env = ElabEnv::new();
            {
                let mut prog = Program::with_resolver(&mut env, prelude_resolver);
                prog.run(&read_example(&name)).expect("loads");
            }
            assert!(
                env.global_term("main").is_some(),
                "{name} defines a buildable `main`"
            );
        })
        .expect("spawn load thread")
        .join()
        .expect("buildable-main thread panicked (see message above)");
}

#[test]
fn list_sum_example_loads() {
    assert_buildable_main("list_sum.bl");
}

#[test]
fn string_length_example_loads() {
    assert_buildable_main("string_length.bl");
}

#[test]
fn string_reverse_example_loads() {
    assert_buildable_main("string_reverse.bl");
}

#[test]
fn palindrome_example_loads() {
    assert_buildable_main("palindrome.bl");
}

#[test]
fn caesar_example_loads() {
    assert_buildable_main("caesar.bl");
}

#[test]
fn fib_example_loads() {
    assert_buildable_main("fib.bl");
}

#[test]
fn factorial_example_loads() {
    assert_buildable_main("factorial.bl");
}

#[test]
fn minmax_example_loads() {
    assert_buildable_main("minmax.bl");
}

#[test]
fn vec_head_example_loads() {
    assert_buildable_main("vec_head.bl");
}

#[test]
fn either_compute_example_loads() {
    assert_buildable_main("either_compute.bl");
}

#[test]
fn region_scratch_example_loads() {
    assert_buildable_main("region_scratch.bl");
}

#[test]
fn tree_sum_example_loads() {
    assert_buildable_main("tree_sum.bl");
}

#[test]
fn gcd_example_loads() {
    assert_buildable_main("gcd.bl");
}

#[test]
fn collatz_steps_example_loads() {
    assert_buildable_main("collatz_steps.bl");
}

#[test]
fn list_sort_example_loads() {
    assert_buildable_main("list_sort.bl");
}

#[test]
fn fizzbuzz_example_loads() {
    // FizzBuzz classification of 15 → 3 (divisible by both 3 and 5); fuel-bounded `nat-mod`.
    assert_buildable_main("fizzbuzz.bl");
}

#[test]
fn rle_example_loads() {
    // Run-length encoding of `[7,7,7,1,1]` → `[(7,3),(1,2)]`, structural on the spine; `main` reads
    // back the first run's count (3).
    assert_buildable_main("rle.bl");
}

#[test]
fn mergesort_example_loads() {
    // Merge sort over `List Nat`, made structural with a `Nat` fuel (merge + split are non-structural
    // classically). Sorts `[5,3,8,1,2,7]`, printing the head (minimum), 1.
    assert_buildable_main("mergesort.bl");
}

#[test]
fn quicksort_example_loads() {
    // Quicksort over `List Nat`, made structural with a `Nat` fuel (partitioning the tail is
    // non-structural). Sorts `[5,3,8,1,2,7]`, printing the head (minimum), 1.
    assert_buildable_main("quicksort.bl");
}

#[test]
fn ackermann_example_loads() {
    // The `force` (delay-eliminator) showcase: `parity` is a non-structural `define-rec` (it
    // recurses two `Succ`s deep), so its result is a `Delay Nat`; `main` drives it with `force` and
    // prints the final numeral. See the example header for the precise non-structural boundary.
    assert_buildable_main("ackermann.bl");
}

#[test]
fn ascii_box_example_loads() {
    // The honest "graphics" demo: builds an N×N `#` grid as a `String` at runtime and prints it.
    assert_buildable_main("ascii_box.bl");
}

#[test]
fn show_dispatch_example_loads() {
    // Trait dictionary dispatch; load-only like `traits.bl` (the resolved `show` term type-checks
    // and re-checks, exercising instance search).
    assert_example_loads("show_dispatch.bl");
}

#[test]
fn mult_one_proof_example_loads() {
    assert_example_loads("mult_one_proof.bl");
}

#[test]
fn functor_example_loads() {
    assert_example_loads("functor.bl");
}

#[test]
fn effects_demo_example_loads() {
    // Effects are out of the re-checker's fragment (it *declines*, not rejects), but the example
    // still elaborates and type-checks through the seed kernel.
    assert_example_loads("effects_demo.bl");
}

#[test]
fn state_handler_example_loads() {
    // A compiled deep handler (tail-resumptive fragment). Like `effects_demo`, effects are out of
    // the re-checker's fragment so it *declines*, but the seed kernel type-checks it; the matching
    // `example_state_handler_builds_and_runs` test compiles and runs it (prints `3`).
    assert_example_loads("state_handler.bl");
}

#[test]
fn effect_nontail_example_loads() {
    // A *general* (non-tail) deep handler: the performed effects are sub-expressions, so the
    // continuation is captured across applications/constructions at runtime. Effects are out of the
    // re-checker's fragment so it *declines*; the seed kernel type-checks it and the matching
    // `example_effect_nontail_builds_and_runs` compiles and runs it (prints `4`).
    assert_example_loads("effect_nontail.bl");
}

#[test]
fn echo_example_loads() {
    // `Console`-effect program (std/io.bl). Effects are out of the re-checker's fragment so it
    // *declines*; the seed kernel type-checks it. `example_echo_builds_and_runs` compiles and runs
    // it through the native top-level Console handler.
    assert_example_loads("echo.bl");
}

#[test]
fn greet_example_loads() {
    // A sequenced-`Console` interactive program (std/io.bl); declined by the re-checker (effects),
    // type-checked by the seed kernel. `example_greet_builds_and_runs` compiles and runs it.
    assert_example_loads("greet.bl");
}

#[test]
fn guess_game_example_loads() {
    // The interactive turn-based game (examples/game/guess.bl): a fuel-bounded `Console` frame loop
    // (`define-rec play` over a `Nat` attempt budget) that reads a guess each turn and branches on
    // `string-eq`. Effects are out of the re-checker's fragment so it *declines*; the seed kernel
    // type-checks it and `example_guess_game_builds_and_runs` compiles + runs it against scripted
    // stdin.
    assert_example_loads("game/guess.bl");
}

#[test]
fn foreign_answer_example_loads() {
    // The FFI escape hatch (spec §7.6): `(foreign answer Nat "bl_foreign_answer")` postulates an
    // opaque `Nat` backed by a C symbol. The seed kernel *trusts* it (it type-checks at `Nat`), so
    // the example loads and defines a buildable `main`. `example_foreign_answer_builds_and_runs`
    // compiles + links the C symbol and runs it (prints 42).
    assert_buildable_main("foreign_answer.bl");

    // Crucially: the independent re-checker must *DECLINE* (not accept, not reject) `main`, because a
    // `foreign` postulate is trusted code it cannot re-verify. This is the safety mechanism guarding
    // the one TCB-growing hatch.
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("foreign_answer.bl")).expect("loads");
    }
    let ty = env.global_type("main").expect("main type").clone();
    let term = env.global_term("main").expect("main term").clone();
    match blight_recheck::recheck_judgement(
        env.signature(),
        &blight_kernel::Judgement::HasType { term, ty },
    ) {
        Err(blight_recheck::RecheckError::Declined(msg)) => {
            assert!(
                msg.contains("foreign"),
                "decline reason should name the foreign postulate, got: {msg}"
            );
        }
        other => panic!("re-checker must DECLINE a foreign-using `main`, got: {other:?}"),
    }
}

/// `int_arith.bl`: native machine `Int` (M11). `(int* (int 100000) (int 100000))` type-checks at
/// `Int` and — unlike the unary-`Nat` tower — the re-checker *ACCEPTS* it: `Int`/`IntLit`/`IntPrim`
/// are primitive kernel nodes the independent re-checker models directly. It defines a buildable
/// `main`; `example_int_arith_builds_and_runs` compiles it and asserts it prints the product.
#[test]
fn int_arith_example_loads_and_rechecks() {
    assert_buildable_main("int_arith.bl");

    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("int_arith.bl")).expect("loads");
    }
    let ty = env.global_type("main").expect("main type").clone();
    let term = env.global_term("main").expect("main term").clone();
    blight_recheck::recheck_judgement(
        env.signature(),
        &blight_kernel::Judgement::HasType { term, ty },
    )
    .expect("re-checker ACCEPTS native Int arithmetic (primitive kernel nodes)");
}

/// `bench_sum.bl`: the unary-`Nat` counterpart of `int_sum.bl` and the Blight side of the
/// cross-language sum workload (docs/benchmarks-game.md). Right-folds `plus` over a `List Nat` of
/// 800 ones, so `main : Nat` is `Succ^800 Zero` — each `+` walks a `Succ` chain (the honest unary
/// cost). Deep, so it runs on an 8 MiB stack; the re-checker ACCEPTS it (`Nat`/`List`/`foldr`).
#[test]
fn bench_sum_example_loads_and_rechecks() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            assert_buildable_main("bench_sum.bl");

            let mut env = ElabEnv::new();
            {
                let mut prog = Program::with_resolver(&mut env, prelude_resolver);
                prog.run(&read_example("bench_sum.bl")).expect("loads");
            }
            let ty = env.global_type("main").expect("main type").clone();
            let term = env.global_term("main").expect("main term").clone();
            blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            )
            .expect("re-checker ACCEPTS the unary-Nat foldr sum (Nat/List/foldr are in-fragment)");
        })
        .expect("spawn bench_sum load thread")
        .join()
        .expect("bench_sum load thread panicked (see message above)");
}

/// `int_sum.bl`: the machine-`Int` counterpart of `bench_sum.bl` — builds a `List Int` of `n` ones
/// (counting on a unary-`Nat` spine, since `Int` has no eliminator) and `foldr int-add`s them via
/// the `std/int.bl` wrappers, giving `800` with O(1) adds (no unary allocation). It defines a
/// buildable `main : Int`; the independent re-checker ACCEPTS it (the only cubical-style decline
/// would be Glue, which this never uses — `Int`/`List`/`foldr` are all in-fragment).
#[test]
fn int_sum_example_loads_and_rechecks() {
    // `int_sum.bl` builds a 800-long `List Int` whose length lives on a unary-`Nat` spine, so
    // elaboration/recheck recurses deeply — run on an 8 MiB stack like the other deep loads.
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            assert_buildable_main("int_sum.bl");

            let mut env = ElabEnv::new();
            {
                let mut prog = Program::with_resolver(&mut env, prelude_resolver);
                prog.run(&read_example("int_sum.bl")).expect("loads");
            }
            assert!(
                env.global_term("int-add").is_some(),
                "int_sum.bl pulls in std/int.bl's `int-add` wrapper"
            );
            let ty = env.global_type("main").expect("main type").clone();
            let term = env.global_term("main").expect("main term").clone();
            blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            )
            .expect("re-checker ACCEPTS the Int foldr sum (Int/List/foldr are in-fragment)");
        })
        .expect("spawn int_sum load thread")
        .join()
        .expect("int_sum load thread panicked (see message above)");
}

/// `calculator.bl`: a tiny `Expr` evaluator over native machine `Int` (M11). `eval` is a structural
/// recursion over the AST lowering each node to an `Int` primitive; like `int_arith.bl`, the
/// independent re-checker *ACCEPTS* it (`Int`/`IntLit`/`IntPrim` are primitive kernel nodes). It
/// defines a buildable `main` evaluating `(2 + 3) * 4 - 1 = 19`.
#[test]
fn calculator_example_loads_and_rechecks() {
    assert_buildable_main("calculator.bl");

    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("calculator.bl")).expect("loads");
    }
    let ty = env.global_type("main").expect("main type").clone();
    let term = env.global_term("main").expect("main term").clone();
    blight_recheck::recheck_judgement(
        env.signature(),
        &blight_kernel::Judgement::HasType { term, ty },
    )
    .expect("re-checker ACCEPTS the Int-expression evaluator (primitive kernel nodes)");
}

/// The `examples/package` spores package: its checked-in `spore.toml` resolves the `std` dependency,
/// and `(import "demo/main")` imports `std/nat` and checks `main`.
#[test]
fn package_example_imports_and_checks() {
    let pkg_dir = examples_dir().join("package");
    let toml = std::fs::read_to_string(pkg_dir.join("spore.toml")).expect("read spore.toml");
    let manifest =
        PackageManifest::parse(&toml, &pkg_dir).expect("examples/package/spore.toml parses");

    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_package(&mut env, manifest);
        prog.run("(import \"demo/main\")")
            .expect("demo/main imports std/nat and type-checks");
    }
    assert!(
        env.global_term("plus").is_some(),
        "std/nat's plus was imported"
    );
    assert!(env.global_term("main").is_some(), "demo/main defines main");
    // Sanity: `main` re-checks through the spore at its declared type.
    let ty = env.global_type("main").expect("main has a type").clone();
    let term = env.global_term("main").expect("main term").clone();
    blight_kernel::check_top_with(env.signature().clone(), term, ty)
        .expect("demo `main` re-checks through the kernel");
}

/// `safe_head.bl`: a length-indexed `safe-head : (Vec A (Succ n)) -> Maybe A`. The example loads,
/// defines a buildable `main`, and — crucially — the `safe-head` eliminator (a `match` over the
/// *indexed* `Vec` family whose result type `Maybe A` is non-`Nat`) re-checks through the
/// independent re-checker. This is the regression guard for the indexed-`match` motive-synthesis
/// fix: before it, `safe-head` could not be kernel-checked at all.
#[test]
fn safe_head_example_loads() {
    assert_buildable_main("safe_head.bl");

    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("safe_head.bl")).expect("loads");
    }
    // The indexed eliminator must agree across both checkers: the independent re-checker may
    // `Decline` an out-of-fragment construct, but a `Rejected` here is a soundness alarm.
    let ty = env
        .global_type("safe-head")
        .expect("safe-head type")
        .clone();
    let term = env
        .global_term("safe-head")
        .expect("safe-head term")
        .clone();
    match blight_recheck::recheck_judgement(
        env.signature(),
        &blight_kernel::Judgement::HasType { term, ty },
    ) {
        Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
        Err(blight_recheck::RecheckError::Rejected(m)) => {
            panic!("re-checker REJECTED `safe-head` (soundness alarm): {m}")
        }
    }
}

/// `safe_tail.bl`: a length-indexed `safe-tail : (Vec A (Succ n)) -> Vec A n`. Unlike `safe-head`
/// (result `Maybe A`, index-independent), the result type `Vec A n` DEPENDS on the index — the
/// dependent indexed motive that used to trip a re-checker soundness alarm. The eliminator must now
/// re-check to `Ok`: the `vnil` arm is unreachable (`Zero` ≠ `Succ n`) and the `vcons` arm forces
/// the tail length to `n`.
#[test]
fn safe_tail_example_loads() {
    assert_buildable_main("safe_tail.bl");

    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("safe_tail.bl")).expect("loads");
    }
    let ty = env
        .global_type("safe-tail")
        .expect("safe-tail type")
        .clone();
    let term = env
        .global_term("safe-tail")
        .expect("safe-tail term")
        .clone();
    blight_recheck::recheck_judgement(
        env.signature(),
        &blight_kernel::Judgement::HasType { term, ty },
    )
    .expect("re-checker AGREES (Ok) on the dependent indexed motive `safe-tail`");
}

/// `vec_map.bl`: a length-preserving `vec-map : (A→B) -> Vec A n -> Vec B n`. The result type
/// `Vec B n` mentions the index AND the `vcons` arm refines `n := Succ m`, typing the recursive
/// call's induction hypothesis at the shorter length `m`. The eliminator must re-check to `Ok` —
/// the headline of the dependent-indexed-motive soundness fix.
#[test]
fn vec_map_example_loads() {
    assert_buildable_main("vec_map.bl");

    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("vec_map.bl")).expect("loads");
    }
    let ty = env.global_type("vec-map").expect("vec-map type").clone();
    let term = env.global_term("vec-map").expect("vec-map term").clone();
    blight_recheck::recheck_judgement(
        env.signature(),
        &blight_kernel::Judgement::HasType { term, ty },
    )
    .expect("re-checker AGREES (Ok) on the dependent indexed motive `vec-map`");
}

/// `zip_vec.bl`: `zip-vec : Vec A n -> Vec B n -> Vec (Pair A B) n`. Matching the first vector with
/// the second still in scope makes the elaborator lift the second vector into a *higher-order*
/// eliminator motive (`… -> Vec B n -> Vec (Pair A B) n`). As of A3 the elaborator lowers this to a
/// core term that BOTH the trusted kernel and the independent re-checker fully certify (the per-arm
/// index refinement of the lifted binder's type is done during lowering), so the re-checker now
/// *ACCEPTS* it — a `Rejected` would be a soundness alarm, and a `Declined` would mean the
/// re-verification regressed back to an honest refusal.
#[test]
fn zip_vec_example_loads() {
    assert_buildable_main("zip_vec.bl");

    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&read_example("zip_vec.bl")).expect("loads");
    }
    let ty = env.global_type("zip-vec").expect("zip-vec type").clone();
    let term = env.global_term("zip-vec").expect("zip-vec term").clone();
    match blight_recheck::recheck_judgement(
        env.signature(),
        &blight_kernel::Judgement::HasType { term, ty },
    ) {
        Ok(()) => {}
        Err(blight_recheck::RecheckError::Declined(m)) => {
            panic!("re-checker DECLINED `zip-vec` (A3 expects full re-verification): {m}")
        }
        Err(blight_recheck::RecheckError::Rejected(m)) => {
            panic!("re-checker REJECTED `zip-vec` (soundness alarm): {m}")
        }
    }
}

/// The whole point of `safe_head.bl`: calling `safe-head` on an empty vector is a *compile-time*
/// type error. We ascribe the bad call `(the (Maybe Nat) (safe-head Nat Zero (vnil)))`, which
/// routes through the trusted kernel, and assert it is rejected (the `vnil` index `Zero` cannot
/// match the demanded `Succ n`). The good call in the same prelude is accepted, so this is not a
/// load failure but a genuine index mismatch.
#[test]
fn safe_head_rejects_empty_vector() {
    let prelude = "\
(load \"std/nat.bl\")
(load \"std/maybe.bl\")
(load \"std/vec.bl\")
(define-rec safe-head (Pi ((A (Type 0)) (n Nat) (v (Vec A (Succ n)))) (Maybe A))
  (lam (A n v)
    (match v
      [(vnil) nothing]
      [(vcons m x xs) (just x)])))
";
    let good =
        format!("{prelude}(the (Maybe Nat) (safe-head Nat Zero (vcons Zero (Succ Zero) (vnil))))");
    let bad = format!("{prelude}(the (Maybe Nat) (safe-head Nat Zero (vnil)))");

    // Run on an 8 MiB stack to match the other example loaders.
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            // Good call: accepted by the kernel.
            {
                let mut env = ElabEnv::new();
                let mut prog = Program::with_resolver(&mut env, prelude_resolver);
                prog.run(&good)
                    .expect("non-empty safe-head call is accepted by the kernel");
            }
            // Bad call: rejected by the kernel (index Zero != Succ n).
            {
                let mut env = ElabEnv::new();
                let mut prog = Program::with_resolver(&mut env, prelude_resolver);
                let err = prog
                    .run(&bad)
                    .expect_err("empty-vector safe-head call must be rejected at compile time");
                let msg = format!("{err:?}");
                assert!(
                    msg.contains("index") || msg.contains("mismatch"),
                    "rejection should be an index mismatch, got: {msg}"
                );
            }
        })
        .expect("spawn safe-head reject thread")
        .join()
        .expect("safe-head reject thread panicked (see message above)");
}
