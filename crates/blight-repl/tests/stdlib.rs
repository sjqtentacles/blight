//! Standard-library load tests (spec §6, §8 M6 stdlib reorg): each `std/` module loads *in
//! isolation* through the public `Program` driver, and every form in it is accepted by the spore.
//! Loading a module also brings in (splices) its declared dependencies, so each test asserts on the
//! symbols the module is responsible for. Black-box: the `blight-elab` `Program` driver only.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Load one std module, assert every form is accepted, and run `check` against the resulting env
/// *on the worker thread* (post-S3, `Term` holds `Rc`s, so an `ElabEnv` cannot cross `join`). Runs on an 8 MiB-stack worker thread (matching `examples.rs`/`spore.rs`): several
/// std modules elaborate/kernel-check deeply-recursive bodies — `char` codepoint chains and the
/// higher-order (`Π`-conclusion) eliminator motives the kernel now fully certifies — which exceed
/// the ~2 MiB `cargo test` worker stack but fit comfortably here (the CLI main thread already uses a
/// large stack).
fn with_module<R: Send + 'static>(
    module: &str,
    check: impl FnOnce(&ElabEnv) -> R + Send + 'static,
) -> R {
    let module = module.to_string();
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || check(&load_module_inner(&module)))
        .expect("spawn std-module load thread")
        .join()
        .expect("std-module load thread panicked (see message above)")
}

fn load_module_inner(module: &str) -> ElabEnv {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&format!("(load \"{module}\")"))
            .unwrap_or_else(|e| panic!("std module {module} loads cleanly, got: {e:?}"))
    };
    assert!(
        outcomes
            .iter()
            .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
        "every form in {module} is a well-typed declaration (or a kernel-checked proof)"
    );
    env
}

#[test]
fn std_nat_loads_in_isolation() {
    with_module("std/nat.bl", |env| {
        assert!(env.data_constructors("Nat").is_some(), "Nat is declared");
        for f in ["plus", "mult", "pred", "min", "max", "sub", "even", "odd"] {
            assert!(env.global_term(f).is_some(), "std/nat defines `{f}`");
        }
    });
}

#[test]
fn std_bool_loads_in_isolation() {
    with_module("std/bool.bl", |env| {
        assert!(env.data_constructors("Bool").is_some(), "Bool is declared");
        for f in ["not", "and", "or"] {
            assert!(env.global_term(f).is_some(), "std/bool defines `{f}`");
        }
    });
}

#[test]
fn std_order_loads_in_isolation() {
    with_module("std/order.bl", |env| {
        for f in ["nat-le", "nat-eq", "show", "cmp", "ORD", "Nat-Ord"] {
            assert!(env.global_term(f).is_some(), "std/order defines `{f}`");
        }
        assert!(env.is_class("Show"), "Show is a registered class");
        assert!(env.is_class("Ord"), "Ord is a registered class");
    });
}

#[test]
fn std_char_loads_in_isolation() {
    with_module("std/char.bl", |env| {
        for f in [
            "char-newline",
            "char-space",
            "char-zero",
            "char-A",
            "char-a",
            "digit-char",
            "is-lower",
            "is-upper",
        ] {
            assert!(env.global_term(f).is_some(), "std/char defines `{f}`");
        }
    });
}

#[test]
fn std_list_loads_in_isolation() {
    with_module("std/list.bl", |env| {
        assert!(env.data_constructors("List").is_some(), "List is declared");
        for f in [
            "length", "append", "map", "filter", "reverse", "foldr", "concat",
        ] {
            assert!(env.global_term(f).is_some(), "std/list defines `{f}`");
        }
    });
}

#[test]
fn std_list_extra_loads_in_isolation() {
    with_module("std/list_extra.bl", |env| {
        for f in ["take", "drop", "foldl", "zip", "elem", "sort"] {
            assert!(env.global_term(f).is_some(), "std/list_extra defines `{f}`");
        }
    });
}

#[test]
fn std_maybe_loads_in_isolation() {
    with_module("std/maybe.bl", |env| {
        assert!(
            env.data_constructors("Maybe").is_some(),
            "Maybe is declared"
        );
        for f in ["maybe", "maybe-map", "from-maybe", "maybe-bind", "maybe-or"] {
            assert!(env.global_term(f).is_some(), "std/maybe defines `{f}`");
        }
    });
}

#[test]
fn std_either_loads_in_isolation() {
    // `Either` is a two-parameter inductive — only loadable after the multi-parameter cap lift.
    with_module("std/either.bl", |env| {
        assert!(
            env.data_constructors("Either").is_some(),
            "Either is declared"
        );
        for f in [
            "either",
            "either-map-right",
            "either-map-left",
            "either-bind",
        ] {
            assert!(env.global_term(f).is_some(), "std/either defines `{f}`");
        }
        // Re-check a multi-parameter eliminator end-to-end through the *independent* re-checker: the
        // cap-lift is a TCB change, so the second checker must agree (or honestly decline), never reject.
        let ty = env.global_type("either").expect("either type").clone();
        let term = env.global_term("either").expect("either term").clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/either `either` (soundness alarm): {m}")
            }
        }
    });
}

#[test]
fn std_hashmap_loads_in_isolation() {
    // The effectful Int-keyed hash map over `Array A` (D4): pure indexing layer + effectful API +
    // CPS `*-then` combinators. The four in-file `define-by … compute` Path pins (bridges +
    // bucket indexing incl. a negative key) are kernel-checked by the load itself.
    with_module("std/hashmap.bl", |env| {
        for f in [
            "hm-nat-to-int",
            "hm-int-to-nat-below",
            "hm-idx",
            "hm-bucket-find",
            "hm-new",
            "hm-put",
            "hm-get",
            "hm-new-then",
            "hm-put-then",
            "hm-get-then",
        ] {
            assert!(env.global_term(f).is_some(), "std/hashmap defines `{f}`");
        }
        // Re-check the pure indexing core through the *independent* re-checker (agree or honestly
        // decline, never reject).
        for f in ["hm-idx", "hm-bucket-find"] {
            let ty = env.global_type(f).expect("hashmap member type").clone();
            let term = env.global_term(f).expect("hashmap member term").clone();
            match blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            ) {
                Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("re-checker REJECTED std/hashmap `{f}` (soundness alarm): {m}")
                }
            }
        }
    });
}

#[test]
fn std_result_loads_in_isolation() {
    // `Result a e` — Either specialized to value-or-error, with the railway combinators (D3).
    with_module("std/result.bl", |env| {
        assert!(
            env.data_constructors("Result").is_some(),
            "Result is declared"
        );
        for f in [
            "result",
            "result-map",
            "result-map-err",
            "result-bind",
            "result-unwrap-or",
        ] {
            assert!(env.global_term(f).is_some(), "std/result defines `{f}`");
        }
        // Re-check the eliminator through the *independent* re-checker (agree or honestly
        // decline, never reject) — same discipline as std/either's pin.
        let ty = env.global_type("result").expect("result type").clone();
        let term = env.global_term("result").expect("result term").clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/result `result` (soundness alarm): {m}")
            }
        }
    });
}

#[test]
fn std_string_loads_in_isolation() {
    with_module("std/string.bl", |env| {
        assert!(
            env.data_constructors("String").is_some(),
            "String is declared"
        );
        for f in [
            "string-length",
            "string-append",
            "string-reverse",
            "string-eq",
            "string-map",
            "string-shift",
        ] {
            assert!(env.global_term(f).is_some(), "std/string defines `{f}`");
        }
    });
}

#[test]
fn std_string_extra_loads_in_isolation() {
    with_module("std/string_extra.bl", |env| {
        for f in [
            "string-take",
            "string-drop",
            "string-repeat",
            "string-concat",
        ] {
            assert!(
                env.global_term(f).is_some(),
                "std/string_extra defines `{f}`"
            );
        }
    });
}

#[test]
fn std_function_loads_in_isolation() {
    with_module("std/function.bl", |env| {
        for f in ["id", "compose", "const", "flip"] {
            assert!(env.global_term(f).is_some(), "std/function defines `{f}`");
        }
    });
}

#[test]
fn std_pair_loads_in_isolation() {
    // `Pair a b` is a two-parameter inductive (non-dependent product).
    with_module("std/pair.bl", |env| {
        assert!(env.data_constructors("Pair").is_some(), "Pair is declared");
        for f in ["pair-fst", "pair-snd", "pair-swap"] {
            assert!(env.global_term(f).is_some(), "std/pair defines `{f}`");
        }
        // Multi-parameter eliminator must agree across both checkers (Declined is acceptable, Rejected
        // is a soundness alarm).
        let ty = env.global_type("pair-fst").expect("pair-fst type").clone();
        let term = env.global_term("pair-fst").expect("pair-fst term").clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/pair `pair-fst` (soundness alarm): {m}")
            }
        }
    });
}

#[test]
fn std_io_loads_in_isolation() {
    // `std/io.bl` declares the `Console` (M7) and `FileIO` (C1) effects plus their convenience
    // wrappers, and splices in `std/string.bl` and `std/pair.bl` (the `Pair` envelope `write-file`
    // uses). Loading it cleanly is the surface-level proof the C1 effect is well-formed.
    with_module("std/io.bl", |env| {
        for f in ["put-str", "get-line", "read-file-str", "write-file-str"] {
            assert!(env.global_term(f).is_some(), "std/io defines `{f}`");
        }
        // `write-file` carries a `(Pair String String)` arg, so the module must pull in `Pair`.
        assert!(
            env.data_constructors("Pair").is_some(),
            "std/io splices in std/pair (write-file's Pair envelope)"
        );
    });
}

#[test]
fn std_bytes_loads_in_isolation() {
    // `std/bytes.bl` declares the C2 `Bytes` effect plus its `bytes-new`/`bytes-length`/`bytes-get`/
    // `bytes-set` wrappers, splicing in `std/nat`, `std/int` (the `Int` handle type), and `std/pair`
    // (the multi-arg envelopes). Loading it cleanly is the surface-level proof the C2 effect is
    // well-formed; `example_bytes_scratch_builds_and_runs` runs it natively.
    with_module("std/bytes.bl", |env| {
        for f in ["bytes-new", "bytes-length", "bytes-get", "bytes-set"] {
            assert!(env.global_term(f).is_some(), "std/bytes defines `{f}`");
        }
        // The handle is a plain `Int` and multi-arg ops are packed with `Pair`.
        assert!(
            env.data_constructors("Pair").is_some(),
            "std/bytes splices in std/pair (the get/set arg envelopes)"
        );
    });
}

#[test]
fn std_array_loads_in_isolation() {
    // `std/array.bl` declares the A3a `Arrays` effect plus its `array-new`/`array-length`/
    // `array-get`/`array-set` wrappers — the exact `Bytes` pattern with `Int` elements instead of
    // bytes, splicing in `std/nat`, `std/int` (both the handle type and the element type), and
    // `std/pair` (the multi-arg envelopes). Loading it cleanly is the surface-level proof the A3a
    // effect is well-formed; `example_array_scratch_builds_and_runs` runs it natively.
    with_module("std/array.bl", |env| {
        for f in ["array-new", "array-length", "array-get", "array-set"] {
            assert!(env.global_term(f).is_some(), "std/array defines `{f}`");
        }
        // The handle is a plain `Int` and multi-arg ops are packed with `Pair`.
        assert!(
            env.data_constructors("Pair").is_some(),
            "std/array splices in std/pair (the get/set arg envelopes)"
        );
    });
}

#[test]
fn std_array_boxed_loads_in_isolation() {
    // `std/array.bl` also declares the A3b `Array A` effect (roadmap Wave 10 / P1) — the generic/
    // boxed sibling of A3a's `Arrays`, parameterized over the element type via Wave 7/E2's effect
    // parameter telescopes — plus its `boxed-array-new`/`boxed-array-length`/`boxed-array-get`/
    // `boxed-array-set` wrappers. Loading it cleanly is the surface-level proof the parameterized
    // effect declaration and its wrappers are well-formed; `example_boxed_array_scratch_builds_and_runs`
    // runs it natively (and `runtime/tests/gc_test.c`'s boxed-array tests prove the GC-safety design
    // this effect rides on: a rooted handle table + write barrier, see boxed_array.c).
    with_module("std/array.bl", |env| {
        for f in [
            "boxed-array-new",
            "boxed-array-length",
            "boxed-array-get",
            "boxed-array-set",
        ] {
            assert!(env.global_term(f).is_some(), "std/array defines `{f}`");
        }
    });
}

/// Layer 1 of P2's four-layer TDD (roadmap Wave 10 / P2, docs/design-wave4-gobars.md §5): the
/// `Graphics` effect declaration + `gfx-*` wrappers are a well-formed, type-checking effect exactly
/// like every prior native-handler effect (`Console`/`Bytes`/`Arrays`/`Array`) — this test never
/// links SDL2 or the `graphics.c` handler (that only happens for an actual `builds_and_runs`
/// compile, layer 3, `example_graphics_scratch_builds_and_runs`, gated behind the `graphics` cargo
/// feature), so it runs unconditionally in every build.
#[test]
fn std_graphics_loads_in_isolation() {
    with_module("std/graphics.bl", |env| {
        for f in [
            "gfx-init-window",
            "gfx-poll-input",
            "gfx-clear",
            "gfx-draw-rect",
            "gfx-present",
        ] {
            assert!(env.global_term(f).is_some(), "std/graphics defines `{f}`");
        }
    });
}

#[test]
fn std_time_loads_in_isolation() {
    // `std/time.bl` declares the Wave 2 `Clock` effect (a single total `now : Unit -> Int` op) plus
    // its `clock-now`/`elapsed-ms` wrappers — the smallest possible native-handler effect, splicing
    // in `std/int` for the `Int` timestamp type. Loading it cleanly is the surface-level proof the
    // effect is well-formed; `example_clock_scratch_builds_and_runs` runs it natively.
    with_module("std/time.bl", |env| {
        for f in ["clock-now", "elapsed-ms"] {
            assert!(env.global_term(f).is_some(), "std/time defines `{f}`");
        }
    });
}

#[test]
fn std_test_loads_in_isolation() {
    // `std/test.bl` is the Wave 2 in-language test framework: `deftest` + assert combinators, plus
    // `TestSuite` reporting. Entirely pure, so every wrapper must re-check (Declined would be a
    // regression — nothing here touches an out-of-fragment construct).
    with_module("std/test.bl", |env| {
        for f in [
            "deftest",
            "assert-true",
            "assert-false",
            "assert-eq-bool",
            "assert-eq-nat",
            "assert-eq-string",
            "suite-total",
            "suite-passed",
            "suite-all-passed",
            "render-suite",
        ] {
            assert!(env.global_term(f).is_some(), "std/test defines `{f}`");
        }
        for f in ["deftest", "suite-all-passed"] {
            let ty = env.global_type(f).expect("test member type").clone();
            let term = env.global_term(f).expect("test member term").clone();
            match blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            ) {
                Ok(()) => {}
                Err(blight_recheck::RecheckError::Declined(m)) => {
                    panic!("std/test `{f}` is pure and should re-check, got Declined: {m}")
                }
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("re-checker REJECTED std/test `{f}` (soundness alarm): {m}")
                }
            }
        }
    });
}

#[test]
fn std_map_loads_in_isolation() {
    // `std/map.bl` is the Wave 2 ordered map/set: a `TreeMap` keyed by an explicit 3-way `compare`
    // (built on `std/ordering.bl`'s `Ordering`, not on `std/tree.bl`'s boolean-`cmp` `Tree` directly,
    // since a map needs to detect key equality to upsert). Entirely pure.
    with_module("std/map.bl", |env| {
        assert!(
            env.data_constructors("TreeMap").is_some(),
            "TreeMap is declared"
        );
        for f in [
            "map-empty",
            "map-insert",
            "map-lookup",
            "map-member",
            "map-to-list",
            "map-size",
            "map-from-list",
            "nat-map-insert",
            "nat-map-lookup",
            "set-empty",
            "set-insert",
            "set-member",
            "set-to-list",
        ] {
            assert!(env.global_term(f).is_some(), "std/map defines `{f}`");
        }
        let ty = env.global_type("nat-map-insert").expect("type").clone();
        let term = env.global_term("nat-map-insert").expect("term").clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) => {}
            Err(blight_recheck::RecheckError::Declined(m)) => {
                panic!("std/map `nat-map-insert` is pure and should re-check, got Declined: {m}")
            }
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/map `nat-map-insert` (soundness alarm): {m}")
            }
        }
    });
}

#[test]
fn std_json_loads_in_isolation() {
    // `std/json.bl` is the Wave 2 JSON value tree + total structural encoder (`BJson`, merged-spine
    // arrays/objects, a 3-member `(mutual …)` group for the encoder — see the module header for why).
    with_module("std/json.bl", |env| {
        assert!(
            env.data_constructors("BJson").is_some(),
            "BJson is declared"
        );
        for f in [
            "json-encode",
            "json-array-rest",
            "json-object-rest",
            "j-arr",
            "j-obj",
            "nat-to-string",
        ] {
            assert!(env.global_term(f).is_some(), "std/json defines `{f}`");
        }
    });
}

#[test]
fn std_regex_loads_in_isolation() {
    // `std/regex.bl` is the Wave 2 minimal regex engine: Brzozowski derivatives over a `Regex` AST,
    // a genuinely structural fit for this kernel's totality checker (see the module header). Entirely
    // pure, so the re-checker must accept (not decline) it.
    with_module("std/regex.bl", |env| {
        assert!(
            env.data_constructors("Regex").is_some(),
            "Regex is declared"
        );
        for f in ["r-str", "nullable", "deriv", "regex-match"] {
            assert!(env.global_term(f).is_some(), "std/regex defines `{f}`");
        }
        let ty = env.global_type("regex-match").expect("type").clone();
        let term = env.global_term("regex-match").expect("term").clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) => {}
            Err(blight_recheck::RecheckError::Declined(m)) => {
                panic!("std/regex `regex-match` is pure and should re-check, got Declined: {m}")
            }
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/regex `regex-match` (soundness alarm): {m}")
            }
        }
    });
}

#[test]
fn std_ordering_loads_in_isolation() {
    with_module("std/ordering.bl", |env| {
        assert!(
            env.data_constructors("Ordering").is_some(),
            "Ordering is declared"
        );
        for f in ["nat-compare", "ordering-flip"] {
            assert!(env.global_term(f).is_some(), "std/ordering defines `{f}`");
        }
        let ty = env
            .global_type("nat-compare")
            .expect("nat-compare type")
            .clone();
        let term = env
            .global_term("nat-compare")
            .expect("nat-compare term")
            .clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/ordering `nat-compare` (soundness alarm): {m}")
            }
        }
    });
}

#[test]
fn std_vec_loads_in_isolation() {
    // `Vec a n` is an indexed family (one parameter + one `Nat` index).
    with_module("std/vec.bl", |env| {
        assert!(env.data_constructors("Vec").is_some(), "Vec is declared");
        assert!(
            env.global_term("vec-length").is_some(),
            "std/vec defines `vec-length`"
        );
        // Indexed-family re-check through the independent checker (Declined is acceptable for the
        // out-of-fragment cubical machinery, but a Rejection would be a soundness alarm).
        let ty = env
            .global_type("vec-length")
            .expect("vec-length type")
            .clone();
        let term = env
            .global_term("vec-length")
            .expect("vec-length term")
            .clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/vec `vec-length` (soundness alarm): {m}")
            }
        }
    });
}

/// `std/equiv.bl` defines the univalence-grade `Equiv A B` (contractible-fibres `is-equiv`) plus
/// `id-equiv`, whose contractibility proof is a De Morgan *connection* term (`p @ (imax (~i) j)`)
/// under nested `plam`s. Regression guard for the kernel boundary-check dimension-depth fix: these
/// must re-check through the independent checker without a *Rejection* (a Declined is acceptable for
/// the out-of-fragment cubical machinery; a Rejection would be a soundness alarm).
#[test]
fn std_equiv_loads_in_isolation() {
    with_module("std/equiv.bl", |env| {
        for f in [
            "is-contr",
            "fiber",
            "is-equiv",
            "Equiv",
            "equiv-fun",
            "id-equiv",
        ] {
            assert!(env.global_term(f).is_some(), "std/equiv defines `{f}`");
        }
        for f in ["id-equiv", "equiv-fun"] {
            let ty = env.global_type(f).expect("equiv member type").clone();
            let term = env.global_term(f).expect("equiv member term").clone();
            match blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            ) {
                Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("re-checker REJECTED std/equiv `{f}` (soundness alarm): {m}")
                }
            }
        }
    });
}

/// `std/path.bl` defines `funext` (function extensionality, pure Path/plam) and `ua : Equiv A B ->
/// Path (Type 0) A B` (built from a single-face `Glue`). The host kernel type-checks both; the
/// independent re-checker is expected to *decline* `ua` (Glue is outside its fragment) but must
/// never *reject* it, while `funext` should re-check cleanly (no Glue). The univalence *computation*
/// rule is verified separately (kernel white-box test + `examples/ua_compute.bl`), not as a
/// polymorphic Blight lemma — see `std/path.bl`/docs/metatheory.md.
#[test]
fn std_path_loads_in_isolation() {
    with_module("std/path.bl", |env| {
        for f in ["funext", "ua"] {
            assert!(env.global_term(f).is_some(), "std/path defines `{f}`");
        }
        for f in ["funext", "ua"] {
            let ty = env.global_type(f).expect("path member type").clone();
            let term = env.global_term(f).expect("path member term").clone();
            match blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            ) {
                Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("re-checker REJECTED std/path `{f}` (soundness alarm): {m}")
                }
            }
        }
    });
}

#[test]
fn std_tree_loads_in_isolation() {
    with_module("std/tree.bl", |env| {
        assert!(env.data_constructors("Tree").is_some(), "Tree is declared");
        for f in ["tree-if", "tree-insert", "RedBlackTree", "NatTree"] {
            assert!(env.global_term(f).is_some(), "std/tree defines `{f}`");
        }
        // Re-check the functor application end-to-end through the spore.
        let ty = env.global_type("NatTree").expect("NatTree type").clone();
        let term = env.global_term("NatTree").expect("NatTree term").clone();
        if let Err(e) = blight_kernel::check_top_with(env.signature().clone(), term, ty) {
            panic!("std/tree NatTree re-check failed: {e:?}");
        }
    });
}

/// `std/int.bl` wraps the primitive machine-`Int` operations as named, first-class total functions.
/// Each wrapper is a non-recursive `deftotal` forwarding to a kernel primitive, so the independent
/// re-checker must *accept* them (`Int`/`IntPrim` are inside its fragment — not declined like Glue),
/// confirming the wrappers add no out-of-fragment surface.
#[test]
fn std_int_loads_in_isolation() {
    with_module("std/int.bl", |env| {
        for f in [
            "int-add",
            "int-sub",
            "int-mul",
            "int-div",
            "int-eq",
            "int-lt",
            "int-zero",
            "int-one",
            "int-double",
            "int-succ",
            "int-pred",
            "int-mod",
            "int-abs",
        ] {
            assert!(env.global_term(f).is_some(), "std/int defines `{f}`");
        }
        for f in [
            "int-add",
            "int-mul",
            "int-double",
            "int-succ",
            "int-mod",
            "int-abs",
        ] {
            let ty = env.global_type(f).expect("int member type").clone();
            let term = env.global_term(f).expect("int member term").clone();
            match blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            ) {
                Ok(()) => {}
                Err(blight_recheck::RecheckError::Declined(m)) => {
                    panic!("std/int `{f}` should re-check (Int is in-fragment), got Declined: {m}")
                }
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("re-checker REJECTED std/int `{f}` (soundness alarm): {m}")
                }
            }
        }
    });
}

/// `std/float.bl` (M23) defines `Float` as an UNTRUSTED fixed-point rational over the trusted `Int`
/// base — no kernel `FloatTy`. It must load in isolation, and because every wrapper bottoms out in
/// `Int` primitives over a plain one-field `Data`, the independent re-checker must *accept* the
/// wrappers (not decline like the cubical machinery), confirming `Float` adds no trusted surface.
#[test]
fn std_float_loads_in_isolation() {
    with_module("std/float.bl", |env| {
        assert!(
            env.data_constructors("Float").is_some(),
            "Float is declared as ordinary data"
        );
        for f in [
            "float-of-int",
            "float-add",
            "float-sub",
            "float-mul",
            "float-div",
            "float-eq",
            "float-lt",
            "float-neg",
            "float-double",
            "float-zero",
            "float-one",
            "float-mantissa",
            "float-scale",
        ] {
            assert!(env.global_term(f).is_some(), "std/float defines `{f}`");
        }
        for f in ["float-add", "float-mul", "float-of-int", "float-double"] {
            let ty = env.global_type(f).expect("float member type").clone();
            let term = env.global_term(f).expect("float member term").clone();
            match blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            ) {
                Ok(()) => {}
                Err(blight_recheck::RecheckError::Declined(m)) => {
                    panic!(
                        "std/float `{f}` should re-check (Float is plain Int data), got Declined: {m}"
                    )
                }
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("re-checker REJECTED std/float `{f}` (soundness alarm): {m}")
                }
            }
        }
    });
}

/// `std/f64.bl` (Wave 2 / L2) defines `F64` as an UNVERIFIED `foreign` postulate over hardware
/// `double`s — the opposite trade-off from `std/float.bl`'s verified fixed-point rational. It must
/// load in isolation, define every operation, and — crucially, the whole point of the `foreign`
/// hatch's safety story — the independent re-checker must *DECLINE* (never silently accept, never
/// reject) any of its members, since each one's type mentions the `foreign` `F64`.
#[test]
fn std_f64_loads_in_isolation() {
    with_module("std/f64.bl", |env| {
        assert!(
            env.data_constructors("F64").is_none(),
            "F64 is a `foreign` postulate, not ordinary `Data` (unlike Float)"
        );
        for f in [
            "f64-of-int",
            "f64-round",
            "f64-add",
            "f64-sub",
            "f64-mul",
            "f64-div",
            "f64-neg",
            "f64-lt",
            "f64-eq",
            "f64-plus",
            "f64-minus",
            "f64-times",
            "f64-over",
            "f64-less-than",
            "f64-equal",
            "f64-zero",
            "f64-one",
        ] {
            assert!(env.global_term(f).is_some(), "std/f64 defines `{f}`");
        }
        // Every member's type mentions the `foreign` `F64`, so the independent re-checker must decline
        // each one (an honest refusal, not a false accept and not a soundness rejection).
        for f in ["f64-of-int", "f64-round", "f64-plus", "f64-zero"] {
            let ty = env.global_type(f).expect("f64 member type").clone();
            let term = env.global_term(f).expect("f64 member term").clone();
            match blight_recheck::recheck_judgement(
                env.signature(),
                &blight_kernel::Judgement::HasType { term, ty },
            ) {
                Err(blight_recheck::RecheckError::Declined(msg)) => {
                    assert!(
                        msg.contains("foreign"),
                        "decline reason for `{f}` should name the foreign postulate, got: {msg}"
                    );
                }
                other => {
                    panic!("re-checker must DECLINE std/f64 `{f}` (foreign F64), got: {other:?}")
                }
            }
        }
    });
}

/// `std/actor.bl` (M16) declares the actor/CSP concurrency surface as a graded `Actor` effect plus
/// a cooperative single-core scheduler handler. It must load and type-check in isolation: the
/// effect declaration, the four `perform` wrappers, and the `run-with-inbox` handler are all
/// well-typed declarations. This test only asserts the kernel accepts them (the grade-violation
/// safety proof lives as a kernel test); `--recheck` agreement on the full `Actor` surface is
/// exercised end-to-end by `actor_pingpong_example_loads` (effects are modeled at the type level
/// by the independent re-checker, not declined).
#[test]
fn std_actor_loads_in_isolation() {
    with_module("std/actor.bl", |env| {
        for f in ["actor-spawn", "actor-send", "actor-receive", "actor-yield"] {
            assert!(env.global_term(f).is_some(), "std/actor defines `{f}`");
        }
    });
}

/// `examples/row_polymorphic_handler.bl` (Wave 7 / E1: row polymorphism, tower-first): a
/// row-polymorphic handler ascription `(the (! (Extra1 | r) Nat) (handle ...))`. The handled
/// computation performs `State.get` (fully discharged by the one clause) and, in its `return`
/// clause, two further unhandled effects `Extra1.bump1`/`Extra2.bump2`. The ascription only names
/// `Extra1`; the elaborator resolves the row variable `r` by asking the trusted kernel checker
/// (`Checker::infer_g`) what the handle's actual row is and unifying the declared pattern against
/// it — so `r` picks up exactly `{Extra2}`, the row's *extension*, with no kernel change at all
/// (`blight-kernel/src/row.rs`'s `RowVar`/open-tail plumbing stays completely dormant). This is
/// the end-to-end (`examples/`-backed, full `Program` driver) twin of
/// `elab::tests::row_polymorphic_handler_ascription_resolves_tail`, which exercises the identical
/// mechanism directly against `blight-elab`.
#[test]
fn row_polymorphic_handler_composes() {
    let src = std::fs::read_to_string(format!(
        "{}/../../examples/row_polymorphic_handler.bl",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("read examples/row_polymorphic_handler.bl");
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&src)
            .unwrap_or_else(|e| panic!("row_polymorphic_handler.bl loads, got: {e:?}"))
    };
    assert!(
        outcomes
            .iter()
            .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
        "every form is accepted; got {outcomes:?}"
    );

    let term = env
        .global_term("composed")
        .expect("`composed` is defined")
        .clone();
    match term {
        blight_kernel::Term::Ann(inner, ty) => {
            assert!(
                matches!(*inner, blight_kernel::Term::Handle { .. }),
                "the ascribed term is the Handle itself"
            );
            match blight_kernel::unshare(ty) {
                blight_kernel::Term::EffTy(row, _) => {
                    assert!(
                        row.contains(&blight_kernel::EffName::new("Extra1")),
                        "Extra1 is present, exactly as declared"
                    );
                    assert!(
                        row.contains(&blight_kernel::EffName::new("Extra2")),
                        "Extra2 is present -- the row variable `r` resolved to it"
                    );
                    assert!(
                        !row.contains(&blight_kernel::EffName::new("State")),
                        "State was fully discharged by the handler, so it does not leak into `r`"
                    );
                }
                other => panic!("expected `composed`'s type to be Term::EffTy, got {other:?}"),
            }
        }
        other => panic!("expected `composed`'s term to be Term::Ann, got {other:?}"),
    }
}

/// `std/lexer.bl` (C3 self-hosting): a byte scanner written entirely in `.bl` over the C2 `Bytes`
/// substrate. The pure classifiers (`is-space`/`is-digit`/`paren-step`) are `deftotal` and need no
/// effect row; `string->bytes`/`max-paren-depth` are `(! Bytes …)` effectful, which the independent
/// re-checker now models at the type level too (not declined). Loading it in isolation is the
/// surface proof the self-hosted scanner is well-formed.
#[test]
fn std_lexer_loads_in_isolation() {
    with_module("std/lexer.bl", |env| {
        for f in [
            "is-space",
            "is-digit",
            "paren-step",
            "scan-depth",
            "string->bytes",
            "max-paren-depth",
        ] {
            assert!(env.global_term(f).is_some(), "std/lexer defines `{f}`");
        }
        // The pure classifier must re-check (it never touches `Bytes`).
        let ty = env.global_type("is-digit").expect("is-digit type").clone();
        let term = env.global_term("is-digit").expect("is-digit term").clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) => {}
            Err(blight_recheck::RecheckError::Declined(m)) => {
                panic!("std/lexer `is-digit` is pure and should re-check, got Declined: {m}")
            }
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/lexer `is-digit` (soundness alarm): {m}")
            }
        }
    });
}

/// `std/parser.bl` (SH1 self-hosting): a tokenizer + pure stack-machine s-expression parser written
/// entirely in `.bl` over the C3 byte scanner. The tokenizer (`tokenize`/`tok-go`) is `(! Bytes …)`,
/// which the independent re-checker now models at the type level too (not declined); the whole
/// parser core (`parse-tokens`, `next-state`, `count-atoms`) is additionally a PURE total function
/// the re-checker must *accept* on that basis as well — the self-hosting payoff.
#[test]
fn std_parser_loads_in_isolation() {
    with_module("std/parser.bl", |env| {
        for f in [
            "tokenize",
            "parse-tokens",
            "parse-string",
            "count-atoms",
            "sexp-atoms",
            "next-state",
        ] {
            assert!(env.global_term(f).is_some(), "std/parser defines `{f}`");
        }
        // The pure parser core re-checks `Ok` (no `Bytes` effect anywhere in `parse-tokens`).
        let ty = env
            .global_type("parse-tokens")
            .expect("parse-tokens type")
            .clone();
        let term = env
            .global_term("parse-tokens")
            .expect("parse-tokens term")
            .clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) => {}
            Err(blight_recheck::RecheckError::Declined(m)) => {
                panic!("std/parser `parse-tokens` is a pure total stack machine and should re-check, got Declined: {m}")
            }
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED std/parser `parse-tokens` (soundness alarm): {m}")
            }
        }
    });
}

/// Coverage guard: *every* `std/*.bl` module must load in isolation. The per-module tests above pin
/// the symbols each module is responsible for; this directory walk additionally guarantees a newly
/// added module cannot silently rot (or be forgotten by the suite) — it will fail here until it both
/// loads cleanly and is wired into the explicit list below.
#[test]
fn every_std_module_loads_in_isolation() {
    let std_dir = format!("{}/../blight-prelude/std", env!("CARGO_MANIFEST_DIR"));
    let mut modules: Vec<String> = std::fs::read_dir(&std_dir)
        .unwrap_or_else(|e| panic!("read std dir {std_dir:?}: {e}"))
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.ends_with(".bl"))
        .collect();
    modules.sort();
    assert!(
        modules.len() >= 20,
        "expected the full std library on disk, found only {}: {modules:?}",
        modules.len()
    );

    // The set of modules with a dedicated `std_*_loads_in_isolation` test above. If you add a module,
    // add a focused test and list it here; the discovery walk then proves the two stay in sync.
    let explicitly_tested: &[&str] = &[
        "actor.bl",
        "array.bl",
        "bool.bl",
        "bytes.bl",
        "char.bl",
        "either.bl",
        "equiv.bl",
        "f64.bl",
        "float.bl",
        "function.bl",
        "graphics.bl",
        "int.bl",
        "io.bl",
        "hashmap.bl",
        "json.bl",
        "lexer.bl",
        "list.bl",
        "list_extra.bl",
        "map.bl",
        "maybe.bl",
        "nat.bl",
        "order.bl",
        "ordering.bl",
        "pair.bl",
        "parser.bl",
        "path.bl",
        "prelude.bl",
        "regex.bl",
        "result.bl",
        "string.bl",
        "string_extra.bl",
        "test.bl",
        "time.bl",
        "tree.bl",
        "vec.bl",
    ];

    for m in &modules {
        // Loading on the shared 8 MiB-stack worker; a parse/type error or panic fails the suite.
        with_module(&format!("std/{m}"), |_| ());
        assert!(
            explicitly_tested.contains(&m.as_str()),
            "std/{m} has no dedicated `std_*_loads_in_isolation` test — add one (and list it in \
             `every_std_module_loads_in_isolation`) so its symbols are pinned, not just that it parses"
        );
    }
}

/// Wave 7/E2 e2e twin: a *parameterized* `Ref A` effect (`get : Unit -> A`, `put : A -> Unit`)
/// declared once at the surface, then genuinely instantiated at two different concrete types in
/// the same program — `Ref Nat` and `Ref Bool` — via the `(perform op (T ...) arg)` explicit
/// type-argument syntax. This is the surface-level, full-`Program`-driver proof that E2 delivers
/// real parametricity (not just one hardcoded instantiation), mirroring the direct-API kernel test
/// `check::tests::parameterized_op_instantiates_type_arg` and its recheck twin
/// `typecheck::tests::parameterized_effect_roundtrips`. Handling a parameterized effect is out of
/// scope for E2 (see `check::tests::handling_parameterized_effect_op_rejected`), so this program
/// only declares and performs — it does not `handle`.
#[test]
fn generic_ref_effect_typechecks() {
    let src = r#"
        (load "std/nat.bl")
        (load "std/bool.bl")

        (defdata Unit () (tt))

        (effect Ref ((A (Type 0)))
          (get Unit A)
          (put A Unit))

        (deftotal get-nat (Pi ((u Unit)) (! Ref Nat))
          (lam (u) (perform get (Nat) u)))

        (deftotal put-bool (Pi ((b Bool)) (! Ref Unit))
          (lam (b) (perform put (Bool) b)))
    "#;
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(src)
            .unwrap_or_else(|e| panic!("generic Ref A program loads, got: {e:?}"))
    };
    assert!(
        outcomes
            .iter()
            .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
        "every form is accepted; got {outcomes:?}"
    );

    // `get-nat : Unit -> ! Ref Nat` — the type argument instantiates the result to `Nat`, not
    // some other type.
    let get_nat_ty = env.global_type("get-nat").expect("get-nat type").clone();
    match get_nat_ty {
        blight_kernel::Term::Pi(_, _, body) => match blight_kernel::unshare(body) {
            blight_kernel::Term::EffTy(row, payload) => {
                assert!(row.contains(&blight_kernel::EffName::new("Ref")));
                assert!(
                    matches!(*payload, blight_kernel::Term::Data(ref d, ..) if d.0 == "Nat"),
                    "get-nat's payload is instantiated to Nat, got {payload:?}"
                );
            }
            other => panic!("expected get-nat's codomain to be Term::EffTy, got {other:?}"),
        },
        other => panic!("expected get-nat's type to be Term::Pi, got {other:?}"),
    }

    // `put-bool : Bool -> ! Ref Unit` — the *same* effect, instantiated at a *different* type in
    // the same program: the whole point of E2 over a hardcoded single-instantiation effect.
    let put_bool_ty = env.global_type("put-bool").expect("put-bool type").clone();
    match put_bool_ty {
        blight_kernel::Term::Pi(_, _, body) => match blight_kernel::unshare(body) {
            blight_kernel::Term::EffTy(row, payload) => {
                assert!(row.contains(&blight_kernel::EffName::new("Ref")));
                assert!(
                    matches!(*payload, blight_kernel::Term::Data(ref d, ..) if d.0 == "Unit"),
                    "put-bool's payload is Unit, got {payload:?}"
                );
            }
            other => panic!("expected put-bool's codomain to be Term::EffTy, got {other:?}"),
        },
        other => panic!("expected put-bool's type to be Term::Pi, got {other:?}"),
    }

    // Both checkers must agree: the independent re-checker now models parameterized `perform`
    // sites, so it must not silently accept nor reject — Ok (modeled) or an honest Decline are
    // both fine, a Rejection would be a soundness alarm.
    for f in ["get-nat", "put-bool"] {
        let ty = env.global_type(f).expect("member type").clone();
        let term = env.global_term(f).expect("member term").clone();
        match blight_recheck::recheck_judgement(
            env.signature(),
            &blight_kernel::Judgement::HasType { term, ty },
        ) {
            Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("re-checker REJECTED generic Ref `{f}` (soundness alarm): {m}")
            }
        }
    }
}

#[test]
fn std_prelude_aggregates_everything() {
    with_module("std/prelude.bl", |env| {
        for f in [
            "plus",
            "not",
            "show",
            "cmp",
            "length",
            "map",
            "filter",
            "reverse",
            "append",
            "tree-insert",
            "NatTree",
            "maybe",
            "either",
            "id",
            "compose",
            "nat-compare",
            "min",
            "max",
        ] {
            assert!(env.global_term(f).is_some(), "std/prelude re-exports `{f}`");
        }
        for d in [
            "Nat", "Bool", "List", "Tree", "Maybe", "Either", "Pair", "Ordering",
        ] {
            assert!(
                env.data_constructors(d).is_some(),
                "std/prelude declares `{d}`"
            );
        }
    });
}
