//! Standard-library load tests (spec §6, §8 M6 stdlib reorg): each `std/` module loads *in
//! isolation* through the public `Program` driver, and every form in it is accepted by the spore.
//! Loading a module also brings in (splices) its declared dependencies, so each test asserts on the
//! symbols the module is responsible for. Black-box: the `blight-elab` `Program` driver only.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Load one std module, assert every form is accepted, and return the resulting env for further
/// assertions.
fn load_module(module: &str) -> ElabEnv {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(&format!("(load \"{module}\")"))
            .unwrap_or_else(|e| panic!("std module {module} loads cleanly, got: {e:?}"))
    };
    assert!(
        outcomes.iter().all(|o| matches!(o, Outcome::Declared)),
        "every form in {module} is a well-typed declaration"
    );
    env
}

#[test]
fn std_nat_loads_in_isolation() {
    let env = load_module("std/nat.bl");
    assert!(env.data_constructors("Nat").is_some(), "Nat is declared");
    for f in ["plus", "mult", "pred", "min", "max", "sub", "even", "odd"] {
        assert!(env.global_term(f).is_some(), "std/nat defines `{f}`");
    }
}

#[test]
fn std_bool_loads_in_isolation() {
    let env = load_module("std/bool.bl");
    assert!(env.data_constructors("Bool").is_some(), "Bool is declared");
    for f in ["not", "and", "or"] {
        assert!(env.global_term(f).is_some(), "std/bool defines `{f}`");
    }
}

#[test]
fn std_order_loads_in_isolation() {
    let env = load_module("std/order.bl");
    for f in ["nat-le", "nat-eq", "show", "cmp", "ORD", "Nat-Ord"] {
        assert!(env.global_term(f).is_some(), "std/order defines `{f}`");
    }
    assert!(env.is_class("Show"), "Show is a registered class");
    assert!(env.is_class("Ord"), "Ord is a registered class");
}

#[test]
fn std_char_loads_in_isolation() {
    let env = load_module("std/char.bl");
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
}

#[test]
fn std_list_loads_in_isolation() {
    let env = load_module("std/list.bl");
    assert!(env.data_constructors("List").is_some(), "List is declared");
    for f in [
        "length", "append", "map", "filter", "reverse", "foldr", "concat",
    ] {
        assert!(env.global_term(f).is_some(), "std/list defines `{f}`");
    }
}

#[test]
fn std_list_extra_loads_in_isolation() {
    let env = load_module("std/list_extra.bl");
    for f in ["take", "drop", "foldl", "zip", "elem", "sort"] {
        assert!(env.global_term(f).is_some(), "std/list_extra defines `{f}`");
    }
}

#[test]
fn std_maybe_loads_in_isolation() {
    let env = load_module("std/maybe.bl");
    assert!(
        env.data_constructors("Maybe").is_some(),
        "Maybe is declared"
    );
    for f in ["maybe", "maybe-map", "from-maybe", "maybe-bind", "maybe-or"] {
        assert!(env.global_term(f).is_some(), "std/maybe defines `{f}`");
    }
}

#[test]
fn std_either_loads_in_isolation() {
    // `Either` is a two-parameter inductive — only loadable after the multi-parameter cap lift.
    let env = load_module("std/either.bl");
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
}

#[test]
fn std_string_loads_in_isolation() {
    let env = load_module("std/string.bl");
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
}

#[test]
fn std_string_extra_loads_in_isolation() {
    let env = load_module("std/string_extra.bl");
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
}

#[test]
fn std_function_loads_in_isolation() {
    let env = load_module("std/function.bl");
    for f in ["id", "compose", "const", "flip"] {
        assert!(env.global_term(f).is_some(), "std/function defines `{f}`");
    }
}

#[test]
fn std_pair_loads_in_isolation() {
    // `Pair a b` is a two-parameter inductive (non-dependent product).
    let env = load_module("std/pair.bl");
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
}

#[test]
fn std_ordering_loads_in_isolation() {
    let env = load_module("std/ordering.bl");
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
}

#[test]
fn std_vec_loads_in_isolation() {
    // `Vec a n` is an indexed family (one parameter + one `Nat` index).
    let env = load_module("std/vec.bl");
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
}

#[test]
fn std_tree_loads_in_isolation() {
    let env = load_module("std/tree.bl");
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
}

#[test]
fn std_prelude_aggregates_everything() {
    let env = load_module("std/prelude.bl");
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
}
