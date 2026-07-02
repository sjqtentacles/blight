//! Tower acceptance tests (spec §9 M3): the `Show`/`Ord` traits and (separately) the functorized
//! `RedBlackTree` are written in Blight and must typecheck through the spore. Black-box: the
//! `blight-elab` public `Program` driver only.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Load `traits.bl`, then exercise `show`/`cmp` so instance search + the spore both run.
#[test]
fn show_ord_trait_typechecks() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(
            "(load \"traits.bl\")\n\
             ; `show` resolves the `Show Nat` dictionary and applies it.\n\
             (the Nat (show (Succ (Succ Zero))))\n\
             ; `show` on a Bool resolves the `Show Bool` dictionary.\n\
             (the Nat (show true))\n\
             ; `cmp` resolves the `Ord Nat` dictionary.\n\
             (the Bool (cmp (Succ Zero) (Succ Zero)))\n\
             ; `cmp` on Bools resolves the `Ord Bool` dictionary.\n\
             (the Bool (cmp false true))",
        )
        .expect("traits.bl loads and the trait uses typecheck")
    };
    // The four ascribed uses (the last four forms passed to `prog.run` above) are all kernel-checked.
    // `traits.bl` transitively loads `std/nat.bl`, whose own Wave 5/N4 `compute`/`decide` dogfood
    // lemmas are *also* `Outcome::Checked` — so the total count is no longer exactly four; instead
    // check specifically the trailing four outcomes, which are these forms in call order.
    let last_four = &outcomes[outcomes.len() - 4..];
    assert!(
        last_four.iter().all(|o| matches!(o, Outcome::Checked(_))),
        "all four trait uses are checked by the spore: {last_four:?}"
    );
}

/// Isolate `tree-if`: the non-recursive Bool selector with trailing-binder generalization.
#[test]
fn tree_if_typechecks() {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::new(&mut env);
        prog.run(
            "(defdata Bool () (false) (true))\n\
             (defdata Tree ((a (Type 0))) (leaf) (node (l (Tree a)) (x a) (r (Tree a))))\n\
             (deftotal tree-if (Pi ((A (Type 0)) (t (Tree A)) (e (Tree A)) (b Bool)) (Tree A)) \
                (lam (A t e b) (match b [(true) t] [(false) e])))",
        )
        .expect("tree-if defines");
    }
    let ty = env.global_type("tree-if").expect("ty").clone();
    let term = env.global_term("tree-if").expect("term").clone();
    if let Err(e) = blight_kernel::check_top_with(env.signature().clone(), term.clone(), ty) {
        panic!("tree-if re-check failed: {e:?}\n term={term:?}");
    }
}

/// Isolate `tree-insert`: define it standalone (no functor) and re-check through the spore.
#[test]
fn tree_insert_typechecks() {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::new(&mut env);
        prog.run(
            "(defdata Bool () (false) (true))\n\
             (defdata Tree ((a (Type 0))) (leaf) (node (l (Tree a)) (x a) (r (Tree a))))\n\
             (deftotal tree-if (Pi ((A (Type 0)) (b Bool) (t (Tree A)) (e (Tree A))) (Tree A)) \
                (lam (A b t e) (match b [(true) t] [(false) e])))\n\
             (deftotal tree-insert \
                (Pi ((A (Type 0)) (cmp (Pi ((x A) (y A)) Bool)) (x A) (tr (Tree A))) (Tree A)) \
                (lam (A cmp x tr) \
                  (match tr \
                    [(leaf) (node (leaf) x (leaf))] \
                    [(node l y r) \
                      (tree-if A (cmp x y) \
                        (node (tree-insert A cmp x l) y r) \
                        (node l y (tree-insert A cmp x r)))])))",
        )
        .expect("tree-insert defines");
    }
    let ty = env.global_type("tree-insert").expect("ty").clone();
    let term = env.global_term("tree-insert").expect("term").clone();
    if let Err(e) = blight_kernel::check_top_with(env.signature().clone(), term.clone(), ty) {
        panic!("tree-insert re-check failed: {e:?}\n term={term:?}");
    }
}

/// Load `modules.bl`: the `ORD` signature (a record type), `Nat-Ord` module (a record value), and
/// the `RedBlackTree` functor (a function between records) all typecheck, and applying the functor
/// to the Nat module yields a tree-API record that re-checks through the spore (spec §9 M3).
#[test]
fn redblacktree_functor_typechecks() {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run("(load \"modules.bl\")")
            .expect("modules.bl loads, the functor and its Nat application typecheck");
    }
    // The functor and its application are recorded as elaborated globals.
    assert!(
        env.global_term("RedBlackTree").is_some(),
        "the functor is defined"
    );
    assert!(
        env.global_term("NatTree").is_some(),
        "the functor applied to Nat-Ord is defined"
    );

    // Re-check `NatTree` through the spore at its declared type, end-to-end.
    let ty = env
        .global_type("NatTree")
        .expect("NatTree has a type")
        .clone();
    let term = env.global_term("NatTree").expect("NatTree term").clone();
    if let Err(e) = blight_kernel::check_top_with(env.signature().clone(), term.clone(), ty.clone())
    {
        panic!("re-check failed: {e:?}\n  term = {term:?}\n  type = {ty:?}");
    }
}
