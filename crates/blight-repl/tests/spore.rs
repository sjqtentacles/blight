//! Phase B acceptance (M6 spec §8.2 Stage 4): the "spore that knows itself". The host kernel
//! certifies that `spore.bl` — a model of Blight's own core term language written *in* Blight —
//! type-checks, and that the small metatheorems in `spore_meta.bl` are proved (by tactics, then
//! re-checked through the kernel door). Black-box: only the public `Program` driver is used.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// RED: `spore.bl` loads and every form is accepted (each `defdata`/`deftotal` is `Declared`; no
/// form errors). This is the kernel certifying the in-Blight model of its own core is well-typed.
#[test]
fn spore_model_typechecks() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run("(load \"spore.bl\")")
            .expect("spore.bl models the core and type-checks through the kernel")
    };
    // Every top-level form is a declaration (datatype or total function); none is an error.
    assert!(
        outcomes.iter().all(|o| matches!(o, Outcome::Declared)),
        "every spore form is a well-typed declaration"
    );
    // The key modeled symbols are recorded as globals/datatypes.
    for fnsym in [
        "bsize",
        "bshift",
        "bshift-var",
        "bctx-len",
        "plus",
        "nat-eq",
        "nat-lt",
    ] {
        assert!(
            env.global_term(fnsym).is_some(),
            "spore model defines fn `{fnsym}`"
        );
    }
    for datasym in ["BTerm", "BGrade", "BCtx", "Nat", "Bool"] {
        assert!(
            env.data_constructors(datasym).is_some(),
            "spore model declares datatype `{datasym}`"
        );
    }
}

/// RED: conv reflexivity (`Π t. t ≡ t`) over the model is proved by tactics and re-checked by the
/// kernel — the base structural property `conv` relies on, established *in Blight*.
#[test]
fn spore_model_conv_refl_proved() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run("(load \"spore.bl\")\n(load \"spore_meta.bl\")")
            .expect("spore metatheorems are proved by tactics and re-checked by the kernel")
    };
    assert!(
        outcomes.iter().any(|o| matches!(o, Outcome::Checked(_))),
        "at least one metatheorem is a kernel-checked proof"
    );
    assert!(
        env.global_term("bconv-refl").is_some(),
        "conv-reflexivity is proved"
    );
}

/// RED: a substitution-shaped lemma (context right-unit `bctx-append g BNil ≡ g`, a genuine
/// induction) is proved by tactics and re-checked by the kernel.
#[test]
fn spore_model_subst_lemma_proved() {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run("(load \"spore.bl\")\n(load \"spore_meta.bl\")")
            .expect("the substitution-shaped lemma is proved and re-checked");
    }
    assert!(
        env.global_term("bctx-append-nil").is_some(),
        "the context right-unit substitution lemma is proved"
    );
}
