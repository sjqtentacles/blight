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

/// RED: `spore_intrinsic.bl` — an *intrinsically-typed* core fragment (`BTy : BCtx -> Type` and a
/// term family `BTm : (g BCtx) -> (a (BTy g)) -> Type`, indexed by **both** its context and its
/// type) — loads and kernel-checks. This exercises the now-lifted multi-index telescope cap: every
/// `defdata`/`deftotal`/`define` form must come back a non-error declaration/checked judgment, with
/// the host kernel certifying that well-typed-syntax-by-construction type-checks.
#[test]
fn spore_intrinsic_loads() {
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run("(load \"spore.bl\")\n(load \"spore_intrinsic.bl\")")
            .expect(
                "spore_intrinsic.bl models the intrinsic core and type-checks through the kernel",
            )
    };
    // Every top-level form is accepted by the kernel (a declaration or a checked judgment); none is
    // a form error.
    assert!(
        outcomes
            .iter()
            .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
        "every intrinsic-spore form is kernel-accepted: {outcomes:?}"
    );
    // The intrinsic families and their elimination/well-typing helpers are recorded.
    for datasym in ["BTy", "BTm"] {
        assert!(
            env.data_constructors(datasym).is_some(),
            "intrinsic spore declares datatype `{datasym}`"
        );
    }
    for fnsym in ["bty-size", "btm-size"] {
        assert!(
            env.global_term(fnsym).is_some(),
            "intrinsic spore defines fn `{fnsym}`"
        );
    }
    // Soundness cross-check: the independent re-checker agrees with the kernel on every typed global
    // of the intrinsic model (the two-index `BVarIn`/`BTm` families included). It may only either
    // re-verify (`Ok`) or honestly decline an out-of-fragment global — never `Rejected`.
    let sig = env.signature();
    for (name, term, ty) in env.typed_globals() {
        let j = blight_kernel::Judgement::HasType { term, ty };
        match blight_recheck::recheck_judgement(sig, &j) {
            Ok(()) | Err(blight_recheck::RecheckError::Declined(_)) => {}
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                panic!("independent re-checker REJECTED intrinsic-spore global `{name}`: {m}")
            }
        }
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
