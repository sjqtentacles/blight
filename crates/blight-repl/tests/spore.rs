//! Phase B acceptance (M6 spec §8.2 Stage 4): the "spore that knows itself". The host kernel
//! certifies that `spore.bl` — a model of Blight's own core term language written *in* Blight —
//! type-checks, and that the small metatheorems in `spore_meta.bl` are proved (by tactics, then
//! re-checked through the kernel door). Black-box: only the public `Program` driver is used.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Run a test body on a worker thread with an 8 MiB stack. The spore models recurse deeply through
/// the core term language — `bsubst`/`bshift` (and, since A3, their *higher-order* `Π`-conclusion
/// eliminator motives, which the kernel now fully certifies rather than skips) push the kernel's
/// recursive `check`/`infer` well past the ~2 MiB `cargo test` worker stack. The CLI's main thread
/// already uses a large stack; mirror that here (matching `examples.rs`).
fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(f)
        .expect("spawn spore test thread")
        .join()
        .expect("spore test thread panicked (see message above)");
}

/// Grand Arc SH4 (Wave 2 / P4): the `BSexp -> BSurf` transcoder (`spore_reader.bl`) closes the
/// self-hosting loop's string front end, bridging `std/parser.bl`'s untyped s-expression reader
/// into `spore_elab.bl`'s typed surface language over a *single*, shared `Nat` (the "two Nat
/// towers" unification the file's header documents — `defdata`/`define` redeclaration of an
/// identical shape is a harmless last-write-wins overwrite). The host kernel certifies the whole
/// pipeline — reader, transcoder, elaborator, ANF compiler — type-checks (see the file's own note
/// on why `resolve-ty`/`resolve-term`'s correctness is certified this way, and not by an additional
/// `refl` proof over the fuel-recursive readers: Wave 5/N1 fixed one real normalizer bottleneck
/// here (confirmed by `blight-kernel`'s `deep_elim_conv_is_bounded_under_wide_ambient_env`) but
/// measurement showed a second, larger one remains — a one-time O(program size²) `Term::clone`
/// cost during closure construction, sharpened into a go-bar in the file's header comment — so this
/// is still a normalizer *performance* gap, not a correctness gap, same category as
/// `parser_self_host_loads` below, which certifies `std/parser.bl` the identical way).
#[test]
fn reader_self_host_loads() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"spore_reader.bl\")").expect(
                "spore_reader.bl transcodes BSexp -> BSurf, type-checking through the kernel",
            )
        };
        // Every top-level form is kernel-accepted (a declaration or a checked judgment); none errors.
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "every reader form is kernel-accepted: {outcomes:?}"
        );
        // The transcoder's entry points are recorded.
        for fnsym in [
            "bsexp-size",
            "resolve-ty",
            "resolve-term",
            "bsexp->bsurf",
            "bsource->bsurf",
            "bcheck-string",
            "reader-demo-sexp",
        ] {
            assert!(
                env.global_term(fnsym).is_some(),
                "reader defines fn `{fnsym}`"
            );
        }
        // Soundness cross-check: the independent re-checker never *rejects* a typed global. The
        // pure transcoder (`resolve-ty`/`resolve-term`/`lookup-name`/…) must re-verify `Ok`; only
        // the `Bytes`-effectful `bsource->bsurf`/`bcheck-string` may honestly *decline*.
        let sig = env.signature();
        let mut pure_reverified = false;
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            match blight_recheck::recheck_judgement(sig, &j) {
                Ok(()) => {
                    if name == "resolve-ty" || name == "resolve-term" {
                        pure_reverified = true;
                    }
                }
                Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("independent re-checker REJECTED reader global `{name}`: {m}")
                }
            }
        }
        assert!(
            pure_reverified,
            "the pure transcoder core is re-verified Ok by the independent re-checker"
        );
    });
}

/// RED: `spore.bl` loads and every form is accepted (each `defdata`/`deftotal` is `Declared`; no
/// form errors). This is the kernel certifying the in-Blight model of its own core is well-typed.
#[test]
fn spore_model_typechecks() {
    on_big_stack(|| {
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
    });
}

/// RED: `spore_intrinsic.bl` — an *intrinsically-typed* core fragment (`BTy : BCtx -> Type` and a
/// term family `BTm : (g BCtx) -> (a (BTy g)) -> Type`, indexed by **both** its context and its
/// type) — loads and kernel-checks. This exercises the now-lifted multi-index telescope cap: every
/// `defdata`/`deftotal`/`define` form must come back a non-error declaration/checked judgment, with
/// the host kernel certifying that well-typed-syntax-by-construction type-checks.
#[test]
fn spore_intrinsic_loads() {
    on_big_stack(|| {
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
    });
}

/// Grand Arc SH1: the self-hosted `.bl` s-expression reader (`std/parser.bl`). The host kernel
/// certifies the whole frontend type-checks, and — crucially — the *pure* half (the structural
/// stack-machine parser) is re-verified `Ok` by the independent re-checker, while only the
/// `Bytes`-effectful tokenizer/`parse-string` are honestly *declined*. Never `Rejected`.
#[test]
fn parser_self_host_loads() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"std/parser.bl\")")
                .expect("std/parser.bl tokenizes + parses, type-checking through the kernel")
        };
        // Every top-level form is kernel-accepted (a declaration or a checked judgment); none errors.
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "every parser form is kernel-accepted: {outcomes:?}"
        );
        // The surface AST + token datatypes and the headline entry points are recorded.
        for datasym in ["Token", "BSexp", "PState"] {
            assert!(
                env.data_constructors(datasym).is_some(),
                "parser declares datatype `{datasym}`"
            );
        }
        for fnsym in ["tokenize", "parse-tokens", "parse-string", "sexp-atoms"] {
            assert!(
                env.global_term(fnsym).is_some(),
                "parser defines fn `{fnsym}`"
            );
        }
        // Soundness cross-check: the independent re-checker never *rejects* a typed global. The pure
        // parser core (`parse-go`/`next-state`/`finish`/…) must re-verify `Ok`; the `Bytes`-effectful
        // tokenizer half may only honestly *decline*.
        let sig = env.signature();
        let mut pure_reverified = false;
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            match blight_recheck::recheck_judgement(sig, &j) {
                Ok(()) => {
                    if name == "parse-go" || name == "finish" || name == "next-state" {
                        pure_reverified = true;
                    }
                }
                Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("independent re-checker REJECTED parser global `{name}`: {m}")
                }
            }
        }
        assert!(
            pure_reverified,
            "the pure parser core is re-verified Ok by the independent re-checker"
        );
    });
}

/// RED: conv reflexivity (`Π t. t ≡ t`) over the model is proved by tactics and re-checked by the
/// kernel — the base structural property `conv` relies on, established *in Blight*.
#[test]
fn spore_model_conv_refl_proved() {
    on_big_stack(|| {
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
    });
}

/// GREEN (Track M2a): `plus-assoc : Π a b c. Path Nat (plus (plus a b) c) (plus a (plus b c))` is
/// proved by tactics and re-checked by the kernel — the fully-general associativity lemma that
/// `spore_codegen_meta.bl`'s `aeval-k-correct` (Track M2b) chains through the `trans` combinator.
/// Before the `tactic.rs::substitute_term` fix this lemma's `induction`-produced sub-goals kept
/// referring to the pre-induction scrutinee inside the trailing `Pi (b c). …` (a real bug this
/// proof caught, not a research gap), so this is also a regression pin for that fix.
#[test]
fn spore_model_plus_assoc_proved() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"spore.bl\")\n(load \"spore_meta.bl\")")
                .expect("spore metatheorems, including plus-assoc, are proved and re-checked");
        }
        assert!(
            env.global_term("plus-assoc").is_some(),
            "plus-assoc is proved by tactics and kernel-re-checked"
        );
    });
}

/// Grand Arc B4 (+ Track M2b): `spore_codegen_meta.bl` — semantics-preservation lemmas for the
/// untrusted backend fast paths (recognizer, SRA, ANF), each proved by a tactic script and
/// re-checked through the kernel door. A passing load is a machine-checked certificate that each
/// representation rewrite preserves meaning (the in-Blight companion to the B1 differential
/// corpus). This also covers `aeval-k-correct`, the CPS/ANF evaluator-preservation theorem that
/// docs/metatheory.md §3 previously named as out of reach of the tactic fragment: an unprovable
/// theorem in that file turns this test red automatically (every form must be `Declared`/
/// `Checked`), so this is the red/green pin for Track M2b's `trans`-based discharge.
#[test]
fn codegen_meta_lemmas_proved() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"spore_codegen_meta.bl\")")
                .expect("backend semantics-preservation lemmas are proved and kernel-re-checked")
        };
        // Every form is kernel-accepted (a declaration or a checked proof); none errors.
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "every codegen-meta form is kernel-accepted: {outcomes:?}"
        );
        assert!(
            outcomes.iter().any(|o| matches!(o, Outcome::Checked(_))),
            "at least one lemma is a kernel-checked proof"
        );
        // The headline lemma of each pass is present: recognizer (Nat right-unit / right-zero), SRA
        // (product β), ANF (let-substitution + the inductive let-normalized identity), and (Track
        // M2b) the CPS/ANF evaluator-preservation theorem `aeval-k-correct` — previously named in
        // docs/metatheory.md §3 as out of reach of the tactic fragment, now discharged via `trans`.
        for lemma in [
            "rec-add-unit-r",
            "rec-mul-zero-r",
            "sra-beta-fst",
            "sra-beta-snd",
            "anf-let-subst",
            "anf-rebuild-id",
            "aeval-k-correct",
        ] {
            assert!(
                env.global_term(lemma).is_some(),
                "codegen-meta lemma `{lemma}` is proved"
            );
        }
    });
}

/// Grand Arc D10 — the **self-host differential** (after C4). A shared corpus of simply-typed
/// lambda-calculus programs is run through *two independent implementations* and the two must agree
/// on accept/reject:
///   - the **Rust** front end (`Program` over a real `Base` type), and
///   - the self-hosted **`.bl`** pipeline `bcheck = belaborate ▷ bcompile` over `spore_pipeline.bl`'s
///     intrinsic core (`BSurf`/`BTy`/`BTm`).
///
/// For each program we (1) compute the Rust verdict (`run` Ok vs Err) and then (2) ask the *kernel*
/// to certify, by `refl`, that the `.bl` side computes the **same** boolean verdict — `bcheck` on a
/// closed `BSurf` reduces definitionally (the pipeline already ships `refl` proofs of this), so a
/// disagreement makes the `Path Bool … refl` fail to type-check and the load errors. The agreement is
/// therefore enforced by the trusted kernel, not merely asserted by the test. This turns self-hosting
/// into a continuously-verified second implementation of elaboration.
///
/// (Scope, per the C4 note in `spore_pipeline.bl`: the `.bl` *string* front end is blocked by the
/// `Nat`-tower split, so the shared corpus is expressed as paired `BSurf`/Rust-surface terms of the
/// same programs — the largest cross-check available without the `BSexp→BSurf` transcoder.)
#[test]
fn self_host_differential_agrees_with_rust() {
    on_big_stack(|| {
        // (label, Rust surface body, the matching `.bl` BSurf term). `Base` ↦ a declared base type;
        // `Arr` ↦ `Pi`; de Bruijn `su-var` indices match the Rust binder nesting.
        struct Case {
            label: &'static str,
            rust: &'static str,
            bsurf: &'static str,
        }
        let corpus = [
            // ── well-typed in both ──
            Case {
                label: "identity",
                rust: "(the (Pi ((x Base)) Base) (lam (x) x))",
                bsurf: "(su-lam Base (su-var Zero))",
            },
            Case {
                label: "const",
                rust: "(the (Pi ((x Base) (y Base)) Base) (lam (x y) x))",
                bsurf: "(su-lam Base (su-lam Base (su-var (Succ Zero))))",
            },
            Case {
                label: "id-on-functions",
                rust: "(the (Pi ((f (Pi ((x Base)) Base))) (Pi ((x Base)) Base)) (lam (f) f))",
                bsurf: "(su-lam (Arr Base Base) (su-var Zero))",
            },
            Case {
                label: "apply",
                rust: "(the (Pi ((f (Pi ((x Base)) Base)) (x Base)) Base) (lam (f x) (f x)))",
                bsurf: "(su-lam (Arr Base Base) (su-lam Base (su-app (su-var (Succ Zero)) (su-var Zero))))",
            },
            // ── ill-typed in both ──
            Case {
                label: "self-application",
                rust: "(the (Pi ((x Base)) Base) (lam (x) (x x)))",
                bsurf: "(su-lam Base (su-app (su-var Zero) (su-var Zero)))",
            },
            Case {
                label: "unbound-variable",
                rust: "(the Base nope)",
                bsurf: "(su-var Zero)",
            },
            Case {
                label: "domain-mismatch",
                rust: "(the Base ((the (Pi ((x Base)) Base) (lam (x) x)) \
                              (the (Pi ((x Base)) Base) (lam (x) x))))",
                bsurf: "(su-app (su-lam Base (su-var Zero)) (su-lam Base (su-var Zero)))",
            },
        ];

        // (1) The Rust verdict per program (the base type is declared in a fresh env each time so the
        // cases never leak definitions into one another).
        fn rust_accepts(body: &str) -> bool {
            let mut env = ElabEnv::new();
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(&format!("(defdata Base () (b0))\n{body}")).is_ok()
        }
        let verdicts: Vec<bool> = corpus.iter().map(|c| rust_accepts(c.rust)).collect();

        // The corpus must actually exercise BOTH outcomes, or the differential proves nothing.
        assert!(
            verdicts.iter().any(|&v| v),
            "some program is accepted by Rust"
        );
        assert!(
            verdicts.iter().any(|&v| !v),
            "some program is rejected by Rust"
        );

        // (2) Build ONE `.bl` program: the bootstrap pipeline + a `Maybe`-is-`just` probe + one
        // kernel-checked `refl` per case asserting the `.bl` verdict equals the Rust verdict.
        let mut src = String::from(
            "(load \"spore_pipeline.bl\")\n\
             (deftotal mij (Pi ((m (Maybe BAnf))) Bool) \
               (lam (m) (match m [(nothing) false] [(just e) true])))\n",
        );
        for (i, c) in corpus.iter().enumerate() {
            let expected = if verdicts[i] { "true" } else { "false" };
            src.push_str(&format!(
                "(define-by agree-{i} (Path Bool (mij (bcheck CNil {bsurf})) {expected}) refl)\n",
                i = i,
                bsurf = c.bsurf,
                expected = expected
            ));
        }

        // The kernel must certify every agreement `refl`. If the self-hosted `bcheck` disagreed with
        // Rust on any program, that case's `Path Bool … refl` would not type-check and `run` errors —
        // naming the offending `agree-<i>` form.
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(&src).unwrap_or_else(|e| {
                let labels: Vec<(usize, &str, bool)> = corpus
                    .iter()
                    .enumerate()
                    .map(|(i, c)| (i, c.label, verdicts[i]))
                    .collect();
                panic!(
                    "self-host differential: the .bl `bcheck` disagreed with the Rust elaborator.\n\
                     verdicts (idx,label,rust_accept) = {labels:?}\nerror: {e:?}"
                )
            });
        }

        // Every agreement proof is recorded as a global — the kernel-checked certificate of accord.
        for (i, c) in corpus.iter().enumerate() {
            assert!(
                env.global_term(&format!("agree-{i}")).is_some(),
                "agreement proof agree-{i} ({}) is kernel-certified",
                c.label
            );
        }
    });
}

/// RED: a substitution-shaped lemma (context right-unit `bctx-append g BNil ≡ g`, a genuine
/// induction) is proved by tactics and re-checked by the kernel.
#[test]
fn spore_model_subst_lemma_proved() {
    on_big_stack(|| {
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
    });
}

/// Grand Arc SH2: the self-hosted, *proof-carrying* elaborator (`spore_elab.bl`). The host kernel
/// certifies that `belaborate : (g) -> BSurf -> Maybe (Sigma a. BTm g a)` type-checks — i.e. Blight
/// describes a type-correct elaborator into its own intrinsically-typed core. Because the result
/// lives in `BTm g a` (well-typed-syntax-by-construction), a successful elaboration *is* a typing
/// derivation: the elaborator cannot forge an ill-typed term, it can only return `nothing`.
#[test]
fn elaborator_self_host_loads() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"spore_elab.bl\")")
                .expect("spore_elab.bl elaborates BSurf into the intrinsic core, kernel-checked")
        };
        // Every top-level form is kernel-accepted (a declaration or a checked judgment); none errors.
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "every elaborator form is kernel-accepted: {outcomes:?}"
        );
        // The surface AST, the existential result packages, and the propositional type-equality are
        // recorded, along with the headline entry points.
        for datasym in ["BSurf", "BSig", "BVarSig", "BtyEq", "BArrSig"] {
            assert!(
                env.data_constructors(datasym).is_some(),
                "elaborator declares datatype `{datasym}`"
            );
        }
        for fnsym in [
            "belaborate",
            "belab-go",
            "bty-deceq",
            "bty-coerce",
            "lookup-var",
        ] {
            assert!(
                env.global_term(fnsym).is_some(),
                "elaborator defines fn `{fnsym}`"
            );
        }
        // Soundness cross-check: the independent re-checker never *rejects* a typed global. The total
        // (`deftotal`) backbone — transport, the arrow view, application, the structural loop — must
        // re-verify `Ok`; only the two general-recursive deciders (`bty-deceq`/`lookup-var`, declared
        // with `define-rec`) may honestly *decline* as out-of-fragment.
        let sig = env.signature();
        let mut backbone_reverified = false;
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            match blight_recheck::recheck_judgement(sig, &j) {
                Ok(()) => {
                    if name == "belab-go" || name == "bty-coerce" || name == "apply-sig" {
                        backbone_reverified = true;
                    }
                }
                Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("independent re-checker REJECTED elaborator global `{name}`: {m}")
                }
            }
        }
        assert!(
            backbone_reverified,
            "the total elaborator backbone is re-verified Ok by the independent re-checker"
        );
    });
}

/// RED: `spore_compile.bl` — the self-hosted compiler (Grand Arc SH3 / C3): an ANF lowering of the
/// intrinsic core `BTm g a` to the IR `BAnf`, written in Blight. Loads and kernel-checks; the whole
/// backbone (`berase`/`uanf`/`bcompile`/`banf-size`) re-verifies `Ok` through the independent
/// re-checker (every function is a `deftotal`, i.e. a single kernel `Elim`), and the bundled `refl`
/// fingerprint (`bcompile demo-id` has `banf-size` 6) is certified by the kernel.
#[test]
fn compiler_self_host_loads() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"spore_compile.bl\")").expect(
                "spore_compile.bl models the ANF backend and type-checks through the kernel",
            )
        };
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "every spore_compile form is kernel-accepted: {outcomes:?}"
        );
        for datasym in ["BAnf", "UTm", "BcOut", "BTm"] {
            assert!(
                env.data_constructors(datasym).is_some(),
                "compiler declares datatype `{datasym}`"
            );
        }
        for fnsym in ["bcompile", "berase", "uanf", "banf-size", "bvar-index"] {
            assert!(
                env.global_term(fnsym).is_some(),
                "compiler defines fn `{fnsym}`"
            );
        }
        // Soundness cross-check: the independent re-checker never *rejects* a typed global; the total
        // backbone re-verifies `Ok`.
        let sig = env.signature();
        let mut backbone_reverified = false;
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            match blight_recheck::recheck_judgement(sig, &j) {
                Ok(()) => {
                    if name == "bcompile" || name == "uanf" || name == "berase" {
                        backbone_reverified = true;
                    }
                }
                Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("independent re-checker REJECTED compiler global `{name}`: {m}")
                }
            }
        }
        assert!(
            backbone_reverified,
            "the self-hosted compiler backbone is re-verified Ok by the independent re-checker"
        );
    });
}

/// RED: `spore_pipeline.bl` — the self-hosting bootstrap (Grand Arc SH4 / C4): the in-Blight
/// elaborator (`belaborate`) wired into the in-Blight compiler (`bcompile`) as
/// `bcheck : BTyCtx -> BSurf -> Maybe BAnf`. Loads and kernel-checks; the bundled `refl` proofs
/// certify the END-TO-END behaviour definitionally — `λx:Base.x` runs the whole pipeline to the
/// size-6 ANF, and the ill-typed `λx:Base. x x` yields `nothing` (size 0). The total backbone
/// (`bcheck`/`compile-sig`) re-verifies `Ok` through the independent re-checker.
#[test]
fn bootstrap_self_host_loads() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"spore_pipeline.bl\")")
                .expect("spore_pipeline.bl wires belaborate->bcompile and type-checks")
        };
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "every spore_pipeline form is kernel-accepted: {outcomes:?}"
        );
        // The bootstrap entry point and both stages it composes are all present.
        for fnsym in ["bcheck", "compile-sig", "belaborate", "bcompile"] {
            assert!(
                env.global_term(fnsym).is_some(),
                "pipeline defines fn `{fnsym}`"
            );
        }
        // The total bootstrap backbone re-verifies Ok; nothing is Rejected.
        let sig = env.signature();
        let mut bcheck_ok = false;
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            match blight_recheck::recheck_judgement(sig, &j) {
                Ok(()) => {
                    if name == "bcheck" || name == "compile-sig" {
                        bcheck_ok = true;
                    }
                }
                Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("independent re-checker REJECTED pipeline global `{name}`: {m}")
                }
            }
        }
        assert!(
            bcheck_ok,
            "the bootstrap pipeline backbone is re-verified Ok by the independent re-checker"
        );
    });
}

/// S2 (v0.1 roadmap): the proposer/disposer bridge printer (`spore_print.bl`) loads and type-checks,
/// its entry points are present, and its pure structural printers are re-verified `Ok` by the
/// independent re-checker (nothing `Rejected`). The end-to-end kernel re-check of the bridge's
/// emitted payloads is the llvm-gated `example_selfhost_bridge…` test in `main.rs`.
#[test]
fn bridge_printer_loads() {
    on_big_stack(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run("(load \"spore_print.bl\")")
                .expect("spore_print.bl renders BSurf/BTy as surface text and type-checks")
        };
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "every spore_print form is kernel-accepted: {outcomes:?}"
        );
        for fnsym in ["bty-print", "bsurf-print", "bridge-line"] {
            assert!(
                env.global_term(fnsym).is_some(),
                "spore_print defines fn `{fnsym}`"
            );
        }
        // The pure printers re-verify Ok; nothing is Rejected (a soundness alarm).
        let sig = env.signature();
        let mut printer_ok = false;
        for (name, term, ty) in env.typed_globals() {
            let j = blight_kernel::Judgement::HasType { term, ty };
            match blight_recheck::recheck_judgement(sig, &j) {
                Ok(()) => {
                    if name == "bsurf-print" || name == "bty-print" {
                        printer_ok = true;
                    }
                }
                Err(blight_recheck::RecheckError::Declined(_)) => {}
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    panic!("independent re-checker REJECTED printer global `{name}`: {m}")
                }
            }
        }
        assert!(
            printer_ok,
            "the bridge printers are re-verified Ok by the independent re-checker"
        );
    });
}

/// The S2-deferred refl-at-scale pin, live since arc N / N5 (the dead-IH fix): the kernel
/// certifies **by definitional computation** that the bridge printer's full output line for the
/// demo term — `belaborate` (the self-hosted elaborator) ▷ `verdict-of` ▷ `bty-print`/
/// `bsurf-print` ▷ string concatenation — equals the expected `BRIDGE 0 ACCEPT …` string. This
/// is the strongest form of the S2 guarantee: not "the payload re-checks" (the llvm-gated
/// differential already pins that) but "the kernel can *run* the whole proposer pipeline inside
/// conversion checking and pin its exact output". Pre-N5 this was infeasible (the eager-IH
/// cliff made the first character comparison ~2^codepoint steps).
#[test]
fn bridge_printer_output_checks_for_demo_id() {
    // The whole-pipeline refl recurses deeper than the shared 8 MiB helper allows in a debug
    // build (evaluating `belaborate` + both printers inside conversion); give it the same
    // 64 MiB the driver/bench big-stack paths use.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
        let mut env = ElabEnv::new();
        let outcomes = {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(
                "(load \"spore_print.bl\")\n\
                 (define-by bridge-demo-refl\n\
                   (Path String (bridge-line Zero demo-id)\n\
                     \"BRIDGE 0 ACCEPT (the (Pi ((v Base)) Base) (lam (v0) v0))\")\n\
                   refl)",
            )
            .expect("the bridge line for demo-id computes to its expected text by refl")
        };
        assert!(
            outcomes
                .iter()
                .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
            "the refl goal kernel-checks: {outcomes:?}"
        );
        assert!(
            env.global_term("bridge-demo-refl").is_some(),
            "the refl-at-scale pin is a named, kernel-checked global"
        );
        })
        .expect("spawn bridge-refl thread")
        .join()
        .expect("bridge-refl thread panicked (see message above)");
}
