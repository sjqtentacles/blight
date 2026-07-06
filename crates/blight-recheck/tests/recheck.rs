//! Phase A RED tests (M6 spec §8.3): the independent re-checker agrees with the kernel on the
//! core fragment, rejects a hand-mutated core term, and matches the kernel's β/η equational
//! theory.
//!
//! These drive the *real* kernel + elaborator to produce a `Proof`, then re-verify the proof's
//! conclusion with `blight-recheck`'s own from-scratch checker.

use blight_elab::ElabEnv;
use blight_kernel::{check_top_with, ConName, DataName, Grade, Judgement, Proof, Signature, Term};
use blight_recheck::{recheck_judgement, recheck_proof, RecheckError};
use std::rc::Rc;

/// The headline cubical `plus-zero` program (spec §5.3).
const PLUS_ZERO_SRC: &str = r#"
(defdata Nat () (Zero) (Succ (n Nat)))
(define-rec plus
  (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))
(define-rec plus-zero
  (lam (n) (match n
    [(Zero)   (plam (i) Zero)]
    [(Succ k) (plam (i) (Succ ((plus-zero k) @ i)))])))
"#;

/// Drive the pipeline and return the kernel `Proof` for the last definition together with the
/// signature it was checked against (the re-checker needs both).
fn check_program(src: &str) -> Result<(Signature, Proof), String> {
    use blight_elab::{elaborate, parse_decl, read_all, Decl};

    let mut env = ElabEnv::new();
    let forms = read_all(src).map_err(|e| format!("read: {e:?}"))?;

    let mut last: Option<(String, Term)> = None;
    for form in &forms {
        let decl = parse_decl(form).map_err(|e| format!("parse_decl: {e:?}"))?;
        match &decl {
            Decl::DefData { .. } | Decl::DefEffect { .. } | Decl::Foreign { .. } => {
                env.declare(&decl, None)
                    .map_err(|e| format!("declare: {e:?}"))?;
            }
            Decl::Define { name, .. }
            | Decl::DefineRec { name, .. }
            | Decl::DefTotal { name, .. } => {
                let ty_surface = declared_type(name)?;
                let ty_core =
                    elaborate(&env, &ty_surface).map_err(|e| format!("elab type: {e:?}"))?;
                env.declare(&decl, Some(&ty_core))
                    .map_err(|e| format!("declare {name}: {e:?}"))?;
                last = Some((name.clone(), ty_core));
            }
        }
    }

    let (name, ty) = last.ok_or_else(|| "no definition to check".to_string())?;
    let term = env
        .global_term(&name)
        .ok_or_else(|| format!("no elaborated term for {name}"))?
        .clone();
    let sig = env.signature().clone();
    let proof = check_top_with(sig.clone(), term, ty).map_err(|e| format!("kernel: {e:?}"))?;
    Ok((sig, proof))
}

fn declared_type(name: &str) -> Result<blight_elab::Surface, String> {
    let src = match name {
        "plus" => "(Pi ((a Nat) (b Nat)) Nat)",
        "plus-zero" => "(Pi ((n Nat)) (Path Nat (plus n Zero) n))",
        other => return Err(format!("no declared type for `{other}`")),
    };
    let (sexpr, _) = blight_elab::read_one(src).map_err(|e| format!("{e:?}"))?;
    blight_elab::parse_surface(&sexpr).map_err(|e| format!("{e:?}"))
}

/// RED: the re-checker re-verifies the headline proof's conclusion from scratch.
#[test]
fn recheck_accepts_plus_zero() {
    let (sig, proof) = check_program(PLUS_ZERO_SRC).expect("kernel should accept plus-zero");
    recheck_proof(&sig, &proof).expect("re-checker should agree the conclusion is well-typed");
}

/// RED: a hand-mutated core term (claimed to have the same type) is *rejected* by the independent
/// checker — the two checkers do not both certify garbage.
#[test]
fn recheck_rejects_mutated_term() {
    // Build a tiny signature with `Nat` so the mutated judgement references a real type.
    let mut sig = Signature::new();
    sig.declare(blight_kernel::DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            blight_kernel::Constructor {
                name: ConName("Zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            blight_kernel::Constructor {
                name: ConName("Succ".into()),
                args: vec![blight_kernel::Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });

    // A blatantly false judgement: `Zero : (Nat -> Nat)`. `Zero` is a `Nat`, not a function.
    let nat = Term::Data(DataName("Nat".into()), vec![], vec![]);
    let bad = Judgement::HasType {
        term: Term::Con(ConName("Zero".into()), vec![]),
        ty: Term::Pi(Grade::Omega, Rc::new(nat.clone()), Rc::new(nat)),
    };
    match recheck_judgement(&sig, &bad) {
        Err(RecheckError::Rejected(_)) => {}
        other => panic!("expected the re-checker to REJECT the mutated term, got {other:?}"),
    }
}

/// A `foreign` postulate (spec §7.6) is trusted FFI: the independent re-checker cannot re-verify
/// an opaque external symbol, so any judgement mentioning a `Foreign` must be honestly **declined**
/// (not accepted, not rejected). This is the safety mechanism guarding the one TCB-growing hatch.
#[test]
fn recheck_declines_foreign() {
    let sig = Signature::new();
    let u0 = Term::Univ(blight_kernel::Level::Zero);
    let j = Judgement::HasType {
        term: Term::Foreign {
            symbol: "bl_foreign_answer".into(),
            ty: Rc::new(u0.clone()),
        },
        ty: u0,
    };
    match recheck_judgement(&sig, &j) {
        Err(RecheckError::Declined(msg)) => {
            assert!(
                msg.contains("foreign"),
                "decline reason should mention the foreign postulate, got: {msg}"
            );
        }
        other => panic!("expected the re-checker to DECLINE the foreign, got {other:?}"),
    }
}

/// The univalence layer (`Glue`) is the one cubical Kan hatch the independent re-checker does **not**
/// duplicate: `std/path.bl`'s `ua` builds a `Glue` type, and re-checking anything mentioning `Glue`
/// must be honestly **declined** (never silently accepted, never crashed in the re-checker's Kan
/// table — the decline happens at `from_kernel`, before normalization). This is the A1/A2b guarantee
/// that the trusted kernel solely owns the Glue computation rule. We form `Glue U₀ (i=0) U₀ e` (the
/// `ua`-shaped single-face Glue head) and assert the re-check declines.
#[test]
fn recheck_declines_glue() {
    let sig = Signature::new();
    let u0 = || Term::Univ(blight_kernel::Level::Zero);
    let glue = Term::Glue {
        base: Rc::new(u0()),
        cofib: blight_kernel::Cofib::Eq0(blight_kernel::Interval::I0),
        ty: Rc::new(u0()),
        equiv: Rc::new(u0()),
    };
    let j = Judgement::HasType {
        term: glue,
        ty: Term::Univ(blight_kernel::Level::Suc(Box::new(
            blight_kernel::Level::Zero,
        ))),
    };
    match recheck_judgement(&sig, &j) {
        Err(RecheckError::Declined(msg)) => {
            assert!(
                msg.to_lowercase().contains("glue"),
                "decline reason should mention Glue, got: {msg}"
            );
        }
        other => panic!("expected the re-checker to DECLINE the Glue type, got {other:?}"),
    }
}

/// T1a: the re-checker independently re-derives `if-zero` — it is MODELED, never declined. A closed
/// folded branch (`if-zero 0 7 9 : Int`) and a stuck-scrutinee form under a binder
/// (`λ^ω (x:Int). if-zero x 1 2 : Int → Int`, exercising the neutral quote/round-trip) both agree.
#[test]
fn recheck_ifzero_roundtrips() {
    let sig = Signature::new();
    let if_zero = |s: Term, t: Term, e: Term| Term::IfZero {
        scrut: Rc::new(s),
        then_: Rc::new(t),
        else_: Rc::new(e),
    };
    // Closed: `if-zero 0 7 9 : Int`.
    let closed = Judgement::HasType {
        term: if_zero(Term::IntLit(0), Term::IntLit(7), Term::IntLit(9)),
        ty: Term::IntTy,
    };
    recheck_judgement(&sig, &closed).expect("if-zero 0 7 9 : Int should re-check");
    // Stuck scrutinee under a binder: `λ^ω (x:Int). if-zero x 1 2 : Int → Int`.
    let lam = Term::Ann(
        Rc::new(Term::Lam(Rc::new(if_zero(
            Term::Var(0),
            Term::IntLit(1),
            Term::IntLit(2),
        )))),
        Rc::new(Term::Pi(
            Grade::Omega,
            Rc::new(Term::IntTy),
            Rc::new(Term::IntTy),
        )),
    );
    let stuck = Judgement::HasType {
        term: lam,
        ty: Term::Pi(Grade::Omega, Rc::new(Term::IntTy), Rc::new(Term::IntTy)),
    };
    recheck_judgement(&sig, &stuck).expect("λ x. if-zero x 1 2 : Int → Int should re-check");
}

/// RED: β/η parity with the kernel. `(λx. x) Zero` and `Zero` are definitionally equal, so a proof
/// that the identity-applied value has type `Nat` re-checks; and an η-expanded identity function
/// `λx. (id x)` re-checks at `Nat -> Nat` just like the bare `id`.
#[test]
fn recheck_conv_eta() {
    let mut sig = Signature::new();
    sig.declare(blight_kernel::DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![blight_kernel::Constructor {
            name: ConName("Zero".into()),
            args: vec![],
            result_indices: vec![],
        }],
        path_constructors: vec![],
    });
    let nat = Term::Data(DataName("Nat".into()), vec![], vec![]);

    // β: `((the (Nat -> Nat) (λx. x)) Zero) : Nat`. The function must be inferable, so it carries
    // an ascription — exactly as the elaborator produces it.
    let id_fn = Term::Ann(
        Rc::new(Term::Lam(Rc::new(Term::Var(0)))),
        Rc::new(Term::Pi(
            Grade::Omega,
            Rc::new(nat.clone()),
            Rc::new(nat.clone()),
        )),
    );
    let beta = Judgement::HasType {
        term: Term::App(
            Rc::new(id_fn),
            Rc::new(Term::Con(ConName("Zero".into()), vec![])),
        ),
        ty: nat.clone(),
    };
    recheck_judgement(&sig, &beta).expect("β: (λx.x) Zero : Nat should re-check");

    // η: `λx. (id x) : Nat -> Nat` where `id = (the (Nat -> Nat) (λy. y))`. The η-expanded form
    // must re-check against the same Π type the kernel accepts.
    let id = Term::Ann(
        Rc::new(Term::Lam(Rc::new(Term::Var(0)))),
        Rc::new(Term::Pi(
            Grade::Omega,
            Rc::new(nat.clone()),
            Rc::new(nat.clone()),
        )),
    );
    let eta = Judgement::HasType {
        term: Term::Lam(Rc::new(Term::App(
            Rc::new(id.clone()),
            Rc::new(Term::Var(0)),
        ))),
        ty: Term::Pi(Grade::Omega, Rc::new(nat.clone()), Rc::new(nat.clone())),
    };
    recheck_judgement(&sig, &eta).expect("η: λx.(id x) : Nat -> Nat should re-check");
}

// ---------------------------------------------------------------------------------------------
// Phase A, part 2: re-check every typed definition the prelude + acceptance proofs produce.
// ---------------------------------------------------------------------------------------------

/// Resolve a prelude module name to its on-disk source under `crates/blight-prelude/`.
fn prelude_resolver(name: &str) -> Result<String, blight_elab::ElabError> {
    let path = format!("{}/../blight-prelude/{}", env!("CARGO_MANIFEST_DIR"), name);
    std::fs::read_to_string(&path)
        .map_err(|e| blight_elab::ElabError::BadForm(format!("cannot load {path:?}: {e}")))
}

/// Load `src` against a fresh env (with the prelude resolver), returning the env and the kernel
/// proofs of any ascribed/`define-by` forms.
fn load(src: &str) -> (ElabEnv, Vec<Proof>) {
    use blight_elab::{Outcome, Program};
    let mut env = ElabEnv::new();
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(src)
            .unwrap_or_else(|e| panic!("prelude load failed: {e:?}"))
    };
    let proofs = outcomes
        .into_iter()
        .filter_map(|o| match o {
            Outcome::Checked(p) => Some(p),
            Outcome::Declared => None,
        })
        .collect();
    (env, proofs)
}

/// Re-check every typed global and every emitted proof against `blight-recheck`. The contract: the
/// independent checker must **agree** (`Ok`) or **honestly decline** (`Declined`, for the
/// out-of-fragment partial/effect/Kan constructs) — it must **never** `Rejected` something the
/// kernel accepted, which would be a soundness alarm.
fn assert_agreement(env: &ElabEnv, proofs: &[Proof], label: &str) {
    let sig = env.signature();
    let mut agreed = 0usize;
    let mut declined = 0usize;
    for (name, term, ty) in env.typed_globals() {
        let j = Judgement::HasType {
            term: term.clone(),
            ty: ty.clone(),
        };
        match recheck_judgement(sig, &j) {
            Ok(()) => agreed += 1,
            Err(RecheckError::Declined(_)) => declined += 1,
            Err(RecheckError::Rejected(m)) => panic!(
                "[{label}] re-checker REJECTED kernel-accepted global `{name}` — soundness alarm: {m}\n  term = {term:?}\n  ty = {ty:?}"
            ),
        }
    }
    for (i, p) in proofs.iter().enumerate() {
        match recheck_proof(sig, p) {
            Ok(()) => agreed += 1,
            Err(RecheckError::Declined(_)) => declined += 1,
            Err(RecheckError::Rejected(m)) => {
                panic!("[{label}] re-checker REJECTED kernel proof #{i} — soundness alarm: {m}")
            }
        }
    }
    // The whole point is that the re-checker actually exercised something; require at least one
    // independent agreement so a vacuous pass cannot hide a broken harness.
    assert!(
        agreed >= 1,
        "[{label}] expected at least one independently re-checked judgement (agreed={agreed}, declined={declined})"
    );
    eprintln!(
        "[{label}] re-check agreement: {agreed} agreed, {declined} declined (out-of-fragment)"
    );
}

/// RED: the independent re-checker agrees with the kernel across the prelude and acceptance proofs.
#[test]
fn recheck_agrees_with_kernel_on_prelude() {
    // The cubical headline proof, with inline types so the `Program` driver accepts it.
    let plus_zero_typed = "\
(defdata Nat () (Zero) (Succ (n Nat)))
(define-rec plus (Pi ((a Nat) (b Nat)) Nat)
  (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))
(define-rec plus-zero (Pi ((n Nat)) (Path Nat (plus n Zero) n))
  (lam (n) (match n
    [(Zero)   (plam (i) Zero)]
    [(Succ k) (plam (i) (Succ ((plus-zero k) @ i)))])))
";
    let (env, proofs) = load(plus_zero_typed);
    assert_agreement(&env, &proofs, "plus-zero");

    // The tactic prelude + the proof-by-tactics `plus-zero` (LCF door).
    let (env, proofs) = load("(load \"tactics.bl\")\n(load \"plus_zero_tac.bl\")");
    assert_agreement(&env, &proofs, "tactics+plus_zero_tac");

    // The traits tower: Show/Ord classes, instances, and trait uses.
    let (env, proofs) = load(
        "(load \"traits.bl\")\n\
         (the Nat (show (Succ (Succ Zero))))\n\
         (the Bool (cmp false true))",
    );
    assert_agreement(&env, &proofs, "traits");

    // The modules/functor tower.
    let (env, proofs) = load("(load \"modules.bl\")");
    assert_agreement(&env, &proofs, "modules");

    // The region prelude (linear capability discipline) — the `Rgn` opaque type and uses.
    let (env, proofs) = load(
        "(load \"regions.bl\")\n\
         (defdata Nat () (Zero) (Succ (n Nat)))\n\
         (the Nat (region r Zero))",
    );
    assert_agreement(&env, &proofs, "regions");
}

/// RED: cubical Kan operations are now **Checked** by the re-checker, not declined. We build a
/// constant-family transport `transp (i. Nat) ⊥ Zero : Nat` (which the kernel accepts and the
/// re-checker must now independently re-derive, returning `Ok` rather than `Declined`). This is the
/// acceptance criterion for modelling the Kan table in the re-checker's value layer.
#[test]
fn recheck_checks_transp_not_declined() {
    use blight_kernel::term::Cofib;
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Term};

    let mut sig = Signature::new();
    sig.declare(DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("Zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("Succ".into()),
                args: vec![Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    let nat = || Term::Data(DataName("Nat".into()), vec![], vec![]);
    let zero = || Term::Con(ConName("Zero".into()), vec![]);

    // transp (i. Nat) ⊥ Zero : Nat — a constant line, so it reduces to `Zero`.
    let transp = Term::Transp {
        family: Rc::new(nat()),
        cofib: Cofib::Bot,
        base: Rc::new(zero()),
    };
    let proof = check_top_with(sig.clone(), transp, nat())
        .expect("kernel accepts the constant transport at type Nat");
    // The headline: the re-checker AGREES (Ok), it does not Decline the Kan op.
    match recheck_proof(&sig, &proof) {
        Ok(()) => {}
        other => panic!("expected the re-checker to CHECK transp (not decline), got {other:?}"),
    }
}

// ---------------------------------------------------------------------------------------------
// extended coverage (indexed / multi-binder eliminators). Effects/handlers and partiality are now
// MODELED (Checked), not declined (see `recheck_agrees_on_surface_effect_program` below). Only
// cubical `Glue`/`ua`/partial-element/system, `foreign` postulates, and universe-level variables
// remain out-of-fragment and are honestly *declined*, never rejected.
// ---------------------------------------------------------------------------------------------

/// RED: the re-checker agrees with the kernel on a **two-parameter** family (`Pair A B`) and a
/// **two-index** family (`Square m n`) — the lifted `<=1 param / <=1 index` cap, re-derived
/// independently. Both eliminators kernel-check *and* re-check with 0 Rejected.
#[test]
fn recheck_agrees_on_multi_param_and_multi_index() {
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Level, Term};

    fn u(n: u32) -> Term {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = Level::Suc(Box::new(l));
        }
        Term::Univ(l)
    }
    let nat = || Term::Data(DataName("Nat".into()), vec![], vec![]);
    let zero = || Term::Con(ConName("Zero".into()), vec![]);
    let succ = |n: Term| Term::Con(ConName("Succ".into()), vec![n]);
    let nat_decl = || DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("Zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("Succ".into()),
                args: vec![Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    };

    // --- two-parameter Pair: fst (mk (Succ Zero) Zero) : Nat ---
    let mut sig = Signature::new();
    sig.declare(nat_decl());
    sig.declare(DataDecl {
        name: DataName("Pair".into()),
        params: vec![u(0), u(0)],
        indices: vec![],
        level: 0,
        constructors: vec![Constructor {
            name: ConName("mk".into()),
            // (x:A)(y:B): with params outermost, x:A = Var(1) (0 earlier args), y:B = Var(1).
            args: vec![Arg::NonRec(Term::Var(1)), Arg::NonRec(Term::Var(1))],
            result_indices: vec![],
        }],
        path_constructors: vec![],
    });
    let pair_nat_nat = Term::Data(DataName("Pair".into()), vec![nat(), nat()], vec![]);
    let mk = Term::Ann(
        Rc::new(Term::Con(ConName("mk".into()), vec![succ(zero()), zero()])),
        Rc::new(pair_nat_nat),
    );
    let elim = Term::Elim {
        data: DataName("Pair".into()),
        motive: Rc::new(Term::Lam(Rc::new(nat()))),
        methods: vec![Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Var(1)))))],
        scrutinee: Rc::new(mk),
    };
    let proof = check_top_with(sig.clone(), elim, nat())
        .expect("kernel accepts the two-parameter Pair eliminator");
    recheck_proof(&sig, &proof)
        .expect("re-checker independently agrees the two-parameter eliminator has type Nat");

    // --- two-index Square: elim over corner : Square Zero Zero, motive constant Nat ---
    let mut sig2 = Signature::new();
    sig2.declare(nat_decl());
    sig2.declare(DataDecl {
        name: DataName("Square".into()),
        params: vec![],
        indices: vec![nat(), nat()],
        level: 0,
        constructors: vec![Constructor {
            name: ConName("corner".into()),
            args: vec![],
            result_indices: vec![zero(), zero()],
        }],
        path_constructors: vec![],
    });
    let elim2 = Term::Elim {
        data: DataName("Square".into()),
        // λ m. λ n. λ (_:Square m n). Nat
        motive: Rc::new(Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Lam(Rc::new(
            nat(),
        ))))))),
        methods: vec![zero()],
        scrutinee: Rc::new(Term::Ann(
            Rc::new(Term::Con(ConName("corner".into()), vec![])),
            Rc::new(Term::Data(
                DataName("Square".into()),
                vec![],
                vec![zero(), zero()],
            )),
        )),
    };
    let proof2 = check_top_with(sig2.clone(), elim2, nat())
        .expect("kernel accepts the two-index Square eliminator");
    recheck_proof(&sig2, &proof2)
        .expect("re-checker independently agrees the two-index eliminator has type Nat");
}

/// Build an *indexed* eliminator over a length-indexed `Vec A n` and re-check it from scratch. This
/// directly exercises the re-checker's extended `infer_elim`/`method_type` (the index threads
/// through the motive `λ n. λ (_:Vec Nat n). Nat` and the conclusion `P n v`), which the old
/// re-checker declined. The kernel accepts the eliminator; the independent checker must *agree*.
#[test]
fn recheck_agrees_on_indexed_elim() {
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Level, Term};

    fn u(n: u32) -> Term {
        let mut l = Level::Zero;
        for _ in 0..n {
            l = Level::Suc(Box::new(l));
        }
        Term::Univ(l)
    }
    let nat = || Term::Data(DataName("Nat".into()), vec![], vec![]);
    let zero = || Term::Con(ConName("Zero".into()), vec![]);
    let succ = |n: Term| Term::Con(ConName("Succ".into()), vec![n]);

    // Signature: Nat + Vec (one parameter A, one index n : Nat).
    let mut sig = Signature::new();
    sig.declare(DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("Zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("Succ".into()),
                args: vec![Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    sig.declare(DataDecl {
        name: DataName("Vec".into()),
        params: vec![u(0)],
        indices: vec![nat()],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("vnil".into()),
                args: vec![],
                result_indices: vec![zero()],
            },
            Constructor {
                name: ConName("vcons".into()),
                // (n : Nat) (x : A) (xs : Vec A n) ⇒ Vec A (Succ n)
                args: vec![
                    Arg::NonRec(nat()),
                    Arg::NonRec(Term::Var(1)),
                    Arg::Rec(vec![Term::Var(1)]),
                ],
                result_indices: vec![succ(Term::Var(2))],
            },
        ],
        path_constructors: vec![],
    });

    // motive P = λ (n : Nat). λ (_ : Vec Nat n). Nat   (the length-erasing "always Nat" motive).
    let motive = Term::Lam(Rc::new(Term::Lam(Rc::new(nat()))));
    // methods: vnil ↦ Zero ;  vcons ↦ λ n. λ x. λ xs. λ ih. Succ ih   (computes the length).
    let m_vnil = zero();
    let m_vcons = Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Lam(
        Rc::new(succ(Term::Var(0))),
    )))))));
    // scrutinee: vcons Zero Zero vnil : Vec Nat (Succ Zero). The constructor of a parameterized
    // family needs a type ascription to be inferable (the kernel cannot recover `A` otherwise).
    let vec_nat = |len: Term| Term::Data(DataName("Vec".into()), vec![nat()], vec![len]);
    let vnil = Term::Ann(
        Rc::new(Term::Con(ConName("vnil".into()), vec![])),
        Rc::new(vec_nat(zero())),
    );
    let vcons = Term::Ann(
        Rc::new(Term::Con(
            ConName("vcons".into()),
            vec![zero(), zero(), vnil],
        )),
        Rc::new(vec_nat(succ(zero()))),
    );
    let elim = Term::Elim {
        data: DataName("Vec".into()),
        motive: Rc::new(motive),
        methods: vec![m_vnil, m_vcons],
        scrutinee: Rc::new(vcons),
    };

    // The kernel accepts `elim : Nat`; the independent checker must agree.
    let proof = check_top_with(sig.clone(), elim.clone(), nat())
        .expect("kernel accepts the indexed Vec eliminator at type Nat");
    recheck_proof(&sig, &proof)
        .expect("re-checker independently agrees the indexed eliminator has type Nat");
}

/// The delay layer (`Delay`/`now`/`later`/`force`) is **modelled** by the re-checker, not declined.
/// We hand the re-checker `Judgement`s directly (exactly as `recheck_rejects_mutated_term` does);
/// each is a valid *typing* judgement — `recheck_judgement` is the general/buildable door, which
/// (like the kernel's `Checker`) accepts partial programs — so all must re-check to `Ok`, including
/// the partial `later`/`force` shapes. (The proof-strength *purity* door that rejects a top-level
/// `later`/`force` is exercised separately by `recheck_proof_path_demands_purity`.)
#[test]
fn recheck_accepts_delay_layer() {
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Level, Term};

    let mut sig = Signature::new();
    sig.declare(DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("Zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("Succ".into()),
                args: vec![Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    let nat = || Term::Data(DataName("Nat".into()), vec![], vec![]);
    let zero = || Term::Con(ConName("Zero".into()), vec![]);
    let delay_nat = || Term::Delay(Rc::new(nat()));

    let accept = |term: Term, ty: Term, what: &str| {
        let j = Judgement::HasType { term, ty };
        match recheck_judgement(&sig, &j) {
            Ok(()) => {}
            other => {
                panic!(
                    "expected the re-checker to ACCEPT {what} (not decline/reject), got {other:?}"
                )
            }
        }
    };

    // `Delay Nat : Univ 0`.
    accept(delay_nat(), Term::Univ(Level::Zero), "`Delay Nat : Univ 0`");
    // `now Zero : Delay Nat`.
    accept(
        Term::Now(Rc::new(zero())),
        delay_nat(),
        "`now Zero : Delay Nat`",
    );
    // `later (now Zero) : Delay Nat` — a partial (possibly-diverging) buildable judgement, accepted.
    accept(
        Term::Later(Rc::new(Term::Now(Rc::new(zero())))),
        delay_nat(),
        "`later (now Zero) : Delay Nat`",
    );
    // The headline: `force (now Zero) : Nat` — forcing re-checks to the underlying type, with
    // `force (now a) ⇝ a` in the independent normalizer. `force` infers its argument, so the
    // payload carries an ascription (`now (the Nat Zero)`), exactly as the elaborator produces.
    let now_zero_ann = Term::Now(Rc::new(Term::Ann(Rc::new(zero()), Rc::new(nat()))));
    accept(
        Term::Force(Rc::new(now_zero_ann)),
        nat(),
        "`force (now Zero) : Nat`",
    );
}

/// B2 (proof-boundary purity, the decline-vs-reject win): the *proof-strength* re-check door
/// (`recheck_judgement_as_proof`, what `recheck_proof` uses) independently re-derives the kernel's
/// `check_top_with` purity invariant — a proof's effect row must be empty. So:
///   * a *pure* judgement (`now Zero : Delay Nat`) passes the proof door, but
///   * an impure/partial one (`later (now Zero)` carrying `Partial`; `force (now Zero)` likewise) is
///     **Rejected** for impurity — where the plain (buildable) `recheck_judgement` accepts it.
///
/// A `Proof` value can never be forged with an impure conclusion (the kernel's purity gate forbids
/// it), so we exercise the re-derivation on hand-built `Judgement`s, which is exactly the soundness
/// scenario: had a buggy kernel minted such a proof, the second checker would now catch it.
#[test]
fn recheck_proof_path_demands_purity() {
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Term};

    let mut sig = Signature::new();
    sig.declare(DataDecl {
        name: DataName("Nat".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            Constructor {
                name: ConName("Zero".into()),
                args: vec![],
                result_indices: vec![],
            },
            Constructor {
                name: ConName("Succ".into()),
                args: vec![Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });
    let nat = || Term::Data(DataName("Nat".into()), vec![], vec![]);
    let zero = || Term::Con(ConName("Zero".into()), vec![]);
    let delay_nat = || Term::Delay(Rc::new(nat()));

    // A pure `now Zero : Delay Nat` is accepted by *both* doors.
    let pure = Judgement::HasType {
        term: Term::Now(Rc::new(zero())),
        ty: delay_nat(),
    };
    assert!(recheck_judgement(&sig, &pure).is_ok());
    assert!(
        blight_recheck::recheck_judgement_as_proof(&sig, &pure).is_ok(),
        "a pure `now Zero` passes the proof-purity door"
    );

    // `later (now Zero) : Delay Nat` carries `Partial`: accepted by the buildable door, REJECTED by
    // the proof door for impurity.
    let later = Judgement::HasType {
        term: Term::Later(Rc::new(Term::Now(Rc::new(zero())))),
        ty: delay_nat(),
    };
    assert!(
        recheck_judgement(&sig, &later).is_ok(),
        "the buildable door accepts a partial `later`"
    );
    match blight_recheck::recheck_judgement_as_proof(&sig, &later) {
        Err(RecheckError::Rejected(msg)) if msg.contains("pure") => {}
        other => panic!("the proof door must REJECT a partial `later` as impure, got {other:?}"),
    }

    // `force (now Zero) : Nat` likewise carries `Partial` and is rejected at the proof boundary.
    let now_zero_ann = Term::Now(Rc::new(Term::Ann(Rc::new(zero()), Rc::new(nat()))));
    let force = Judgement::HasType {
        term: Term::Force(Rc::new(now_zero_ann)),
        ty: nat(),
    };
    match blight_recheck::recheck_judgement_as_proof(&sig, &force) {
        Err(RecheckError::Rejected(msg)) if msg.contains("pure") => {}
        other => panic!("the proof door must REJECT a `force` as impure, got {other:?}"),
    }

    // Silence the unused `Arg` import warning (kept for parity with the sibling delay-layer test).
    let _ = Arg::Rec(vec![]);
}

/// RED: the re-checker independently ACCEPTS primitive `Int` programs (M11). It re-runs the same
/// definitional arithmetic in its own normalizer, so `2 * 3 + 4 : Int` is *re-verified*, not
/// declined. Comparisons (`int<`) also conclude `Int` (1/0), matching the kernel's choice.
#[test]
fn recheck_accepts_int_arith() {
    use blight_kernel::{IntPrimOp, Level, Term};

    let sig = Signature::new();
    let int_ty = || Term::IntTy;
    let lit = |n: i64| Term::IntLit(n);
    let prim = |op, a: Term, b: Term| Term::IntPrim {
        op,
        lhs: Rc::new(a),
        rhs: Rc::new(b),
    };

    let accept = |term: Term, ty: Term, what: &str| {
        let j = Judgement::HasType { term, ty };
        match recheck_judgement(&sig, &j) {
            Ok(()) => {}
            other => {
                panic!(
                    "expected the re-checker to ACCEPT {what} (not decline/reject), got {other:?}"
                )
            }
        }
    };

    // `Int : Univ 0`.
    accept(int_ty(), Term::Univ(Level::Zero), "`Int : Univ 0`");
    // `5 : Int`.
    accept(lit(5), int_ty(), "`5 : Int`");
    // `2 * 3 + 4 : Int` (and it definitionally reduces to `10` in the independent normalizer).
    let expr = prim(IntPrimOp::Add, prim(IntPrimOp::Mul, lit(2), lit(3)), lit(4));
    accept(expr, int_ty(), "`2 * 3 + 4 : Int`");
    // `(int< 1 2) : Int` — comparisons conclude `Int` (1/0), like the kernel.
    accept(
        prim(IntPrimOp::Lt, lit(1), lit(2)),
        int_ty(),
        "`1 < 2 : Int`",
    );
}

/// The effect/handler layer is **modelled** by the re-checker. We hand it `Judgement`s directly via
/// the general/buildable door (`recheck_judgement`), which accepts effectful programs: `! E Unit`
/// (a type former), a bare `perform op tt` (carries the unhandled label `E`), and a fully *handled*
/// program (whose effect `E` is discharged) all re-check to `Ok`. (The proof-strength door would
/// reject the bare `perform` for impurity — see `recheck_proof_path_demands_purity`; the handler's
/// independent continuation-grade discipline is `recheck_enforces_continuation_grade`.) We build a
/// tiny signature with one effect `E` whose op `op : Π(_:Unit). Unit`.
#[test]
fn recheck_accepts_effects_and_handlers() {
    use blight_kernel::row::EffName;
    use blight_kernel::signature::{EffDecl, OpSig};
    use blight_kernel::{Arg, ConName, Constructor, DataDecl, DataName, Grade, Level, Row, Term};

    let mut sig = Signature::new();
    // A `Unit` type so the op's parameter/result are concrete.
    sig.declare(DataDecl {
        name: DataName("Unit".into()),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![Constructor {
            name: ConName("tt".into()),
            args: vec![],
            result_indices: vec![],
        }],
        path_constructors: vec![],
    });
    let unit_ty = || Term::Data(DataName("Unit".into()), vec![], vec![]);
    let tt = || Term::Con(ConName("tt".into()), vec![]);

    // effect E { op : Π(_:Unit). Unit }  (continuation grade is irrelevant to the re-checker).
    let decl = EffDecl {
        name: EffName::new("E"),
        params: vec![],
        ops: vec![OpSig {
            name: "op".into(),
            param_ty: unit_ty(),
            result_ty: unit_ty(),
            cont_grade: Grade::Omega,
        }],
    };
    sig.check_effect(&decl).expect("E is well-formed");
    sig.declare_effect(decl);

    let accept = |term: Term, ty: Term, what: &str| {
        let j = Judgement::HasType { term, ty };
        match recheck_judgement(&sig, &j) {
            Ok(()) => {}
            other => {
                panic!(
                    "expected the re-checker to ACCEPT {what} (not decline/reject), got {other:?}"
                )
            }
        }
    };

    // `! E Unit : Univ 0` — the effectful computation *type* is a (pure) type former.
    accept(
        Term::EffTy(
            Row::single(EffName::new("E"), Grade::One),
            Rc::new(unit_ty()),
        ),
        Term::Univ(Level::Zero),
        "`! E Unit : Univ 0`",
    );

    // `perform op tt : Unit` — the op result type, re-derived from the signature. The buildable door
    // accepts the unhandled effect (the proof door would not — see the purity test).
    accept(
        Term::Op {
            effect: EffName::new("E"),
            op: "op".into(),
            type_args: vec![],
            arg: Rc::new(tt()),
        },
        unit_ty(),
        "`perform op tt : Unit`",
    );

    // `handle (perform op tt) { return x. x ; (op x k. (k tt)) } : Unit`. The return clause binds
    // `x:Unit` (de Bruijn 0) and yields `x`; the op clause binds `x:Unit` then `k:Unit→Unit`
    // (`k` = de Bruijn 0, `x` = de Bruijn 1) and resumes `k tt`. The Handle's type is `Unit`.
    accept(
        Term::Handle {
            body: Rc::new(Term::Op {
                effect: EffName::new("E"),
                op: "op".into(),
                type_args: vec![],
                arg: Rc::new(tt()),
            }),
            return_clause: Rc::new(Term::Var(0)),
            op_clauses: vec![(
                "op".into(),
                Rc::new(Term::App(Rc::new(Term::Var(0)), Rc::new(tt()))),
            )],
        },
        unit_ty(),
        "`handle (perform op tt) { return x. x ; op x k. (k tt) } : Unit`",
    );

    // Sanity: silence the otherwise-unused `Arg` import (kept for parity with sibling tests).
    let _ = Arg::Rec(vec![]);
}

/// B2 (continuation-multiplicity grade): the re-checker now independently enforces a handler
/// clause's continuation grade, mirroring the kernel. We build a handler whose op clause resumes its
/// continuation `k` **twice** (`k (k tt)`), and show that the *only* thing distinguishing acceptance
/// from rejection is the operation's declared `cont_grade`:
///   * with `cont_grade = ω` (resume freely) the whole handled program is pure → `Ok`;
///   * with `cont_grade = 1` (resume at most once) the double-resume is a grade violation → the
///     re-checker `Rejected`s it, where before B2 the grade was ignored and it slipped through.
#[test]
fn recheck_enforces_continuation_grade() {
    use blight_kernel::row::EffName;
    use blight_kernel::signature::{EffDecl, OpSig};
    use blight_kernel::{ConName, Constructor, DataDecl, DataName, Grade, Term};

    // Build a signature with `Unit` and an effect `E { op : Unit -> Unit }` at a chosen cont grade.
    let make_sig = |cont_grade: Grade| {
        let mut sig = Signature::new();
        sig.declare(DataDecl {
            name: DataName("Unit".into()),
            params: vec![],
            indices: vec![],
            level: 0,
            constructors: vec![Constructor {
                name: ConName("tt".into()),
                args: vec![],
                result_indices: vec![],
            }],
            path_constructors: vec![],
        });
        let decl = EffDecl {
            name: EffName::new("E"),
            params: vec![],
            ops: vec![OpSig {
                name: "op".into(),
                param_ty: Term::Data(DataName("Unit".into()), vec![], vec![]),
                result_ty: Term::Data(DataName("Unit".into()), vec![], vec![]),
                cont_grade,
            }],
        };
        sig.check_effect(&decl).expect("E is well-formed");
        sig.declare_effect(decl);
        sig
    };

    let unit_ty = || Term::Data(DataName("Unit".into()), vec![], vec![]);
    let tt = || Term::Con(ConName("tt".into()), vec![]);
    // `handle (perform op tt) { return x. x ; op x k. (k (k tt)) } : Unit`. The op clause binds
    // `x:Unit` (de Bruijn 1) then `k:Unit→Unit` (de Bruijn 0) and resumes `k` *twice* — `k (k tt)`.
    let double_resume_handle = || Term::Handle {
        body: Rc::new(Term::Op {
            effect: EffName::new("E"),
            op: "op".into(),
            type_args: vec![],
            arg: Rc::new(tt()),
        }),
        return_clause: Rc::new(Term::Var(0)),
        op_clauses: vec![(
            "op".into(),
            Rc::new(Term::App(
                Rc::new(Term::Var(0)),
                Rc::new(Term::App(Rc::new(Term::Var(0)), Rc::new(tt()))),
            )),
        )],
    };

    // ω continuation: resuming twice is allowed; the effect is discharged → pure → accepted.
    let sig_omega = make_sig(Grade::Omega);
    let j_ok = Judgement::HasType {
        term: double_resume_handle(),
        ty: unit_ty(),
    };
    assert!(
        recheck_judgement(&sig_omega, &j_ok).is_ok(),
        "with cont_grade=ω, a double-resume handler is well-graded and pure → re-check Ok"
    );

    // grade-1 continuation: resuming twice violates the multiplicity → independently Rejected.
    let sig_one = make_sig(Grade::One);
    let j_bad = Judgement::HasType {
        term: double_resume_handle(),
        ty: unit_ty(),
    };
    match recheck_judgement(&sig_one, &j_bad) {
        Err(RecheckError::Rejected(msg)) if msg.contains("continuation") => {}
        other => panic!(
            "with cont_grade=1, a double-resume handler must be REJECTED for its continuation \
             multiplicity, got {other:?}"
        ),
    }
}

/// RED (M7): the re-checker AGREES with the kernel on a full surface effect program loaded through
/// the elaborator (`effects_demo.bl`-style): an effect declaration plus a handled `perform`. The
/// handled computation's definition is in-fragment for the re-checker (it re-derives the result
/// type `Nat`), so it must re-check to `Ok` rather than `Declined`.
#[test]
fn recheck_agrees_on_surface_effect_program() {
    let src = "\
(load \"std/nat.bl\")
(defdata Unit () (tt))
(effect State (get Unit Nat) (put Nat Unit))
(define main Nat
  (handle (perform get tt)
    (return x x)
    (get x k (k (Succ (Succ (Succ Zero)))))))
";
    let (env, proofs) = load(src);
    let sig = env.signature();
    // The `main` definition (a handled effect program) must be re-checked to `Ok`.
    let mut saw_effect_global = false;
    for (name, term, ty) in env.typed_globals() {
        if name == "main" {
            saw_effect_global = true;
            let j = Judgement::HasType {
                term: term.clone(),
                ty: ty.clone(),
            };
            match recheck_judgement(sig, &j) {
                Ok(()) => {}
                other => panic!(
                    "expected the re-checker to ACCEPT the handled effect program `main`, got {other:?}"
                ),
            }
        }
    }
    assert!(
        saw_effect_global,
        "expected a `main` effect global to re-check"
    );
    // And no kernel proof anywhere may be rejected.
    assert_agreement(&env, &proofs, "M7:surface-effects");
}

/// The elaborator now supports a **parameterized / state-passing handler**: one whose result type
/// is itself a function `State -> A`, threading the state through the continuation, with each clause
/// a lambda over that state (`handle : Nat -> Nat`). Before this landed, elaboration failed "cannot
/// infer a type" on the un-annotated clause lambdas. Two elaborator-only fixes enable it: (a) the
/// handle's expected result type is flowed into its clauses (so their lambdas *check* against it),
/// and (b) `synth_type` recognizes `perform` (so a `let` binding a performed value in the handle
/// body can ascribe its desugared lambda). The kernel already typed `k : opCod -> C` in check mode.
/// This pins that the shape elaborates, kernel-checks, and — the two-checker guarantee — the
/// independent re-checker AGREES (`Ok`).
#[test]
fn recheck_agrees_on_state_passing_handler() {
    let src = "\
(load \"std/nat.bl\")
(defdata MyUnit () (myu))
(effect St (getS MyUnit Nat) (putS Nat MyUnit))
(define prog (Pi ((s0 Nat)) Nat)
  (handle
    (let ((a (perform getS myu)))
      (let ((u (perform putS (Succ a)))) (perform getS myu)))
    (return x (lam (s) x))
    (getS u k (lam (s) ((k s) s)))
    (putS v k (lam (s) ((k myu) v)))))
";
    let (env, proofs) = load(src);
    let sig = env.signature();
    let mut saw = false;
    for (name, term, ty) in env.typed_globals() {
        if name == "prog" {
            saw = true;
            let j = Judgement::HasType {
                term: term.clone(),
                ty: ty.clone(),
            };
            match recheck_judgement(sig, &j) {
                Ok(()) => {}
                other => panic!(
                    "re-checker must ACCEPT the state-passing handler `prog` (soundness/agreement), got {other:?}"
                ),
            }
        }
    }
    assert!(
        saw,
        "expected the state-passing handler global `prog` to elaborate and re-check"
    );
    assert_agreement(&env, &proofs, "state-passing-handler");
}

/// False-alarm fix: an effectful **`Path` computation demo**. `run3` runs a handler that resolves
/// `tick` to `3`, so `run3 ≡ 3` definitionally — the KERNEL verifies this by running the whole
/// handler inside conversion and accepts the constant `Path` proof `run3-is-3`. The independent
/// re-checker deliberately does NOT run effect semantics (`normalize.rs`: `handle`/`perform`
/// evaluate to *stuck neutrals*), so it cannot decide the boundary `3 ≡ run3`. The only sound
/// verdict is to **`Declined`** (abstain): it must NEVER `Rejected` a program the kernel accepted
/// (that would be a false soundness alarm), and must never certify a computation it did not run.
/// This locks in the `is_stuck_on_effect` boundary-abstention path — the fix the effect-parser
/// flagship exposed. Before it, this global `Rejected`.
#[test]
fn recheck_declines_not_rejects_effectful_path_boundary() {
    let src = "\
(load \"std/nat.bl\")
(defdata MyUnit () (myu))
(effect Tick (tick MyUnit Nat))
(define run3 Nat
  (handle (perform tick myu)
    (return x x)
    (tick u k (k (Succ (Succ (Succ Zero)))))))
(define run3-is-3 (Path Nat run3 (Succ (Succ (Succ Zero)))) (plam (i) (Succ (Succ (Succ Zero)))))
";
    let (env, _proofs) = load(src);
    let sig = env.signature();
    let mut saw = false;
    for (name, term, ty) in env.typed_globals() {
        if name == "run3-is-3" {
            saw = true;
            let j = Judgement::HasType {
                term: term.clone(),
                ty: ty.clone(),
            };
            match recheck_judgement(sig, &j) {
                Err(RecheckError::Declined(_)) => {}
                Err(RecheckError::Rejected(m)) => panic!(
                    "re-checker must DECLINE (abstain) on an effectful `Path` boundary it cannot run, \
                     NOT reject a kernel-accepted program (false soundness alarm); got Rejected: {m}"
                ),
                Ok(()) => panic!(
                    "re-checker must not certify an effectful `Path` boundary it never ran; got Ok"
                ),
            }
        }
    }
    assert!(
        saw,
        "expected the effectful `Path` demo `run3-is-3` to elaborate and be kernel-accepted"
    );
}

/// RED (soundness alarm): a dependent **indexed-motive** eliminator whose result type DEPENDS on
/// the index. `safe-tail : Π(A:U)(n:Nat)(v:Vec A (Succ n)). Vec A n` drops the head; its motive's
/// result type is `Vec A n` (it mentions the index), unlike the length-erasing "always Nat" motive
/// in [`recheck_agrees_on_indexed_elim`]. The kernel ACCEPTS it; the re-checker must AGREE (`Ok`),
/// never `Rejected` (which would be a soundness alarm).
#[test]
fn recheck_agrees_on_dependent_indexed_motive_safe_tail() {
    let src = "\
(load \"std/nat.bl\")
(load \"std/vec.bl\")
(define-rec safe-tail (Pi ((A (Type 0)) (n Nat) (v (Vec A (Succ n)))) (Vec A n))
  (lam (A n v)
    (match v
      [(vnil) vnil]
      [(vcons m x xs) xs])))
";
    let (env, _proofs) = load(src);
    let sig = env.signature();
    let mut saw = false;
    for (name, term, ty) in env.typed_globals() {
        if name == "safe-tail" {
            saw = true;
            let j = Judgement::HasType {
                term: term.clone(),
                ty: ty.clone(),
            };
            match recheck_judgement(sig, &j) {
                Ok(()) => {}
                other => panic!(
                    "expected the re-checker to AGREE (Ok) on the dependent indexed motive `safe-tail`, got {other:?}"
                ),
            }
        }
    }
    assert!(saw, "expected a `safe-tail` global to re-check");
}

/// RED (soundness alarm): a **length-preserving** dependent indexed-motive eliminator.
/// `vec-map : Π(A B:U)(f:A→B)(n:Nat)(v:Vec A n). Vec B n` rebuilds the spine, so its result type
/// `Vec B n` mentions the index AND its `vcons` arm must refine `n := Succ m` and type the recursive
/// call's induction hypothesis at the *shorter* length `m`. The kernel ACCEPTS it; the re-checker
/// must AGREE (`Ok`), never `Rejected`. This exercises the motive-strengthening + per-branch index
/// refinement that closed the soundness alarm.
#[test]
fn recheck_agrees_on_dependent_indexed_motive_vec_map() {
    let src = "\
(load \"std/nat.bl\")
(load \"std/vec.bl\")
(define-rec vec-map (Pi ((A (Type 0)) (B (Type 0)) (f (Pi ((x A)) B)) (n Nat) (v (Vec A n))) (Vec B n))
  (lam (A B f n v)
    (match v
      [(vnil) vnil]
      [(vcons m x xs) (vcons m (f x) (vec-map A B f m xs))])))
";
    let (env, _proofs) = load(src);
    let sig = env.signature();
    let mut saw = false;
    for (name, term, ty) in env.typed_globals() {
        if name == "vec-map" {
            saw = true;
            let j = Judgement::HasType {
                term: term.clone(),
                ty: ty.clone(),
            };
            match recheck_judgement(sig, &j) {
                Ok(()) => {}
                other => panic!(
                    "expected the re-checker to AGREE (Ok) on the dependent indexed motive `vec-map`, got {other:?}"
                ),
            }
        }
    }
    assert!(saw, "expected a `vec-map` global to re-check");
}

/// RED: the independent re-checker agrees with the kernel across a corpus spanning the M0–M5
/// milestones. The contract (via [`assert_agreement`]): 0 `Rejected` anywhere; out-of-fragment
/// constructs are counted as honest `Declined`. Each milestone is labelled so a regression points
/// at the offending stage.
#[test]
#[allow(non_snake_case)]
fn recheck_agrees_with_kernel_on_M0_M5() {
    // M0 — the core dependent layer + structural recursion: Nat arithmetic.
    let (env, proofs) = load(
        "(defdata Nat () (Zero) (Succ (n Nat)))\n\
         (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n\
           (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))\n\
         (the Nat (plus (Succ Zero) (Succ (Succ Zero))))",
    );
    assert_agreement(&env, &proofs, "M0:nat-arith");

    // M1 — grades / linearity: a linear binder used exactly once (kernel-checked `the`).
    let (env, proofs) = load(
        "(defdata Nat () (Zero) (Succ (n Nat)))\n\
         (the (Pi ((x Nat 1)) Nat) (lam (x) x))",
    );
    assert_agreement(&env, &proofs, "M1:linear");

    // M2 — effects: declaring/using an effect now produces **in-fragment** terms for the
    // re-checker (M7). It re-derives `! E A`/`perform`/`handle` *types* (ignoring rows and
    // continuation grades, the kernel's job), so a handled effect program is now ACCEPTED, not
    // declined. The harness still asserts no Rejected.
    let (env, proofs) = load(
        "(load \"std/nat.bl\")\n\
         (defdata Unit () (tt))\n\
         (effect State (get Unit Nat) (put Nat Unit))\n\
         (define main Nat\n\
           (handle (perform get tt)\n\
             (return x x)\n\
             (get x k (k (Succ (Succ (Succ Zero)))))))",
    );
    assert_agreement(&env, &proofs, "M2:effects");

    // M3 — the tower (traits + functorized tree) via the std modules.
    let (env, proofs) = load(
        "(load \"traits.bl\")\n\
         (the Nat (show (Succ (Succ Zero))))\n\
         (the Bool (cmp false true))",
    );
    assert_agreement(&env, &proofs, "M3:traits");
    let (env, proofs) = load("(load \"modules.bl\")");
    assert_agreement(&env, &proofs, "M3:modules");

    // M3 — proof by tactics (LCF door): `plus-zero` proved by `induction`+`cong`/`refl`.
    let (env, proofs) = load("(load \"tactics.bl\")\n(load \"plus_zero_tac.bl\")");
    assert_agreement(&env, &proofs, "M3:tactics");

    // M4 — the cubical headline: `plus-zero : Π n. Path Nat (plus n Zero) n` (Path/PLam/PApp are
    // in-fragment for the re-checker; the proof must re-check).
    let (env, proofs) = load(
        "(defdata Nat () (Zero) (Succ (n Nat)))\n\
         (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n\
           (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))\n\
         (define-rec plus-zero (Pi ((n Nat)) (Path Nat (plus n Zero) n))\n\
           (lam (n) (match n\n\
             [(Zero)   (plam (i) Zero)]\n\
             [(Succ k) (plam (i) (Succ ((plus-zero k) @ i)))])))",
    );
    assert_agreement(&env, &proofs, "M4:cubical-path");

    // M5 — regions: the opaque `Rgn` capability and a single-use region scope.
    let (env, proofs) = load(
        "(load \"regions.bl\")\n\
         (defdata Nat () (Zero) (Succ (n Nat)))\n\
         (the Nat (region r Zero))",
    );
    assert_agreement(&env, &proofs, "M5:regions");
}

// =================================================================================================
// Wave 5 / N1: NbE-with-sharing `conv` fast path — kernel/re-checker parity golden.
//
// Both `blight-kernel` and `blight-recheck` independently normalize via NbE, and both had the
// same "no sharing across reduction steps" cost (see `ValueChain`'s doc-comment in each crate's
// `value.rs`). This builds a raw kernel `Term` directly (bypassing the elaborator, for exact
// control over recursion depth) proving `plus (nat_lit depth) Zero ≡ nat_lit depth` by a
// constant path — the same shape as the `plus-zero` proof above, but deep enough that the
// pre-N1 `Vec`-backed `Env` made both checkers' `conv` prohibitively slow. `check_top_with`
// (kernel) must produce a `Proof`, and `recheck_proof` (the independent re-checker) must then
// independently agree — both within the same generous, non-flaky bound.
// =================================================================================================

fn deep_plus_zero_proof(depth: u32) -> (Signature, Term) {
    let nat = DataName("Nat".into());
    let zero_con = ConName("Zero".into());
    let succ_con = ConName("Succ".into());

    let mut sig = Signature::new();
    sig.declare(blight_kernel::DataDecl {
        name: nat.clone(),
        params: vec![],
        indices: vec![],
        level: 0,
        constructors: vec![
            blight_kernel::Constructor {
                name: zero_con.clone(),
                args: vec![],
                result_indices: vec![],
            },
            blight_kernel::Constructor {
                name: succ_con.clone(),
                args: vec![blight_kernel::Arg::Rec(vec![])],
                result_indices: vec![],
            },
        ],
        path_constructors: vec![],
    });

    let nat_ty = || Term::Data(nat.clone(), vec![], vec![]);
    let zero = || Term::Con(zero_con.clone(), vec![]);
    let succ = |n: Term| Term::Con(succ_con.clone(), vec![n]);
    let nat_lit = |n: u32| {
        let mut t = zero();
        for _ in 0..n {
            t = succ(t);
        }
        t
    };

    // `plus = λa. λb. Elim Nat (λ_. Nat) [b, λn.λih. Succ ih] a` — structurally recursive on
    // its *first* argument, so `plus (nat_lit depth) Zero` drives a `depth`-deep `do_elim`.
    //
    // Ascribed with its Pi type (`Term::Ann`), matching how the elaborator always produces
    // curried definitions in practice (a named global with a *known* type, never a bare anonymous
    // `Lam` in inference position): the re-checker's bidirectional `infer` cannot synthesize a
    // type for a bare introduction form (by design — the kernel's `CannotInfer`/the re-checker's
    // matching `Declined`, a documented fragment limitation, not a soundness gap), so building
    // this raw term without the ascription would make the re-checker *decline* rather than agree,
    // for a reason unrelated to what N1 fixes.
    let plus_ty = Term::Pi(
        Grade::Omega,
        Rc::new(nat_ty()),
        Rc::new(Term::Pi(Grade::Omega, Rc::new(nat_ty()), Rc::new(nat_ty()))),
    );
    let plus = Term::Ann(
        Rc::new(Term::Lam(Rc::new(Term::Lam(Rc::new(Term::Elim {
            data: nat.clone(),
            motive: Rc::new(Term::Lam(Rc::new(nat_ty()))),
            methods: vec![
                Term::Var(0),
                Term::Lam(Rc::new(Term::Lam(Rc::new(succ(Term::Var(0)))))),
            ],
            scrutinee: Rc::new(Term::Var(1)),
        }))))),
        Rc::new(plus_ty),
    );
    let plus_applied = Term::App(
        Rc::new(Term::App(Rc::new(plus), Rc::new(nat_lit(depth)))),
        Rc::new(zero()),
    );

    // Proof term: the constant path `λi. nat_lit depth`, checked against
    // `Path Nat (plus (nat_lit depth) Zero) (nat_lit depth)` — the boundary check at `i = 0`
    // forces exactly the deep `conv` this golden pins.
    let ty = Term::PathP {
        family: Rc::new(nat_ty()),
        lhs: Rc::new(plus_applied),
        rhs: Rc::new(nat_lit(depth)),
    };
    let proof_term = Term::PLam(Rc::new(nat_lit(depth)));
    (sig, Term::Ann(Rc::new(proof_term), Rc::new(ty)))
}

/// `eval`/`check`/`conv` recurse natively in the Rust call stack; mirrors
/// `crates/blight-repl/tests/spore.rs`'s `on_big_stack` for the same reason.
fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(f)
        .expect("spawn big-stack test thread")
        .join()
        .expect("big-stack test thread panicked (see message above)");
}

/// Red-first (Wave 5/N1): before the `ValueChain` sharing fix, a deep `plus (nat_lit n) Zero ≡
/// nat_lit n` proof made the kernel's own `conv` prohibitively slow well before the re-checker
/// was even reached. Green: both the kernel's `check_top_with` and the re-checker's
/// `recheck_proof` independently finish and agree, within a generous bound.
#[test]
fn deep_plus_zero_conv_kernel_and_recheck_agree_in_bounded_time() {
    on_big_stack(|| {
        let (sig, ann) = deep_plus_zero_proof(1_500);
        let Term::Ann(term, ty) = ann else {
            unreachable!()
        };

        let start = std::time::Instant::now();
        let proof = check_top_with(
            sig.clone(),
            blight_kernel::unshare(term),
            blight_kernel::unshare(ty.clone()),
        )
        .expect("kernel accepts the deep plus-zero proof");
        let recheck_result = blight_recheck::recheck_proof(&sig, &proof);
        let elapsed = start.elapsed();

        assert!(
            recheck_result.is_ok(),
            "the re-checker must independently AGREE the deep plus-zero proof checks, got {recheck_result:?}"
        );
        // Machine-speed-independent regression guard (converted from a 15 s wall-clock bound
        // after repeated loaded-machine false alarms): scale-pair — the same pipeline at a
        // quarter of the depth, in the same process. Converting the instrument immediately
        // taught something the wall clock hid: the pipeline is *quadratic today* (measured
        // 19.6× for the 4× depth pre-N6) — the IH here is genuinely used, so N5's skip doesn't
        // apply. N6's Value-tree sharing (Box→Rc, both engines) cut the *constant* ~1.9× (paired
        // twin: 16.6× → 15.3× ratio, 1.37 s → 0.73 s absolute) but falsified the deep-clone
        // hypothesis for the *ratio*: the surviving quadratic is re-evaluation churn — eval/
        // do_elim materialize a fresh O(level) chain per level and drop it (profile: recursive
        // drop_in_place/clone under eval; the N6 item-3 refl endpoint re-evaluation target's
        // measured justification). Bound: catch the pre-ValueChain recurrence (≥ cubic, ~64×+),
        // which still fails loudly, WITHOUT flaking on a shared runner. The ratio is ~15–17× on a
        // quiet machine (17.5× measured on a fast dev host, above the original 15.3×) but a loaded
        // CI runner inflates the longer leg enough to graze 20× and false-alarm, so the ceiling is
        // 40× — ~2× headroom over a quiet run, still well under the ~64× cubic-regression signal.
        // Tighten when item 3 (re-evaluation sharing) lands and the absolute times shrink.
        let (small_sig, small_ann) = deep_plus_zero_proof(375);
        let Term::Ann(small_term, small_ty) = small_ann else {
            unreachable!()
        };
        let small_start = std::time::Instant::now();
        let small_proof = check_top_with(
            small_sig.clone(),
            blight_kernel::unshare(small_term),
            blight_kernel::unshare(small_ty),
        )
        .expect("kernel accepts the quarter-depth plus-zero proof");
        let _ = blight_recheck::recheck_proof(&small_sig, &small_proof);
        let small_elapsed = small_start
            .elapsed()
            .max(std::time::Duration::from_micros(1));
        let ratio = elapsed.as_secs_f64() / small_elapsed.as_secs_f64();
        eprintln!("N6 payoff: depth-1500/depth-375 ratio = {ratio:.2}x ({elapsed:?} vs {small_elapsed:?})");
        assert!(
            ratio < 40.0,
            "kernel + re-checker at depth 1,500 cost {ratio:.1}× the depth-375 twin \
             ({elapsed:?} vs {small_elapsed:?}) — post-N6 quadratic-with-headroom is today's \
             law (~15–17× quiet, ceiling 40× to absorb CI noise); past 40× either the ValueChain \
             sharing or the N6 Rc sharing has regressed to ≥ cubic (see each crate's value.rs)"
        );
    });
}

/// Discriminator twin: the sharing fast path must change only *how much work* is repeated, never
/// *what* is decided — an off-by-one deep proof must still be rejected by both checkers.
#[test]
fn deep_plus_zero_conv_off_by_one_still_rejected_by_kernel() {
    on_big_stack(|| {
        let (sig, ann) = deep_plus_zero_proof(200);
        let Term::Ann(term, ty) = ann else {
            unreachable!()
        };
        // Corrupt the claimed type's `rhs` endpoint by one `Succ`, matching `deep_plus_zero_proof`'s
        // internal shape without needing to reconstruct it (off-by-one term instead).
        let Term::PathP { family, lhs, rhs } = blight_kernel::unshare(ty) else {
            unreachable!()
        };
        let bumped_rhs = Term::Con(ConName("Succ".into()), vec![blight_kernel::unshare(rhs)]);
        let bumped_ty = Term::PathP {
            family,
            lhs,
            rhs: Rc::new(bumped_rhs),
        };
        match check_top_with(sig, blight_kernel::unshare(term), bumped_ty) {
            Err(_) => {}
            Ok(p) => panic!("kernel must reject the off-by-one plus-zero proof, got {p:?}"),
        }
    });
}
