//! L7 acceptance test (spec §5.3 / §9): the kernel must accept the cubical `plus-zero` and
//! reject a deliberately wrong step. Black-box: kernel + elaborator public APIs only.
//!
//! This is intentionally RED until the full L1..L6 stack is green. It is the M0 north star.
//!
//! The program under test (spec §5.3):
//!
//! ```scheme
//! (defdata Nat () (Zero) (Succ (n Nat)))
//! (define-rec plus
//!   (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))
//! (define-rec plus-zero
//!   (lam (n) (match n
//!     [(Zero)   (plam (i) Zero)]
//!     [(Succ k) (plam (i) (Succ ((plus-zero k) @ i)))])))
//! ```
//!
//! Acceptance: `plus-zero : (Pi ((n Nat)) (Path Nat (plus n Zero) n))` is accepted; the mutated
//! step `(plam (i) k)` is rejected.

use blight_elab::ElabEnv;

/// The source of the accepted program (spec §5.3).
const PLUS_ZERO_SRC: &str = r#"
(defdata Nat () (Zero) (Succ (n Nat)))
(define-rec plus
  (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))
(define-rec plus-zero
  (lam (n) (match n
    [(Zero)   (plam (i) Zero)]
    [(Succ k) (plam (i) (Succ ((plus-zero k) @ i)))])))
"#;

/// A deliberately wrong step: `(plam (i) k)` instead of `(plam (i) (Succ ((plus-zero k) @ i)))`.
const WRONG_STEP_SRC: &str = r#"
(defdata Nat () (Zero) (Succ (n Nat)))
(define-rec plus
  (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))
(define-rec plus-zero
  (lam (n) (match n
    [(Zero)   (plam (i) Zero)]
    [(Succ k) (plam (i) k)])))
"#;

#[test]
fn kernel_accepts_plus_zero() {
    let proof = check_program(PLUS_ZERO_SRC).expect("plus-zero should typecheck");
    let _ = proof.concl();
}

#[test]
fn kernel_accepts_plus_alone() {
    const SRC: &str = r#"
(defdata Nat () (Zero) (Succ (n Nat)))
(define-rec plus
  (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))
"#;
    check_program(SRC).expect("plus should typecheck");
}

#[test]
fn kernel_rejects_wrong_step() {
    assert!(
        check_program(WRONG_STEP_SRC).is_err(),
        "the wrong (plam (i) k) step must be rejected"
    );
}

/// Drive the whole pipeline for the program, returning the kernel `Proof` for `plus-zero`.
///
/// The source carries no type signatures, so we supply the intended types here (the elaborator
/// reads each `define-rec`'s motive off its declared type). The kernel re-checks everything; an
/// ill-typed body — including the mutated `(plam (i) k)` — is rejected.
fn check_program(src: &str) -> Result<blight_kernel::Proof, String> {
    use blight_elab::{elaborate, parse_decl, read_all, Decl};
    use blight_kernel::{check_top_with, Term};

    let mut env = ElabEnv::new();
    let forms = read_all(src).map_err(|e| format!("read: {e:?}"))?;

    let mut last: Option<(String, Term)> = None; // (name, core type) of the last definition
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
    check_top_with(env.signature().clone(), term, ty).map_err(|e| format!("kernel: {e:?}"))
}

/// The intended core-less surface types for the program's definitions (spec §5.3).
fn declared_type(name: &str) -> Result<blight_elab::Surface, String> {
    let src = match name {
        // plus : Pi (a Nat) (Pi (b Nat) Nat)
        "plus" => "(Pi ((a Nat) (b Nat)) Nat)",
        // plus-zero : Pi (n Nat) (Path Nat (plus n Zero) n)
        "plus-zero" => "(Pi ((n Nat)) (Path Nat (plus n Zero) n))",
        other => return Err(format!("no declared type for `{other}`")),
    };
    let (sexpr, _) = blight_elab::read_one(src).map_err(|e| format!("{e:?}"))?;
    blight_elab::parse_surface(&sexpr).map_err(|e| format!("{e:?}"))
}
