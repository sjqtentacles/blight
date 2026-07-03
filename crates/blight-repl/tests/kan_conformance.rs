//! L5 conformance: `funext` as a derived theorem at the surface (spec §2.6). This drives the
//! cubical machinery end-to-end, independently of the `plus-zero` acceptance proof. Black-box.
//!
//! `funext : (Pi ((f (Pi A B)) (g (Pi A B)) (h (Pi ((x A)) (Path B (f x) (g x))))) (Path (Pi A B) f g))`
//! realized by `(plam (i) (lam (x) ((h x) @ i)))` (spec §2.6).
//!
//! Drives the cubical path machinery end-to-end via type-directed reflection of applied path
//! neutrals (`(h x) @ r`).

use blight_elab::{elaborate, Decl, ElabEnv};
use blight_kernel::{check_top_with, Term};

const FUNEXT_SRC: &str = r#"
(define funext
  (the (Pi ((A (Type 0))
            (B (Type 0))
            (f (Pi ((x A)) B))
            (g (Pi ((x A)) B))
            (h (Pi ((x A)) (Path B (f x) (g x)))))
           (Path (Pi ((x A)) B) f g))
       (lam (A B f g h) (plam (i) (lam (x) ((h x) @ i))))))
"#;

#[test]
fn funext_is_provable() {
    let proof = check_program(FUNEXT_SRC).expect("funext should typecheck via cubical paths");
    let _ = proof.concl();
}

/// `ua` formation conformance (spec §7 cubical layer; plan A2b): an equivalence becomes a path
/// between types, realized by the single-face `Glue` line `i. Glue B (i=0) A e`. This drives the
/// kernel's `Glue` formation *and* the CCHM Glue boundary reductions end-to-end — the `Path`
/// endpoint check only succeeds because `Glue B ⊤ A e ≡ A` (at `i0`) and `Glue B ⊥ A e ≡ B`
/// (at `i1`) hold definitionally. Black-box, kernel-only.
const UA_SRC: &str = r#"
(define ua
  (the (Pi ((A (Type 0))
            (B (Type 0))
            (e (Sigma ((f (Pi ((x A)) B)))
                 (Pi ((y B))
                   (Sigma ((c (Sigma ((x A)) (Path B (f x) y))))
                     (Pi ((w (Sigma ((x A)) (Path B (f x) y))))
                       (Path (Sigma ((x A)) (Path B (f x) y)) c w)))))))
           (Path (Type 0) A B))
       (lam (A B e) (plam (i) (Glue B (ieq0 i) A e)))))
"#;

#[test]
fn ua_formation_is_conformant() {
    let proof = check_program(UA_SRC)
        .expect("ua should typecheck: single-face Glue line with definitional CCHM boundaries");
    let _ = proof.concl();
}

/// `ua` *computation* conformance (the univalence computation rule; plan A2b/A1/C2): transporting
/// along `ua e` reduces to the equivalence's forward map,
///   `transp (i. (ua e) @ i) ⊥ a ≡ equiv-fun e a`,
/// driven by the `transp`-over-`Glue` reduction in `crates/blight-kernel/src/kan.rs`. This golden
/// pins it **black-box through the full elaborate→kernel pipeline** on a closed, fully *inlined*
/// instance. The conformance harness runs with a bare `ElabEnv` (no prelude), so everything is
/// built from kernel primitives only: the transported type is `T := Π (A:Type 0)(x:A). A` (the
/// polymorphic-identity type, closed + inhabited), the point is `a := λA x. x : T`, and the
/// equivalence is the *inlined* `id-equiv T` (forward map `λx.x`, contractibility by the De Morgan
/// singleton connection). Transporting `a` along `ua (id-equiv T)` must land back on `a`; the proof
/// term is plain `refl` (`λ_. a`) — it type-checks **only because** the kernel actually performs the
/// Glue transport (`transp_glue`) and lands on `a`; otherwise the two `Path T` endpoints would be
/// distinct neutrals and the boundary check would fail.
///
/// The genuine *distinct-endpoint* forward-map application (`A ≠ B`, forward map `λ_.true`) is the
/// kernel white-box golden `kan.rs::transp_ua_glue_line_applies_forward_map`; doing it at the
/// surface would require a closed `Equiv` between distinct types, which for a non-identity map does
/// not exist axiom-free, so the closed identity instance is the strongest *axiom-free* surface
/// witness. Together the two goldens pin both directions of the computation rule.
const UA_COMPUTES_SRC: &str = r#"
(define ua-computes
  (the
    (Path (Pi ((A (Type 0)) (x A)) A)
      (transp
        (plam (i)
          (Glue (Pi ((A (Type 0)) (x A)) A) (ieq0 i) (Pi ((A (Type 0)) (x A)) A)
            (pair
              (lam (f) f)
              (lam (y)
                (pair
                  (pair y (plam (j) y))
                  (lam (fib)
                    (plam (k)
                      (pair
                        ((snd fib) @ (~ k))
                        (plam (j) ((snd fib) @ (imax (~ k) j)))))))))))
        cbot
        (lam (A x) x))
      (lam (A x) x))
    (plam (i) (lam (A x) x))))
"#;

#[test]
fn ua_computes_is_conformant() {
    let proof = check_program(UA_COMPUTES_SRC).expect(
        "ua computation rule: transp over the inlined `ua (id-equiv T)` line must reduce the \
         identity point back to itself (the forward map), so `refl` checks the `Path T` boundary",
    );
    let _ = proof.concl();
}

fn check_program(src: &str) -> Result<blight_kernel::Proof, String> {
    use blight_elab::{parse_decl, read_all};

    let env = ElabEnv::new();
    let forms = read_all(src).map_err(|e| format!("read: {e:?}"))?;
    let form = forms.first().ok_or_else(|| "empty program".to_string())?;
    let decl = parse_decl(form).map_err(|e| format!("parse_decl: {e:?}"))?;
    let body = match &decl {
        Decl::Define { body, .. } => body,
        _ => return Err("conformance program must be a `define`".into()),
    };
    // The body is `(the T e)`, so elaboration yields an ascription `Ann(e, T)`.
    let core = elaborate(&env, body).map_err(|e| format!("elab: {e:?}"))?;
    match core {
        Term::Ann(e, t) => {
            check_top_with(env.signature().clone(), blight_kernel::unshare(e), blight_kernel::unshare(t)).map_err(|e| format!("kernel: {e:?}"))
        }
        other => Err(format!("expected an ascribed `(the T e)`, got {other:?}")),
    }
}
