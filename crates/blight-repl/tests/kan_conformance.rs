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

fn check_program(src: &str) -> Result<blight_kernel::Proof, String> {
    use blight_elab::{parse_decl, read_all};

    let env = ElabEnv::new();
    let forms = read_all(src).map_err(|e| format!("read: {e:?}"))?;
    let form = forms.first().ok_or_else(|| "empty program".to_string())?;
    let decl = parse_decl(form).map_err(|e| format!("parse_decl: {e:?}"))?;
    let body = match &decl {
        Decl::Define { body, .. } => body,
        _ => return Err("funext must be a `define`".into()),
    };
    // The body is `(the T e)`, so elaboration yields an ascription `Ann(e, T)`.
    let core = elaborate(&env, body).map_err(|e| format!("elab: {e:?}"))?;
    match core {
        Term::Ann(e, t) => {
            check_top_with(env.signature().clone(), *e, *t).map_err(|e| format!("kernel: {e:?}"))
        }
        other => Err(format!("expected an ascribed `(the T e)`, got {other:?}")),
    }
}
