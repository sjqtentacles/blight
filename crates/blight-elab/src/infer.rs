//! Standalone-expression type inference (spec §6.1's inference direction, applied outside a
//! top-level form). UNTRUSTED tooling glue: elaborates one bare expression against an existing
//! [`ElabEnv`] and asks the kernel to infer its type, exactly as if it were entered at a REPL
//! `:type` prompt. Shared by the REPL's `:type` command, `blight-lsp`'s hover, and the T2 doc
//! generator (`crate::docs`) — previously three independent copies of the same dozen lines; this
//! is the single source of truth they all now call.

use crate::elab::ElabEnv;
use crate::sexpr::read_one;

/// Infer the type of a surface expression and pretty-print it. Elaborates `expr_src` to a core
/// term against `env`, asks the kernel to infer its type, and re-sugars the result back to
/// surface syntax. Works for globals and nullary constructors; a bare local (`lam`-bound)
/// variable has no meaning outside its binder, so this only ever sees names `env` already knows.
pub fn infer_type_str(env: &ElabEnv, expr_src: &str) -> Result<String, String> {
    let (sexpr, _rest) = read_one(expr_src).map_err(|e| format!("{e:?}"))?;
    let surface = crate::elab::parse_surface(&sexpr).map_err(|e| format!("{e}"))?;
    let term = crate::elab::elaborate(env, &surface).map_err(|e| format!("{e}"))?;
    let checker = blight_kernel::Checker::new(std::rc::Rc::new(env.signature().clone()));
    let ctx = blight_kernel::Context::empty();
    let ty_val = checker
        .infer(&ctx, &term)
        .map_err(|e| format!("cannot infer a type: {e}"))?;
    let ty_term = blight_kernel::normalize::quote(0, &ty_val);
    Ok(crate::pretty::pretty_term(&ty_term))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Program;

    #[test]
    fn infers_the_type_of_a_global() {
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::new(&mut env);
            prog.run("(defdata Nat () (Zero) (Succ (n Nat)))\n(define one (the Nat (Succ Zero)))")
                .expect("setup");
        }
        assert_eq!(infer_type_str(&env, "one").unwrap(), "Nat");
    }

    #[test]
    fn reports_an_error_for_an_unbound_name() {
        let env = ElabEnv::new();
        assert!(infer_type_str(&env, "nope").is_err());
    }
}

/// Evaluate `expr_src` in `env` and render the resulting *value* re-sugared (decimals post-E1) —
/// the REPL's bare-expression path (E9). Elaborates, infers (so the expression must be
/// inferable, which applications of typed globals are), evaluates under the metering budget
/// (a divergent expression reports an error instead of hanging the REPL), and pretty-prints the
/// quoted normal form.
pub fn eval_value_str(env: &ElabEnv, expr_src: &str) -> Result<String, String> {
    let _ = (env, expr_src);
    Err("E9: pending".into())
}
