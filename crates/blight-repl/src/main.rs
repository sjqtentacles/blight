//! # blight — the REPL (untrusted)
//!
//! Read a form, elaborate it to a core term, hand it to the spore to check, and report
//! accept/reject (spec §8 stage 1). The REPL is the M0 user-facing surface.

use std::io::{self, Write};

use blight_elab::{elaborate, parse_decl, parse_surface, read_one, ElabEnv, Sexpr};
use blight_kernel::{check_top_with, Term};

fn main() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut env = ElabEnv::new();

    eprintln!("blight repl (M0). enter a `(defdata ...)`, `(define ...)`, or `(the T e)` form; Ctrl-D to exit.");
    loop {
        write!(stdout, "blight> ")?;
        stdout.flush()?;

        let mut line = String::new();
        if stdin.read_line(&mut line)? == 0 {
            break; // EOF
        }
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        match eval_line(&mut env, line) {
            Ok(msg) => println!("{msg}"),
            Err(msg) => println!("error: {msg}"),
        }
    }
    Ok(())
}

/// Read -> elaborate -> check one form, returning a human-facing message. Kept separate from
/// `main` so it is testable.
fn eval_line(env: &mut ElabEnv, line: &str) -> Result<String, String> {
    let (sexpr, _rest) = read_one(line).map_err(|e| format!("{e:?}"))?;

    // A top-level declaration keyword?
    if let Sexpr::List(items) = &sexpr {
        if let Some(Sexpr::Atom(kw)) = items.first() {
            match kw.as_str() {
                "defdata" | "define" => {
                    let decl = parse_decl(&sexpr).map_err(|e| format!("{e:?}"))?;
                    env.declare(&decl, None).map_err(|e| format!("{e:?}"))?;
                    return Ok("ok".into());
                }
                "define-rec" => {
                    return Err(
                        "define-rec at the REPL needs a declared type; use a driver for now".into(),
                    );
                }
                _ => {}
            }
        }
    }

    // Otherwise treat it as a term; if it is `(the T e)`, check `e` against `T`.
    let surface = parse_surface(&sexpr).map_err(|e| format!("{e:?}"))?;
    let core = elaborate(env, &surface).map_err(|e| format!("{e:?}"))?;
    match core {
        Term::Ann(e, t) => {
            let proof = check_top_with(env.signature().clone(), *e, *t)
                .map_err(|err| format!("{err:?}"))?;
            Ok(format!("{:?}", proof.concl()))
        }
        _ => Err("expected an ascribed term `(the T e)` to check".into()),
    }
}
