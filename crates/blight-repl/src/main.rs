//! # blight — the REPL (untrusted)
//!
//! Read a form, elaborate it to a core term, hand it to the spore to check, and report
//! accept/reject (spec §8 stage 1). M3 upgrades the REPL to the Stage-2 driver
//! ([`blight_elab::Program`]): it reads multi-line forms, threads one environment, supports
//! `(load "path")`, and accepts the typed recursive form `(define-rec name T body)`.

use std::io::{self, Write};
use std::path::Path;

use blight_elab::{read_all, read_one, ElabEnv, ElabError, Outcome, Program};

mod prelude_embed;

/// Resolve a `(load "path")` form for CLI/REPL use. We try the real filesystem first — relative to
/// `base` (the directory of the file being built, or the cwd for the REPL) and then the cwd — so a
/// user's own files and local overrides always win. Only when no on-disk file matches do we fall
/// back to the prelude tree embedded in this binary, which is what makes the shipped examples
/// (`(load "std/nat.bl")`) work from any directory without a source checkout.
fn cli_load(base: &Path, path: &str) -> Result<String, ElabError> {
    let candidates = [base.join(path), Path::new(path).to_path_buf()];
    for cand in &candidates {
        if let Ok(src) = std::fs::read_to_string(cand) {
            return Ok(src);
        }
    }
    if let Some(src) = prelude_embed::embedded(path) {
        return Ok(src.to_string());
    }
    Err(ElabError::BadForm(format!(
        "cannot load {path:?}: not found on disk (looked in {} and the current directory) \
         and not a bundled prelude module",
        base.display()
    )))
}

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() >= 2 && args[1] == "build" {
        match run_build(&args[2..]) {
            Ok(out) => {
                eprintln!("blight: wrote {out}");
                return Ok(());
            }
            Err(msg) => {
                eprintln!("blight build: error: {msg}");
                std::process::exit(1);
            }
        }
    }
    repl()
}

/// `blight build <file.bl> [-o <bin>]` — elaborate `file.bl`, type-check every form, then compile
/// its `main` global to a native executable (spec §7). Returns the output path on success.
///
/// Compilation requires the `llvm` feature (a system LLVM 18 + clang). Without it the subcommand
/// reports that the binary was built without native-backend support.
#[cfg(feature = "llvm")]
fn run_build(args: &[String]) -> Result<String, String> {
    let opts = parse_build_args(args)?;
    let src =
        std::fs::read_to_string(&opts.input).map_err(|e| format!("reading {}: {e}", opts.input))?;

    let mut env = ElabEnv::new();
    let base = Path::new(&opts.input)
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| Path::new(".").to_path_buf());
    let outcomes = {
        let mut prog = Program::with_resolver(&mut env, |path: &str| cli_load(&base, path));
        prog.run_with_diagnostics(&src)
            .map_err(|d| d.render(&src))?
    };

    // `--recheck`: before emitting any code, re-verify every kernel-accepted judgement with the
    // *independent* re-checker (`blight-recheck`). This is the spec §9 "host as seed + re-checker"
    // posture — the trusted kernel checked it, and a second, separately-implemented checker must
    // agree (or honestly decline an out-of-fragment construct) before we compile. A `Rejected`
    // here is a soundness alarm and aborts the build.
    if opts.recheck {
        recheck_before_emit(&env, &outcomes)?;
    }

    let term = env
        .global_term("main")
        .ok_or("no `main` global to compile")?
        .clone();
    let ty = env
        .global_type("main")
        .cloned()
        .unwrap_or_else(|| term.clone());
    let sig = env.signature().clone();

    let out_path = std::path::PathBuf::from(&opts.output);
    // For wasm32: try to link a runnable `.wasm` module (needs a wasm-capable clang + wasm-ld).
    // When that toolchain is absent we fall back to emitting the WebAssembly *object* only, with a
    // note — the codegen path retargets either way.
    if matches!(opts.target, blight_codegen::Target::Wasm32) {
        let work = wasm_work_dir(&out_path);
        match blight_codegen::driver::link_wasm(&term, &ty, &sig, &out_path, &work) {
            Ok(()) => return Ok(opts.output),
            Err(link_err) => {
                eprintln!(
                    "blight: wasm link unavailable ({link_err}); emitting WebAssembly object only"
                );
                blight_codegen::driver::emit_program_object_for_target(
                    &term,
                    &ty,
                    &sig,
                    &out_path,
                    opts.target,
                )?;
                return Ok(opts.output);
            }
        }
    }
    // Per-build scratch dir: derive it from the output path (not just the pid) so concurrent builds
    // in the same process (e.g. parallel tests) never share a `program.o` and clobber each other.
    let work = wasm_work_dir(&out_path);
    blight_codegen::driver::build_binary_opt(&term, &ty, &sig, &out_path, &work, opts.opt)?;
    Ok(opts.output)
}

/// Per-build scratch directory keyed by the output path + pid, so concurrent builds in the same
/// process never share intermediates.
#[cfg(feature = "llvm")]
fn wasm_work_dir(out_path: &std::path::Path) -> std::path::PathBuf {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    out_path.hash(&mut h);
    let work_key = h.finish();
    std::env::temp_dir().join(format!(
        "blight_build_{}_{:x}",
        std::process::id(),
        work_key
    ))
}

/// Re-verify every typed global and every emitted proof with the independent re-checker. Agreement
/// (`Ok`) or an honest `Declined` (out-of-fragment) passes; a `Rejected` aborts the build.
#[cfg(feature = "llvm")]
fn recheck_before_emit(env: &ElabEnv, outcomes: &[Outcome]) -> Result<(), String> {
    use blight_kernel::Judgement;
    let sig = env.signature();
    let mut checked = 0usize;
    let mut declined = 0usize;
    for (name, term, ty) in env.typed_globals() {
        let j = Judgement::HasType { term, ty };
        match blight_recheck::recheck_judgement(sig, &j) {
            Ok(()) => checked += 1,
            Err(blight_recheck::RecheckError::Declined(_)) => declined += 1,
            Err(blight_recheck::RecheckError::Rejected(m)) => {
                return Err(format!(
                    "--recheck: independent re-checker REJECTED `{name}` (soundness alarm): {m}"
                ));
            }
        }
    }
    for o in outcomes {
        if let Outcome::Checked(p) = o {
            match blight_recheck::recheck_proof(sig, p) {
                Ok(()) => checked += 1,
                Err(blight_recheck::RecheckError::Declined(_)) => declined += 1,
                Err(blight_recheck::RecheckError::Rejected(m)) => {
                    return Err(format!(
                        "--recheck: independent re-checker REJECTED a checked form (soundness alarm): {m}"
                    ));
                }
            }
        }
    }
    eprintln!("blight: --recheck re-verified {checked} judgement(s) independently before emit");
    if declined > 0 {
        eprintln!(
            "blight: --recheck honestly DECLINED {declined} judgement(s) outside its fragment \
             (e.g. effects, cubical, or trusted `foreign` postulates — not re-verifiable)"
        );
    }
    Ok(())
}

#[cfg(not(feature = "llvm"))]
fn run_build(_args: &[String]) -> Result<String, String> {
    Err(
        "this `blight` was built without the native backend; rebuild with `--features llvm` \
         (requires LLVM 18 + clang) to use `blight build`"
            .to_string(),
    )
}

/// Parsed `blight build` options.
#[cfg(feature = "llvm")]
struct BuildOpts {
    input: String,
    output: String,
    recheck: bool,
    target: blight_codegen::Target,
    opt: blight_codegen::OptLevel,
}

/// Parse `<file.bl> [-o <bin>] [--recheck] [--target=wasm32] [--opt=<level>]`, defaulting the output
/// to the input stem (or `a.out`). With `--target=wasm32`, only a WebAssembly object is emitted (no
/// link), so the output defaults to `<stem>.wasm`. `--opt` selects the IR optimization pipeline
/// (`0`/`none`, `2`/`default` (the default), `3`/`aggressive`).
#[cfg(feature = "llvm")]
fn parse_build_args(args: &[String]) -> Result<BuildOpts, String> {
    let mut input: Option<String> = None;
    let mut output: Option<String> = None;
    let mut recheck = false;
    let mut target = blight_codegen::Target::Native;
    let mut opt = blight_codegen::OptLevel::default();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-o" => {
                i += 1;
                output = Some(args.get(i).ok_or("`-o` requires an argument")?.clone());
            }
            "--recheck" => {
                recheck = true;
            }
            "--target=wasm32" => {
                target = blight_codegen::Target::Wasm32;
            }
            "--target=native" => {
                target = blight_codegen::Target::Native;
            }
            other if other.starts_with("--target=") => {
                return Err(format!(
                    "unknown target `{}` (expected `native` or `wasm32`)",
                    &other["--target=".len()..]
                ));
            }
            "--opt" => {
                i += 1;
                let level = args.get(i).ok_or("`--opt` requires an argument")?;
                opt = blight_codegen::OptLevel::parse(level)?;
            }
            other if other.starts_with("--opt=") => {
                opt = blight_codegen::OptLevel::parse(&other["--opt=".len()..])?;
            }
            other => {
                if input.is_some() {
                    return Err(format!("unexpected argument `{other}`"));
                }
                input = Some(other.to_string());
            }
        }
        i += 1;
    }
    let input = input.ok_or(
        "usage: blight build <file.bl> [-o <bin>] [--recheck] [--target=wasm32] [--opt=<level>]",
    )?;
    let output = output.unwrap_or_else(|| {
        let stem = std::path::Path::new(&input)
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "a.out".to_string());
        match target {
            blight_codegen::Target::Wasm32 => format!("{stem}.wasm"),
            blight_codegen::Target::Native => stem,
        }
    });
    Ok(BuildOpts {
        input,
        output,
        recheck,
        target,
        opt,
    })
}

fn repl() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let mut env = ElabEnv::new();

    eprintln!(
        "blight repl (M3). enter `(defdata …)`, `(define …)`, `(define-rec name T body)`, \
         `(load \"path\")`, or `(the T e)`; multi-line forms are read until balanced; Ctrl-D to exit. \
         `:help` lists commands."
    );
    let mut buffer = String::new();
    loop {
        let prompt = if buffer.is_empty() {
            "blight> "
        } else {
            "   ...> "
        };
        write!(stdout, "{prompt}")?;
        stdout.flush()?;

        let mut line = String::new();
        if stdin.read_line(&mut line)? == 0 {
            break; // EOF
        }
        // REPL commands (only when not mid-form): `:help`, `:type <expr>`, `:load <file>`, `:quit`.
        if buffer.is_empty() && line.trim_start().starts_with(':') {
            if repl_command(&mut env, line.trim()) {
                break; // `:quit`
            }
            continue;
        }
        buffer.push_str(&line);
        // Wait for a complete (balanced) set of forms before evaluating.
        if !is_balanced(&buffer) {
            continue;
        }
        let input = std::mem::take(&mut buffer);
        if input.trim().is_empty() {
            continue;
        }
        match eval_program(&mut env, &input) {
            Ok(msgs) => {
                for m in msgs {
                    println!("{m}");
                }
            }
            Err(rendered) => println!("{rendered}"),
        }
    }
    Ok(())
}

/// Handle a REPL `:` command. Returns `true` if the REPL should exit (`:quit`).
fn repl_command(env: &mut ElabEnv, line: &str) -> bool {
    let (cmd, rest) = match line.split_once(char::is_whitespace) {
        Some((c, r)) => (c, r.trim()),
        None => (line, ""),
    };
    match cmd {
        ":quit" | ":q" => return true,
        ":help" | ":h" | ":?" => {
            println!(
                "commands:\n  \
                 :help                show this help\n  \
                 :type <expr>  (:t)   infer and print the type of an expression\n  \
                 :load <file>  (:l)   load and check a file of forms (filesystem path)\n  \
                 :quit         (:q)   exit the repl\n\
                 anything else is read as one or more top-level forms (multi-line until balanced)."
            );
        }
        ":type" | ":t" => {
            if rest.is_empty() {
                println!("usage: :type <expr>");
            } else {
                match infer_type_str(env, rest) {
                    Ok(ty) => println!("{ty}"),
                    Err(rendered) => println!("{rendered}"),
                }
            }
        }
        ":load" | ":l" => {
            if rest.is_empty() {
                println!("usage: :load <file>");
            } else {
                match std::fs::read_to_string(rest) {
                    Ok(src) => match eval_program(env, &src) {
                        Ok(msgs) => println!("loaded {rest}: {} form(s) ok", msgs.len()),
                        Err(rendered) => println!("{rendered}"),
                    },
                    Err(e) => println!("cannot read {rest}: {e}"),
                }
            }
        }
        other => println!("unknown command `{other}` (try `:help`)"),
    }
    false
}

/// Infer the type of a surface expression and pretty-print it. Elaborates the expression to a core
/// term against the REPL env, then asks the kernel to infer its type and re-sugars the result.
fn infer_type_str(env: &ElabEnv, expr_src: &str) -> Result<String, String> {
    let (sexpr, _rest) = read_one(expr_src).map_err(|e| format!("{e:?}"))?;
    let surface = blight_elab::parse_surface(&sexpr).map_err(|e| format!("{e}"))?;
    let term = blight_elab::elaborate(env, &surface).map_err(|e| format!("{e}"))?;
    let checker = blight_kernel::Checker::new(std::rc::Rc::new(env.signature().clone()));
    let ctx = blight_kernel::Context::empty();
    let ty_val = checker
        .infer(&ctx, &term)
        .map_err(|e| format!("cannot infer a type: {e}"))?;
    let ty_term = blight_kernel::normalize::quote(0, &ty_val);
    Ok(blight_elab::pretty_term(&ty_term))
}

/// Run one or more forms through the [`Program`] driver, returning a human-facing line per form.
/// Kept separate from `main` so it is testable. On error, returns the rendered diagnostic (with a
/// caret pointing at the offending form) ready to print.
fn eval_program(env: &mut ElabEnv, src: &str) -> Result<Vec<String>, String> {
    let base = std::env::current_dir().unwrap_or_else(|_| Path::new(".").to_path_buf());
    let mut prog = Program::with_resolver(env, |path: &str| cli_load(&base, path));
    let outcomes = prog.run_with_diagnostics(src).map_err(|d| d.render(src))?;
    Ok(outcomes
        .into_iter()
        .map(|o| match o {
            Outcome::Declared => "ok".to_string(),
            Outcome::Checked(proof) => blight_elab::pretty_concl(&proof),
        })
        .collect())
}

/// Whether `src` parses into a whole number of top-level forms (i.e. parens balance). Used to let
/// the REPL accept multi-line input.
fn is_balanced(src: &str) -> bool {
    read_all(src).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A typed recursive definition entered across (logical) lines elaborates at the REPL.
    #[test]
    fn repl_multiline_define_rec() {
        let mut env = ElabEnv::new();
        eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat");
        let src = "(define-rec double\n\
                     (Pi ((n Nat)) Nat)\n\
                     (lam (n) (match n [(Zero) Zero] [(Succ k) (Succ (Succ (double k)))])))";
        let msgs = eval_program(&mut env, src).expect("define-rec elaborates");
        assert_eq!(msgs, vec!["ok".to_string()]);
        assert!(env.global_term("double").is_some());
    }

    /// An incomplete form is detected as unbalanced; once closed it parses.
    #[test]
    fn balance_detection() {
        assert!(!is_balanced("(define-rec double"));
        assert!(is_balanced("(the Nat Zero)"));
    }

    /// An elaboration error (unbound name) renders as a caret diagnostic pointing at the offending
    /// top-level form, not a raw `Debug` dump.
    #[test]
    fn elab_error_renders_a_caret() {
        let mut env = ElabEnv::new();
        let err = eval_program(&mut env, "(the Nat nope)").expect_err("nope is unbound");
        assert!(err.starts_with("error: "), "rendered, got: {err}");
        assert!(
            err.contains("unbound") || err.contains("nope"),
            "names the issue: {err}"
        );
        assert!(err.contains('^'), "has a caret underline: {err}");
        assert!(
            err.contains("(the Nat nope)"),
            "quotes the source line: {err}"
        );
    }

    /// A reader error (unterminated list) renders with a caret too.
    #[test]
    fn reader_error_renders_a_caret() {
        let mut env = ElabEnv::new();
        let err = eval_program(&mut env, "(the Nat").expect_err("unterminated");
        assert!(err.starts_with("error: "), "rendered, got: {err}");
        assert!(err.contains('^'), "has a caret underline: {err}");
    }

    /// A checked conclusion pretty-prints via the surface re-sugaring rather than `Debug`.
    #[test]
    fn checked_conclusion_pretty_prints() {
        let mut env = ElabEnv::new();
        eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat");
        let msgs = eval_program(&mut env, "(the Nat (Succ Zero))").expect("checks");
        assert_eq!(msgs.len(), 1);
        assert!(
            msgs[0].contains('⊢'),
            "turnstile in conclusion: {}",
            msgs[0]
        );
        assert!(msgs[0].contains("(Succ Zero)"), "pretty term: {}", msgs[0]);
        assert!(!msgs[0].contains("Con("), "no Debug leakage: {}", msgs[0]);
    }

    /// `:type` infers and pretty-prints the type of an expression against the REPL env.
    #[test]
    fn repl_type_command_infers() {
        let mut env = ElabEnv::new();
        eval_program(&mut env, "(defdata Nat () (Zero) (Succ (n Nat)))").expect("nat");
        let ty = infer_type_str(&env, "(Succ Zero)").expect("infers");
        assert_eq!(ty, "Nat", "Succ Zero : Nat, got {ty}");
        // An ill-typed / un-inferable expression reports an error string, not a panic.
        let err = infer_type_str(&env, "(Succ Succ)").expect_err("ill-typed");
        assert!(!err.is_empty(), "non-empty error: {err}");
    }

    /// `:quit` returns the exit signal; an unknown command does not.
    #[test]
    fn repl_command_quit_and_unknown() {
        let mut env = ElabEnv::new();
        assert!(repl_command(&mut env, ":quit"), ":quit exits");
        assert!(repl_command(&mut env, ":q"), ":q exits");
        assert!(!repl_command(&mut env, ":help"), ":help does not exit");
        assert!(!repl_command(&mut env, ":bogus"), "unknown does not exit");
    }

    /// `blight build file.bl -o bin` elaborates the file and produces a runnable native binary
    /// whose `main` evaluates to `Succ Zero` (printed as the numeral `1`).
    #[cfg(feature = "llvm")]
    #[test]
    fn build_command_produces_binary() {
        let dir = std::env::temp_dir().join(format!("blight_buildcli_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define main Nat (Succ Zero))\n";
        let file = dir.join("prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("prog");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ])
        .expect("build succeeds");
        assert_eq!(out, bin.to_string_lossy());
        assert!(bin.exists(), "binary was produced");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "binary runs");
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert_eq!(stdout.trim(), "1", "main = Succ Zero prints as 1");
    }

    /// `blight build --opt 3 …` runs the aggressive IR pipeline and still produces a correct binary
    /// (musttail survives the pipeline; result unchanged). Also exercises the `--opt=<level>` spelling
    /// and the rejection of an unknown level.
    #[cfg(feature = "llvm")]
    #[test]
    fn build_command_opt_flag() {
        let dir = std::env::temp_dir().join(format!("blight_buildopt_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define main Nat (Succ (Succ Zero)))\n";
        let file = dir.join("prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("prog_o3");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
            "--opt".to_string(),
            "3".to_string(),
        ])
        .expect("build with --opt 3 succeeds");
        assert_eq!(out, bin.to_string_lossy());
        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "binary runs");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            "2",
            "main = Succ (Succ Zero) prints as 2 at --opt 3"
        );

        // The `--opt=<level>` spelling parses too.
        assert!(parse_build_args(&["x.bl".into(), "--opt=2".into()])
            .is_ok_and(|o| o.opt == blight_codegen::OptLevel::Default));
        // An unknown level is rejected.
        assert!(parse_build_args(&["x.bl".into(), "--opt".into(), "O2".into()]).is_err());
    }

    /// A `main` that uses `(region r …)` builds and runs — regression for the missing `arena.c`
    /// link (M6 Phase C). The region scope makes the backend emit arena allocations, whose runtime
    /// (`bl_arena_*`) lives in `arena.c`; before the driver fix the link failed with undefined
    /// `bl_arena_*` symbols. `Rgn`/`region` come from the prelude (inlined here so the build needs
    /// no `(load …)` resolver).
    #[cfg(feature = "llvm")]
    #[test]
    fn build_command_compiles_region_main() {
        let dir = std::env::temp_dir().join(format!("blight_regionbuild_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (defdata Rgn () (rgn-tok))\n\
                   (define main Nat (region r (Succ Zero)))\n";
        let file = dir.join("region_prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("region_prog");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ])
        .expect("region-using main builds (arena.c is linked)");
        assert_eq!(out, bin.to_string_lossy());
        assert!(bin.exists(), "region binary was produced");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "region binary runs");
        let stdout = String::from_utf8_lossy(&run.stdout);
        assert_eq!(
            stdout.trim(),
            "1",
            "main = (region r (Succ Zero)) prints as 1"
        );
    }

    /// `blight build --recheck` re-verifies every kernel-accepted judgement with the *independent*
    /// `blight-recheck` checker before emitting code, then still produces a runnable binary (M6
    /// Phase C: the host as seed + re-checker). A `Rejected` would abort the build; here all
    /// judgements agree, so the binary is produced and runs.
    #[cfg(feature = "llvm")]
    #[test]
    fn build_rechecks_before_emit() {
        let dir = std::env::temp_dir().join(format!("blight_recheckbuild_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        // A typed global (`two`) plus `main`, so `--recheck` independently re-checks more than just
        // a trivial literal.
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define two Nat (Succ (Succ Zero)))\n\
                   (define main Nat (Succ Zero))\n";
        let file = dir.join("prog.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("prog");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
            "--recheck".to_string(),
        ])
        .expect("build with --recheck succeeds (independent checker agrees)");
        assert_eq!(out, bin.to_string_lossy());
        assert!(bin.exists(), "binary produced after independent re-check");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "re-checked binary runs");
        assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "1");
    }

    /// A self-hosting round-trip oracle (M6 Phase C): compile a *non-trivial* `.bl` program — Nat
    /// arithmetic via a recursive `plus` — to native with `--recheck`, run it, and assert the
    /// printed result. This demonstrates the bootstrap host acting purely as seed + re-checker for
    /// a real program: the kernel checks it, the independent re-checker re-verifies it, then it
    /// compiles and runs with the expected numeric output.
    #[cfg(feature = "llvm")]
    #[test]
    fn self_host_seed_roundtrip() {
        let dir = std::env::temp_dir().join(format!("blight_selfhost_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        // plus 2 1 = 3.
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n\
                     (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))\n\
                   (define main Nat (plus (Succ (Succ Zero)) (Succ Zero)))\n";
        let file = dir.join("arith.bl");
        std::fs::write(&file, src).unwrap();
        let bin = dir.join("arith");

        run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
            "--recheck".to_string(),
        ])
        .expect("the host (seed + re-checker) compiles and re-verifies the arithmetic program");

        let run = std::process::Command::new(&bin)
            .output()
            .expect("run binary");
        assert!(run.status.success(), "round-trip binary runs");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            "3",
            "plus 2 1 evaluates to 3 natively"
        );
    }

    /// `blight build --target=wasm32` emits a WebAssembly object (no link). The codegen path
    /// retargets to `wasm32-unknown-unknown`; we assert the output begins with the WebAssembly
    /// object magic bytes `\0asm` (M6 D3).
    #[cfg(feature = "llvm")]
    #[test]
    fn emits_wasm_object_for_main() {
        let dir = std::env::temp_dir().join(format!("blight_wasm_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
                   (define main Nat (Succ (Succ Zero)))\n";
        let file = dir.join("wasm_prog.bl");
        std::fs::write(&file, src).unwrap();
        let obj = dir.join("wasm_prog.wasm");

        let out = run_build(&[
            file.to_string_lossy().to_string(),
            "-o".to_string(),
            obj.to_string_lossy().to_string(),
            "--target=wasm32".to_string(),
        ])
        .expect("wasm32 object emission succeeds");
        assert_eq!(out, obj.to_string_lossy());
        assert!(obj.exists(), "wasm object was produced");

        let bytes = std::fs::read(&obj).expect("read wasm object");
        assert!(
            bytes.starts_with(&[0x00, 0x61, 0x73, 0x6d]),
            "output begins with the WebAssembly magic `\\0asm` (got {:?})",
            &bytes[..bytes.len().min(8)]
        );
    }

    /// End-to-end regression for the shipped examples (the user-visible `blight build … && ./out`
    /// flow): build the *real* `examples/*.bl` files — whose `(load "std/…")` forms resolve against
    /// the prelude **embedded in this binary**, so the build works from any directory with no source
    /// checkout — re-check them independently, run them, and assert their numeric output. This guards
    /// the three bugs that previously broke the examples: the prelude not being found from the CLI,
    /// the indexed-`Vec` eliminator miscompiling (method lambdas wrongly lowered to `Fix`), and the
    /// indexed-`Elim` motive the re-checker rejected.
    #[cfg(feature = "llvm")]
    fn build_and_run_example(name: &str, expected_stdout: &str) {
        build_and_run_example_opts(name, expected_stdout, true);
    }

    /// As [`build_and_run_example`], but `recheck` selects whether the independent re-checker runs
    /// during the native build. It defaults to on (the strong guarantee). It is turned off only for
    /// examples whose *concrete* result forces a pathologically large normal form through the
    /// re-checker — e.g. `palindrome.bl`, which compares a real word against its reverse where each
    /// letter is a ~100-deep unary-`Nat` codepoint (std/string.bl). The example's *definitions*
    /// still re-check via the load corpus (`examples.rs`); only forcing the giant concrete value is
    /// skipped here, since it is a normalization-cost issue (the honest unary-`Nat` tax), not a
    /// soundness rejection.
    #[cfg(feature = "llvm")]
    fn build_and_run_example_opts(name: &str, expected_stdout: &str, recheck: bool) {
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join(name);
        let dir = std::env::temp_dir().join(format!(
            "blight_example_{}_{}",
            name.replace('.', "_"),
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");

        // Build on a thread with a generous stack. Test threads default to a small (~2 MiB) stack,
        // but the build pipeline recurses structurally over the program term — and with strings
        // modeled as unary-`Nat` codepoint chains (std/string.bl), even a short literal is a deep
        // term. The real CLI runs the build on the main thread (default ~8 MiB), so this mirrors
        // that; it does not change the compiler, only the harness's stack budget.
        let mut build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        if recheck {
            build_args.push("--recheck".to_string());
        }
        let name_owned = name.to_string();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_build(&build_args).unwrap_or_else(|e| {
                    panic!("example {name_owned} builds (seed + independent re-checker): {e}")
                });
            })
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        assert!(bin.exists(), "example {name} produced a binary");

        let run = std::process::Command::new(&bin)
            .output()
            .unwrap_or_else(|e| panic!("run example {name}: {e}"));
        assert!(run.status.success(), "example {name} runs successfully");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim(),
            expected_stdout,
            "example {name} prints {expected_stdout}"
        );
    }

    /// As [`build_and_run_example_opts`] but feeds `stdin` to the built binary and compares the raw
    /// (untrimmed) stdout. Used for the `Console`-effect examples (echo/greet), whose output is
    /// produced by `perform print` and read back here exactly as written. Effects are outside the
    /// re-checker fragment, so these build without `--recheck`.
    #[cfg(feature = "llvm")]
    fn build_and_run_example_stdin(name: &str, stdin: &str, expected_stdout: &str) {
        use std::io::Write;
        use std::process::Stdio;
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        let example = repo.join("examples").join(name);
        let dir = std::env::temp_dir().join(format!(
            "blight_example_{}_{}",
            name.replace('.', "_"),
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("out");
        let build_args = vec![
            example.to_string_lossy().to_string(),
            "-o".to_string(),
            bin.to_string_lossy().to_string(),
        ];
        let name_owned = name.to_string();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                run_build(&build_args)
                    .unwrap_or_else(|e| panic!("example {name_owned} builds: {e}"));
            })
            .expect("spawn build thread")
            .join()
            .expect("build thread completes");
        assert!(bin.exists(), "example {name} produced a binary");

        let mut child = std::process::Command::new(&bin)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap_or_else(|e| panic!("spawn example {name}: {e}"));
        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(stdin.as_bytes())
            .unwrap();
        let run = child
            .wait_with_output()
            .unwrap_or_else(|e| panic!("run example {name}: {e}"));
        assert!(run.status.success(), "example {name} runs successfully");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            expected_stdout,
            "example {name} echoes its scripted stdin"
        );
    }

    /// `hello_nat.bl`: `(2 * 3) + 1 = 7`, computed with `std/nat`'s `plus`/`mult`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_hello_nat_builds_and_runs() {
        build_and_run_example("hello_nat.bl", "7");
    }

    /// `foreign_answer.bl`: the FFI escape hatch (spec §7.6). `(foreign answer Nat
    /// "bl_foreign_answer")` postulates an opaque `Nat` whose C symbol (`runtime/prelude_rt.c`)
    /// builds and returns the unary `Nat` 42; `main` returns it, so the program prints `42` —
    /// produced entirely by trusted C and threaded back into checked code, linked automatically
    /// because the symbol lives in the always-linked prelude runtime. Built *without* `--recheck`:
    /// a `foreign` is outside the independent re-checker's certifiable fragment (it declines).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_foreign_answer_builds_and_runs() {
        build_and_run_example_opts("foreign_answer.bl", "42", false);
    }

    /// `int_arith.bl`: native machine `Int` (M11). `(int* (int 100000) (int 100000))` lowers to a
    /// single hardware multiply on a `BL_INT` payload, so the product `10000000000` prints instantly
    /// — the headline contrast with the O(unary) `Nat` tower. Built *with* `--recheck`: `Int` is a
    /// primitive the independent re-checker certifies (unlike the `foreign` hatch).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_int_arith_builds_and_runs() {
        build_and_run_example("int_arith.bl", "10000000000");
    }

    /// `int_sum.bl`: the machine-`Int` counterpart of `bench_sum.bl`. Folds `int-add` (std/int.bl)
    /// over a `List Int` of 800 ones, printing `800` with O(1) adds — the integer side of the
    /// unary-`Nat`-vs-`Int` benchmark in docs/benchmarks-game.md. Built with `--recheck` (Int/List
    /// are in-fragment).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_int_sum_builds_and_runs() {
        build_and_run_example("int_sum.bl", "800");
    }

    /// `bench_sum.bl`: the unary-`Nat` counterpart of `int_sum.bl` — `foldr plus` over 800 ones,
    /// so `main` evaluates to `Succ^800 Zero` and prints `800`. Same answer as `int_sum.bl`, but
    /// every `+` walks a `Succ` chain (the unary cost the benchmark narrative measures).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_bench_sum_builds_and_runs() {
        build_and_run_example("bench_sum.bl", "800");
    }

    /// `hello_string.bl`: a `String`-typed `main` prints as *text* (`hello`), end-to-end proof that
    /// the reader sugar + runtime `bl_print_string` path works. No kernel change.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_hello_string_builds_and_runs() {
        build_and_run_example("hello_string.bl", "hello");
    }

    /// `string_length.bl`: `string-length "hello" = 5`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_string_length_builds_and_runs() {
        build_and_run_example("string_length.bl", "5");
    }

    /// `string_reverse.bl`: `string-reverse "abc"` prints `cba`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_string_reverse_builds_and_runs() {
        build_and_run_example("string_reverse.bl", "cba");
    }

    /// `palindrome.bl`: `"level"` is a palindrome → `1`. Built without the re-checker (see
    /// `build_and_run_example_opts`): the concrete `string-eq word (reverse word)` normal form over
    /// real letters (~100-deep unary codepoints) is a normalization-cost blowup for the re-checker,
    /// not a soundness issue — the definitions re-check fine in the load corpus.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_palindrome_builds_and_runs() {
        build_and_run_example_opts("palindrome.bl", "1", false);
    }

    /// `caesar.bl`: shift `"abc"` by 1 → `bcd`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_caesar_builds_and_runs() {
        build_and_run_example("caesar.bl", "bcd");
    }

    /// `containers.bl`: builds a length-indexed `Vec Nat 2` and reads its length back, exercising the
    /// indexed-family eliminator end-to-end (the bug fixed here). Result: `2`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_containers_builds_and_runs() {
        build_and_run_example("containers.bl", "2");
    }

    /// `list_sum.bl`: `foldr plus 0 [1,2,3] = 6`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_list_sum_builds_and_runs() {
        build_and_run_example("list_sum.bl", "6");
    }

    /// `fib.bl`: structural Fibonacci, `fib 7 = 13` (0,1,1,2,3,5,8,13).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_fib_builds_and_runs() {
        build_and_run_example("fib.bl", "13");
    }

    /// `minmax.bl`: `plus (min 2 5) (max 2 5) = 2 + 5 = 7`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_minmax_builds_and_runs() {
        build_and_run_example("minmax.bl", "7");
    }

    /// `vec_head.bl`: a `Vec Nat 3`'s recovered length is `3`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_vec_head_builds_and_runs() {
        build_and_run_example("vec_head.bl", "3");
    }

    /// `safe_tail.bl`: the tail of a length-2 vector has length `1`. Built *with* `--recheck`: the
    /// dependent indexed motive `Vec A n` re-checks through the independent re-checker (no soundness
    /// alarm) before the binary is emitted.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_safe_tail_builds_and_runs() {
        build_and_run_example("safe_tail.bl", "1");
    }

    /// `vec_map.bl`: mapping over a length-2 vector preserves the length, so the result's recovered
    /// length is `2`. Built *with* `--recheck`: the length-preserving dependent indexed motive
    /// `Vec B n` re-checks independently before emit.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_vec_map_builds_and_runs() {
        build_and_run_example("vec_map.bl", "2");
    }

    /// `zip_vec.bl`: zipping two length-2 vectors yields a length-2 vector of pairs (recovered
    /// length `2`). Built *with* `--recheck`: the re-checker honestly *declines* zip-vec's
    /// higher-order eliminator motive (never rejects it), so the `--recheck` build still succeeds.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_zip_vec_builds_and_runs() {
        build_and_run_example("zip_vec.bl", "2");
    }

    /// `either_compute.bl`: an `Either`/`Maybe` pipeline that nets `4`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_either_compute_builds_and_runs() {
        build_and_run_example("either_compute.bl", "4");
    }

    /// `region_scratch.bl`: a `(region r …)` scratch computation returning `2`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_region_scratch_builds_and_runs() {
        build_and_run_example("region_scratch.bl", "2");
    }

    /// `tree_sum.bl`: sum of the `Nat`s in a binary search tree built by `tree-insert` = `6`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_tree_sum_builds_and_runs() {
        build_and_run_example("tree_sum.bl", "6");
    }

    /// `gcd.bl`: subtractive Euclidean GCD, `gcd 12 8 = 4` (fuel-bounded structural recursion).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_gcd_builds_and_runs() {
        build_and_run_example("gcd.bl", "4");
    }

    /// `collatz_steps.bl`: Collatz step count for `6` is `8` (6→3→10→5→16→8→4→2→1).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_collatz_steps_builds_and_runs() {
        build_and_run_example("collatz_steps.bl", "8");
    }

    /// `list_sort.bl`: insertion-sort `[3,1,2]` → `[1,2,3]`, whose head (smallest element) is `1`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_list_sort_builds_and_runs() {
        build_and_run_example("list_sort.bl", "1");
    }

    /// `ascii_box.bl`: a 3×3 grid of `#` built as a `String` and printed as text. The runtime emits
    /// a trailing newline after the last row; the harness `.trim()`s it, so the comparison is the
    /// three rows joined by newlines.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_ascii_box_builds_and_runs() {
        build_and_run_example("ascii_box.bl", "###\n###\n###");
    }

    /// `ackermann.bl`: the `force` (delay-eliminator) showcase. `parity` is a *non-structural*
    /// `define-rec` (it recurses on `n - 2`, two `Succ`s deep) so its result is a `Delay Nat`;
    /// `main` drives it with `(force (parity seven))`. Seven is odd, so the program prints `1`. This
    /// also runs under `--recheck`, so the independent re-checker accepts the forced delay layer.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_ackermann_builds_and_runs() {
        build_and_run_example("ackermann.bl", "1");
    }

    /// `state_handler.bl`: a compiled algebraic-effect deep handler. The body performs `get` in tail
    /// position; `handle` lowers each clause to a closure and installs them via the runtime's
    /// `bl_handle_clo` deep-handler trampoline. The `get` clause resumes with `3`, the `return`
    /// clause yields it, so the native binary prints `3`. (Effects are outside the re-checker's
    /// fragment, so this is built *without* `--recheck`; the seed kernel still type-checks it.)
    #[cfg(feature = "llvm")]
    #[test]
    fn example_state_handler_builds_and_runs() {
        build_and_run_example_opts("state_handler.bl", "3", false);
    }

    /// `effect_nontail.bl`: a *general* (non-tail) algebraic-effect handler. The performed `get`s are
    /// ordinary sub-expressions of `(plus (perform get tt) (perform get tt))`, so the continuation
    /// must be captured across the application — a genuine delimited continuation. The native backend
    /// does this at runtime: every elimination site (`bl_app` for application, `bl_con_bubble` for
    /// construction) is OpNode-aware, so the effect bubbles out with the pending work composed onto
    /// its continuation, mirroring the kernel's `apply`/`replay`. Resuming every `get` with `2` yields
    /// `plus 2 2 = 4`. Built without `--recheck` (effects are outside the re-checker's fragment).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_effect_nontail_builds_and_runs() {
        build_and_run_example_opts("effect_nontail.bl", "4", false);
    }

    /// `echo.bl`: the smallest `Console`-effect program — `read` a line, `print` it back. Exercises
    /// the native top-level Console handler (`bl_run_console`): `bl_program_entry` yields a bubbling
    /// `Console` OpNode tree, which the generated `main` folds against real stdio. With `world\n` on
    /// stdin it echoes `world` (no trailing newline — `print` adds none).
    #[cfg(feature = "llvm")]
    #[test]
    fn example_echo_builds_and_runs() {
        build_and_run_example_stdin("echo.bl", "world\n", "world");
    }

    /// `greet.bl`: an interactive `Console` program — print a prompt, read a name, print a greeting.
    /// Exercises *sequenced* Console operations through the delimited-continuation machinery and the
    /// native top-level handler. With `Ada\n` on stdin it prints `Name: Hi, Ada!\n`.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_greet_builds_and_runs() {
        build_and_run_example_stdin("greet.bl", "Ada\n", "Name: Hi, Ada!\n");
    }

    /// `game/guess.bl`: the interactive turn-based "guess the word" game — a fuel-bounded `Console`
    /// frame loop that reads a guess each turn, compares it to the secret with `string-eq`, and
    /// branches (win + stop, or hint + recurse). This exercises *recursion over an effectful
    /// computation* (`define-rec play : Nat -> (! Console Unit)`) driven through the native
    /// top-level Console handler and the delimited-continuation machinery. With the secret `"dog"`
    /// and `cat\ndog\n` on stdin, the player misses then wins.
    #[cfg(feature = "llvm")]
    #[test]
    fn example_guess_game_builds_and_runs() {
        build_and_run_example_stdin(
            "game/guess.bl",
            "cat\ndog\n",
            "guess: nope, try again.\nguess: you win!\n",
        );
    }
}
