//! Kernel-normalizer oracle — an *independent semantic* safety net that complements the differential
//! harness.
//!
//! The differential test (`differential_fast_paths_are_bit_identical`) only proves *fast-path ==
//! slow-path* codegen. Both paths compile the **same** elaborated kernel term, so a term whose
//! *meaning* differs from intent (an elaborator bug, not a codegen bug) slips through identically on
//! every path — exactly how the nested-match `fib` once evaluated to `65` instead of `5` in the
//! kernel itself, undetected by any fast/slow comparison.
//!
//! This oracle closes that gap: it normalizes `main` with the **trusted kernel evaluator** and
//! asserts the result equals the *intended* decimal value. A mismatch is a meaning bug (the
//! elaborated term does not denote what the program says). Combined with the `*_builds_and_runs`
//! tests (which assert *compiled output == intended*), this pins down the full chain:
//!
//!   compiled output  ==  intended value  ==  kernel normal form (the term's true meaning).
//!
//! Scope: programs whose `main` is a *pure* `Nat`/`Int` of a small, representable value (so the
//! unary `Nat` normal form does not blow up). Effectful/string/large-`Nat` mains are out of scope
//! and covered by their own build-and-run tests.

#[path = "support/mod.rs"]
mod support;

use blight_elab::{ElabEnv, Program};
use blight_kernel::normalize::{eval, quote};
use blight_kernel::value::Env as KernelEnv;
use blight_kernel::{ConName, Term};
use std::rc::Rc;

/// Render a closed kernel normal form to the decimal string the runtime would print: an `Int`
/// literal verbatim, or a `Nat` (`Succ`/`Zero` chain) as its `Succ`-depth. `None` if the NF is not a
/// numeral (out of this oracle's scope).
fn render_decimal(t: &Term) -> Option<String> {
    if let Term::IntLit(i) = t {
        return Some(i.to_string());
    }
    let mut n: u128 = 0;
    let mut cur = t;
    loop {
        match cur {
            Term::Con(ConName(c), args) if c == "Zero" && args.is_empty() => {
                return Some(n.to_string())
            }
            Term::Con(ConName(c), args) if c == "Succ" && args.len() == 1 => {
                n += 1;
                cur = &args[0];
            }
            _ => return None,
        }
    }
}

/// Elaborate `src` (resolving `(load …)` against the prelude) and return `main`'s kernel normal
/// form rendered as a decimal string.
fn kernel_nf_decimal(src: &str) -> Result<String, String> {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, support::prelude_resolver);
        prog.run(src)
            .map_err(|e| format!("elaboration failed: {e:?}"))?;
    }
    let term = env
        .global_term("main")
        .ok_or("program has no `main` global")?
        .clone();
    let sig = Rc::new(env.signature().clone());
    let value = eval(&KernelEnv::with_sig(sig), &term);
    let nf = quote(0, &value);
    render_decimal(&nf).ok_or_else(|| format!("`main` normal form is not a numeral: {nf:?}"))
}

/// A random well-typed `Int` expression tree, used by the property fuzzer. Leaves are small literals
/// (rendered via `(int n)` / `int-` for negatives); nodes are the wrapping `Int` primitives the
/// kernel folds. We deliberately omit `int/` (a zero divisor leaves the term stuck rather than a
/// literal) and the comparison ops (their `Nat`-less `Int` 0/1 result is exercised elsewhere).
enum IntExpr {
    Lit(i64),
    Add(Box<IntExpr>, Box<IntExpr>),
    Sub(Box<IntExpr>, Box<IntExpr>),
    Mul(Box<IntExpr>, Box<IntExpr>),
}

impl IntExpr {
    /// The independent reference semantics: wrapping `i64`, matching `normalize::int_prim` exactly.
    fn eval(&self) -> i64 {
        match self {
            IntExpr::Lit(n) => *n,
            IntExpr::Add(a, b) => a.eval().wrapping_add(b.eval()),
            IntExpr::Sub(a, b) => a.eval().wrapping_sub(b.eval()),
            IntExpr::Mul(a, b) => a.eval().wrapping_mul(b.eval()),
        }
    }

    /// Render to Blight surface syntax. A negative literal `-n` becomes `(int- (int 0) (int n))`
    /// since the reader's `(int …)` takes a non-negative numeral.
    fn render(&self, out: &mut String) {
        match self {
            IntExpr::Lit(n) if *n < 0 => {
                out.push_str("(int- (int 0) (int ");
                out.push_str(&(-*n).to_string());
                out.push_str("))");
            }
            IntExpr::Lit(n) => {
                out.push_str("(int ");
                out.push_str(&n.to_string());
                out.push(')');
            }
            IntExpr::Add(a, b) => Self::render_bin("int+", a, b, out),
            IntExpr::Sub(a, b) => Self::render_bin("int-", a, b, out),
            IntExpr::Mul(a, b) => Self::render_bin("int*", a, b, out),
        }
    }

    fn render_bin(op: &str, a: &IntExpr, b: &IntExpr, out: &mut String) {
        out.push('(');
        out.push_str(op);
        out.push(' ');
        a.render(out);
        out.push(' ');
        b.render(out);
        out.push(')');
    }
}

/// A tiny deterministic PRNG (SplitMix64) so the fuzzer is reproducible from a fixed seed.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Generate a random `IntExpr` of at most `depth` operator levels. Literals stay in `[-9, 9]` so a
/// shallow tree's wrapping result is interesting but the source stays small.
fn gen_int_expr(rng: &mut Rng, depth: u32) -> IntExpr {
    if depth == 0 || rng.below(3) == 0 {
        return IntExpr::Lit(rng.below(19) as i64 - 9);
    }
    let l = Box::new(gen_int_expr(rng, depth - 1));
    let r = Box::new(gen_int_expr(rng, depth - 1));
    match rng.below(3) {
        0 => IntExpr::Add(l, r),
        1 => IntExpr::Sub(l, r),
        _ => IntExpr::Mul(l, r),
    }
}

/// **Property fuzzer.** For many random well-typed `Int` programs, the elaborated term's *kernel
/// normal form* must equal an *independent* wrapping-`i64` evaluation of the very same expression.
/// This is the value-miscompile net generalized: rather than trusting one example, it samples the
/// space of programs and pins *meaning == reference* on each. (Pure Rust — no LLVM build per case —
/// so thousands of cases run in well under a second.)
#[test]
fn fuzz_int_expr_kernel_nf_matches_reference() {
    let mut rng = Rng(0x000B_1167_5EED);
    let mut failures = Vec::new();
    for i in 0..2000u32 {
        let expr = gen_int_expr(&mut rng, 4);
        let expected = expr.eval();
        let mut body = String::new();
        expr.render(&mut body);
        let src = format!("(define main Int {body})");
        match kernel_nf_decimal(&src) {
            Ok(got) if got == expected.to_string() => {}
            Ok(got) => failures.push(format!(
                "case {i}: kernel NF {got} != reference {expected} for source {src}"
            )),
            Err(e) => failures.push(format!("case {i}: {e} for source {src}")),
        }
        if failures.len() >= 10 {
            break; // enough signal; do not bury the report
        }
    }
    assert!(
        failures.is_empty(),
        "int-expression fuzzer found meaning mismatches:\n{}",
        failures.join("\n")
    );
}

fn example(name: &str) -> String {
    let path = format!("{}/../../examples/{}", env!("CARGO_MANIFEST_DIR"), name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {path}: {e}"))
}

/// The oracle corpus: `(source, intended decimal)` for pure, small `Nat`/`Int` mains. Each intended
/// value is the same constant the program's `*_builds_and_runs` test asserts for compiled output, so
/// agreement here proves the elaborated term *means* what the binary *prints*.
#[test]
fn kernel_normal_form_matches_intended_value() {
    // Pure, *cheap-to-normalize* mains. Programs that build large intermediate structures (an
    // 800-element list) or drive fuel-bounded higher-order CPS recursion (`gcd`, `collatz`) are
    // omitted: the unoptimized kernel evaluator normalizes them far too slowly to belong in the
    // standard suite, and they are already covered by build-and-run + the differential harness.
    let mut cases: Vec<(&str, String, String)> = vec![
        ("hello_nat.bl", example("hello_nat.bl"), "7".into()),
        (
            "int_arith.bl",
            example("int_arith.bl"),
            "10000000000".into(),
        ),
        ("list_sum.bl", example("list_sum.bl"), "6".into()),
        ("fib.bl", example("fib.bl"), "13".into()),
        ("minmax.bl", example("minmax.bl"), "7".into()),
        ("vec_head.bl", example("vec_head.bl"), "3".into()),
        (
            "either_compute.bl",
            example("either_compute.bl"),
            "4".into(),
        ),
    ];
    // The corrected structural `fib` benchmark (the program whose nested-match miscompile motivated
    // this oracle): `fib 32 = 2178309`.
    let fibrec_path = format!(
        "{}/../../bench/games/fibrec/fibrec_int.bl",
        env!("CARGO_MANIFEST_DIR")
    );
    if let Ok(fibrec_src) = std::fs::read_to_string(&fibrec_path) {
        cases.push((
            "bench/games/fibrec/fibrec_int.bl",
            fibrec_src,
            "2178309".into(),
        ));
    }

    let mut failures = Vec::new();
    for (name, src, intended) in &cases {
        // The kernel evaluator is naturally recursive; normalize on a generous stack (the build
        // harness does the same for the codegen pipeline). A per-case timeout keeps a pathological
        // normalization from wedging the suite while still flagging it.
        let src_owned = src.clone();
        let (tx, rx) = std::sync::mpsc::channel();
        let start = std::time::Instant::now();
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || {
                let _ = tx.send(kernel_nf_decimal(&src_owned));
            })
            .expect("spawn oracle eval thread");
        let result = match rx.recv_timeout(std::time::Duration::from_secs(30)) {
            Ok(r) => r,
            Err(_) => {
                failures.push(format!("{name}: kernel normalization timed out (>30s)"));
                continue;
            }
        };
        let _ = start;
        match result {
            Ok(got) if &got == intended => {}
            Ok(got) => failures.push(format!(
                "{name}: kernel normal form is {got}, but the program intends {intended} \
                 (the elaborated term does not mean what the program says)"
            )),
            Err(e) => failures.push(format!("{name}: {e}")),
        }
    }
    assert!(
        failures.is_empty(),
        "kernel-oracle meaning mismatches:\n{}",
        failures.join("\n")
    );
}
