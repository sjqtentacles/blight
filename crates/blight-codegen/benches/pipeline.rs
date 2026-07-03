//! Compile-pipeline microbenchmarks (spec §7): time each pure-Rust backend stage
//! (`lower -> region::analyze -> closure::convert -> mono::monomorphize -> anf::normalize`) on
//! representative `main` programs of growing size. No LLVM is required — this is the whole
//! erase/lower/closure/mono/ANF pipeline, which is the part that runs on every `blight build`
//! before object emission.
//!
//! Inputs are real `.bl` snippets elaborated through `blight-elab` (so they are known to compile
//! and type-check), exactly as `blight build` would feed the backend.

use blight_codegen::{anf, closure, lower, mono, region};
use blight_elab::{ElabEnv, Program};
use blight_kernel::{Signature, Term};
use criterion::{criterion_group, BenchmarkId, Criterion};

/// Resolve `(load "std/…")` against the checked-in prelude, mirroring the test harness.
fn prelude_resolver(name: &str) -> Result<String, blight_elab::ElabError> {
    let path = format!("{}/../blight-prelude/{}", env!("CARGO_MANIFEST_DIR"), name);
    std::fs::read_to_string(&path)
        .map_err(|e| blight_elab::ElabError::BadForm(format!("cannot load {path:?}: {e}")))
}

/// Elaborate `src` and return the `(term, type, signature)` triple for its `main` global, the same
/// inputs `driver::build_binary` hands the backend. Deep-recursive elaboration (the string-tower
/// inputs) is why `main` below runs the whole harness on a 64 MiB-stack thread rather than
/// criterion's default main thread.
fn elaborate_main(src: &str) -> (Term, Term, Signature) {
    let mut env = ElabEnv::new();
    {
        let mut prog = Program::with_resolver(&mut env, prelude_resolver);
        prog.run(src)
            .unwrap_or_else(|e| panic!("bench input elaborates: {e:?}"));
    }
    let term = env
        .global_term("main")
        .expect("bench input defines `main`")
        .clone();
    let ty = env.global_type("main").expect("`main` has a type").clone();
    (term, ty, env.signature().clone())
}

/// A Nat literal as surface syntax. Written as a bare decimal (E1 sugar): it elaborates to exactly
/// the same `Succ`-chain core term as a hand-nested `(Succ (Succ …))`, but stays flat in the
/// reader — a nested chain of 256+ would trip the reader's s-expression nesting limit, which is
/// why the pre-E1 form of this helper capped the whole bench at n < 256.
fn nat_lit(n: usize) -> String {
    n.to_string()
}

/// `main : Nat` = `plus n n` where `n` is a literal of the given size — drives the eliminator-heavy
/// `plus` through the whole pipeline.
fn plus_program(n: usize) -> String {
    format!(
        "(load \"std/nat.bl\")\n(define main Nat (plus {lit} {lit}))\n",
        lit = nat_lit(n)
    )
}

/// `main : Nat` = the length of a literal `List Nat` of the given size — exercises a parametric
/// inductive + a structurally-recursive `length`.
fn list_length_program(n: usize) -> String {
    let mut list = String::from("nil");
    for i in 0..n {
        list = format!("(cons {} {list})", nat_lit(i % 3));
    }
    // The literal cons-chain has no synthesizable type of its own, so `length`'s implicit `A`
    // needs the ascription (the standard E2 pattern for constructor-literal arguments).
    format!("(load \"std/list.bl\")\n(define main Nat (length (the (List Nat) {list})))\n")
}

/// A literal `List Nat` of the given size, smallest codepoints first (values cycle `0,1,2`).
fn list_lit(n: usize) -> String {
    let mut list = String::from("nil");
    for i in 0..n {
        list = format!("(cons {} {list})", nat_lit(i % 3));
    }
    list
}

/// `main : Nat` = `length (reverse xs)` over an `n`-element `List Nat`. `reverse` is an
/// accumulator-threaded structural recursion (tier-1 TCO in ANF), so this charts the closure/ANF
/// cost of a real list algorithm rather than a single eliminator.
fn list_reverse_program(n: usize) -> String {
    format!(
        "(load \"std/list.bl\")\n(define main Nat (length (reverse Nat {})))\n",
        list_lit(n)
    )
}

/// `main : Nat` = sum of a `Tree Nat` built by inserting `n` values (`0,1,2,…` mod 3) with
/// `tree-insert`, then folded with a structural `tree-sum`. Exercises a *two-recursive-field*
/// inductive (the `node`'s `l`/`r`) through lower→closure→mono→ANF — the heaviest structural shape
/// in the prelude.
fn tree_sum_program(n: usize) -> String {
    let mut tree = String::from("(leaf)");
    for i in 0..n {
        tree = format!("(tree-insert Nat nat-le {} {tree})", nat_lit(i % 3));
    }
    format!(
        "(load \"std/tree.bl\")\n\
         (deftotal tree-sum (Pi ((tr (Tree Nat))) Nat)\n\
           (lam (tr) (match tr\n\
             [(leaf) Zero]\n\
             [(node l x r) (plus (tree-sum l) (plus x (tree-sum r)))])))\n\
         (define main Nat (tree-sum {tree}))\n"
    )
}

/// `main : Int` = a left-nested chain of `int+` of depth `n`, i.e. `(int+ (int+ … (int 0)) (int 1))`.
/// `Int` is a primitive kernel type (no `(load …)` needed); each `int+` lowers to a single hardware
/// add, so this charts the pure-pipeline cost of an arithmetic-heavy `main` as the AST deepens.
fn int_arith_program(n: usize) -> String {
    let mut expr = String::from("(int 0)");
    for i in 0..n {
        expr = format!("(int+ {expr} (int {}))", i % 7);
    }
    format!("(define main Int {expr})\n")
}

/// `main : String` = `string-reverse` over a `string-append` chain that builds an `n`-codepoint
/// literal, exercising the String tower (a `push`/`empty` cons-list of `Nat` codepoints from
/// std/string.bl) through the whole backend. Literals use the reader's quoted-string sugar.
fn string_program(n: usize) -> String {
    let mut expr = String::from("\"\"");
    for _ in 0..n {
        expr = format!("(string-append \"ab\" {expr})");
    }
    format!("(load \"std/string.bl\")\n(define main String (string-reverse {expr}))\n")
}

/// Lower an elaborated `main` all the way to ANF (the full pure-Rust backend). Used by the
/// `end_to_end` bench bodies.
fn lower_to_anf(term: &Term, ty: &Term, sig: &Signature) -> blight_codegen::anf::AnfProgram {
    let cir = lower::lower(term, ty, sig);
    let cir = region::analyze(&cir);
    let prog = closure::convert(&cir);
    let prog = mono::monomorphize(&prog);
    anf::normalize(&prog)
}

fn bench_pipeline(c: &mut Criterion) {
    // Each stage benched individually + the full chain, across growing inputs. The wider range
    // (up to 512) charts the super-linear ANF/normalization scaling the doc reports.
    let mut group = c.benchmark_group("pipeline/plus");
    for &n in &[8usize, 32, 128, 256, 512] {
        let src = plus_program(n);
        let (term, ty, sig) = elaborate_main(&src);

        group.bench_with_input(BenchmarkId::new("lower", n), &n, |b, _| {
            b.iter(|| lower::lower(&term, &ty, &sig))
        });

        let cir = lower::lower(&term, &ty, &sig);
        group.bench_with_input(BenchmarkId::new("region", n), &n, |b, _| {
            b.iter(|| region::analyze(&cir))
        });

        let cir = region::analyze(&cir);
        group.bench_with_input(BenchmarkId::new("closure", n), &n, |b, _| {
            b.iter(|| closure::convert(&cir))
        });

        let prog = closure::convert(&cir);
        group.bench_with_input(BenchmarkId::new("mono", n), &n, |b, _| {
            b.iter(|| mono::monomorphize(&prog))
        });

        let prog = mono::monomorphize(&prog);
        group.bench_with_input(BenchmarkId::new("anf", n), &n, |b, _| {
            b.iter(|| anf::normalize(&prog))
        });

        group.bench_with_input(BenchmarkId::new("end_to_end", n), &n, |b, _| {
            b.iter(|| lower_to_anf(&term, &ty, &sig))
        });
    }
    group.finish();

    // List/int/string inputs nest *structurally* in the reader (`(cons _ (cons _ …))`), so their
    // sizes stay under the reader's 256-deep s-expression nesting limit: 240 is the largest clean
    // size that fits with the wrapping forms. (The `plus` group is exempt — its depth lives in the
    // decimal literal, which is flat at the reader level.)
    let mut group = c.benchmark_group("pipeline/list_length");
    for &n in &[8usize, 32, 128, 240] {
        let src = list_length_program(n);
        let (term, ty, sig) = elaborate_main(&src);
        group.bench_with_input(BenchmarkId::new("end_to_end", n), &n, |b, _| {
            b.iter(|| lower_to_anf(&term, &ty, &sig))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("pipeline/list_reverse");
    for &n in &[8usize, 32, 128, 240] {
        let src = list_reverse_program(n);
        let (term, ty, sig) = elaborate_main(&src);
        group.bench_with_input(BenchmarkId::new("end_to_end", n), &n, |b, _| {
            b.iter(|| lower_to_anf(&term, &ty, &sig))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("pipeline/tree_sum");
    for &n in &[8usize, 32, 96, 192] {
        let src = tree_sum_program(n);
        let (term, ty, sig) = elaborate_main(&src);
        group.bench_with_input(BenchmarkId::new("end_to_end", n), &n, |b, _| {
            b.iter(|| lower_to_anf(&term, &ty, &sig))
        });
    }
    group.finish();

    // Native-`Int` arithmetic: a deepening left-nested `int+` chain. `Int` is a primitive kernel
    // type, so no prelude load is needed — this isolates the backend cost of an arithmetic AST.
    let mut group = c.benchmark_group("pipeline/int_arith");
    for &n in &[8usize, 32, 128, 240] {
        let src = int_arith_program(n);
        let (term, ty, sig) = elaborate_main(&src);
        group.bench_with_input(BenchmarkId::new("end_to_end", n), &n, |b, _| {
            b.iter(|| lower_to_anf(&term, &ty, &sig))
        });
    }
    group.finish();

    // String tower: `string-reverse` over a growing `string-append` chain of codepoint literals,
    // pushing the std/string.bl `push`/`empty` cons-list through lower→region→closure→mono→ANF.
    let mut group = c.benchmark_group("pipeline/string");
    for &n in &[8usize, 32, 128, 240] {
        let src = string_program(n);
        let (term, ty, sig) = elaborate_main(&src);
        group.bench_with_input(BenchmarkId::new("end_to_end", n), &n, |b, _| {
            b.iter(|| lower_to_anf(&term, &ty, &sig))
        });
    }
    group.finish();
}

criterion_group!(benches, bench_pipeline);

/// Hand-rolled `criterion_main!`: the harness runs on a 64 MiB-stack worker thread because
/// elaborating the deep bench inputs (notably the string tower) overflows the default main-thread
/// stack — the same rationale as `driver::bench_support::compile_source_to_anf`, applied to the
/// whole harness rather than per elaboration so the elaborated terms never cross a thread
/// boundary (they are not `Send` once `Term`'s recursive fields are `Rc`).
fn main() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            benches();
            Criterion::default().configure_from_args().final_summary();
        })
        .expect("spawn bench harness thread")
        .join()
        .expect("bench harness thread panicked (see message above)");
}
