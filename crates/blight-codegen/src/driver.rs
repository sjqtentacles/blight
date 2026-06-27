//! The backend driver (spec §7): orchestrates erase → lower → closure-conv → mono → ANF → LLVM
//! object emission, compiles the C runtime, and links a native binary via `clang`. Gated behind
//! the `llvm` feature.

use crate::{anf, closure, lower, mono, region};
use blight_kernel::{Signature, Term};
use std::path::Path;
use std::process::Command;

/// Compile a checked global `term : ty` (with the program `sig`) to a native executable at
/// `out_bin`. `work` is a scratch directory for intermediates.
pub fn build_binary(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_bin: &Path,
    work: &Path,
) -> Result<(), String> {
    std::fs::create_dir_all(work).map_err(|e| e.to_string())?;

    // The pure-Rust pipeline. Region escape analysis runs on the lowered `Cir` (after `lower`,
    // before `closure`): it reads the `Cir::Region` scopes and retags non-escaping allocations
    // `Arena`, which then ride through closure conversion / mono / ANF unchanged.
    let cir = lower::lower(term, ty, sig);
    if std::env::var_os("BL_DUMP_CIR").is_some() {
        eprintln!("[lower] {cir:#?}");
    }
    let cir = region::analyze(&cir);
    let prog = closure::convert(&cir);
    let prog = mono::monomorphize(&prog);
    let mut anf = anf::normalize(&prog);
    anf.con_tags = anf::con_tags_from_sig(sig);
    if std::env::var_os("BL_DUMP_ANF").is_some() {
        eprintln!("[anf] {anf:#?}");
    }

    // Emit the program object.
    let prog_obj = work.join("program.o");
    crate::llvm::emit_object(&anf, &prog_obj)?;

    // Compile the C runtime objects. We author our own `main` (below) so that printing can be
    // result-type-aware (text for a `String`, numeral otherwise), so `prelude_rt.c` is compiled
    // with `-DBL_NO_MAIN` to suppress its built-in numeric `main` while keeping its printers and
    // constructors. This stays entirely in tower code — no kernel/IR change.
    let runtime_dir = runtime_src_dir();
    let mut runtime_objs = Vec::new();
    for src in ["gc.c", "arena.c", "stack.c", "delay.c", "effects.c"] {
        let obj = work.join(format!("{src}.o"));
        compile_c(&runtime_dir.join(src), &obj, &runtime_dir)?;
        runtime_objs.push(obj);
    }
    {
        let obj = work.join("prelude_rt.c.o");
        compile_c_with_defs(
            &runtime_dir.join("prelude_rt.c"),
            &obj,
            &runtime_dir,
            &["-DBL_NO_MAIN"],
        )?;
        runtime_objs.push(obj);
    }

    // Author a tiny `main.c` that selects the printer by the program's result type. A `String`
    // (std/string.bl) prints as text via `bl_print_string`; everything else uses the historical
    // numeric/constructor `bl_print`.
    let main_c = main_source_for(ty);
    let main_path = work.join("main.c");
    std::fs::write(&main_path, &main_c).map_err(|e| e.to_string())?;
    let main_obj = work.join("main.c.o");
    compile_c(&main_path, &main_obj, &runtime_dir)?;
    runtime_objs.push(main_obj);

    // Link everything into the binary via clang.
    let mut cmd = Command::new("clang");
    cmd.arg("-o").arg(out_bin).arg(&prog_obj);
    for o in &runtime_objs {
        cmd.arg(o);
    }
    let status = cmd
        .status()
        .map_err(|e| format!("clang link failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("clang link failed with status {status}"));
    }
    Ok(())
}

/// Is `ty` the `String` data type (std/string.bl)? Used to pick the text printer for `main`.
fn term_is_string(ty: &Term) -> bool {
    matches!(ty, Term::Data(name, _, _) if name.0 == "String")
}

/// If `ty` is an effect type `(! E A)` whose row carries the `Console` effect, return its inner
/// result type `A`. A `main : (! Console A)` is run through the native top-level Console handler
/// (`bl_run_console`) instead of being treated as a pure value.
fn console_inner(ty: &Term) -> Option<&Term> {
    match ty {
        Term::EffTy(row, inner) if row.contains(&blight_kernel::EffName::new("Console")) => {
            Some(inner)
        }
        _ => None,
    }
}

/// The C `main` source for a program whose result type is `ty`: a `String` result prints as text
/// (`bl_print_string`), otherwise the numeric/constructor printer (`bl_print`, via prelude_rt.c's
/// historical path replicated here). Both initialize the same 64 MiB heap + stack as the original
/// baked-in `main`, so non-String programs are byte-for-byte unchanged.
fn main_source_for(ty: &Term) -> String {
    // `main : (! Console A)`: run the bubbling Console computation through the native top-level
    // handler, which performs the real I/O, then print the pure result `A` (Unit/String/numeral).
    if let Some(inner) = console_inner(ty) {
        let printer = result_printer_for(inner);
        return format!(
            r#"#include "blight_rt.h"
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init(64 * 1024 * 1024); /* 64 MiB initial heap (the collector grows it on demand) */
  bl_stack_init();
  BlValue result = bl_run_console(bl_program_entry());
  {printer}
  return 0;
}}
"#
        );
    }
    let printer = result_printer_for(ty);
    format!(
        r#"#include "blight_rt.h"
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init(64 * 1024 * 1024); /* 64 MiB initial heap (the collector grows it on demand) */
  bl_stack_init();
  BlValue result = bl_program_entry();
  {printer}
  return 0;
}}
"#
    )
}

/// Pick the result printer call for a (pure) result type `ty`. A `String` prints as text; the
/// `Unit` type prints nothing (its sole value carries no information — used by Console programs
/// whose observable output already happened via `print`); everything else uses the numeric printer.
fn result_printer_for(ty: &Term) -> &'static str {
    if term_is_string(ty) {
        "bl_print_string(result);"
    } else if matches!(ty, Term::Data(name, _, _) if name.0 == "Unit") {
        "(void) result;"
    } else {
        "bl_print_default(result);"
    }
}

/// Emit only the program object (no link) — used by the grade-0-absent acceptance test to scan
/// symbols.
pub fn emit_program_object(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_obj: &Path,
) -> Result<(), String> {
    emit_program_object_for_target(term, ty, sig, out_obj, crate::llvm::Target::Native)
}

/// Emit only the program object (no link) for the requested `target`. The `wasm32` target produces
/// a WebAssembly object (`\0asm` magic) rather than a host object; it is not linked here.
pub fn emit_program_object_for_target(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_obj: &Path,
    target: crate::llvm::Target,
) -> Result<(), String> {
    let cir = lower::lower(term, ty, sig);
    let cir = region::analyze(&cir);
    let prog = closure::convert(&cir);
    let prog = mono::monomorphize(&prog);
    let mut anf = anf::normalize(&prog);
    anf.con_tags = anf::con_tags_from_sig(sig);
    crate::llvm::emit_object_for_target(&anf, out_obj, target)
}

/// Emit textual LLVM IR for the full pipeline (used by tests to assert on tailcc/musttail).
pub fn emit_ir(term: &Term, ty: &Term, sig: &Signature) -> Result<String, String> {
    let cir = lower::lower(term, ty, sig);
    let cir = region::analyze(&cir);
    let prog = closure::convert(&cir);
    let prog = mono::monomorphize(&prog);
    let mut anf = anf::normalize(&prog);
    anf.con_tags = anf::con_tags_from_sig(sig);
    crate::llvm::emit_ir(&anf)
}

/// Link a runnable WebAssembly module (`out_wasm`) for a checked `term : ty`. Emits the program as
/// a wasm object, compiles the minimal freestanding wasm ABI shim (`runtime/wasm_rt.c`) to a wasm
/// object, and links both with `wasm-ld` into a `.wasm` module exporting `bl_main`.
///
/// This needs a wasm-capable toolchain: a `clang` whose backend knows `wasm32` (the LLVM-bundled
/// clang, not Apple clang) and a `wasm-ld`. Override either via `BLIGHT_WASM_CC` / `BLIGHT_WASM_LD`;
/// otherwise we look on `PATH`. When the toolchain is absent we return a clear, actionable error so
/// callers can fall back to object-only emission.
pub fn link_wasm(
    term: &Term,
    ty: &Term,
    sig: &Signature,
    out_wasm: &Path,
    work: &Path,
) -> Result<(), String> {
    let wasm_cc = which_tool("BLIGHT_WASM_CC", &["clang"]).ok_or_else(|| {
        "wasm link needs a wasm-capable clang; set BLIGHT_WASM_CC or install LLVM clang \
         (Apple clang has no wasm backend)"
            .to_string()
    })?;
    let wasm_ld = which_tool("BLIGHT_WASM_LD", &["wasm-ld", "wasm-ld-18", "wasm-ld-19"])
        .ok_or_else(|| {
            "wasm link needs `wasm-ld`; set BLIGHT_WASM_LD or install lld".to_string()
        })?;

    std::fs::create_dir_all(work).map_err(|e| e.to_string())?;

    // 1. The program object, retargeted to wasm32.
    let prog_obj = work.join("program.wasm.o");
    emit_program_object_for_target(term, ty, sig, &prog_obj, crate::llvm::Target::Wasm32)?;

    // 2. The freestanding wasm ABI shim → wasm object.
    let shim_src = runtime_src_dir().join("wasm_rt.c");
    let shim_obj = work.join("wasm_rt.o");
    let status = Command::new(&wasm_cc)
        .args(["--target=wasm32-unknown-unknown", "-O2", "-nostdlib", "-c"])
        .arg("-I")
        .arg(runtime_src_dir())
        .arg(&shim_src)
        .arg("-o")
        .arg(&shim_obj)
        .status()
        .map_err(|e| format!("wasm cc failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("compiling wasm_rt.c failed: {status}"));
    }

    // 3. Link to a runnable module exporting `bl_main` (no entry, no libc).
    let status = Command::new(&wasm_ld)
        .args(["--no-entry", "--export=bl_main", "--allow-undefined"])
        .arg(&prog_obj)
        .arg(&shim_obj)
        .arg("-o")
        .arg(out_wasm)
        .status()
        .map_err(|e| format!("wasm-ld failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("wasm-ld link failed with status {status}"));
    }
    Ok(())
}

/// Resolve a tool: an explicit `$ENV` override if set, else the first of `candidates` found on
/// `PATH`. Returns the resolved program name/path to hand to `Command::new`.
fn which_tool(env_var: &str, candidates: &[&str]) -> Option<std::ffi::OsString> {
    if let Some(p) = std::env::var_os(env_var) {
        if !p.is_empty() {
            return Some(p);
        }
    }
    let path = std::env::var_os("PATH")?;
    for cand in candidates {
        for dir in std::env::split_paths(&path) {
            let full = dir.join(cand);
            if full.is_file() {
                return Some(full.into_os_string());
            }
        }
    }
    None
}

fn compile_c(src: &Path, obj: &Path, include_dir: &Path) -> Result<(), String> {
    compile_c_with_defs(src, obj, include_dir, &[])
}

/// Like [`compile_c`] but passes extra `clang` flags (e.g. `-DBL_NO_MAIN`).
fn compile_c_with_defs(
    src: &Path,
    obj: &Path,
    include_dir: &Path,
    defs: &[&str],
) -> Result<(), String> {
    let status = Command::new("clang")
        .arg("-c")
        .arg("-O2")
        .arg("-I")
        .arg(include_dir)
        .args(defs)
        .args(if std::env::var_os("BL_EFFECTS_DEBUG").is_some() {
            &["-DBL_EFFECTS_DEBUG"][..]
        } else {
            &[][..]
        })
        .arg(src)
        .arg("-o")
        .arg(obj)
        .status()
        .map_err(|e| format!("clang -c failed to start: {e}"))?;
    if !status.success() {
        return Err(format!("compiling {} failed: {status}", src.display()));
    }
    Ok(())
}

/// Locate the `runtime/` directory shipped with this crate.
fn runtime_src_dir() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime")
}

/// Support for runtime/memory benchmarks and their sanity tests: build a hand-written
/// [`crate::AnfProgram`] (exposing `bl_program_entry`) into a native binary linked against a custom
/// C `main` (which can read the runtime counters `bl_gc_collections()`, `bl_arena_live_bytes()`,
/// `bl_arena_alloc_count()`), run it, and capture stdout. This deliberately mirrors the
/// `region_workload_bypasses_gc` acceptance test so the bench harness and that test share one path.
pub mod bench_support {
    use super::{compile_c, runtime_src_dir};
    use crate::{Alloc, AnfFunc, AnfProgram, Atom, Comp, Tail, TailArm};
    use blight_kernel::ConName;
    use std::path::Path;
    use std::process::Command;

    /// Resolve `(load "std/…")` against the checked-in prelude (same convention the test/bench
    /// harnesses use). `CARGO_MANIFEST_DIR` is `crates/blight-codegen`, so the prelude is one level
    /// up under `blight-prelude/`.
    pub fn prelude_resolver(name: &str) -> Result<String, blight_elab::ElabError> {
        let path = format!("{}/../blight-prelude/{}", env!("CARGO_MANIFEST_DIR"), name);
        std::fs::read_to_string(&path)
            .map_err(|e| blight_elab::ElabError::BadForm(format!("cannot load {path:?}: {e}")))
    }

    /// Elaborate `src` (which must define a `main` global) and lower it all the way to ANF through
    /// the full pure-Rust backend (lower → region → closure → mono → anf). This is exactly what
    /// `build_binary` feeds the object emitter, so a `build_run_with_main` over the result measures
    /// the *runtime* cost of a real `.bl` program (deep recursion, list/tree algorithms, …) rather
    /// than a hand-built ANF stub. Panics with context on any elaboration failure.
    pub fn compile_source_to_anf(src: &str) -> AnfProgram {
        // Elaborating long unary-`Nat` programs recurses deeply through the term, so do the work on
        // a generous (64 MiB) stack — mirrors the CLI build thread; callers (benches/tests) need not
        // arrange their own large stack.
        let src = src.to_string();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || compile_source_to_anf_inner(&src))
            .expect("spawn compile thread")
            .join()
            .expect("compile thread")
    }

    fn compile_source_to_anf_inner(src: &str) -> AnfProgram {
        use blight_elab::{ElabEnv, Program};
        let mut env = ElabEnv::new();
        {
            let mut prog = Program::with_resolver(&mut env, prelude_resolver);
            prog.run(src)
                .unwrap_or_else(|e| panic!("bench source elaborates: {e:?}"));
        }
        let term = env
            .global_term("main")
            .expect("bench source defines `main`")
            .clone();
        let ty = env.global_type("main").expect("`main` has a type").clone();
        let sig = env.signature().clone();
        let cir = crate::lower::lower(&term, &ty, &sig);
        let cir = crate::region::analyze(&cir);
        let prog = crate::closure::convert(&cir);
        let prog = crate::mono::monomorphize(&prog);
        let mut anf = crate::anf::normalize(&prog);
        // Constructor tags must come from the signature (declaration order) so `case` arms dispatch
        // correctly — exactly as `build_binary` does. Without this, multi-constructor types like
        // `List`/`Tree` fall back to name-derived ids that need not match, miscompiling the switch.
        anf.con_tags = crate::anf::con_tags_from_sig(&sig);
        anf
    }

    /// A `Nat` literal `Succ^(n) Zero` as surface syntax.
    pub fn nat_lit(n: usize) -> String {
        let mut s = String::from("(Zero)");
        for _ in 0..n {
            s = format!("(Succ {s})");
        }
        s
    }

    /// `main : Nat` summing an `n`-element `List Nat` with `foldr plus 0` — deep structural
    /// recursion that *actually runs* (no delay), allocating a list spine and the unary result on
    /// the GC heap. The element values cycle `0,1,2`.
    pub fn list_sum_source(n: usize) -> String {
        let mut list = String::from("nil");
        for i in 0..n {
            list = format!("(cons {} {list})", nat_lit(i % 3));
        }
        format!(
            "(load \"std/list.bl\")\n\
             (define main Nat (foldr Nat Nat (lam (x acc) (plus x acc)) Zero {list}))\n"
        )
    }

    /// `main : Nat` = `length (reverse xs)` over an `n`-element `List Nat`: an accumulator-threaded
    /// reverse (tier-1 TCO loop) followed by a structural length. Runs fully.
    pub fn list_reverse_source(n: usize) -> String {
        let mut list = String::from("nil");
        for i in 0..n {
            list = format!("(cons {} {list})", nat_lit(i % 3));
        }
        format!("(load \"std/list.bl\")\n(define main Nat (length Nat (reverse Nat {list})))\n")
    }

    /// `main : Nat` = sum of a `Tree Nat` built by inserting `n` values with `tree-insert`, folded
    /// by a structural `tree-sum`. Exercises a two-recursive-field inductive at runtime.
    pub fn tree_sum_source(n: usize) -> String {
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

    /// A C `main` (spec §7.3 — dynamic heap) that initializes a deliberately **tiny** `heap_kib`-KiB
    /// GC heap, then builds a single linked list of `nodes` GC-allocated `BL_CON` cells **all held
    /// live at once** (each node points at the previous via `fields[0]`; the head is kept on the
    /// shadow stack across every `bl_alloc`). The live set far exceeds the initial heap, so the
    /// collector must *grow* its semi-spaces instead of aborting. Prints `RESULT collections=<n>
    /// length=<n>`, where `length` walks the final list iteratively to prove it is intact (no node
    /// was lost or corrupted across the growing collections). No Blight program drives this — it is a
    /// focused unit test of the allocator/collector growth path, immune to compiler/C-stack limits.
    pub fn grow_heap_main(heap_kib: usize, nodes: usize) -> String {
        format!(
            r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void); /* unused; linked for symmetry */
int main(void) {{
  bl_gc_init({heap_kib} * 1024);
  bl_stack_init();
  BlValue head = bl_alloc(BL_CON, 1, 0); /* sentinel: one field, initially NULL */
  bl_gc_push_root(&head);
  for (size_t i = 0; i < {nodes}; i++) {{
    BlValue node = bl_alloc(BL_CON, 1, 1); /* allocation may trigger a (growing) collection */
    node->fields[0] = head; /* keep the whole chain reachable from `head` */
    head = node;
  }}
  size_t len = 0;
  for (BlValue p = head; p != 0; p = p->fields[0]) len++;
  printf("RESULT collections=%zu length=%zu\n", bl_gc_collections(), len);
  bl_gc_pop_roots(1);
  return 0;
}}
"#
        )
    }

    /// Parse `length=<n>` out of a `grow_heap_main` stdout line.
    pub fn parse_length(stdout: &str) -> usize {
        stdout
            .split_whitespace()
            .find_map(|tok| tok.strip_prefix("length="))
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no length= field in: {stdout:?}"))
    }

    /// A counted scratch loop over a `DEPTH`-deep `Nat`: each `Succ` iteration allocates
    /// `scratch_per_iter` dead 2-tuples (region-arena'd when `arena`, GC-heap otherwise) then jumps
    /// to the predecessor. The exact shape of `region_workload_bypasses_gc`; the workload that shows
    /// region reclamation bypassing the collector.
    pub fn scratch_loop_program(arena: bool, depth: usize, scratch_per_iter: usize) -> AnfProgram {
        let alloc = if arena { Alloc::Arena } else { Alloc::Gc };
        let mut body: Tail = Tail::Jump(Atom::Var(scratch_per_iter));
        for _ in 0..scratch_per_iter {
            body = Tail::Let(
                Comp::Tuple(vec![Atom::Var(0), Atom::Var(0)], alloc),
                Box::new(body),
            );
        }
        let succ_body = if arena {
            Tail::Region(Box::new(body))
        } else {
            body
        };
        let loop_body = Tail::Case(
            Atom::Var(0),
            vec![
                TailArm {
                    con: ConName("Zero".into()),
                    binders: 0,
                    body: Tail::Ret(Atom::Var(0)),
                },
                TailArm {
                    con: ConName("Succ".into()),
                    binders: 1,
                    body: succ_body,
                },
            ],
        );
        let loopf = AnfFunc {
            name: "scratch_loop".into(),
            recursive: true,
            body: loop_body,
        };

        let mut entry: Tail = Tail::TailCall(Atom::Global("scratch_loop".into()), Atom::Var(0));
        for _ in 0..depth {
            entry = Tail::Let(
                Comp::Con(ConName("Succ".into()), vec![Atom::Var(0)], Alloc::Gc),
                Box::new(entry),
            );
        }
        entry = Tail::Let(
            Comp::Con(ConName("Zero".into()), vec![], Alloc::Gc),
            Box::new(entry),
        );
        AnfProgram {
            funcs: vec![loopf],
            entry,
            con_tags: Default::default(),
        }
    }

    /// A C `main` that initializes a `heap_mib`-MiB GC heap + stack, runs `bl_program_entry`, and
    /// prints one machine-readable line: `RESULT collections=<n> arena_allocs=<n>`.
    pub fn counters_main(heap_mib: usize) -> String {
        format!(
            r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {{
  bl_gc_init({heap_mib} * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  (void)r;
  printf("RESULT collections=%zu arena_allocs=%zu\n",
         bl_gc_collections(), bl_arena_alloc_count());
  return 0;
}}
"#
        )
    }

    /// Parse `collections=<n>` out of a `counters_main` stdout line.
    pub fn parse_collections(stdout: &str) -> usize {
        stdout
            .split_whitespace()
            .find_map(|tok| tok.strip_prefix("collections="))
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no collections= field in: {stdout:?}"))
    }

    /// Build `prog` (which must expose `bl_program_entry`) plus the C source `main_c` (a full
    /// translation unit defining `int main(void)`) into a binary at `<work>/<name>`, run it, and
    /// return its captured stdout as a `String`. Panics on any build/link/run failure with context.
    pub fn build_run_with_main(prog: &AnfProgram, main_c: &str, work: &Path, name: &str) -> String {
        std::fs::create_dir_all(work).expect("create work dir");
        let runtime = runtime_src_dir();

        let prog_obj = work.join(format!("{name}_program.o"));
        crate::llvm::emit_object(prog, &prog_obj).expect("emit program object");

        let mut objs = vec![prog_obj];
        for src in ["gc.c", "arena.c", "stack.c", "delay.c", "effects.c"] {
            let obj = work.join(format!("{name}_{src}.o"));
            compile_c(&runtime.join(src), &obj, &runtime).expect("compile runtime object");
            objs.push(obj);
        }

        let main_path = work.join(format!("{name}_main.c"));
        std::fs::write(&main_path, main_c).expect("write main.c");
        let main_obj = work.join(format!("{name}_main.o"));
        compile_c(&main_path, &main_obj, &runtime).expect("compile main.c");
        objs.push(main_obj);

        let bin = work.join(name);
        let mut link = Command::new("clang");
        link.arg("-o").arg(&bin);
        for o in &objs {
            link.arg(o);
        }
        let st = link.status().expect("clang link starts");
        assert!(st.success(), "link {name}");

        let out = Command::new(&bin).output().expect("run benchmark binary");
        assert!(
            out.status.success(),
            "benchmark binary {name} exits 0; stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).into_owned()
    }
}

#[cfg(test)]
mod bench_sanity_tests {
    use super::bench_support::*;

    /// Sanity guard for the runtime benchmark harness (TDD seam, mirrors
    /// `llvm::tests::region_workload_bypasses_gc`): on a small heap the GC-heap scratch loop is
    /// forced to collect (`collections > 0`), while the region/arena twin reclaims each iteration in
    /// O(1) and never collects (`collections == 0`). If this ever flips, the bench's "regions bypass
    /// the GC" measurement is meaningless, so we assert it before trusting any timing.
    #[test]
    fn bench_harness_region_bypasses_gc_and_heap_collects() {
        let dir = std::env::temp_dir().join(format!("blight_bench_sanity_{}", std::process::id()));
        let main_c = counters_main(8); // 8 MiB heap, ~1 MiB nursery
        let depth = 300;
        let scratch = 256;

        let gc = build_run_with_main(
            &scratch_loop_program(false, depth, scratch),
            &main_c,
            &dir,
            "sanity_gc",
        );
        let arena = build_run_with_main(
            &scratch_loop_program(true, depth, scratch),
            &main_c,
            &dir,
            "sanity_arena",
        );

        assert!(
            parse_collections(&gc) > 0,
            "GC-heap scratch loop forces collections; got {gc:?}"
        );
        assert_eq!(
            parse_collections(&arena),
            0,
            "region/arena scratch loop bypasses the GC; got {arena:?}"
        );
    }

    /// `compile_source_to_anf` lowers a real `.bl` program (here a `List Nat` sum) through the full
    /// backend and the produced binary runs to completion. Guards the source-driven runtime benches.
    #[test]
    fn bench_harness_source_program_builds_and_runs() {
        // Elaborating a long unary-`Nat` list recurses deeply; run on an 8 MiB stack (the default
        // test thread is ~2 MiB), matching the real CLI's main thread.
        std::thread::Builder::new()
            .stack_size(8 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("blight_bench_src_{}", std::process::id()));
                let main_c = counters_main(64);
                let out = build_run_with_main(
                    &compile_source_to_anf(&list_sum_source(200)),
                    &main_c,
                    &dir,
                    "src_list_sum",
                );
                assert!(
                    out.contains("collections="),
                    "source-compiled list-sum runs to completion; got {out:?}"
                );
            })
            .expect("spawn")
            .join()
            .expect("source-program sanity thread");
    }

    /// Acceptance test for the **dynamic (growable) heap** (spec §7.3): a workload whose *live* set
    /// dwarfs the initial heap must run to completion by *growing* the collector's semi-spaces, not
    /// abort with "heap exhausted". We start the GC with a deliberately tiny **64 KiB** heap and then
    /// allocate a single linked list of 200 000 `BL_CON` nodes held live all at once (~5 MiB), which
    /// cannot remotely fit in 64 KiB. Before the dynamic-heap fix this aborted; now the major
    /// collector reallocates ever-larger semi-spaces and the binary exits 0 with the list fully
    /// intact (`length == 200001`, counting the sentinel) and at least one collection having run
    /// (proving the GC actually engaged — and thus grew — rather than the heap being large enough).
    #[test]
    fn growable_heap_survives_live_set_exceeding_initial_heap() {
        let dir = std::env::temp_dir().join(format!("blight_grow_heap_{}", std::process::id()));
        const NODES: usize = 200_000;
        let out = build_run_with_main(
            &scratch_loop_program(false, 0, 0), // trivial entry program (unused by this main)
            &grow_heap_main(64, NODES),         // 64 KiB initial heap
            &dir,
            "grow_heap",
        );
        assert!(
            parse_collections(&out) > 0,
            "the 5 MiB live set must force the collector (and thus heap growth); got {out:?}"
        );
        assert_eq!(
            parse_length(&out),
            NODES + 1,
            "the entire live list (plus sentinel) must survive every growing collection; got {out:?}"
        );
    }
}
