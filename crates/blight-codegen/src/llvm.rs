//! LLVM IR emission via `inkwell` (spec §7.4 tier 2). Gated behind the `llvm` feature.
//!
//! Every Blight value is an opaque pointer (`BlValue`, LLVM `ptr`). A compiled top-level function
//! has signature `ptr (ptr env, ptr arg)` using the `tailcc` calling convention so that
//! `TailCall`s can be marked `musttail` (a missed tail call is then a hard error, never silent
//! stack growth — spec §7.4). The emitter lowers the ANF program produced by [`crate::anf`].
//!
//! GC safepoints (`bl_gc_poll`) are emitted at function entry and at loop back-edges (`Jump`),
//! **never** immediately before a `musttail` call, preserving tail-call validity.
//!
//! This is the realistic-but-minimal emitter for the M4 subset: constructors, tuples/projections,
//! closures, the delay monad (with the `bl_force` trampoline for `Trampoline`), and effect
//! operations. It is untrusted: a miscompilation is a bug, never an unsoundness.

use crate::anf::{AnfProgram, Atom, Comp, Tail, TailArm};
use crate::ir::Alloc;
use crate::runtime::{sym, tag};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::values::{CallSiteValue, FunctionValue, IntValue, LLVMTailCallKind, PointerValue};
use inkwell::AddressSpace;
use std::collections::HashMap;

/// The code-generation target. `Native` targets the host machine (the default); `Wasm32` targets
/// `wasm32-unknown-unknown`. The driver can link the wasm object into a runnable module when a
/// wasm toolchain is available (see `driver::link_wasm`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    /// The host machine.
    Native,
    /// `wasm32-unknown-unknown`.
    Wasm32,
}

/// IR-level optimization applied before object emission via LLVM's new pass manager
/// ([`inkwell::module::Module::run_passes`]). Prior to B1 the emitter ran **no** IR passes (only the
/// target machine's `OptimizationLevel::Default` governed instruction selection), so the lowered ANF
/// went to the backend essentially verbatim. Each level runs the corresponding `opt`-style default
/// pipeline. All default pipelines preserve `musttail` markers, so tail-call soundness (spec §7.4)
/// is unaffected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OptLevel {
    /// No IR passes (fastest compile; largest/slowest code). The historical behavior.
    None,
    /// `default<O2>` — the balanced pipeline. The default for `blight build`.
    #[default]
    Default,
    /// `default<O3>` — the aggressive pipeline.
    Aggressive,
}

impl OptLevel {
    /// The `opt`-style pass-pipeline string for this level, or `None` to skip the pass manager.
    fn pipeline(self) -> Option<&'static str> {
        match self {
            OptLevel::None => None,
            OptLevel::Default => Some("default<O2>"),
            OptLevel::Aggressive => Some("default<O3>"),
        }
    }

    /// Parse a CLI `--opt` value (`0`/`none`, `2`/`default`, `3`/`aggressive`).
    pub fn parse(s: &str) -> Result<OptLevel, String> {
        match s {
            "0" | "none" => Ok(OptLevel::None),
            "2" | "default" => Ok(OptLevel::Default),
            "3" | "aggressive" => Ok(OptLevel::Aggressive),
            other => Err(format!(
                "unknown --opt level `{other}` (expected 0/none, 2/default, or 3/aggressive)"
            )),
        }
    }
}

/// Emit an object file for `prog` at `out_path` (e.g. `foo.o`) for the host (native) target at the
/// default optimization level.
pub fn emit_object(prog: &AnfProgram, out_path: &std::path::Path) -> Result<(), String> {
    emit_object_for_target(prog, out_path, Target::Native, OptLevel::default())
}

/// Emit an object file for `prog` at `out_path` for the requested `target` and `opt` level.
pub fn emit_object_for_target(
    prog: &AnfProgram,
    out_path: &std::path::Path,
    target: Target,
    opt: OptLevel,
) -> Result<(), String> {
    let context = Context::create();
    let codegen =
        Codegen::with_tags_for_target(&context, "blight_module", prog.con_tags.clone(), target);
    codegen.emit_program(prog)?;
    codegen.write_object(out_path, target, opt)
}

/// Emit LLVM bitcode (`.bc`) for `prog` at `out_path` for the requested `target`/`opt` — the Blight
/// half of the Phase 3 cross-object LTO link. Mirrors [`emit_object_for_target`] but serializes the
/// optimized module as bitcode so a subsequent `clang -flto` link can inline across the
/// Blight/runtime boundary. Produces the same program, just as IR rather than machine code.
pub fn emit_bitcode_for_target(
    prog: &AnfProgram,
    out_path: &std::path::Path,
    target: Target,
    opt: OptLevel,
) -> Result<(), String> {
    let context = Context::create();
    let codegen =
        Codegen::with_tags_for_target(&context, "blight_module", prog.con_tags.clone(), target);
    codegen.emit_program(prog)?;
    codegen.write_bitcode(out_path, target, opt)
}

/// Emit textual LLVM IR for `prog` (used by tests to assert on `tailcc`/`musttail`).
pub fn emit_ir(prog: &AnfProgram) -> Result<String, String> {
    let context = Context::create();
    let codegen = Codegen::with_tags(&context, "blight_module", prog.con_tags.clone());
    codegen.emit_program(prog)?;
    Ok(codegen.module.print_to_string().to_string())
}

/// The `tailcc` calling-convention id in LLVM (CallingConv::Tail). Numeric to avoid relying on an
/// inkwell enum that varies across versions.
const TAILCC: u32 = 18;

/// Per-function emission state implementing the precise **shadow-stack** GC rooting discipline
/// (spec §7.4). Every live Blight value is held in a stack *slot* (an `alloca ptr` in the entry
/// block) that is registered with the runtime via `bl_gc_push_root`; a collection scans these slots
/// and rewrites them in place when it moves objects, so reloading a value from its slot after any
/// allocation always yields the up-to-date (possibly relocated) pointer. Roots are balanced with
/// `bl_gc_pop_roots` at every function-exit terminator (return / tail-call / jump / trampoline).
struct Frame<'ctx> {
    /// A builder pinned at the function's entry block, used to allocate root slots so they dominate
    /// all uses and are not re-executed on a `musttail` loop back-edge.
    entry: Builder<'ctx>,
    /// The entry basic block itself, so alloca insertion can be re-anchored before its terminator.
    entry_bb: BasicBlock<'ctx>,
    /// Slot holding the closure environment pointer (rooted; reloaded on each `EnvRef`).
    env_slot: PointerValue<'ctx>,
    /// de Bruijn stack of value slots (innermost last). `Var(i)` reads `slots[len-1-i]`.
    slots: Vec<PointerValue<'ctx>>,
}

struct Codegen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    /// Per-constructor tag (index within its data decl), used to stamp `Con` objects so `case` can
    /// switch on the constructor's declaration order. Empty falls back to a name-derived id.
    con_tags: HashMap<blight_kernel::ConName, u64>,
    /// Emit `!invariant.load` on immutable header/field reads and `readonly` on the (never-written)
    /// `env`/`arg` parameters, letting LLVM CSE/hoist redundant reads. Sound because Blight values
    /// are immutable once constructed and every variable access reloads its pointer from a
    /// GC-rewritten root slot (so no raw object pointer is carried across a collection safepoint).
    /// Disabled by `BL_NO_ALIASMETA` (a differential fast-path flag).
    aliasmeta: bool,
    /// Emit a non-tail *direct* call for a captureless global callee (`Comp::CallGlobal`) when the
    /// argument is not a bubbling effect, instead of routing through the C `bl_app_global`. The pure
    /// path of `bl_app_global` is exactly `fnptr(NULL, arg)`, so the direct `tailcc` call is
    /// bit-identical — but inlined into LLVM IR, letting the optimizer see (and often inline) the
    /// callee and skip the C call boundary. The rare effectful-argument case still defers to
    /// `bl_app_global` for identical continuation composition. Disabled by `BL_NO_DIRECTCALL`.
    directcall: bool,
    /// The calling convention used for every lifted function (`TAILCC` on the native target,
    /// LLVM's ordinary C convention — numeric `0` — on `wasm32`). LLVM's wasm32 backend rejects
    /// `tailcc` outright ("WebAssembly doesn't support non-C calling conventions"): `wasm32-unknown-
    /// unknown` predates the (still-nonstandard) wasm tail-call proposal in this LLVM version, so
    /// there is no calling convention it could lower `tailcc` to. Falling back to the ordinary C
    /// convention on this target is a real, honest trade-off (see `musttail_ok` below), not a
    /// silent behavior change: values still round-trip through the same `ptr (ptr, ptr)` signature
    /// either way, so this only affects register/stack ABI details a caller never observes.
    call_conv: u32,
    /// Whether `musttail` tail-call markers are sound to emit at all on this target. LLVM's wasm32
    /// backend cannot guarantee tail calls (no wasm tail-call-proposal codegen in this LLVM
    /// version), so marking a call `musttail` there would be asking the backend for a guarantee it
    /// cannot give — silently *not* an error at emission time, just a lost optimization at best or
    /// a backend assertion at worst. We emit ordinary (non-`musttail`) calls on wasm32 instead: this
    /// is the one honest scope limitation of the wasm target beyond `wasm_rt.c`'s own — deep
    /// non-structural recursion still terminates (compiled the same, driven by the Delay
    /// trampoline's `later`/`force` for anything the elaborator judged genuinely non-structural
    /// exactly as on native — see `wasm_rt.c`'s `bl_force`), but the *mutual-tail-call* loops this
    /// backend compiles as a native `musttail` loop on every other target instead grow the wasm call
    /// stack there. wasm32 has no fixed native call-stack-depth guarantee to begin with (a wasm
    /// engine enforces its own configurable limit), so this is a quantitative, not qualitative,
    /// difference — documented here rather than silently shipped.
    musttail_ok: bool,
    /// The width, in bytes, of a `BlValue` pointer on the target: `8` on native (x86_64/aarch64),
    /// `4` on `wasm32`. `BlObj`'s `fields[]` array is a C `struct BlObj *fields[]` — its element
    /// stride is the target's *pointer* size, which is NOT the fixed 8-byte width of the `header`
    /// itself (`{ u32 tag, u32 nfields, u64 aux }` is fixed-width regardless of target). Every field
    /// GEP (`load_field`/`store_field`) must scale by this, not a hardcoded `8`: a wasm32 program
    /// with a 2+-field object (any closure capturing 2+ values, an OpNode, a 2-tuple, …) computed
    /// with a hardcoded 8-byte stride reads/writes 4 bytes *past* where the real 4-byte-wide field
    /// actually lives once `k >= 1` — silently reading adjacent heap garbage. This is exactly what
    /// the wasm target's headline "uninitialized element" `call_indirect` traps turned out to be:
    /// a self-recursive closure's second captured field (`k=1`) read at byte offset 24 (native's
    /// `16 + 1*8`) instead of the correct wasm offset 20 (`16 + 1*4`), landing 4 bytes past a
    /// 24-byte object into whatever the allocator placed next.
    ptr_bytes: u64,
}

impl<'ctx> Codegen<'ctx> {
    fn with_tags(
        context: &'ctx Context,
        name: &str,
        con_tags: HashMap<blight_kernel::ConName, u64>,
    ) -> Self {
        Self::with_tags_for_target(context, name, con_tags, Target::Native)
    }

    fn with_tags_for_target(
        context: &'ctx Context,
        name: &str,
        con_tags: HashMap<blight_kernel::ConName, u64>,
        target: Target,
    ) -> Self {
        let module = context.create_module(name);
        let builder = context.create_builder();
        let is_wasm = matches!(target, Target::Wasm32);
        Codegen {
            context,
            module,
            builder,
            con_tags,
            aliasmeta: std::env::var_os("BL_NO_ALIASMETA").is_none(),
            directcall: std::env::var_os("BL_NO_DIRECTCALL").is_none(),
            call_conv: if is_wasm { 0 } else { TAILCC },
            musttail_ok: !is_wasm,
            ptr_bytes: if is_wasm { 4 } else { 8 },
        }
    }

    /// Mark `call` `musttail` iff both the caller requested it (`mt`, already gated on lexical
    /// position/pending arena leaves by callers) and the target's backend can actually guarantee
    /// tail calls (`musttail_ok`; see that field's doc comment). Centralizing this (rather than
    /// repeating `if mt && self.musttail_ok` at every one of `emit_tail`'s call sites) makes the
    /// wasm carve-out a single, auditable point.
    fn mark_musttail(&self, call: CallSiteValue<'ctx>, mt: bool) {
        if mt && self.musttail_ok {
            call.set_tail_call_kind(LLVMTailCallKind::LLVMTailCallKindMustTail);
        }
    }

    /// Tag a *just-built* load as `!invariant.load`. Sound **only** for reads of immutable memory —
    /// object headers (tag/aux) and constructor/closure fields — never the GC-mutated root slots or
    /// env slot. No-op when alias metadata is disabled.
    fn mark_invariant(&self, loaded: inkwell::values::BasicValueEnum<'ctx>) {
        if !self.aliasmeta {
            return;
        }
        if let Some(inst) = loaded.as_instruction_value() {
            let kind = self.context.get_kind_id("invariant.load");
            let node = self.context.metadata_node(&[]);
            let _ = inst.set_metadata(node, kind);
        }
    }

    /// The tag stamped into a `Con` object: the constructor's declaration index when known (from the
    /// signature), else a stable name-derived fallback for signature-less test programs.
    fn con_index(&self, con: &blight_kernel::ConName) -> u64 {
        if let Some(&t) = self.con_tags.get(con) {
            return t;
        }
        con_index_fallback(con)
    }

    fn ptr_ty(&self) -> inkwell::types::PointerType<'ctx> {
        self.context.ptr_type(AddressSpace::default())
    }

    /// `ptr (ptr, ptr)` — the type of every lifted function.
    fn func_ty(&self) -> inkwell::types::FunctionType<'ctx> {
        let p = self.ptr_ty();
        p.fn_type(&[p.into(), p.into()], false)
    }

    /// Declare a runtime intrinsic with the given parameter and return pointer-ness. All Blight
    /// values are pointers; integer/aux parameters use i64/i32.
    fn declare_runtime(&self) {
        let p = self.ptr_ty();
        let i64t = self.context.i64_type();
        let i32t = self.context.i32_type();
        let void = self.context.void_type();

        // bl_con(i64 ctor, i32 nfields) -> ptr
        let con_ty = p.fn_type(&[i64t.into(), i32t.into()], false);
        self.module
            .add_function(sym::CON, con_ty, Some(Linkage::External));
        // bl_alloc(i32 tag, i32 nfields, i64 aux) -> ptr
        let alloc_ty = p.fn_type(&[i32t.into(), i32t.into(), i64t.into()], false);
        self.module
            .add_function(sym::ALLOC, alloc_ty, Some(Linkage::External));
        // bl_gc_poll() -> void
        let poll_ty = void.fn_type(&[], false);
        self.module
            .add_function(sym::GC_POLL, poll_ty, Some(Linkage::External));
        // bl_gc_push_root(ptr slot) -> void
        let push_root_ty = void.fn_type(&[p.into()], false);
        self.module
            .add_function(sym::GC_PUSH_ROOT, push_root_ty, Some(Linkage::External));
        // bl_gc_pop_roots(i64 n) -> void
        let pop_roots_ty = void.fn_type(&[i64t.into()], false);
        self.module
            .add_function(sym::GC_POP_ROOTS, pop_roots_ty, Some(Linkage::External));
        // bl_force(ptr) -> ptr
        let force_ty = p.fn_type(&[p.into()], false);
        self.module
            .add_function(sym::FORCE, force_ty, Some(Linkage::External));
        // bl_perform(ptr, ptr, ptr) -> ptr  (effect/op name string ptrs + arg)
        let perform_ty = p.fn_type(&[p.into(), p.into(), p.into()], false);
        self.module
            .add_function(sym::PERFORM, perform_ty, Some(Linkage::External));
        // bl_handle_clo(ptr body_clo, ptr ret_clo, i64 n_ops, ptr op_names, ptr op_clos) -> ptr
        let handle_ty = p.fn_type(
            &[p.into(), p.into(), i64t.into(), p.into(), p.into()],
            false,
        );
        self.module
            .add_function(sym::HANDLE_CLO, handle_ty, Some(Linkage::External));
        // bl_app(ptr f, ptr a) -> ptr  (OpNode-aware application / delimited-continuation capture)
        let app_ty = p.fn_type(&[p.into(), p.into()], false);
        self.module
            .add_function(sym::APP, app_ty, Some(Linkage::External));
        // bl_app_global(ptr fnptr, ptr a) -> ptr  (A3: captureless direct call, null env)
        let app_global_ty = p.fn_type(&[p.into(), p.into()], false);
        self.module
            .add_function(sym::APP_GLOBAL, app_global_ty, Some(Linkage::External));
        // bl_con_bubble(ptr obj) -> ptr  (OpNode-aware Con/Tuple construction)
        let con_bubble_ty = p.fn_type(&[p.into()], false);
        self.module
            .add_function(sym::CON_BUBBLE, con_bubble_ty, Some(Linkage::External));
        // bl_int(i64) -> ptr
        let int_ty = p.fn_type(&[i64t.into()], false);
        self.module
            .add_function(sym::INT, int_ty, Some(Linkage::External));
        // bl_int_val(ptr) -> i64 : read an int payload, decoding a tagged immediate (M21).
        let int_val_ty = i64t.fn_type(&[p.into()], false);
        self.module
            .add_function(sym::INT_VAL, int_val_ty, Some(Linkage::External));
        // bl_arena_enter() -> void ; bl_arena_leave() -> void
        let arena_scope_ty = void.fn_type(&[], false);
        self.module
            .add_function(sym::ARENA_ENTER, arena_scope_ty, Some(Linkage::External));
        self.module
            .add_function(sym::ARENA_LEAVE, arena_scope_ty, Some(Linkage::External));
        // bl_arena_alloc(i32 tag, i32 nfields, i64 aux) -> ptr (same shape as bl_alloc)
        self.module
            .add_function(sym::ARENA_ALLOC, alloc_ty, Some(Linkage::External));
        // bl_write_barrier(ptr obj, ptr val) -> void
        let wb_ty = void.fn_type(&[p.into(), p.into()], false);
        self.module
            .add_function(sym::WRITE_BARRIER, wb_ty, Some(Linkage::External));
        // Machine-word Nat helpers (numeric.c, M20): binary ops take two ptrs, pred takes one,
        // from_u64 takes an i64; all return a fresh BL_NAT ptr.
        let nat_bin_ty = p.fn_type(&[p.into(), p.into()], false);
        self.module
            .add_function(sym::NAT_ADD, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::NAT_MUL, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::NAT_SUB, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::NAT_MIN, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::NAT_MAX, nat_bin_ty, Some(Linkage::External));
        let nat_un_ty = p.fn_type(&[p.into()], false);
        self.module
            .add_function(sym::NAT_PRED, nat_un_ty, Some(Linkage::External));
        let nat_from_ty = p.fn_type(&[i64t.into()], false);
        self.module
            .add_function(sym::NAT_FROM_U64, nat_from_ty, Some(Linkage::External));
        // bl_string_from_codepoints(ptr cps, i64 n) -> ptr : allocate a packed BL_STRING from a
        // contiguous codepoint run (A2). Used for folded `String` literals.
        let str_from_ty = p.fn_type(&[p.into(), i64t.into()], false);
        self.module.add_function(
            sym::STRING_FROM_CODEPOINTS,
            str_from_ty,
            Some(Linkage::External),
        );
        // bl_nat_to_con(ptr) -> ptr : materialize one inductive layer for a generic destructuring
        // reader (emit_case). Identity on a real Zero/Succ Con.
        self.module
            .add_function(sym::NAT_TO_CON, nat_un_ty, Some(Linkage::External));
        // bl_string_to_con(ptr) -> ptr : materialize one inductive `empty`/`push` layer of a packed
        // BL_STRING for a generic destructuring reader (emit_case). Identity on any non-BL_STRING
        // value (a real Con, a materialized Nat, etc.), so it composes after NAT_TO_CON (A2).
        self.module
            .add_function(sym::STRING_TO_CON, nat_un_ty, Some(Linkage::External));
        // No-alloc Nat peel (numeric.c, M25): `bl_nat_is_succ(ptr) -> i64` (the inductive tag) and
        // `bl_nat_pred_value(ptr) -> ptr` (the Succ predecessor). Let `emit_case` destructure a
        // fast-`Nat` loop driver with zero allocation per step.
        let nat_is_succ_ty = i64t.fn_type(&[p.into()], false);
        self.module
            .add_function(sym::NAT_IS_SUCC, nat_is_succ_ty, Some(Linkage::External));
        self.module
            .add_function(sym::NAT_PRED_VALUE, nat_un_ty, Some(Linkage::External));
        // Fixed-point Float helpers (numeric.c, M23): binary ops take two `mkfloat` ptrs, neg takes
        // one; all return a fresh `mkfloat` ptr over the scaled Int mantissa. Same ptr signatures as
        // the Nat helpers.
        self.module
            .add_function(sym::FLOAT_ADD, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::FLOAT_SUB, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::FLOAT_MUL, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::FLOAT_DIV, nat_bin_ty, Some(Linkage::External));
        self.module
            .add_function(sym::FLOAT_NEG, nat_un_ty, Some(Linkage::External));
    }

    fn rt(&self, name: &str) -> FunctionValue<'ctx> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| panic!("runtime intrinsic {name} not declared"))
    }

    fn emit_program(&self, prog: &AnfProgram) -> Result<(), String> {
        self.declare_runtime();

        // Declare all lifted functions with tailcc.
        let mut funcs: HashMap<String, FunctionValue<'ctx>> = HashMap::new();
        for f in &prog.funcs {
            let fv = self.module.add_function(&f.name, self.func_ty(), None);
            fv.set_call_conventions(self.call_conv);
            // The lifted functions are pure: they never write *through* their `env`/`arg` pointers
            // (construction always allocates fresh objects). Marking both params `readonly` lets
            // LLVM treat reads through them as non-clobbered by stores. (We deliberately do *not*
            // add `noalias`: a captured argument can legitimately make `env` and `arg` alias.)
            if self.aliasmeta {
                let kind = inkwell::attributes::Attribute::get_named_enum_kind_id("readonly");
                if kind != 0 {
                    let attr = self.context.create_enum_attribute(kind, 0);
                    use inkwell::attributes::AttributeLoc;
                    fv.add_attribute(AttributeLoc::Param(0), attr);
                    fv.add_attribute(AttributeLoc::Param(1), attr);
                }
            }
            funcs.insert(f.name.clone(), fv);
        }
        // Stash funcs via interior reassembly: rebuild a Codegen view with funcs populated. Since
        // `self` is shared, use a local map passed explicitly.
        let funcs_ref = &funcs;
        // P5 (roadmap Wave 10 / code mobility): the codegen-emitted function-index table is authored
        // as a small separate C translation unit by `driver.rs` (`code_table_source_for`), not as
        // LLVM IR here — see that function's doc comment for why (chiefly: it must link into every
        // real `blight build` binary without becoming a hard link-time dependency for the many C-only
        // runtime test harnesses that link `serialize.c` but never build a Blight program at all).

        // Emit each function body.
        for f in &prog.funcs {
            let fv = funcs_ref[&f.name];
            let entry = self.context.append_basic_block(fv, "entry");
            self.builder.position_at_end(entry);
            // A dedicated builder pinned at the entry block for root-slot allocas.
            let entry_builder = self.context.create_builder();
            entry_builder.position_at_end(entry);
            // GC safepoint at entry.
            self.poll_gc();
            // Parameters: env = param 0, arg = param 1. Both are rooted in entry-block slots so a
            // collection can relocate the objects they point at; reads reload from the slots.
            let argp = fv.get_nth_param(1).unwrap().into_pointer_value();
            let envp = fv.get_nth_param(0).unwrap().into_pointer_value();
            let mut fr = Frame {
                entry: entry_builder,
                entry_bb: entry,
                env_slot: self.ptr_ty().const_null(),
                slots: Vec::new(),
            };
            fr.env_slot = self.new_root_slot(&mut fr, envp, "env");
            // Local 0 inside the body = the argument.
            self.push_local(&mut fr, argp);
            self.emit_tail(&f.body, fv, &mut fr, funcs_ref, true, 0)?;
        }

        // P0 (Linux x86_64 fix): emit the strong `bl_call_tailcc` adapter. Lifted functions use the
        // `tailcc` convention on native, whose x86_64 register/stack ABI differs from C's — so the C
        // runtime (bl_apply1 / bl_app_global / the delay stepper / graphics) cannot call a lifted code
        // pointer through a plain C function pointer without corrupting the stack (segfault; the two
        // ABIs happen to coincide on arm64, which is why it only bit x86_64). Those sites route through
        // this adapter instead: a C-callable (ccc) function that performs the closure-code indirect
        // call under the lifted convention. Native only — on wasm the lifted convention is already
        // ccc, so the weak ccc fallback in effects.c is correct and no strong override is needed.
        if self.call_conv == TAILCC {
            let p = self.ptr_ty();
            let adapter_ty = p.fn_type(&[p.into(), p.into(), p.into()], false);
            let adapter =
                self.module
                    .add_function("bl_call_tailcc", adapter_ty, Some(Linkage::External));
            let abb = self.context.append_basic_block(adapter, "entry");
            let ab = self.context.create_builder();
            ab.position_at_end(abb);
            let fnp = adapter.get_nth_param(0).unwrap().into_pointer_value();
            let a0 = adapter.get_nth_param(1).unwrap();
            let a1 = adapter.get_nth_param(2).unwrap();
            let call = ab
                .build_indirect_call(self.func_ty(), fnp, &[a0.into(), a1.into()], "adapt")
                .unwrap();
            call.set_call_convention(self.call_conv);
            let r = call.try_as_basic_value().unwrap_basic();
            ab.build_return(Some(&r)).unwrap();

            // Tailcc trampoline for the runtime's delimited continuation (`bl_cont_apply`, effects.c).
            // A continuation `k` is a BL_CLOSURE whose code is an ordinary C (ccc) function, but user
            // code applies `(k v)` through the pure application path — `build_indirect_call` under the
            // lifted (tailcc) convention (see `Tail::TailCall`) — where a ccc callee corrupts the
            // x86_64 stack. Emit a STRONG tailcc wrapper that ccc-calls the C impl; `make_cont` stores
            // THIS as the continuation's code pointer, so both the IR path and `bl_apply1` reach it as
            // tailcc, uniformly. effects.c ships a weak ccc `bl_cont_apply_tc` for C-only harnesses.
            let cont_impl = self
                .module
                .get_function("bl_cont_apply")
                .unwrap_or_else(|| {
                    self.module.add_function(
                        "bl_cont_apply",
                        self.func_ty(),
                        Some(Linkage::External),
                    )
                });
            let cont_tc = self.module.add_function(
                "bl_cont_apply_tc",
                self.func_ty(),
                Some(Linkage::External),
            );
            cont_tc.set_call_conventions(self.call_conv); // tailcc entry
            let cbb = self.context.append_basic_block(cont_tc, "entry");
            let cb = self.context.create_builder();
            cb.position_at_end(cbb);
            let c0 = cont_tc.get_nth_param(0).unwrap();
            let c1 = cont_tc.get_nth_param(1).unwrap();
            // Plain ccc call to the C impl (do NOT set tailcc on this call).
            let ccall = cb
                .build_call(cont_impl, &[c0.into(), c1.into()], "cont_impl")
                .unwrap();
            let cr = ccall.try_as_basic_value().unwrap_basic();
            cb.build_return(Some(&cr)).unwrap();
        }

        // Emit `bl_program_entry() -> ptr` wrapping the entry tail.
        let entry_fn =
            self.module
                .add_function("bl_program_entry", self.ptr_ty().fn_type(&[], false), None);
        let bb = self.context.append_basic_block(entry_fn, "entry");
        self.builder.position_at_end(bb);
        let entry_builder = self.context.create_builder();
        entry_builder.position_at_end(bb);
        self.poll_gc();
        let null = self.ptr_ty().const_null();
        let mut fr = Frame {
            entry: entry_builder,
            entry_bb: bb,
            env_slot: self.ptr_ty().const_null(),
            slots: Vec::new(),
        };
        fr.env_slot = self.new_root_slot(&mut fr, null, "env");
        self.push_local(&mut fr, null);
        // The entry uses the C calling convention (called from `main`), so tail calls here are
        // ordinary calls — `musttail` would be invalid across calling conventions.
        self.emit_tail(&prog.entry, entry_fn, &mut fr, funcs_ref, false, 0)?;

        if let Err(e) = self.module.verify() {
            return Err(format!(
                "LLVM module verification failed: {}",
                e.to_string()
            ));
        }
        Ok(())
    }

    fn poll_gc(&self) {
        let _ = self.builder.build_call(self.rt(sym::GC_POLL), &[], "");
    }

    /// Allocate a fresh root slot (`alloca ptr`) in the function entry block, initialise it to
    /// `val`, register it as a GC root, and return the slot pointer. Placing the alloca in the entry
    /// block keeps the native stack bounded across `musttail` loop iterations.
    fn new_root_slot(
        &self,
        fr: &mut Frame<'ctx>,
        val: PointerValue<'ctx>,
        name: &str,
    ) -> PointerValue<'ctx> {
        // Anchor the alloca at the *top* of the entry block. Allocas requested mid-body (nested
        // `let`/case binders) must not append after the entry block's terminator (which already
        // exists by then), so we always reposition the dedicated entry builder before the first
        // instruction. This also keeps the native frame bounded across `musttail` loop iterations.
        let entry_bb = fr.entry_bb;
        match entry_bb.get_first_instruction() {
            Some(first) => fr.entry.position_before(&first),
            None => fr.entry.position_at_end(entry_bb),
        }
        let slot = fr.entry.build_alloca(self.ptr_ty(), name).unwrap();
        self.builder.build_store(slot, val).unwrap();
        self.builder
            .build_call(self.rt(sym::GC_PUSH_ROOT), &[slot.into()], "")
            .unwrap();
        slot
    }

    /// Push a new innermost local: bind `val` into a fresh rooted slot.
    fn push_local(&self, fr: &mut Frame<'ctx>, val: PointerValue<'ctx>) {
        let slot = self.new_root_slot(fr, val, "local");
        fr.slots.push(slot);
    }

    /// Pop `n` innermost locals' slots (the matching `bl_gc_pop_roots` is emitted once at exit).
    fn pop_locals(&self, fr: &mut Frame<'ctx>, n: usize) {
        for _ in 0..n {
            fr.slots.pop();
        }
    }

    /// Push a short-lived GC root that is deliberately *not* part of the de Bruijn frame
    /// (`fr.slots`), so it does not shift the indices that `atom_val` resolves. Used to keep a value
    /// (e.g. a callee closure) alive across an allocating sub-evaluation within one straight-line
    /// `emit_comp`/`emit_tail` step. Returns the slot pointer to reload from. Must be balanced by
    /// `pop_temp_root` before any terminator's `emit_pop_roots` (the runtime root stack is a LIFO
    /// count; temps are always the innermost, so they pop first).
    fn push_temp_root(&self, fr: &mut Frame<'ctx>, val: PointerValue<'ctx>) -> PointerValue<'ctx> {
        // Reuse the entry-block alloca machinery (bounded native frame across musttail loops), but do
        // NOT record the slot in `fr.slots`.
        let entry_bb = fr.entry_bb;
        match entry_bb.get_first_instruction() {
            Some(first) => fr.entry.position_before(&first),
            None => fr.entry.position_at_end(entry_bb),
        }
        let slot = fr.entry.build_alloca(self.ptr_ty(), "temp_root").unwrap();
        self.builder.build_store(slot, val).unwrap();
        self.builder
            .build_call(self.rt(sym::GC_PUSH_ROOT), &[slot.into()], "")
            .unwrap();
        slot
    }

    /// Balance a single `push_temp_root` (emits `bl_gc_pop_roots(1)`; pops the innermost root).
    fn pop_temp_root(&self) {
        let i64t = self.context.i64_type();
        self.builder
            .build_call(
                self.rt(sym::GC_POP_ROOTS),
                &[i64t.const_int(1, false).into()],
                "",
            )
            .unwrap();
    }

    /// Emit the balancing `bl_gc_pop_roots(n)` just before a terminator, where `n` is the number of
    /// roots currently live on this control path: the env slot plus every value slot in scope. The
    /// runtime root stack is a count, and along any path exactly this many `bl_gc_push_root` calls
    /// have executed, so this restores it precisely.
    fn emit_pop_roots(&self, fr: &Frame<'ctx>) {
        let n = fr.slots.len() + 1; // +1 for the env slot
        let i64t = self.context.i64_type();
        self.builder
            .build_call(
                self.rt(sym::GC_POP_ROOTS),
                &[i64t.const_int(n as u64, false).into()],
                "",
            )
            .unwrap();
    }

    /// Resolve an atom to an LLVM pointer value, reloading from rooted slots so the value reflects
    /// any relocation a GC may have performed since the slot was written.
    fn atom_val(
        &self,
        a: &Atom,
        fr: &Frame<'ctx>,
        funcs: &HashMap<String, FunctionValue<'ctx>>,
    ) -> PointerValue<'ctx> {
        match a {
            Atom::Var(i) => {
                // de Bruijn index from the innermost local; load the current value from its slot.
                let n = fr.slots.len();
                let slot = fr.slots[n - 1 - *i];
                self.builder
                    .build_load(self.ptr_ty(), slot, "var")
                    .unwrap()
                    .into_pointer_value()
            }
            Atom::EnvRef(k) => {
                // Reload env from its slot (it may have moved), then load env->fields[k].
                let env = self
                    .builder
                    .build_load(self.ptr_ty(), fr.env_slot, "env")
                    .unwrap()
                    .into_pointer_value();
                self.load_field(env, *k)
            }
            Atom::Global(g) => {
                // A bare global function as a value: wrap it in a 1-field closure with no env.
                let fv = funcs.get(g).unwrap_or_else(|| panic!("unknown global {g}"));
                self.make_closure(*fv, &[])
            }
            Atom::Erased => self.ptr_ty().const_null(),
        }
    }

    /// Load the `k`-th field of a BlObj `obj`. The C layout is `{ i32 tag, i32 nfields, i64 aux,
    /// ptr fields[] }` = a 16-byte header then the pointer array. We GEP into an i8 array.
    fn load_field(&self, obj: PointerValue<'ctx>, k: usize) -> PointerValue<'ctx> {
        let i8t = self.context.i8_type();
        let i64t = self.context.i64_type();
        let header = 16u64;
        let offset = header + (k as u64) * self.ptr_bytes;
        let gep = unsafe {
            self.builder
                .build_gep(i8t, obj, &[i64t.const_int(offset, false)], "fldptr")
                .unwrap()
        };
        let v = self.builder.build_load(self.ptr_ty(), gep, "fld").unwrap();
        self.mark_invariant(v);
        v.into_pointer_value()
    }

    /// Read the integer payload of `obj` through the runtime `bl_int_val`, which decodes a tagged
    /// immediate (M21) or reads a boxed `BL_INT`'s `aux`. Used by `IntPrim` since operands may be
    /// unboxed.
    fn int_val(&self, obj: PointerValue<'ctx>) -> inkwell::values::IntValue<'ctx> {
        self.builder
            .build_call(self.rt(sym::INT_VAL), &[obj.into()], "intval")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_int_value()
    }

    /// Box a 64-bit integer into a `BL_INT` value via the runtime `bl_int`, which returns a tagged
    /// immediate when the value fits (M21 unboxing) and a heap box otherwise. Routing through the
    /// runtime keeps the unbox/box decision in one place and observationally identical to a box.
    fn box_int(&self, v: inkwell::values::IntValue<'ctx>) -> PointerValue<'ctx> {
        self.builder
            .build_call(self.rt(sym::INT), &[v.into()], "int")
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value()
    }

    /// Store `val` into field `k` of a freshly-allocated `obj`. Construction-time stores need no
    /// write barrier: the object was just allocated (it is the youngest), so no field store can
    /// create an old→young edge. The generational write barrier ([`sym::WRITE_BARRIER`]) is reserved
    /// for genuine *post-initialization* mutations (the runtime's delay/effect trampolines), not
    /// these initializing stores. `_alloc` is accepted for symmetry with the allocation site.
    fn store_field_barrier(
        &self,
        obj: PointerValue<'ctx>,
        k: usize,
        val: PointerValue<'ctx>,
        _alloc: Alloc,
    ) {
        self.store_field(obj, k, val);
    }

    fn store_field(&self, obj: PointerValue<'ctx>, k: usize, val: PointerValue<'ctx>) {
        let i8t = self.context.i8_type();
        let i64t = self.context.i64_type();
        let header = 16u64;
        let offset = header + (k as u64) * self.ptr_bytes;
        let gep = unsafe {
            self.builder
                .build_gep(i8t, obj, &[i64t.const_int(offset, false)], "fldptr")
                .unwrap()
        };
        self.builder.build_store(gep, val).unwrap();
    }

    /// Allocate a `nfields`-field object with the given `tag`/`aux`, choosing the GC heap or the
    /// current region arena per the [`Alloc`] tag (spec §3.5). Arena allocation never triggers a GC.
    fn alloc_obj(
        &self,
        tag: u64,
        nfields: u64,
        aux: u64,
        alloc: Alloc,
        name: &str,
    ) -> PointerValue<'ctx> {
        let i32t = self.context.i32_type();
        let i64t = self.context.i64_type();
        let sym = match alloc {
            Alloc::Gc => sym::ALLOC,
            Alloc::Arena => sym::ARENA_ALLOC,
        };
        self.builder
            .build_call(
                self.rt(sym),
                &[
                    i32t.const_int(tag, false).into(),
                    i32t.const_int(nfields, false).into(),
                    i64t.const_int(aux, false).into(),
                ],
                name,
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value()
    }

    fn make_closure(
        &self,
        fv: FunctionValue<'ctx>,
        caps: &[PointerValue<'ctx>],
    ) -> PointerValue<'ctx> {
        let obj = self.alloc_closure(fv, caps.len() as u64, Alloc::Gc);
        for (i, c) in caps.iter().enumerate() {
            self.store_field(obj, i, *c);
        }
        obj
    }

    /// Allocate (but do not populate) a closure object for `fv` with room for `nfields` captures,
    /// on the GC heap or current arena per `alloc`. The function pointer is stored in `header.aux`
    /// as an integer and is deliberately *not* a traced field (it points at code, not heap), so the
    /// GC traces only the captured environment. Callers must store captures afterwards, reloading
    /// each from its rooted slot (this allocation may move other live objects).
    fn alloc_closure(
        &self,
        fv: FunctionValue<'ctx>,
        nfields: u64,
        alloc: Alloc,
    ) -> PointerValue<'ctx> {
        let i64t = self.context.i64_type();
        let fnptr = fv.as_global_value().as_pointer_value();
        let fnint = self.builder.build_ptr_to_int(fnptr, i64t, "fnint").unwrap();
        let sym = match alloc {
            Alloc::Gc => sym::ALLOC,
            Alloc::Arena => sym::ARENA_ALLOC,
        };
        let i32t = self.context.i32_type();
        self.builder
            .build_call(
                self.rt(sym),
                &[
                    i32t.const_int(tag::CLOSURE, false).into(),
                    i32t.const_int(nfields, false).into(),
                    fnint.into(),
                ],
                "clo",
            )
            .unwrap()
            .try_as_basic_value()
            .unwrap_basic()
            .into_pointer_value()
    }

    /// Load the closure's function pointer from `obj`'s header `aux` field (offset 8, i64), as a
    /// callable `ptr`.
    fn load_fnptr(&self, obj: PointerValue<'ctx>) -> PointerValue<'ctx> {
        let i8t = self.context.i8_type();
        let i64t = self.context.i64_type();
        let aux_gep = unsafe {
            self.builder
                .build_gep(i8t, obj, &[i64t.const_int(8, false)], "auxptr")
                .unwrap()
        };
        let fnint_v = self.builder.build_load(i64t, aux_gep, "fnint").unwrap();
        self.mark_invariant(fnint_v);
        let fnint = fnint_v.into_int_value();
        self.builder
            .build_int_to_ptr(fnint, self.ptr_ty(), "fnptr")
            .unwrap()
    }

    /// Load an object's tag (the `uint32_t` at header offset 0) as an i32 value. Caller must ensure
    /// `obj` is boxed (not a tagged immediate), else this faults.
    fn load_tag(&self, obj: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i32t = self.context.i32_type();
        let v = self.builder.build_load(i32t, obj, "tag").unwrap();
        self.mark_invariant(v);
        v.into_int_value()
    }

    /// True (i1) iff `v` is a tagged immediate (low pointer bit set, M21). Immediates are never
    /// OpNodes and must not be dereferenced.
    fn is_immediate(&self, v: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i64t = self.context.i64_type();
        let asint = self.builder.build_ptr_to_int(v, i64t, "imm_int").unwrap();
        let low = self
            .builder
            .build_and(asint, i64t.const_int(1, false), "imm_bit")
            .unwrap();
        self.builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                low,
                i64t.const_int(0, false),
                "is_imm",
            )
            .unwrap()
    }

    /// Emit `clo.tag == OPNODE || arg.tag == OPNODE` as an i1 — the guard that routes an application
    /// through the OpNode-aware `bl_app` (delimited-continuation capture) instead of a direct call.
    /// Immediate operands (M21 unboxing) are never OpNodes; the tag load is gated so an immediate's
    /// non-pointer bit pattern is never dereferenced. Implemented as
    /// `(!imm(clo) && tag(clo)==OP) || (!imm(arg) && tag(arg)==OP)` using `select` to feed a known
    /// non-OPNODE tag for immediates instead of loading from them.
    fn either_is_opnode(&self, clo: PointerValue<'ctx>, arg: PointerValue<'ctx>) -> IntValue<'ctx> {
        let c_is = self.one_is_opnode(clo);
        let a_is = self.one_is_opnode(arg);
        self.builder.build_or(c_is, a_is, "either_op").unwrap()
    }

    /// `!immediate(v) && tag(v) == OPNODE`, never dereferencing an immediate. We branch on the
    /// immediate bit so the `load_tag` only executes on the boxed path; a `phi` merges the result.
    fn one_is_opnode(&self, v: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i32t = self.context.i32_type();
        let bool_ty = self.context.bool_type();
        let op = i32t.const_int(crate::runtime::tag::OPNODE, false);
        let is_imm = self.is_immediate(v);
        let cur_fn = self
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();
        let boxed_bb = self.context.append_basic_block(cur_fn, "op_boxed");
        let cont_bb = self.context.append_basic_block(cur_fn, "op_cont");
        let pre_bb = self.builder.get_insert_block().unwrap();
        self.builder
            .build_conditional_branch(is_imm, cont_bb, boxed_bb)
            .unwrap();
        // Boxed path: load the tag and compare to OPNODE.
        self.builder.position_at_end(boxed_bb);
        let t = self.load_tag(v);
        let is_op = self
            .builder
            .build_int_compare(inkwell::IntPredicate::EQ, t, op, "is_op")
            .unwrap();
        self.builder.build_unconditional_branch(cont_bb).unwrap();
        let boxed_end = self.builder.get_insert_block().unwrap();
        // Continuation: phi false (immediate) / is_op (boxed).
        self.builder.position_at_end(cont_bb);
        let phi = self.builder.build_phi(bool_ty, "is_op_phi").unwrap();
        phi.add_incoming(&[(&bool_ty.const_int(0, false), pre_bb), (&is_op, boxed_end)]);
        phi.as_basic_value().into_int_value()
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_tail(
        &self,
        t: &Tail,
        cur_fn: FunctionValue<'ctx>,
        fr: &mut Frame<'ctx>,
        funcs: &HashMap<String, FunctionValue<'ctx>>,
        musttail: bool,
        arena_scopes: usize,
    ) -> Result<(), String> {
        match t {
            Tail::Ret(a) => {
                let v = self.atom_val(a, fr, funcs);
                // Close any enclosing region arenas at the lexical boundary, before returning the
                // (GC-heap) result value (spec §3.5 / §7.4 safepoint discipline).
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                self.builder.build_return(Some(&v)).unwrap();
            }
            Tail::Let(comp, rest) => {
                let v = self.emit_comp(comp, fr, funcs);
                self.push_local(fr, v);
                self.emit_tail(rest, cur_fn, fr, funcs, musttail, arena_scopes)?;
                self.pop_locals(fr, 1);
            }
            Tail::TailCall(f, a) => {
                // GC hazard (same as `Comp::Call`): `atom_val(f)` may allocate (a `Global` callee
                // materializes a closure), and `atom_val(a)` may then collect — which would relocate
                // that fresh closure and leave a raw `clo` SSA value stale. Root `clo` in a temp slot
                // (kept *out* of the de Bruijn frame so `a`'s indices still resolve correctly) across
                // the argument evaluation, reload it, then release the temp: from here `clo`/`arg` are
                // SSA values consumed directly, and the callee roots its own arguments.
                let clo0 = self.atom_val(f, fr, funcs);
                let clo_slot = self.push_temp_root(fr, clo0);
                let arg = self.atom_val(a, fr, funcs);
                let clo = self
                    .builder
                    .build_load(self.ptr_ty(), clo_slot, "tc_clo_reload")
                    .unwrap()
                    .into_pointer_value();
                self.pop_temp_root();
                // A region never lexically wraps a bare tail call (the elaborator/lowering keep the
                // arena-leave at the scope boundary, before the tail position). If we somehow have
                // pending leaves here, emit them first and drop musttail — correctness over the TCO.
                let mt = musttail && arena_scopes == 0;
                // OpNode-aware tail call: if either operand is a bubbling effect, route through the
                // delimited-continuation-capturing `bl_app`; otherwise take the fast direct (musttail)
                // call. The tag compare is cheap and preserves TCO for all pure recursion.
                let either_op = self.either_is_opnode(clo, arg);
                let op_bb = self.context.append_basic_block(cur_fn, "tc_op");
                let pure_bb = self.context.append_basic_block(cur_fn, "tc_pure");
                self.builder
                    .build_conditional_branch(either_op, op_bb, pure_bb)
                    .unwrap();

                // Effectful: bl_app(clo, arg), then return (after closing arenas / popping roots).
                self.builder.position_at_end(op_bb);
                let app = self
                    .builder
                    .build_call(self.rt(sym::APP), &[clo.into(), arg.into()], "tc_app")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                self.builder.build_return(Some(&app)).unwrap();

                // Pure: the original direct tailcc call.
                self.builder.position_at_end(pure_bb);
                let fnptr = self.load_fnptr(clo);
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                let call = self
                    .builder
                    .build_indirect_call(self.func_ty(), fnptr, &[clo.into(), arg.into()], "tc")
                    .unwrap();
                call.set_call_convention(self.call_conv);
                self.mark_musttail(call, mt);
                let v = call.try_as_basic_value().unwrap_basic();
                self.builder.build_return(Some(&v)).unwrap();
            }
            Tail::Jump(a) => {
                self.poll_gc();
                let arg = self.atom_val(a, fr, funcs);
                let env = self
                    .builder
                    .build_load(self.ptr_ty(), fr.env_slot, "env")
                    .unwrap()
                    .into_pointer_value();
                let mt = musttail && arena_scopes == 0;
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                let call = self
                    .builder
                    .build_indirect_call(
                        self.func_ty(),
                        cur_fn.as_global_value().as_pointer_value(),
                        &[env.into(), arg.into()],
                        "jmp",
                    )
                    .unwrap();
                call.set_call_convention(self.call_conv);
                self.mark_musttail(call, mt);
                let v = call.try_as_basic_value().unwrap_basic();
                self.builder.build_return(Some(&v)).unwrap();
            }
            Tail::TailCallGlobal(name, a) => {
                // M26: a captureless callee reads no environment, so we call its lifted function
                // directly (no per-step `MkClosure` alloc), passing a null env. Mirrors `Tail::Jump`
                // but targets a *different* function by name. Same OpNode-aware split as
                // `Tail::TailCallKnown`/`Comp::CallGlobal`: the argument may itself be a bubbling
                // effect (e.g. capspec/A3 can fuse a tail call whose argument is a just-`perform`ed
                // result), which must defer to the OpNode-aware `bl_app_global` rather than being fed
                // straight to the callee as an ordinary value.
                self.poll_gc();
                let arg = self.atom_val(a, fr, funcs);
                let callee = *funcs
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown function {name} in TailCallGlobal"));
                let fnptr = callee.as_global_value().as_pointer_value();
                let mt = musttail && arena_scopes == 0;
                let arg_is_op = self.one_is_opnode(arg);
                let op_bb = self.context.append_basic_block(cur_fn, "tcg_op");
                let pure_bb = self.context.append_basic_block(cur_fn, "tcg_pure");
                self.builder
                    .build_conditional_branch(arg_is_op, op_bb, pure_bb)
                    .unwrap();

                // Effectful: route through the OpNode-aware `bl_app_global`, then return.
                self.builder.position_at_end(op_bb);
                let app = self
                    .builder
                    .build_call(
                        self.rt(sym::APP_GLOBAL),
                        &[fnptr.into(), arg.into()],
                        "tcg_appg",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                self.builder.build_return(Some(&app)).unwrap();

                // Pure: the direct `tailcc`/`musttail` call with a null environment.
                self.builder.position_at_end(pure_bb);
                let null_env = self.ptr_ty().const_null();
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                let call = self
                    .builder
                    .build_indirect_call(
                        self.func_ty(),
                        fnptr,
                        &[null_env.into(), arg.into()],
                        "tcg",
                    )
                    .unwrap();
                call.set_call_convention(self.call_conv);
                self.mark_musttail(call, mt);
                let v = call.try_as_basic_value().unwrap_basic();
                self.builder.build_return(Some(&v)).unwrap();
            }
            Tail::TailCallKnown(name, env, a) => {
                // P10 defunc: a devirtualized tail apply. Identical to `Tail::TailCall` except the
                // callee is the statically-known lifted function `name` — so we use its module
                // function pointer directly instead of `load_fnptr(clo)` (the closure-header load the
                // analysis proved redundant). The closure object `env` is still passed as the first
                // (environment) argument, so the callee reads its captures exactly as before. Same GC
                // rooting and OpNode-aware split as `TailCall`: an effectful operand defers to
                // `bl_app(env, arg)` (unchanged semantics), the pure path is the direct `tailcc` call.
                let callee = *funcs
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown function {name} in TailCallKnown"));
                let clo0 = self.atom_val(env, fr, funcs);
                let clo_slot = self.push_temp_root(fr, clo0);
                let arg = self.atom_val(a, fr, funcs);
                let clo = self
                    .builder
                    .build_load(self.ptr_ty(), clo_slot, "tck_clo_reload")
                    .unwrap()
                    .into_pointer_value();
                self.pop_temp_root();
                let mt = musttail && arena_scopes == 0;
                let either_op = self.either_is_opnode(clo, arg);
                let op_bb = self.context.append_basic_block(cur_fn, "tck_op");
                let pure_bb = self.context.append_basic_block(cur_fn, "tck_pure");
                self.builder
                    .build_conditional_branch(either_op, op_bb, pure_bb)
                    .unwrap();

                // Effectful: route through the OpNode-aware `bl_app`, then return.
                self.builder.position_at_end(op_bb);
                let app = self
                    .builder
                    .build_call(self.rt(sym::APP), &[clo.into(), arg.into()], "tck_app")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                self.builder.build_return(Some(&app)).unwrap();

                // Pure: the direct `tailcc` call to the known lifted function (no fnptr load).
                self.builder.position_at_end(pure_bb);
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                let call = self
                    .builder
                    .build_call(callee, &[clo.into(), arg.into()], "tck")
                    .unwrap();
                call.set_call_convention(self.call_conv);
                self.mark_musttail(call, mt);
                let v = call.try_as_basic_value().unwrap_basic();
                self.builder.build_return(Some(&v)).unwrap();
            }
            Tail::Trampoline(a) => {
                let d = self.atom_val(a, fr, funcs);
                let v = self
                    .builder
                    .build_call(self.rt(sym::FORCE), &[d.into()], "force")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                self.builder.build_return(Some(&v)).unwrap();
            }
            Tail::Case(scrut, arms) => {
                self.emit_case(scrut, arms, cur_fn, fr, funcs, musttail, arena_scopes)?;
            }
            // `if-zero scrut then else` (T1a): a native `i64` compare-and-branch. Decode the
            // scrutinee's payload (`int_val`, tolerating a tagged-immediate or boxed `BL_INT`),
            // compare to `0`, and branch to one of two blocks. Each branch is itself a tail — it
            // emits its own terminator (return / tail-call / nested switch) — so there is no join
            // block or phi, exactly like the per-arm blocks of a `Case`. The branches bind no
            // variables, so (unlike `emit_case`) there is nothing to push/pop on the root frame.
            Tail::IfZero(scrut, then_, else_) => {
                let sval = self.atom_val(scrut, fr, funcs);
                let svi = self.int_val(sval);
                let zero = self.context.i64_type().const_zero();
                let is_zero = self
                    .builder
                    .build_int_compare(inkwell::IntPredicate::EQ, svi, zero, "ifz")
                    .unwrap();
                let then_bb = self.context.append_basic_block(cur_fn, "ifz_then");
                let else_bb = self.context.append_basic_block(cur_fn, "ifz_else");
                self.builder
                    .build_conditional_branch(is_zero, then_bb, else_bb)
                    .unwrap();
                self.builder.position_at_end(then_bb);
                self.emit_tail(then_, cur_fn, fr, funcs, musttail, arena_scopes)?;
                self.builder.position_at_end(else_bb);
                self.emit_tail(else_, cur_fn, fr, funcs, musttail, arena_scopes)?;
            }
            // A region scope: open an arena, emit the body with one more pending leave (each return
            // site inside closes it), then continue. The body itself drives the return; there is no
            // code after it in this block.
            Tail::Region(body) => {
                let _ = self.builder.build_call(self.rt(sym::ARENA_ENTER), &[], "");
                self.emit_tail(body, cur_fn, fr, funcs, musttail, arena_scopes + 1)?;
            }
            Tail::Handle {
                body,
                return_clause,
                op_clauses,
            } => {
                let body_v = self.atom_val(body, fr, funcs);
                let ret_v = self.atom_val(return_clause, fr, funcs);
                let n = op_clauses.len();
                let i64t = self.context.i64_type();
                let pt = self.ptr_ty();
                // Stack arrays: `op_names : [n x ptr]` (C strings) and `op_clos : [n x ptr]` (closure
                // values). `bl_handle_clo` reads `n` entries from each.
                let names_arr_ty = pt.array_type(n as u32);
                let clos_arr_ty = pt.array_type(n as u32);
                let names_alloca = self.builder.build_alloca(names_arr_ty, "op_names").unwrap();
                let clos_alloca = self.builder.build_alloca(clos_arr_ty, "op_clos").unwrap();
                for (i, (name, clo)) in op_clauses.iter().enumerate() {
                    let name_ptr = self.global_str(name);
                    let clo_v = self.atom_val(clo, fr, funcs);
                    let idx = i64t.const_int(i as u64, false);
                    let zero = i64t.const_zero();
                    let nslot = unsafe {
                        self.builder
                            .build_gep(names_arr_ty, names_alloca, &[zero, idx], "nslot")
                            .unwrap()
                    };
                    self.builder.build_store(nslot, name_ptr).unwrap();
                    let cslot = unsafe {
                        self.builder
                            .build_gep(clos_arr_ty, clos_alloca, &[zero, idx], "cslot")
                            .unwrap()
                    };
                    self.builder.build_store(cslot, clo_v).unwrap();
                }
                let names_ptr = self
                    .builder
                    .build_pointer_cast(names_alloca, pt, "names_ptr")
                    .unwrap();
                let clos_ptr = self
                    .builder
                    .build_pointer_cast(clos_alloca, pt, "clos_ptr")
                    .unwrap();
                let result = self
                    .builder
                    .build_call(
                        self.rt(sym::HANDLE_CLO),
                        &[
                            body_v.into(),
                            ret_v.into(),
                            i64t.const_int(n as u64, false).into(),
                            names_ptr.into(),
                            clos_ptr.into(),
                        ],
                        "handle",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic();
                self.emit_arena_leaves(arena_scopes);
                self.emit_pop_roots(fr);
                self.builder.build_return(Some(&result)).unwrap();
            }
        }
        Ok(())
    }

    /// Emit `n` `bl_arena_leave()` calls (closing nested region arenas, innermost first).
    fn emit_arena_leaves(&self, n: usize) {
        for _ in 0..n {
            let _ = self.builder.build_call(self.rt(sym::ARENA_LEAVE), &[], "");
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_case(
        &self,
        scrut: &Atom,
        arms: &[TailArm],
        cur_fn: FunctionValue<'ctx>,
        fr: &mut Frame<'ctx>,
        funcs: &HashMap<String, FunctionValue<'ctx>>,
        musttail: bool,
        arena_scopes: usize,
    ) -> Result<(), String> {
        let sval = self.atom_val(scrut, fr, funcs);
        let i8t = self.context.i8_type();
        let i64t = self.context.i64_type();

        // Fast-`Nat` loop driver (M25): if the arms are exactly the `Nat` eliminator shape —
        // `[Zero{binders:0}, Succ{binders:1}]` — read the tag WITHOUT materializing a `Succ` box.
        // `bl_nat_is_succ` is the inductive tag (0 = Zero, 1 = Succ) of a fast `BL_NAT`, computed by
        // reading the machine word (no allocation); the `Succ` arm's predecessor field is then
        // `bl_nat_pred_value` (a fast Nat, still no allocation). This turns a structural
        // `match fuel […]` loop from O(n) heap (one `bl_nat_to_con` `Succ` cell per step) into O(1)
        // heap. We keep the SAME switch + arm-block CFG as the generic path below (so tail-call /
        // `musttail` placement is identical — only the tag source and field source change);
        // observationally identical, gated by numeric_diff.c `check_peel`. Any other constructor
        // shape falls through to the generic `bl_nat_to_con` destructuring, never a miscompile.
        let nat_peel = is_nat_eliminator_shape(arms);
        // `sval` is reused inside each arm to extract fields: for the peel it stays the original
        // (un-materialized) fast Nat that `bl_nat_pred_value` reads; for the generic path it is the
        // materialized one-layer `Zero`/`Succ` Con that `load_field` GEPs into.
        let (tagv, sval) = if nat_peel {
            let tag = self
                .builder
                .build_call(self.rt(sym::NAT_IS_SUCC), &[sval.into()], "nat_is_succ")
                .unwrap()
                .try_as_basic_value()
                .unwrap_basic()
                .into_int_value();
            (tag, sval)
        } else {
            // Coherence shim (M20): a scrutinee may be a fast machine-word `Nat` (BL_NAT).
            // Materialize one inductive `Zero`/`Succ` layer via `bl_nat_to_con` so the tag/field
            // reads below see the chain shape they expect. This is the identity on any non-BL_NAT
            // value (a real Con, tuple, etc.), so it is always safe to call and only fast-Nats pay
            // the (single-allocation) cost. The predecessor of a materialized `Succ` is itself a
            // BL_NAT, so repeated matching peels one layer per step and never forces the whole chain.
            let sval = self
                .builder
                .build_call(self.rt(sym::NAT_TO_CON), &[sval.into()], "nat_mat")
                .unwrap()
                .try_as_basic_value()
                .unwrap_basic()
                .into_pointer_value();
            // Coherence shim (A2): the scrutinee may also be a packed `String` (BL_STRING).
            // `bl_string_to_con` materializes one `empty`/`push` layer; it is the identity on any
            // non-BL_STRING value (including the Nat Con just materialized above), so chaining it is
            // always safe and only packed Strings pay the (single-allocation) cost. The `push` tail
            // stays packed, so repeated matching peels one layer per step and never forces the chain.
            let sval = self
                .builder
                .build_call(self.rt(sym::STRING_TO_CON), &[sval.into()], "str_mat")
                .unwrap()
                .try_as_basic_value()
                .unwrap_basic()
                .into_pointer_value();
            let aux_gep = unsafe {
                self.builder
                    .build_gep(i8t, sval, &[i64t.const_int(8, false)], "auxptr")
                    .unwrap()
            };
            let tag_v = self.builder.build_load(i64t, aux_gep, "ctoridx").unwrap();
            self.mark_invariant(tag_v);
            let tag = tag_v.into_int_value();
            (tag, sval)
        };

        let default_bb = self.context.append_basic_block(cur_fn, "case_default");
        let mut cases = Vec::new();
        let mut arm_bbs = Vec::new();
        for (idx, _arm) in arms.iter().enumerate() {
            let bb = self.context.append_basic_block(cur_fn, "arm");
            cases.push((i64t.const_int(idx as u64, false), bb));
            arm_bbs.push(bb);
        }
        self.builder.build_switch(tagv, default_bb, &cases).unwrap();

        self.builder.position_at_end(default_bb);
        self.builder.build_unreachable().unwrap();

        for (idx, arm) in arms.iter().enumerate() {
            self.builder.position_at_end(arm_bbs[idx]);
            // Re-extract the scrutinee's fields in *this* block and bind each as a rooted local. We
            // reload the scrutinee from the (already rooted) scrutinee value: it cannot have moved
            // since we computed `sval` (no allocation between), so `sval` is still valid here.
            let pushed = arm.binders;
            for k in 0..arm.binders {
                // M25 peel: the `Succ` arm's single field (the predecessor) is read allocation-free
                // via `bl_nat_pred_value`; otherwise GEP the materialized Con's `k`-th field.
                let f = if nat_peel {
                    self.builder
                        .build_call(self.rt(sym::NAT_PRED_VALUE), &[sval.into()], "nat_pred")
                        .unwrap()
                        .try_as_basic_value()
                        .unwrap_basic()
                        .into_pointer_value()
                } else {
                    self.load_field(sval, k)
                };
                self.push_local(fr, f);
            }
            self.emit_tail(&arm.body, cur_fn, fr, funcs, musttail, arena_scopes)?;
            self.pop_locals(fr, pushed);
        }
        Ok(())
    }

    fn emit_comp(
        &self,
        comp: &Comp,
        fr: &mut Frame<'ctx>,
        funcs: &HashMap<String, FunctionValue<'ctx>>,
    ) -> PointerValue<'ctx> {
        match comp {
            Comp::Atom(a) => self.atom_val(a, fr, funcs),
            Comp::MkClosure(name, caps, alloc) => {
                let fv = funcs
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown function {name}"));
                // Allocate the closure first (this may GC), then store each capture reloaded fresh
                // from its rooted slot so we never write a stale (pre-relocation) pointer.
                let obj = self.alloc_closure(*fv, caps.len() as u64, *alloc);
                // A capture atom may itself allocate (e.g. `Atom::Global` materializes a closure),
                // and that allocation can collect and *move* `obj`. Root `obj` in a temp slot across
                // the capture loop and reload it before each store so we never GEP into a stale
                // pre-relocation address. (Arena allocs never move, but rooting is harmless there.)
                let obj_slot = self.push_temp_root(fr, obj);
                for (i, c) in caps.iter().enumerate() {
                    let v = self.atom_val(c, fr, funcs);
                    let obj = self
                        .builder
                        .build_load(self.ptr_ty(), obj_slot, "clo_obj")
                        .unwrap()
                        .into_pointer_value();
                    self.store_field_barrier(obj, i, v, *alloc);
                }
                let obj = self
                    .builder
                    .build_load(self.ptr_ty(), obj_slot, "clo_obj_final")
                    .unwrap()
                    .into_pointer_value();
                self.pop_temp_root();
                obj
            }
            Comp::Call(f, a) => {
                // Route non-tail applications through the OpNode-aware `bl_app` so that effects
                // performed inside `f` or `a` bubble out with this pending application composed onto
                // their continuation (native delimited-continuation capture, spec §4.3). For a pure
                // call this is just a closure apply.
                //
                // GC hazard: `atom_val(f)` may *allocate* (e.g. `Atom::Global` materializes a
                // closure), and so may `atom_val(a)`. A raw SSA pointer is not a GC root, so holding
                // `clo` across the (possibly-collecting) evaluation of `a` would leave it pointing at
                // a stale pre-relocation address. Root `clo` in a slot first, evaluate `a`, then
                // reload `clo` fresh from the slot so it reflects any relocation. (Symmetric to the
                // `MkClosure` capture-store discipline.)
                let clo0 = self.atom_val(f, fr, funcs);
                // Root `clo` in a temp slot that is *not* part of the de Bruijn frame (`fr.slots`),
                // so evaluating `a` below still resolves its indices against the original frame.
                let clo_slot = self.push_temp_root(fr, clo0);
                let arg = self.atom_val(a, fr, funcs);
                let clo = self
                    .builder
                    .build_load(self.ptr_ty(), clo_slot, "clo_reload")
                    .unwrap()
                    .into_pointer_value();
                let res = self
                    .builder
                    .build_call(self.rt(sym::APP), &[clo.into(), arg.into()], "app")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value();
                // Balance the temp root. `res` is held only until the caller's immediate `push_local`,
                // with no allocation in between.
                self.pop_temp_root();
                res
            }
            Comp::CallGlobal(name, a) => {
                // A3: the callee is a captureless global (proved by ANF: `MkClosure(name, [])`), so it
                // reads no env — call its lifted code directly with a null env via the OpNode-aware
                // `bl_app_global`, skipping the per-call closure allocation. The function pointer is a
                // module global (not a GC object), so it needs no rooting across `atom_val(a)` (which
                // may allocate); `bl_app_global` handles an effectful (OpNode) argument itself.
                let callee = *funcs
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown function {name} in CallGlobal"));
                let fnptr = callee.as_global_value().as_pointer_value();
                let arg = self.atom_val(a, fr, funcs);
                if !self.directcall {
                    return self
                        .builder
                        .build_call(
                            self.rt(sym::APP_GLOBAL),
                            &[fnptr.into(), arg.into()],
                            "appg",
                        )
                        .unwrap()
                        .try_as_basic_value()
                        .unwrap_basic()
                        .into_pointer_value();
                }
                // Direct-call fast path: split on whether the argument is a bubbling effect. The pure
                // branch calls the lifted code directly (`fnptr(null_env, arg)` via `tailcc`),
                // bit-identical to `bl_app_global`'s pure path but visible to LLVM; the effectful
                // branch defers to `bl_app_global` so continuation composition is unchanged.
                let cur_fn = self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();
                let arg_is_op = self.one_is_opnode(arg);
                let op_bb = self.context.append_basic_block(cur_fn, "cg_op");
                let pure_bb = self.context.append_basic_block(cur_fn, "cg_pure");
                let cont_bb = self.context.append_basic_block(cur_fn, "cg_cont");
                self.builder
                    .build_conditional_branch(arg_is_op, op_bb, pure_bb)
                    .unwrap();

                // Effectful argument: defer to the OpNode-aware runtime helper.
                self.builder.position_at_end(op_bb);
                let op_res = self
                    .builder
                    .build_call(
                        self.rt(sym::APP_GLOBAL),
                        &[fnptr.into(), arg.into()],
                        "appg",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value();
                let op_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                // Pure argument: direct `tailcc` call with a null environment.
                self.builder.position_at_end(pure_bb);
                let null_env = self.ptr_ty().const_null();
                let dcall = self
                    .builder
                    .build_call(callee, &[null_env.into(), arg.into()], "dcg")
                    .unwrap();
                dcall.set_call_convention(self.call_conv);
                let pure_res = dcall
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value();
                let pure_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                // Merge.
                self.builder.position_at_end(cont_bb);
                let phi = self.builder.build_phi(self.ptr_ty(), "cg_phi").unwrap();
                phi.add_incoming(&[(&op_res, op_end), (&pure_res, pure_end)]);
                phi.as_basic_value().into_pointer_value()
            }
            Comp::CallKnown(name, env, a) => {
                // P10 defunc: a devirtualized non-tail apply. Identical to `Comp::Call` except the
                // callee is the statically-known lifted function `name`, so the pure branch calls it
                // directly (`callee(env, arg)` via `tailcc`) instead of going through the indirect
                // `bl_app` fnptr load — bit-identical to `bl_app`'s pure path but visible to LLVM (so
                // it can inline `name`). The closure object `env` is passed as the first (environment)
                // argument, preserving captures. An effectful operand defers to `bl_app(env, arg)` so
                // continuation composition is unchanged. Mirrors `CallGlobal`'s direct-call split, but
                // with the closure object as env rather than a null env.
                let callee = *funcs
                    .get(name)
                    .unwrap_or_else(|| panic!("unknown function {name} in CallKnown"));
                let clo0 = self.atom_val(env, fr, funcs);
                let clo_slot = self.push_temp_root(fr, clo0);
                let arg = self.atom_val(a, fr, funcs);
                let clo = self
                    .builder
                    .build_load(self.ptr_ty(), clo_slot, "ck_clo_reload")
                    .unwrap()
                    .into_pointer_value();
                self.pop_temp_root();
                let cur_fn = self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();
                let either_op = self.either_is_opnode(clo, arg);
                let op_bb = self.context.append_basic_block(cur_fn, "ck_op");
                let pure_bb = self.context.append_basic_block(cur_fn, "ck_pure");
                let cont_bb = self.context.append_basic_block(cur_fn, "ck_cont");
                self.builder
                    .build_conditional_branch(either_op, op_bb, pure_bb)
                    .unwrap();

                // Effectful operand: defer to the OpNode-aware runtime helper.
                self.builder.position_at_end(op_bb);
                let op_res = self
                    .builder
                    .build_call(self.rt(sym::APP), &[clo.into(), arg.into()], "ck_app")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value();
                let op_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                // Pure: direct `tailcc` call to the known lifted function (closure object as env).
                self.builder.position_at_end(pure_bb);
                let dcall = self
                    .builder
                    .build_call(callee, &[clo.into(), arg.into()], "ck")
                    .unwrap();
                dcall.set_call_convention(self.call_conv);
                let pure_res = dcall
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value();
                let pure_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(cont_bb).unwrap();

                // Merge.
                self.builder.position_at_end(cont_bb);
                let phi = self.builder.build_phi(self.ptr_ty(), "ck_phi").unwrap();
                phi.add_incoming(&[(&op_res, op_end), (&pure_res, pure_end)]);
                phi.as_basic_value().into_pointer_value()
            }
            Comp::Con(con, args, alloc) => {
                let idx = self.con_index(con);
                let obj = self.alloc_obj(tag::CON, args.len() as u64, idx, *alloc, "con");
                // Root `obj` across the field stores: a field atom may allocate (and a GC heap
                // collection would relocate `obj`), so reload it before each barrier store.
                let obj_slot = self.push_temp_root(fr, obj);
                for (i, a) in args.iter().enumerate() {
                    let v = self.atom_val(a, fr, funcs);
                    let obj = self
                        .builder
                        .build_load(self.ptr_ty(), obj_slot, "con_obj")
                        .unwrap()
                        .into_pointer_value();
                    self.store_field_barrier(obj, i, v, *alloc);
                }
                let obj = self
                    .builder
                    .build_load(self.ptr_ty(), obj_slot, "con_obj_final")
                    .unwrap()
                    .into_pointer_value();
                self.pop_temp_root();
                // Bubble an effectful field (e.g. `Succ (perform op a)`) so the construction is
                // captured into the continuation rather than burying the OpNode.
                self.builder
                    .build_call(self.rt(sym::CON_BUBBLE), &[obj.into()], "con_b")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::Tuple(args, alloc) => {
                let obj = self.alloc_obj(tag::TUPLE, args.len() as u64, 0, *alloc, "tup");
                let obj_slot = self.push_temp_root(fr, obj);
                for (i, a) in args.iter().enumerate() {
                    let v = self.atom_val(a, fr, funcs);
                    let obj = self
                        .builder
                        .build_load(self.ptr_ty(), obj_slot, "tup_obj")
                        .unwrap()
                        .into_pointer_value();
                    self.store_field_barrier(obj, i, v, *alloc);
                }
                let obj = self
                    .builder
                    .build_load(self.ptr_ty(), obj_slot, "tup_obj_final")
                    .unwrap()
                    .into_pointer_value();
                self.pop_temp_root();
                self.builder
                    .build_call(self.rt(sym::CON_BUBBLE), &[obj.into()], "tup_b")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::Proj(i, a) => {
                let obj = self.atom_val(a, fr, funcs);
                self.load_field(obj, *i)
            }
            Comp::Now(a, alloc) => {
                let v = self.atom_val(a, fr, funcs);
                let obj = self.alloc_obj(tag::NOW, 1, 0, *alloc, "now");
                self.store_field_barrier(obj, 0, v, *alloc);
                obj
            }
            Comp::Later(a, alloc) => {
                let v = self.atom_val(a, fr, funcs);
                let obj = self.alloc_obj(tag::LATER, 1, 0, *alloc, "later");
                self.store_field_barrier(obj, 0, v, *alloc);
                obj
            }
            Comp::Op { effect, op, arg } => {
                let a = self.atom_val(arg, fr, funcs);
                let eff = self.global_str(effect);
                let opn = self.global_str(op);
                self.builder
                    .build_call(
                        self.rt(sym::PERFORM),
                        &[eff.into(), opn.into(), a.into()],
                        "perform",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::Foreign(symbol, arg) => {
                // An FFI postulate (spec §7.6): declare (once) and call the external C function
                // `BlValue <symbol>(void)` or `BlValue <symbol>(BlValue)` — depending on whether
                // this call site is 0- or 1-arg (Wave 2 / L2's `F64` hatch; multi-operand ops pack
                // their operands into a single `Pair` argument, see `ir.rs`'s `Cir::Foreign` doc
                // comment) — taking its result as this computation's value. The C symbol is
                // responsible for any GC-heap allocation of the value it returns.
                let func = self.module.get_function(symbol).unwrap_or_else(|| {
                    let fty = match arg {
                        Some(_) => self.ptr_ty().fn_type(&[self.ptr_ty().into()], false),
                        None => self.ptr_ty().fn_type(&[], false),
                    };
                    self.module
                        .add_function(symbol, fty, Some(Linkage::External))
                });
                let args: Vec<_> = match arg {
                    Some(a) => vec![self.atom_val(a, fr, funcs).into()],
                    None => vec![],
                };
                self.builder
                    .build_call(func, &args, "foreign")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::IntLit(n) => {
                let i64t = self.context.i64_type();
                self.box_int(i64t.const_int(*n as u64, true))
            }
            Comp::NatLit(n) => {
                let i64t = self.context.i64_type();
                self.builder
                    .build_call(
                        self.rt(sym::NAT_FROM_U64),
                        &[i64t.const_int(*n, false).into()],
                        "natlit",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::StrLit(cps) => {
                // Emit the codepoints as a private constant `[N x i64]` global and hand
                // `bl_string_from_codepoints` a pointer to it; the runtime copies them into a
                // program-lifetime intern buffer and returns one packed BL_STRING (A2). An empty
                // literal passes a null pointer + length 0 (the runtime never reads the pointer then).
                let i64t = self.context.i64_type();
                let n = cps.len();
                let ptr = self.context.ptr_type(inkwell::AddressSpace::default());
                let cps_ptr = if n == 0 {
                    ptr.const_null()
                } else {
                    let vals: Vec<_> = cps.iter().map(|c| i64t.const_int(*c, false)).collect();
                    let arr = i64t.const_array(&vals);
                    let gv = self
                        .module
                        .add_global(i64t.array_type(n as u32), None, "strlit_cps");
                    gv.set_initializer(&arr);
                    gv.set_constant(true);
                    gv.set_linkage(Linkage::Private);
                    gv.as_pointer_value()
                };
                self.builder
                    .build_call(
                        self.rt(sym::STRING_FROM_CODEPOINTS),
                        &[cps_ptr.into(), i64t.const_int(n as u64, false).into()],
                        "strlit",
                    )
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::IntPrim { op, lhs, rhs } => {
                use blight_kernel::IntPrimOp;
                let l = self.atom_val(lhs, fr, funcs);
                let r = self.atom_val(rhs, fr, funcs);
                // Read each operand's payload through the runtime `bl_int_val`, which decodes a tagged
                // immediate (M21) — operands may now be unboxed, so a raw header GEP is unsound.
                let lv = self.int_val(l);
                let rv = self.int_val(r);
                let b = &self.builder;
                let res = match op {
                    IntPrimOp::Add => b.build_int_add(lv, rv, "iadd").unwrap(),
                    IntPrimOp::Sub => b.build_int_sub(lv, rv, "isub").unwrap(),
                    IntPrimOp::Mul => b.build_int_mul(lv, rv, "imul").unwrap(),
                    IntPrimOp::Div => b.build_int_signed_div(lv, rv, "idiv").unwrap(),
                    IntPrimOp::Eq => {
                        let c = b
                            .build_int_compare(inkwell::IntPredicate::EQ, lv, rv, "ieq")
                            .unwrap();
                        b.build_int_z_extend(c, self.context.i64_type(), "ieqz")
                            .unwrap()
                    }
                    IntPrimOp::Lt => {
                        let c = b
                            .build_int_compare(inkwell::IntPredicate::SLT, lv, rv, "ilt")
                            .unwrap();
                        b.build_int_z_extend(c, self.context.i64_type(), "iltz")
                            .unwrap()
                    }
                };
                self.box_int(res)
            }
            Comp::NatPrim { op, lhs, rhs } => {
                use crate::ir::NatPrimOp;
                let l = self.atom_val(lhs, fr, funcs);
                let sym_name = match op {
                    NatPrimOp::Add => sym::NAT_ADD,
                    NatPrimOp::Mul => sym::NAT_MUL,
                    NatPrimOp::Sub => sym::NAT_SUB,
                    NatPrimOp::Pred => sym::NAT_PRED,
                    NatPrimOp::Min => sym::NAT_MIN,
                    NatPrimOp::Max => sym::NAT_MAX,
                };
                match rhs {
                    Some(r) => {
                        let rv = self.atom_val(r, fr, funcs);
                        self.builder
                            .build_call(self.rt(sym_name), &[l.into(), rv.into()], "natprim")
                            .unwrap()
                            .try_as_basic_value()
                            .unwrap_basic()
                            .into_pointer_value()
                    }
                    None => self
                        .builder
                        .build_call(self.rt(sym_name), &[l.into()], "natprim1")
                        .unwrap()
                        .try_as_basic_value()
                        .unwrap_basic()
                        .into_pointer_value(),
                }
            }
            Comp::FloatPrim { op, lhs, rhs } => {
                use crate::ir::FloatPrimOp;
                let l = self.atom_val(lhs, fr, funcs);
                let sym_name = match op {
                    FloatPrimOp::Add => sym::FLOAT_ADD,
                    FloatPrimOp::Sub => sym::FLOAT_SUB,
                    FloatPrimOp::Mul => sym::FLOAT_MUL,
                    FloatPrimOp::Div => sym::FLOAT_DIV,
                    FloatPrimOp::Neg => sym::FLOAT_NEG,
                };
                match rhs {
                    Some(r) => {
                        let rv = self.atom_val(r, fr, funcs);
                        self.builder
                            .build_call(self.rt(sym_name), &[l.into(), rv.into()], "floatprim")
                            .unwrap()
                            .try_as_basic_value()
                            .unwrap_basic()
                            .into_pointer_value()
                    }
                    None => self
                        .builder
                        .build_call(self.rt(sym_name), &[l.into()], "floatprim1")
                        .unwrap()
                        .try_as_basic_value()
                        .unwrap_basic()
                        .into_pointer_value(),
                }
            }
        }
    }

    fn global_str(&self, s: &str) -> PointerValue<'ctx> {
        let gv = self.builder.build_global_string_ptr(s, "str").unwrap();
        gv.as_pointer_value()
    }

    fn write_object(
        &self,
        out_path: &std::path::Path,
        target: Target,
        opt: OptLevel,
    ) -> Result<(), String> {
        use inkwell::targets::{
            CodeModel, FileType, InitializationConfig, RelocMode, Target as LlvmTarget,
            TargetMachine, TargetTriple,
        };
        use inkwell::OptimizationLevel;

        // Initialize the requested target's backend, pick its triple, and (for wasm) neutral
        // cpu/feature strings. The host target uses the running machine's cpu + features.
        let (triple, cpu, features, reloc) = match target {
            Target::Native => {
                LlvmTarget::initialize_native(&InitializationConfig::default())
                    .map_err(|e| format!("native target init: {e}"))?;
                let triple = TargetMachine::get_default_triple();
                let cpu = TargetMachine::get_host_cpu_name()
                    .to_str()
                    .unwrap_or("")
                    .to_string();
                let features = TargetMachine::get_host_cpu_features()
                    .to_str()
                    .unwrap_or("")
                    .to_string();
                (triple, cpu, features, RelocMode::PIC)
            }
            Target::Wasm32 => {
                LlvmTarget::initialize_webassembly(&InitializationConfig::default());
                let triple = TargetTriple::create("wasm32-unknown-unknown");
                (triple, String::new(), String::new(), RelocMode::Static)
            }
        };
        let target_obj = LlvmTarget::from_triple(&triple).map_err(|e| e.to_string())?;
        let machine = target_obj
            .create_target_machine(
                &triple,
                &cpu,
                &features,
                OptimizationLevel::Default,
                reloc,
                CodeModel::Default,
            )
            .ok_or("could not create target machine")?;
        // The module must carry the target machine's triple + data layout before any target-aware IR
        // pass or emission runs — for EVERY target, not just wasm. With an empty/default layout the
        // optimizer and instruction selector assume the wrong pointer size / alignment / ABI: native
        // x86_64 was silently miscompiled (it worked by luck on the arm64 dev host, but segfaulted on
        // Linux x86_64). `machine.get_target_data()` gives the exact layout for the triple we emit with.
        self.module.set_triple(&triple);
        self.module
            .set_data_layout(&machine.get_target_data().get_data_layout());
        // Run the IR-level optimization pipeline (new pass manager) before object emission. The
        // `default<Ox>` pipelines preserve `musttail` markers, so tail-call soundness is unaffected;
        // a verifier pass guards against a malformed module reaching the backend.
        if let Some(pipeline) = opt.pipeline() {
            use inkwell::passes::PassBuilderOptions;
            let options = PassBuilderOptions::create();
            self.module
                .run_passes(pipeline, &machine, options)
                .map_err(|e| format!("LLVM pass pipeline `{pipeline}` failed: {e}"))?;
        }
        machine
            .write_to_file(&self.module, FileType::Object, out_path)
            .map_err(|e| e.to_string())
    }

    /// Emit LLVM **bitcode** for the module at `out_path`, after running the same target setup and
    /// `opt` IR pipeline as [`write_object`]. This is the producer half of the cross-object LTO path
    /// (Phase 3): the Blight program is shipped as `.bc` so that, when `clang -flto` links it against
    /// the runtime's `.bc`, LLVM can finally inline `bl_alloc`/`bl_app`/`bl_force`/`bl_nat_*` into hot
    /// Blight code — the optimization boundary that the plain-object path can never cross.
    ///
    /// We deliberately run only the cheap, always-sound part of the pipeline here (the same
    /// `default<Ox>` passes, which preserve `musttail`); the heavyweight cross-module inlining is the
    /// LTO link step's job. Emitting bitcode never changes observable results — it is the *same*
    /// module, just serialized as IR instead of machine code.
    fn write_bitcode(
        &self,
        out_path: &std::path::Path,
        target: Target,
        opt: OptLevel,
    ) -> Result<(), String> {
        use inkwell::targets::{
            CodeModel, InitializationConfig, RelocMode, Target as LlvmTarget, TargetMachine,
            TargetTriple,
        };
        use inkwell::OptimizationLevel;

        let (triple, cpu, features, reloc) = match target {
            Target::Native => {
                LlvmTarget::initialize_native(&InitializationConfig::default())
                    .map_err(|e| format!("native target init: {e}"))?;
                let triple = TargetMachine::get_default_triple();
                let cpu = TargetMachine::get_host_cpu_name()
                    .to_str()
                    .unwrap_or("")
                    .to_string();
                let features = TargetMachine::get_host_cpu_features()
                    .to_str()
                    .unwrap_or("")
                    .to_string();
                (triple, cpu, features, RelocMode::PIC)
            }
            Target::Wasm32 => {
                LlvmTarget::initialize_webassembly(&InitializationConfig::default());
                let triple = TargetTriple::create("wasm32-unknown-unknown");
                (triple, String::new(), String::new(), RelocMode::Static)
            }
        };
        let target_obj = LlvmTarget::from_triple(&triple).map_err(|e| e.to_string())?;
        let machine = target_obj
            .create_target_machine(
                &triple,
                &cpu,
                &features,
                OptimizationLevel::Default,
                reloc,
                CodeModel::Default,
            )
            .ok_or("could not create target machine")?;
        // Same defect/fix as `write_object`: the module must carry the target machine's triple + data
        // layout for EVERY target before passes/emission run. This is the LTO/bitcode path (the default
        // `blight build`, `BL_NO_LTO` unset → `build_lto`), so the missing native layout here is what the
        // segfaulting Linux benches actually went through.
        self.module.set_triple(&triple);
        self.module
            .set_data_layout(&machine.get_target_data().get_data_layout());
        if let Some(pipeline) = opt.pipeline() {
            use inkwell::passes::PassBuilderOptions;
            let options = PassBuilderOptions::create();
            self.module
                .run_passes(pipeline, &machine, options)
                .map_err(|e| format!("LLVM pass pipeline `{pipeline}` failed: {e}"))?;
        }
        if self.module.write_bitcode_to_path(out_path) {
            Ok(())
        } else {
            Err(format!(
                "failed to write LLVM bitcode to {}",
                out_path.display()
            ))
        }
    }
}

/// Fallback constructor tag for signature-less programs (tests): `Zero` = 0, `Succ` = 1; otherwise
/// a stable small id from the name's first byte. Real builds derive the tag from the signature (the
/// constructor's index within its `DataDecl`) via [`AnfProgram::con_tags`].
fn con_index_fallback(con: &blight_kernel::ConName) -> u64 {
    match con.0.as_str() {
        "Zero" => 0,
        "Succ" => 1,
        other => other.bytes().next().map(|b| b as u64).unwrap_or(0),
    }
}

/// Is this arm set exactly the `Nat` eliminator shape — `[Zero{binders:0}, Succ{binders:1}]`, in
/// declaration order? This is the destructuring of a `match (n : Nat) [Zero …][Succ k …]` loop
/// driver, which the codegen can peel allocation-free off a fast `BL_NAT` word (M25). Matching by
/// constructor name + binder count (Succ binds exactly its one predecessor field; there is no
/// recursive-IH binder for a `Nat` `case`, which is structural over the scrutinee). Any other shape
/// (extra arms, wrong binder counts, a user datatype that happens to name a `Succ`) does not match,
/// so the generic `bl_nat_to_con` path is used — never a miscompile, only a missed optimization.
fn is_nat_eliminator_shape(arms: &[TailArm]) -> bool {
    // The no-alloc `Nat` peel (M25). Its `bl_nat_is_succ`/`bl_nat_pred_value` helpers are
    // differentially gated by numeric_diff.c `check_peel`, and the peel keeps the generic path's
    // exact CFG (same switch/arms/binder pushes — only the tag/field *sources* change).
    //
    // HISTORY: originally landed opt-in (`BL_NAT_PEEL=1`, commit 4bfd712) because the then-current
    // pipeline crashed on deep curried multi-arg eliminator loops ("a captured fast-Nat immediate
    // reached where a closure is expected"). Re-audited 2026-07-05, after the passes that rewrote
    // exactly the implicated partial-application spines (A3 spine fusion, A1′ post-mono layout,
    // P10/P10.1 defunc + capture specialization): the full example corpus, the codegen suite, the
    // bench goldens, and the hofold A/B pin all run value-identical with the peel ON, and the
    // historical crash could not be reproduced — the same stale-claim pattern
    // docs/c1-uncurry-investigation.md §1 documents for `binrec`. Default is therefore ON, with
    // the standard per-pass discipline: `BL_NO_NATPEEL=1` disables it, and the B1 differential
    // matrix (DIFF_FLAGS) enforces bit-identity between the two paths on every corpus program.
    if std::env::var_os("BL_NO_NATPEEL").is_some() {
        return false;
    }
    arms.len() == 2
        && arms[0].con.0 == "Zero"
        && arms[0].binders == 0
        && arms[1].con.0 == "Succ"
        && arms[1].binders == 1
}

#[allow(unused_imports)]
use inkwell::values::BasicValue as _;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::anf::{AnfFunc, AnfProgram, Atom, Comp, Tail, TailArm};
    use blight_kernel::ConName;
    use std::process::Command;

    /// `Succ Zero` as an ANF entry returning the constructor value.
    fn succ_zero_program() -> AnfProgram {
        // entry = let z = Con Zero [] in let s = Con Succ [z] in Ret s
        let entry = Tail::Let(
            Comp::Con(ConName("Zero".into()), vec![], Alloc::Gc),
            Box::new(Tail::Let(
                Comp::Con(ConName("Succ".into()), vec![Atom::Var(0)], Alloc::Gc),
                Box::new(Tail::Ret(Atom::Var(0))),
            )),
        );
        AnfProgram {
            funcs: vec![],
            entry,
            con_tags: Default::default(),
        }
    }

    /// An identity top-level function plus a tail self-call loop to exercise tailcc/musttail.
    fn loop_program() -> AnfProgram {
        // func loop(env, arg): case arg of Zero -> Ret arg ; Succ n -> Jump n
        let body = Tail::Case(
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
                    // the field is now innermost local (Var 0)
                    body: Tail::Jump(Atom::Var(0)),
                },
            ],
        );
        let f = AnfFunc {
            name: "loop".into(),
            recursive: true,
            body,
        };
        AnfProgram {
            funcs: vec![f],
            entry: Tail::Ret(Atom::Erased),
            con_tags: Default::default(),
        }
    }

    #[test]
    fn emits_object_for_identity() {
        let prog = succ_zero_program();
        let dir = std::env::temp_dir().join(format!("blight_obj_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let obj = dir.join("id.o");
        emit_object(&prog, &obj).expect("object emission");
        let meta = std::fs::metadata(&obj).expect("object exists");
        assert!(meta.len() > 0, "object file is non-empty");
    }

    #[test]
    fn tailcc_musttail_on_general_tail() {
        let prog = loop_program();
        let ir = emit_ir(&prog).expect("ir emission");
        assert!(
            ir.contains("tailcc"),
            "uses tailcc calling convention:\n{ir}"
        );
        assert!(
            ir.contains("musttail"),
            "uses musttail on the self tail call:\n{ir}"
        );
    }

    /// End-to-end: compile `Succ Zero`, link the runtime, run it, expect the numeral `1`.
    #[test]
    fn hello_nat_runs() {
        let prog = succ_zero_program();
        let dir = std::env::temp_dir().join(format!("blight_hello_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let obj = dir.join("program.o");
        emit_object(&prog, &obj).expect("object emission");

        let runtime = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
        let mut objs = vec![obj.clone()];
        for src in [
            "gc.c",
            "stack.c",
            "delay.c",
            "effects.c",
            "numeric.c",
            "boxed_array.c",
            "prelude_rt.c",
        ] {
            let o = dir.join(format!("{src}.o"));
            let st = Command::new("clang")
                .args(["-c", "-O2", "-I"])
                .arg(&runtime)
                .arg(runtime.join(src))
                .arg("-o")
                .arg(&o)
                .status()
                .expect("clang -c");
            assert!(st.success(), "compiling {src}");
            objs.push(o);
        }
        let bin = dir.join("hello");
        let mut link = Command::new("clang");
        link.arg("-o").arg(&bin);
        for o in &objs {
            link.arg(o);
        }
        assert!(link.status().expect("clang link").success(), "link");

        let out = Command::new(&bin).output().expect("run binary");
        assert!(out.status.success(), "binary exits 0");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert_eq!(stdout.trim(), "1", "Succ Zero prints as the numeral 1");
    }

    /// End-to-end acceptance (spec §9 / M5 headline): a region-disciplined scratch loop allocates
    /// all its per-iteration scratch in an arena (reclaimed each iteration), so the GC never runs
    /// (`bl_gc_collections() == 0`); the *identical* loop allocating the scratch on the GC heap
    /// forces collections — and both compute the same result. This is the proof that regions bypass
    /// the collector.
    #[test]
    fn region_workload_bypasses_gc() {
        // A counted loop `scratch_loop(env, counter)`:
        //   case counter of
        //     Zero   -> Ret counter                       (the loop result; here Zero)
        //     Succ n -> <scratch ...> ; Jump n            (allocate S scratch tuples, recurse on n)
        // The scratch tuples are dead at the end of each iteration. In the region variant the whole
        // Succ arm is wrapped in a `Tail::Region` and the scratch is `Alloc::Arena` (reclaimed at the
        // arena-leave emitted before the back-edge `Jump`); in the GC variant it is `Alloc::Gc`.
        const SCRATCH_PER_ITER: usize = 256; // enough GC garbage/iter to overflow the nursery quickly
        const DEPTH: usize = 300; // loop iterations (also the input Nat depth)

        fn scratch_loop(arena: bool) -> AnfProgram {
            let alloc = if arena { Alloc::Arena } else { Alloc::Gc };
            // Succ-arm body: bind SCRATCH_PER_ITER scratch tuples, then Jump to the predecessor `n`.
            // After the Case binds the Succ field, `n` is the innermost local (Var 0). Each scratch
            // `let` pushes a new innermost local, so `n` stays reachable as Var(i) at depth i — but we
            // only need it at the end, where it is Var(SCRATCH_PER_ITER) (n shifted by the binds).
            let mut body: Tail = Tail::Jump(Atom::Var(SCRATCH_PER_ITER));
            for _ in 0..SCRATCH_PER_ITER {
                // a 2-field scratch tuple; its contents are irrelevant (only that it allocates), so
                // it just references the current innermost local (Var 0) twice.
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

            // Entry: build a DEPTH-deep Nat (Gc), then tail-call the loop with it.
            // let z = Con Zero [] ; let s1 = Con Succ [z] ; ... ; let sD = Con Succ [s{D-1}] ;
            // TailCall scratch_loop sD
            let mut entry: Tail = Tail::TailCall(Atom::Global("scratch_loop".into()), Atom::Var(0));
            // Innermost local before the tail call is the deepest Succ (Var 0).
            for _ in 0..DEPTH {
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

        fn build_and_run(prog: &AnfProgram, dir: &std::path::Path, name: &str) -> (i32, usize) {
            std::fs::create_dir_all(dir).unwrap();
            let obj = dir.join(format!("{name}.o"));
            emit_object(prog, &obj).expect("object emission");
            let runtime = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");
            let mut objs = vec![obj.clone()];
            // Link the full runtime *including arena.c* (region allocations call into it).
            for src in [
                "gc.c",
                "stack.c",
                "delay.c",
                "effects.c",
                "arena.c",
                "numeric.c",
                "boxed_array.c",
            ] {
                let o = dir.join(format!("{name}_{src}.o"));
                let st = Command::new("clang")
                    .args(["-c", "-O2", "-I"])
                    .arg(&runtime)
                    .arg(runtime.join(src))
                    .arg("-o")
                    .arg(&o)
                    .status()
                    .expect("clang -c");
                assert!(st.success(), "compiling {src}");
                objs.push(o);
            }
            // A custom harness main: small heap (so the GC variant is forced to collect), run the
            // program, print the result's *constructor tag* (kind) and the collection count.
            let main_c = dir.join(format!("{name}_main.c"));
            std::fs::write(
                &main_c,
                r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {
  bl_gc_init(8 * 1024 * 1024); /* 8 MiB heap: nursery ~1 MiB */
  bl_stack_init();
  BlValue r = bl_program_entry();
  unsigned tag = r ? (unsigned)bl_obj_tag(r) : 999u;
  unsigned long long aux = r ? (unsigned long long)bl_obj_aux(r) : 0ull;
  printf("RESULT tag=%u aux=%llu collections=%zu\n", tag, aux, bl_gc_collections());
  return 0;
}
"#,
            )
            .unwrap();
            let mo = dir.join(format!("{name}_main.o"));
            let st = Command::new("clang")
                .args(["-c", "-O2", "-I"])
                .arg(&runtime)
                .arg(&main_c)
                .arg("-o")
                .arg(&mo)
                .status()
                .expect("clang -c main");
            assert!(st.success(), "compiling harness main");
            objs.push(mo);

            let bin = dir.join(name);
            let mut link = Command::new("clang");
            link.arg("-o").arg(&bin);
            for o in &objs {
                link.arg(o);
            }
            assert!(link.status().expect("clang link").success(), "link {name}");

            let out = Command::new(&bin).output().expect("run binary");
            let stdout = String::from_utf8_lossy(&out.stdout);
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert!(
                out.status.success(),
                "{name} exits 0\nstdout:{stdout}\nstderr:{stderr}"
            );
            // Parse "RESULT tag=.. aux=.. collections=.."
            let line = stdout
                .lines()
                .find(|l| l.starts_with("RESULT"))
                .unwrap_or_else(|| {
                    panic!("{name}: no RESULT line\nstdout:{stdout}\nstderr:{stderr}")
                });
            let tag: i32 = line
                .split_whitespace()
                .find_map(|w| w.strip_prefix("tag="))
                .unwrap()
                .parse()
                .unwrap();
            let collections: usize = line
                .split_whitespace()
                .find_map(|w| w.strip_prefix("collections="))
                .unwrap()
                .parse()
                .unwrap();
            (tag, collections)
        }

        let dir = std::env::temp_dir().join(format!("blight_region_bypass_{}", std::process::id()));
        let region_prog = scratch_loop(true);
        let gc_prog = scratch_loop(false);

        let (region_tag, region_collections) = build_and_run(&region_prog, &dir, "region");
        let (gc_tag, gc_collections) = build_and_run(&gc_prog, &dir, "gcheap");

        // Identical results: both loops bottom out at `Zero` (constructor tag 0 / BL_CON).
        assert_eq!(
            region_tag, gc_tag,
            "region and GC variants must compute the same result"
        );

        // The headline assertions: the region-disciplined workload bypasses the collector entirely,
        // while the GC-heap workload is forced to collect.
        assert_eq!(
            region_collections, 0,
            "region-scoped scratch must bypass the GC (got {region_collections} collections)"
        );
        assert!(
            gc_collections > 0,
            "the non-region workload must force GC collections (got {gc_collections})"
        );
    }

    /// `--opt` parsing accepts the documented spellings and rejects anything else.
    #[test]
    fn opt_level_parse() {
        assert_eq!(OptLevel::parse("0").unwrap(), OptLevel::None);
        assert_eq!(OptLevel::parse("none").unwrap(), OptLevel::None);
        assert_eq!(OptLevel::parse("2").unwrap(), OptLevel::Default);
        assert_eq!(OptLevel::parse("default").unwrap(), OptLevel::Default);
        assert_eq!(OptLevel::parse("3").unwrap(), OptLevel::Aggressive);
        assert_eq!(OptLevel::parse("aggressive").unwrap(), OptLevel::Aggressive);
        assert_eq!(OptLevel::default(), OptLevel::Default);
        assert!(OptLevel::parse("O2").is_err());
        assert!(OptLevel::parse("").is_err());
    }

    /// The IR pass pipeline runs for every level without error and preserves correctness: emitting
    /// the *same* program at `None`/`Default`/`Aggressive` must each produce a valid object that
    /// links and runs to the *same* result (musttail markers survive the `default<Ox>` pipelines, so
    /// tail-call soundness is unaffected — spec §7.4). This is the B1 regression guard that wiring
    /// `--opt` did not break codegen.
    #[test]
    fn opt_levels_emit_runnable_objects() {
        // A program returning `Succ Zero` — a concrete constructor value, so the result tag is a
        // meaningful correctness witness that each opt level must preserve. (The musttail-survival
        // property of the pipelines is also exercised by the loop-based IR tests.)
        let prog = succ_zero_program();
        let dir = std::env::temp_dir().join(format!("blight_opt_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let runtime = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("runtime");

        let mut tags = Vec::new();
        for (label, opt) in [
            ("o0", OptLevel::None),
            ("o2", OptLevel::Default),
            ("o3", OptLevel::Aggressive),
        ] {
            let obj = dir.join(format!("opt_{label}.o"));
            emit_object_for_target(&prog, &obj, Target::Native, opt)
                .unwrap_or_else(|e| panic!("emit at {label} failed: {e}"));
            let mut objs = vec![obj.clone()];
            for src in [
                "gc.c",
                "stack.c",
                "delay.c",
                "effects.c",
                "arena.c",
                "numeric.c",
                "boxed_array.c",
            ] {
                let o = dir.join(format!("opt_{label}_{src}.o"));
                let st = Command::new("clang")
                    .args(["-c", "-O2", "-I"])
                    .arg(&runtime)
                    .arg(runtime.join(src))
                    .arg("-o")
                    .arg(&o)
                    .status()
                    .expect("clang -c");
                assert!(st.success(), "compiling {src} for {label}");
                objs.push(o);
            }
            let main_c = dir.join(format!("opt_{label}_main.c"));
            std::fs::write(
                &main_c,
                r#"
#include "blight_rt.h"
#include <stdio.h>
extern BlValue bl_program_entry(void);
int main(void) {
  bl_gc_init(8 * 1024 * 1024);
  bl_stack_init();
  BlValue r = bl_program_entry();
  unsigned tag = r ? (unsigned)bl_obj_tag(r) : 999u;
  printf("RESULT tag=%u\n", tag);
  return 0;
}
"#,
            )
            .unwrap();
            let main_obj = dir.join(format!("opt_{label}_main.o"));
            let st = Command::new("clang")
                .args(["-c", "-O2", "-I"])
                .arg(&runtime)
                .arg(&main_c)
                .arg("-o")
                .arg(&main_obj)
                .status()
                .expect("clang -c main");
            assert!(st.success(), "compiling main for {label}");
            objs.push(main_obj);

            let bin = dir.join(format!("opt_{label}_bin"));
            let mut link = Command::new("clang");
            link.arg("-o").arg(&bin);
            for o in &objs {
                link.arg(o);
            }
            assert!(link.status().expect("link").success(), "link {label}");

            let out = Command::new(&bin).output().expect("run");
            assert!(out.status.success(), "{label} runs");
            let stdout = String::from_utf8_lossy(&out.stdout);
            let line = stdout
                .lines()
                .find(|l| l.starts_with("RESULT"))
                .unwrap_or_else(|| panic!("{label}: no RESULT line: {stdout}"));
            let tag: i32 = line
                .split_whitespace()
                .find_map(|t| t.strip_prefix("tag="))
                .and_then(|v| v.parse().ok())
                .unwrap_or_else(|| panic!("{label}: bad RESULT line: {line}"));
            tags.push((label, tag));
        }
        // All opt levels must compute the identical result tag.
        let first = tags[0].1;
        for (label, tag) in &tags {
            assert_eq!(
                *tag, first,
                "opt level {label} changed the result tag ({tag} != {first})"
            );
        }
    }
}
