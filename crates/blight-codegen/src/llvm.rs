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
use inkwell::values::{FunctionValue, IntValue, LLVMTailCallKind, PointerValue};
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

/// Emit an object file for `prog` at `out_path` (e.g. `foo.o`) for the host (native) target.
pub fn emit_object(prog: &AnfProgram, out_path: &std::path::Path) -> Result<(), String> {
    emit_object_for_target(prog, out_path, Target::Native)
}

/// Emit an object file for `prog` at `out_path` for the requested `target`.
pub fn emit_object_for_target(
    prog: &AnfProgram,
    out_path: &std::path::Path,
    target: Target,
) -> Result<(), String> {
    let context = Context::create();
    let codegen = Codegen::with_tags(&context, "blight_module", prog.con_tags.clone());
    codegen.emit_program(prog)?;
    codegen.write_object(out_path, target)
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
}

impl<'ctx> Codegen<'ctx> {
    fn with_tags(
        context: &'ctx Context,
        name: &str,
        con_tags: HashMap<blight_kernel::ConName, u64>,
    ) -> Self {
        let module = context.create_module(name);
        let builder = context.create_builder();
        Codegen {
            context,
            module,
            builder,
            con_tags,
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
        // bl_con_bubble(ptr obj) -> ptr  (OpNode-aware Con/Tuple construction)
        let con_bubble_ty = p.fn_type(&[p.into()], false);
        self.module
            .add_function(sym::CON_BUBBLE, con_bubble_ty, Some(Linkage::External));
        // bl_int(i64) -> ptr
        let int_ty = p.fn_type(&[i64t.into()], false);
        self.module
            .add_function(sym::INT, int_ty, Some(Linkage::External));
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
            fv.set_call_conventions(TAILCC);
            funcs.insert(f.name.clone(), fv);
        }
        // Stash funcs via interior reassembly: rebuild a Codegen view with funcs populated. Since
        // `self` is shared, use a local map passed explicitly.
        let funcs_ref = &funcs;

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
        let offset = header + (k as u64) * 8;
        let gep = unsafe {
            self.builder
                .build_gep(i8t, obj, &[i64t.const_int(offset, false)], "fldptr")
                .unwrap()
        };
        self.builder
            .build_load(self.ptr_ty(), gep, "fld")
            .unwrap()
            .into_pointer_value()
    }

    /// Load the `header.aux` 64-bit payload of `obj` (offset 8: past the `tag`+`nfields` u32 pair).
    /// For a `BL_INT` this is the machine-integer value.
    fn load_aux_i64(&self, obj: PointerValue<'ctx>) -> inkwell::values::IntValue<'ctx> {
        let i8t = self.context.i8_type();
        let i64t = self.context.i64_type();
        let gep = unsafe {
            self.builder
                .build_gep(i8t, obj, &[i64t.const_int(8, false)], "auxptr")
                .unwrap()
        };
        self.builder
            .build_load(i64t, gep, "aux")
            .unwrap()
            .into_int_value()
    }

    /// Box a 64-bit integer into a fresh `BL_INT` object (no fields; payload in `aux`).
    fn box_int(&self, v: inkwell::values::IntValue<'ctx>) -> PointerValue<'ctx> {
        let i32t = self.context.i32_type();
        self.builder
            .build_call(
                self.rt(sym::ALLOC),
                &[
                    i32t.const_int(tag::INT, false).into(),
                    i32t.const_int(0, false).into(),
                    v.into(),
                ],
                "int",
            )
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
        let offset = header + (k as u64) * 8;
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
        let fnint = self
            .builder
            .build_load(i64t, aux_gep, "fnint")
            .unwrap()
            .into_int_value();
        self.builder
            .build_int_to_ptr(fnint, self.ptr_ty(), "fnptr")
            .unwrap()
    }

    /// Load an object's tag (the `uint32_t` at header offset 0) as an i32 value.
    fn load_tag(&self, obj: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i32t = self.context.i32_type();
        self.builder
            .build_load(i32t, obj, "tag")
            .unwrap()
            .into_int_value()
    }

    /// Emit `clo.tag == OPNODE || arg.tag == OPNODE` as an i1 — the guard that routes an application
    /// through the OpNode-aware `bl_app` (delimited-continuation capture) instead of a direct call.
    fn either_is_opnode(&self, clo: PointerValue<'ctx>, arg: PointerValue<'ctx>) -> IntValue<'ctx> {
        let i32t = self.context.i32_type();
        let op = i32t.const_int(crate::runtime::tag::OPNODE, false);
        let ct = self.load_tag(clo);
        let at = self.load_tag(arg);
        let c_is = self
            .builder
            .build_int_compare(inkwell::IntPredicate::EQ, ct, op, "clo_is_op")
            .unwrap();
        let a_is = self
            .builder
            .build_int_compare(inkwell::IntPredicate::EQ, at, op, "arg_is_op")
            .unwrap();
        self.builder.build_or(c_is, a_is, "either_op").unwrap()
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
                let clo = self.atom_val(f, fr, funcs);
                let arg = self.atom_val(a, fr, funcs);
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
                call.set_call_convention(TAILCC);
                if mt {
                    call.set_tail_call_kind(LLVMTailCallKind::LLVMTailCallKindMustTail);
                }
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
                call.set_call_convention(TAILCC);
                if mt {
                    call.set_tail_call_kind(LLVMTailCallKind::LLVMTailCallKindMustTail);
                }
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
        let aux_gep = unsafe {
            self.builder
                .build_gep(i8t, sval, &[i64t.const_int(8, false)], "auxptr")
                .unwrap()
        };
        let tagv = self
            .builder
            .build_load(i64t, aux_gep, "ctoridx")
            .unwrap()
            .into_int_value();

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
                let f = self.load_field(sval, k);
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
        fr: &Frame<'ctx>,
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
                for (i, c) in caps.iter().enumerate() {
                    let v = self.atom_val(c, fr, funcs);
                    self.store_field_barrier(obj, i, v, *alloc);
                }
                obj
            }
            Comp::Call(f, a) => {
                // Route non-tail applications through the OpNode-aware `bl_app` so that effects
                // performed inside `f` or `a` bubble out with this pending application composed onto
                // their continuation (native delimited-continuation capture, spec §4.3). For a pure
                // call this is just a closure apply.
                let clo = self.atom_val(f, fr, funcs);
                let arg = self.atom_val(a, fr, funcs);
                self.builder
                    .build_call(self.rt(sym::APP), &[clo.into(), arg.into()], "app")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::Con(con, args, alloc) => {
                let idx = self.con_index(con);
                let obj = self.alloc_obj(tag::CON, args.len() as u64, idx, *alloc, "con");
                for (i, a) in args.iter().enumerate() {
                    let v = self.atom_val(a, fr, funcs);
                    self.store_field_barrier(obj, i, v, *alloc);
                }
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
                for (i, a) in args.iter().enumerate() {
                    let v = self.atom_val(a, fr, funcs);
                    self.store_field_barrier(obj, i, v, *alloc);
                }
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
            Comp::Foreign(symbol) => {
                // An FFI postulate (spec §7.6): declare (once) and call the external C function
                // `BlValue <symbol>(void)`, taking its result as this computation's value. The C
                // symbol is responsible for any GC-heap allocation of the value it returns.
                let func = self.module.get_function(symbol).unwrap_or_else(|| {
                    let fty = self.ptr_ty().fn_type(&[], false);
                    self.module
                        .add_function(symbol, fty, Some(Linkage::External))
                });
                self.builder
                    .build_call(func, &[], "foreign")
                    .unwrap()
                    .try_as_basic_value()
                    .unwrap_basic()
                    .into_pointer_value()
            }
            Comp::IntLit(n) => {
                let i64t = self.context.i64_type();
                self.box_int(i64t.const_int(*n as u64, true))
            }
            Comp::IntPrim { op, lhs, rhs } => {
                use blight_kernel::IntPrimOp;
                let l = self.atom_val(lhs, fr, funcs);
                let r = self.atom_val(rhs, fr, funcs);
                let lv = self.load_aux_i64(l);
                let rv = self.load_aux_i64(r);
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
        }
    }

    fn global_str(&self, s: &str) -> PointerValue<'ctx> {
        let gv = self.builder.build_global_string_ptr(s, "str").unwrap();
        gv.as_pointer_value()
    }

    fn write_object(&self, out_path: &std::path::Path, target: Target) -> Result<(), String> {
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
                // The module's data layout/triple must match the target machine for wasm.
                self.module.set_triple(&triple);
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
        if matches!(target, Target::Wasm32) {
            self.module
                .set_data_layout(&machine.get_target_data().get_data_layout());
        }
        machine
            .write_to_file(&self.module, FileType::Object, out_path)
            .map_err(|e| e.to_string())
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
        for src in ["gc.c", "stack.c", "delay.c", "effects.c", "prelude_rt.c"] {
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
            for src in ["gc.c", "stack.c", "delay.c", "effects.c", "arena.c"] {
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
  unsigned tag = r ? (unsigned)BL_TAG(r) : 999u;
  unsigned long long aux = r ? (unsigned long long)r->header.aux : 0ull;
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
}
