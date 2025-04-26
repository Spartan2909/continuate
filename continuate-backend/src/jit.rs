#![allow(unsafe_code)]

use crate::call_entry_point;
use crate::pretty_unwrap;
use crate::Compiler;

use std::mem;

use bumpalo::Bump;

use continuate_ir::common::FuncRef;
use continuate_ir::mid_level_ir::Program;

use cranelift::codegen::ir::types;
use cranelift::codegen::ir::AbiParam;
use cranelift::codegen::ir::Function;
use cranelift::codegen::ir::InstBuilder;
use cranelift::codegen::ir::UserExternalName;
use cranelift::codegen::ir::UserFuncName;
use cranelift::frontend::FunctionBuilder;
use cranelift::jit::JITBuilder;
use cranelift::jit::JITModule;
use cranelift::module::default_libcall_names;
use cranelift::module::Module;

pub struct JitResult {
    module: Option<JITModule>,
    f: extern "C" fn() -> i64,
}

impl JitResult {
    unsafe fn new(module: JITModule, f: extern "C" fn() -> i64) -> JitResult {
        JitResult {
            module: Some(module),
            f,
        }
    }

    pub fn run(&self) -> i64 {
        (self.f)()
    }
}

impl Drop for JitResult {
    fn drop(&mut self) {
        if let Some(module) = self.module.take() {
            // SAFETY: No functions from `self.module` will be used outside of `self`.
            unsafe {
                module.free_memory();
            }
        }
    }
}

impl Compiler<'_, JITModule> {
    fn compile_jit(mut self) -> JitResult {
        self.compile_module();

        let mut signature = self.module.make_signature();
        signature.returns.push(AbiParam::new(types::I64));

        let main = pretty_unwrap(self.module.declare_anonymous_function(&signature));
        let name = UserFuncName::User(UserExternalName::new(1, 0));
        let mut function = Function::with_name_signature(name, signature);
        let mut func_ctx = self.builder_contexts.get();
        let mut builder = FunctionBuilder::new(&mut function, &mut func_ctx);

        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);

        let termination_ref = self.program.lib_std.fn_termination;
        let rval = call_entry_point(
            self.functions[&FuncRef::ENTRY_POINT].0,
            self.functions[&termination_ref].0,
            &self.triple,
            &mut builder,
            &mut self.module,
        );

        builder.ins().return_(&[rval]);

        builder.finalize();

        let mut context = self.contexts.get();
        context.clear();
        context.func = function;
        pretty_unwrap(self.module.define_function(main, &mut context));

        pretty_unwrap(self.module.finalize_definitions());

        let main = self.module.get_finalized_function(main);

        // SAFETY: This is the correct signature for `main`.
        let main = unsafe { mem::transmute::<*const u8, extern "C" fn() -> i64>(main) };

        // SAFETY: No functions from `self.module` are ever called.
        unsafe { JitResult::new(self.module, main) }
    }
}

#[allow(clippy::missing_panics_doc)]
pub fn jit_compile(program: Program) -> JitResult {
    use continuate_rt::garbage_collector as rt;
    let mut builder = JITBuilder::with_flags(
        &[
            ("preserve_frame_pointers", "true"),
            ("is_pic", "true"),
            ("enable_llvm_abi_extensions", "true"),
        ],
        default_libcall_names(),
    )
    .unwrap();
    builder.symbols([
        ("cont_rt_alloc_string", rt::alloc_string as _),
        ("cont_rt_alloc_gc", rt::alloc_gc as _),
        ("cont_rt_mark_root", rt::mark_root as _),
        ("cont_rt_unmark_root", rt::unmark_root as _),
        ("cont_rt_unmark_temp_root", rt::unmark_temp_root as _),
    ]);
    let module = JITModule::new(builder);

    let arena = Bump::new();
    let compiler = Compiler::new(program, module, &arena);
    compiler.compile_jit()
}
