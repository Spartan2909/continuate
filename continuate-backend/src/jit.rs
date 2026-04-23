#![allow(unsafe_code)]

use crate::{Compiler, call_entry_point};

use std::mem;

use bumpalo::Bump;

use continuate_ir::{common::FuncRef, mid_level_ir::Program};

use cranelift::{
    codegen::ir::{AbiParam, Function, InstBuilder, UserExternalName, UserFuncName, types},
    frontend::FunctionBuilder,
    jit::{JITBuilder, JITModule},
    module::{Module, ModuleResult, default_libcall_names},
};

pub struct JitResult {
    module: Option<JITModule>,
    f: extern "C" fn() -> i64,
    stack_maps: *const (),
}

impl JitResult {
    unsafe fn new(
        module: JITModule,
        f: extern "C" fn() -> i64,
        stack_maps: *const (),
    ) -> JitResult {
        JitResult {
            module: Some(module),
            f,
            stack_maps,
        }
    }

    #[inline]
    pub fn run(&self) -> i64 {
        let _lock = continuate_rt::garbage_collector::set_stack_maps_ptr(self.stack_maps);
        (self.f)()
    }
}

impl Drop for JitResult {
    #[inline]
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
    fn compile_jit(mut self) -> crate::ModuleResult<JitResult> {
        let stack_maps = self.compile_module()?;

        let mut signature = self.module.make_signature();
        signature.returns.push(AbiParam::new(types::I64));

        let main = self.module.declare_anonymous_function(&signature)?;
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
        self.module.define_function(main, &mut context)?;

        self.module.finalize_definitions()?;

        let main = self.module.get_finalized_function(main);

        // SAFETY: This is the correct signature for `main`.
        let main = unsafe { mem::transmute::<*const u8, extern "C" fn() -> i64>(main) };

        let stack_maps = self.module.get_finalized_data(stack_maps).0;

        // SAFETY: No functions from `self.module` are ever called.
        let res = unsafe { JitResult::new(self.module, main, stack_maps.cast()) };
        Ok(res)
    }
}

/// Compile a program to an immediately runnable [`JitResult`].
///
/// # Errors
///
/// Returns an error if the module fails to encode the program.
#[expect(clippy::result_large_err, reason = "this is a standard cranelift type")]
#[inline]
pub fn compile(program: Program) -> ModuleResult<JitResult> {
    use continuate_rt::garbage_collector as rt;
    let mut builder = JITBuilder::with_flags(crate::flags(), default_libcall_names())?;
    builder.symbols([
        ("cont_rt_alloc_string", rt::alloc_string as _),
        ("cont_rt_alloc_gc", rt::alloc_gc as _),
    ]);
    let module = JITModule::new(builder);

    let arena = Bump::new();
    let compiler = Compiler::new(program, module, &arena)?;
    Ok(compiler.compile_jit()?)
}
