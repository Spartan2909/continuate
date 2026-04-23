use crate::{Compiler, call_entry_point};

use bumpalo::Bump;

use continuate_ir::{common::FuncRef, mid_level_ir::Program};

use cranelift::{
    codegen::{
        ir::{AbiParam, Function, InstBuilder, Type, UserExternalName, UserFuncName},
        isa,
        settings::{self, Configurable, Flags},
    },
    frontend::FunctionBuilder,
    module::{Linkage, Module, ModuleResult, default_libcall_names},
    object::{ObjectBuilder, ObjectModule, ObjectProduct},
};

impl Compiler<'_, ObjectModule> {
    #[tracing::instrument(skip(self))]
    fn c_int_ty(&self) -> Type {
        Type::int(self.triple.data_model().unwrap().int_size().bits().into()).unwrap()
    }

    fn compile_library(mut self) -> crate::ModuleResult<ObjectProduct> {
        self.compile_module()?;

        Ok(self.module.finish())
    }

    fn compile_binary(mut self) -> crate::ModuleResult<ObjectProduct> {
        self.compile_module()?;

        let c_int = self.c_int_ty();

        let mut signature = self.module.make_signature();
        signature.returns.push(AbiParam::new(c_int));

        let main = self
            .module
            .declare_function("main", Linkage::Export, &signature)?;
        let name = UserFuncName::User(UserExternalName::new(1, 0));
        let mut function = Function::with_name_signature(name, signature);
        let mut func_ctx = self.builder_contexts.get();
        let mut builder = FunctionBuilder::new(&mut function, &mut func_ctx);

        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);

        let init = self.module.declare_function(
            "cont_rt_init",
            Linkage::Import,
            &self.module.make_signature(),
        )?;

        let init = self.module.declare_func_in_func(init, builder.func);
        let results = builder.ins().call(init, &[]);
        debug_assert_eq!(builder.inst_results(results).len(), 0);

        let termination_ref = self.program.lib_std.fn_termination;
        let rval = call_entry_point(
            self.functions[&FuncRef::ENTRY_POINT].0,
            self.functions[&termination_ref].0,
            &self.triple,
            &mut builder,
            &mut self.module,
        );

        let cleanup = self.module.declare_function(
            "cont_rt_cleanup",
            Linkage::Import,
            &self.module.make_signature(),
        )?;

        let cleanup = self.module.declare_func_in_func(cleanup, builder.func);
        let results = builder.ins().call(cleanup, &[]);
        debug_assert_eq!(builder.inst_results(results).len(), 0);

        let rval = builder.ins().ireduce(c_int, rval);
        builder.ins().return_(&[rval]);

        builder.finalize();

        let mut context = self.contexts.get();
        context.clear();
        context.func = function;
        self.module.define_function(main, &mut context)?;

        Ok(self.module.finish())
    }
}

/// Compile a program to an object.
///
/// # Errors
///
/// Returns an error if the module fails to encode the program.
#[expect(clippy::result_large_err, reason = "this is a standard cranelift type")]
#[inline]
pub fn compile(program: Program, binary: bool) -> ModuleResult<ObjectProduct> {
    let mut flags = settings::builder();
    for (flag, value) in crate::flags() {
        flags.set(flag, value)?;
    }
    let isa = isa::lookup(target_lexicon::HOST)
        .map_err(|_| {
            cranelift::codegen::CodegenError::Unsupported(format!(
                "target {}",
                target_lexicon::HOST
            ))
        })?
        .finish(Flags::new(flags))?;
    let mut builder = ObjectBuilder::new(isa, program.name.clone(), default_libcall_names())?;
    if cfg!(debug_assertions) {
        builder.per_function_section(true);
    }

    let module = ObjectModule::new(builder);

    let arena = Bump::new();
    let compiler = Compiler::new(program, module, &arena)?;
    if binary {
        Ok(compiler.compile_binary()?)
    } else {
        Ok(compiler.compile_library()?)
    }
}
