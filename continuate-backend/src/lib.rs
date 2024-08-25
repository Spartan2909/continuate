mod function;
use function::FunctionCompiler;
use function::FunctionRuntime;

use std::collections::HashMap;
use std::mem;

use bumpalo::Bump;

use continuate_ir::common::FuncRef;
use continuate_ir::common::Ident;
use continuate_ir::common::TypeRef;
use continuate_ir::lib_std::StdLib;
use continuate_ir::mid_level_ir::Function as MirFunction;
use continuate_ir::mid_level_ir::FunctionTy;
use continuate_ir::mid_level_ir::Program;
use continuate_ir::mid_level_ir::Type as MirType;
use continuate_ir::mid_level_ir::TypeConstructor;
use continuate_ir::mid_level_ir::UserDefinedType;

use continuate_common::SingleLayout;
use continuate_common::Slice;
use continuate_common::TyLayout;

use cranelift::codegen::ir::types;
use cranelift::codegen::ir::AbiParam;
use cranelift::codegen::ir::Function;
use cranelift::codegen::ir::InstBuilder;
use cranelift::codegen::ir::Signature;
use cranelift::codegen::ir::Type;
use cranelift::codegen::ir::UserExternalName;
use cranelift::codegen::ir::UserFuncName;
use cranelift::codegen::isa;
use cranelift::codegen::isa::CallConv;
use cranelift::codegen::settings;
use cranelift::codegen::settings::Configurable;
use cranelift::codegen::settings::Flags;
use cranelift::codegen::settings::FlagsOrIsa;
use cranelift::codegen::verify_function;
use cranelift::codegen::Context;
use cranelift::frontend::FunctionBuilder;
use cranelift::frontend::FunctionBuilderContext;

use cranelift_module::default_libcall_names;
use cranelift_module::DataDescription;
use cranelift_module::DataId;
use cranelift_module::FuncId;
use cranelift_module::Linkage;
use cranelift_module::Module;

use cranelift_object::ObjectBuilder;
use cranelift_object::ObjectModule;
use cranelift_object::ObjectProduct;

use itertools::Itertools as _;

use tracing::info;
use tracing::warn;

use target_lexicon::Endianness;
use target_lexicon::PointerWidth;
use target_lexicon::Triple;

struct Runtime {
    /// `fn(ty_layout: &'static TyLayout<'static>) -> *mut ()`
    alloc_gc: FuncId,

    /// `fn(len: usize) -> *mut ()`
    alloc_string: FuncId,

    /// `fn(ptr: *const ())`
    mark_root: FuncId,

    /// `fn(ptr: *const ())`
    unmark_root: FuncId,

    /// `fn()`
    init: FuncId,
}

impl Runtime {
    fn new<M: Module>(module: &mut M) -> Runtime {
        let ptr_ty = Type::triple_pointer_type(module.isa().triple());

        let mut alloc_gc_sig = module.make_signature();
        alloc_gc_sig.params.push(AbiParam::new(ptr_ty));
        alloc_gc_sig.returns.push(AbiParam::new(ptr_ty));
        let alloc_gc = module
            .declare_function("cont_rt_alloc_gc", Linkage::Import, &alloc_gc_sig)
            .unwrap();

        let mut alloc_string_sig = module.make_signature();
        alloc_string_sig.params.push(AbiParam::new(ptr_ty));
        alloc_string_sig.returns.push(AbiParam::new(ptr_ty));
        let alloc_string = module
            .declare_function("cont_rt_alloc_string", Linkage::Import, &alloc_string_sig)
            .unwrap();

        let mut mark_unmark_root_sig = module.make_signature();
        mark_unmark_root_sig.params.push(AbiParam::new(types::I64));
        let mark_root = module
            .declare_function("cont_rt_mark_root", Linkage::Import, &mark_unmark_root_sig)
            .unwrap();
        let unmark_root = module
            .declare_function(
                "cont_rt_unmark_root",
                Linkage::Import,
                &mark_unmark_root_sig,
            )
            .unwrap();

        let init = module
            .declare_function("cont_rt_init", Linkage::Import, &module.make_signature())
            .unwrap();

        Runtime {
            alloc_gc,
            alloc_string,
            mark_root,
            unmark_root,
            init,
        }
    }
}

const fn u64_as_endianness(value: u64, endianness: Endianness) -> [u8; 8] {
    match endianness {
        Endianness::Big => value.to_be_bytes(),
        Endianness::Little => value.to_le_bytes(),
    }
}

enum Callable {
    FuncRef(FuncRef),
    Variable(Ident),
}

fn ptr_ty(triple: &Triple) -> Type {
    Type::triple_pointer_type(triple)
}

fn fat_ptr_ty(triple: &Triple) -> Type {
    Type::int(ptr_ty(triple).bits() as u16 * 2).unwrap()
}

fn int_as_target_usize<T: Into<u64>>(i: T, sink: &mut Vec<u8>, triple: &Triple) {
    let i: u64 = i.into();
    match (
        triple.endianness().unwrap(),
        triple.pointer_width().unwrap(),
    ) {
        (Endianness::Big, PointerWidth::U64) => sink.extend(i.to_be_bytes()),
        (Endianness::Little, PointerWidth::U64) => sink.extend(i.to_le_bytes()),
        (Endianness::Big, PointerWidth::U32) => {
            sink.extend(u32::try_from(i).unwrap().to_be_bytes());
        }
        (Endianness::Little, PointerWidth::U32) => {
            sink.extend(u32::try_from(i).unwrap().to_le_bytes());
        }
        (_, PointerWidth::U16) => unimplemented!("16-bit pointers are not supported"),
    }
}

fn declare_static<M: Module>(
    contents: Box<[u8]>,
    align: Option<u64>,
    module: &mut M,
    data_description: &mut DataDescription,
) -> Option<DataId> {
    if contents.is_empty() {
        return None;
    }

    let global = module.declare_anonymous_data(false, false).unwrap();
    data_description.clear();
    data_description.define(contents);
    data_description.align = align;
    module.define_data(global, data_description).unwrap();

    Some(global)
}

fn dangling_static_ptr<M: Module>(
    align: Option<u64>,
    module: &mut M,
    data_description: &mut DataDescription,
    triple: &Triple,
) -> DataId {
    let ptr = module.declare_anonymous_data(false, false).unwrap();
    data_description.clear();
    let mut contents = Vec::with_capacity(ptr_ty(triple).bytes() as usize);
    int_as_target_usize(align.unwrap_or(1), &mut contents, triple);
    data_description.define(contents.into_boxed_slice());
    module.define_data(ptr, data_description).unwrap();
    ptr
}

fn ty_for(ty: TypeRef, triple: &Triple, lib_std: &StdLib) -> Type {
    if ty == lib_std.ty_int {
        types::I64
    } else if ty == lib_std.ty_float {
        types::F64
    } else if ty == lib_std.ty_bool {
        types::I8
    } else if ty == lib_std.ty_string {
        types::I128
    } else {
        ptr_ty(triple)
    }
}

fn ty_ref_size_align_ptr(ty: TypeRef, program: &Program) -> (u64, u64, bool) {
    match **program.types.get_by_left(&ty).unwrap() {
        _ if ty == program.lib_std.ty_bool => (1, 1, false),
        MirType::Int | MirType::Float => (8, 8, false),
        MirType::Array(_, _)
        | MirType::Tuple(_)
        | MirType::Function(_)
        | MirType::UserDefined(_) => (8, 8, true),
        MirType::String => (16, 8, true),
        MirType::Unknown => unreachable!(),
        MirType::None => (0, 1, false),
    }
}

fn signature_from_function_ty(
    function_ty: &FunctionTy,
    call_conv: CallConv,
    triple: &Triple,
    program: &Program,
) -> Signature {
    let mut signature = Signature::new(call_conv);
    signature.params = function_ty
        .params
        .iter()
        .copied()
        .chain(
            function_ty
                .continuations
                .iter()
                .sorted_by_key(|&(&param, _)| param)
                .map(|(_, &param_ty)| param_ty),
        )
        .map(|param_ty| AbiParam::new(ty_for(param_ty, triple, &program.lib_std)))
        .collect();
    signature.returns.push(AbiParam::new(types::I64));
    signature
}

struct Compiler<'arena, 'a, M> {
    program: Program<'a>,
    module: M,
    context: Context,
    data_description: DataDescription,
    triple: Triple,
    runtime: Runtime,
    functions: HashMap<FuncRef, (FuncId, Signature)>,
    ty_layouts: HashMap<TypeRef, (&'arena TyLayout<'arena>, DataId)>,
    arena: &'arena &'arena Bump,
}

impl<'arena, 'a, M: Module> Compiler<'arena, 'a, M> {
    fn new(
        program: Program<'a>,
        mut module: M,
        arena: &'arena &'arena Bump,
    ) -> Compiler<'arena, 'a, M> {
        let triple = module.isa().triple().clone();
        let runtime = Runtime::new(&mut module);
        Compiler {
            program,
            module,
            context: Context::new(),
            data_description: DataDescription::new(),
            triple,
            runtime,
            functions: HashMap::new(),
            ty_layouts: HashMap::new(),
            arena,
        }
    }

    #[tracing::instrument(skip(self))]
    fn c_int_ty(&self) -> Type {
        Type::int(self.triple.data_model().unwrap().int_size().bits().into()).unwrap()
    }

    #[tracing::instrument(skip_all)]
    fn function(
        &mut self,
        mir_function: &MirFunction,
        func_ref: FuncRef,
        func_ctx: &mut FunctionBuilderContext,
    ) {
        let name = &mir_function.name;
        info!("compiling function '{name}'");

        let params: Vec<_> = mir_function
            .params
            .iter()
            .copied()
            .chain(
                mir_function
                    .continuations
                    .iter()
                    .map(|(&param, &param_ty)| (param, param_ty))
                    .sorted_by_key(|&(param, _)| param),
            )
            .collect();

        let (func_id, ref sig) = self.functions[&func_ref];

        let name = UserFuncName::User(UserExternalName::new(2, func_ref.into()));
        let mut function = Function::with_name_signature(name, sig.clone());
        let mut builder = FunctionBuilder::new(&mut function, func_ctx);

        let block_map: HashMap<_, _> = mir_function
            .blocks
            .keys()
            .map(|&id| (id, builder.create_block()))
            .collect();

        let function_runtime = FunctionRuntime {
            alloc_gc: self
                .module
                .declare_func_in_func(self.runtime.alloc_gc, builder.func),
            alloc_string: self
                .module
                .declare_func_in_func(self.runtime.alloc_string, builder.func),
            mark_root: self
                .module
                .declare_func_in_func(self.runtime.mark_root, builder.func),
            unmark_root: self
                .module
                .declare_func_in_func(self.runtime.unmark_root, builder.func),
        };

        let function_compiler = FunctionCompiler {
            program: &self.program,
            module: &mut self.module,
            data_description: &mut self.data_description,
            triple: &self.triple,
            functions: &self.functions,
            ty_layouts: &self.ty_layouts,
            builder: &mut builder,
            block_map: &block_map,
            mir_function,
            params: &params,
            function_runtime,
            vars: HashMap::new(),
            temp_roots: Vec::new(),
        };

        function_compiler.compile();

        builder.seal_all_blocks();
        builder.finalize();

        let flags = Flags::new(settings::builder());
        let fisa = FlagsOrIsa {
            flags: &flags,
            isa: Some(self.module.isa()),
        };
        if let Err(errors) = verify_function(&function, fisa) {
            panic!("{errors}");
        }

        self.context.clear();
        #[cfg(debug_assertions)]
        {
            self.context.want_disasm = true;
        }
        self.context.func = function;
        self.module
            .define_function(func_id, &mut self.context)
            .unwrap();
    }

    fn compund_ty_layout(&self, types: &[&[TypeRef]]) -> SingleLayout<'arena> {
        let mut size = 0;
        let mut align = 1;
        let mut field_locations = Vec::with_capacity(types.len());
        let mut gc_pointer_locations = Vec::with_capacity(types.len());
        for &ty in types.iter().copied().flatten() {
            let (field_size, field_align, ptr) = ty_ref_size_align_ptr(ty, &self.program);
            let misalignment = size % field_align;
            if misalignment != 0 {
                size += field_align - misalignment;
            }
            field_locations.push(size);
            if ptr {
                gc_pointer_locations.push(size);
            }
            size += field_size;
            align = align.max(field_align);
        }
        SingleLayout {
            size,
            align,
            field_locations: Slice::allocate_slice(&field_locations, self.arena),
            gc_pointer_locations: Slice::allocate_slice(&gc_pointer_locations, self.arena),
        }
    }

    fn append_single_layout_global(
        &mut self,
        layout: &SingleLayout,
        contents: &mut Vec<u8>,
    ) -> (u32, DataId) {
        let gc_pointer_locations = declare_static(
            layout.field_locations.as_byte_slice().as_slice().into(),
            Some(8),
            &mut self.module,
            &mut self.data_description,
        );

        let endianness = self.triple.endianness().unwrap();
        let offset = contents.len();

        contents.extend(u64_as_endianness(layout.size, endianness));
        contents.extend(u64_as_endianness(layout.align, endianness));
        int_as_target_usize(8u64, contents, &self.triple); // field_locations.ptr
        int_as_target_usize(0u64, contents, &self.triple); // field_locations.len
        int_as_target_usize(8u64, contents, &self.triple); // gc_pointer_locations.ptr
        int_as_target_usize(
            layout.gc_pointer_locations.len() as u64,
            contents,
            &self.triple,
        );

        (
            (mem::offset_of!(SingleLayout, gc_pointer_locations) + offset) as u32,
            gc_pointer_locations.unwrap_or_else(|| {
                dangling_static_ptr(
                    Some(8),
                    &mut self.module,
                    &mut self.data_description,
                    &self.triple,
                )
            }),
        )
    }

    fn declare_single_layout_global(
        &mut self,
        layout: &SingleLayout,
        mut contents: Vec<u8>,
    ) -> DataId {
        let (offset, gc_pointer_locations) =
            self.append_single_layout_global(layout, &mut contents);

        let layout_global = self.module.declare_anonymous_data(false, false).unwrap();
        self.data_description.clear();
        self.data_description.define(contents.into_boxed_slice());

        let gc_pointer_locations = self
            .module
            .declare_data_in_data(gc_pointer_locations, &mut self.data_description);
        self.data_description
            .write_data_addr(offset, gc_pointer_locations, 0);

        self.module
            .define_data(layout_global, &self.data_description)
            .unwrap();

        layout_global
    }

    fn declare_ty_layout_global(&mut self, layout: &TyLayout) -> DataId {
        match *layout {
            TyLayout::Single(ref layout) => {
                let contents = vec![0; ptr_ty(&self.triple).bytes() as usize];
                self.declare_single_layout_global(layout, contents)
            }
            TyLayout::Sum {
                layouts,
                size,
                align,
            } => {
                let mut contents = Vec::new();
                let mut relocs = Vec::with_capacity(layouts.len());
                for layout in layouts {
                    relocs.push(self.append_single_layout_global(layout, &mut contents));
                }

                let variant_layouts = self.module.declare_anonymous_data(false, false).unwrap();
                self.data_description.clear();
                self.data_description.define(contents.into_boxed_slice());
                for (offset, data_id) in relocs {
                    let data = self
                        .module
                        .declare_data_in_data(data_id, &mut self.data_description);
                    self.data_description.write_data_addr(offset, data, 0);
                }
                self.module
                    .define_data(variant_layouts, &self.data_description)
                    .unwrap();

                let layout = self.module.declare_anonymous_data(false, false).unwrap();
                self.data_description.clear();

                let ptr_size = ptr_ty(&self.triple).bytes();
                let mut contents = vec![1];
                contents.extend(vec![0; ptr_size as usize - 1]);
                int_as_target_usize(8u64, &mut contents, &self.triple); // layouts.ptr
                int_as_target_usize(layouts.len() as u64, &mut contents, &self.triple);

                let gv = self
                    .module
                    .declare_data_in_data(variant_layouts, &mut self.data_description);
                self.data_description.write_data_addr(ptr_size, gv, 0);

                let endianness = self.triple.endianness().unwrap();
                contents.extend(u64_as_endianness(size, endianness));
                contents.extend(u64_as_endianness(align, endianness));
                self.data_description.define(contents.into_boxed_slice());

                self.module
                    .define_data(layout, &self.data_description)
                    .unwrap();

                layout
            }
            TyLayout::String => declare_static(
                [2].into(),
                None,
                &mut self.module,
                &mut self.data_description,
            )
            .unwrap(),
        }
    }

    fn calc_ty_layout(&mut self, ty_ref: TypeRef) {
        let ty = *self.program.types.get_by_left(&ty_ref).unwrap();
        let layout: TyLayout<'arena> = match *ty {
            _ if ty_ref == self.program.lib_std.ty_bool => SingleLayout::primitive(1, 1).into(),
            MirType::Int | MirType::Float | MirType::Function(_) => {
                SingleLayout::primitive(8, 8).into()
            }
            MirType::String => TyLayout::String,
            MirType::Array(elem_ty, len) => {
                let (elem_size, elem_align, ptr) = ty_ref_size_align_ptr(elem_ty, &self.program);
                let field_locations: Vec<_> =
                    (0..elem_size * len).step_by(elem_size as usize).collect();
                let field_locations = Slice::allocate_slice(&field_locations, self.arena);
                SingleLayout {
                    size: elem_align * len,
                    align: elem_align,
                    field_locations,
                    gc_pointer_locations: if ptr {
                        field_locations
                    } else {
                        Slice::new(&[])
                    },
                }
                .into()
            }
            MirType::Tuple(ref types)
            | MirType::UserDefined(UserDefinedType {
                constructor: TypeConstructor::Product(ref types),
            }) => self.compund_ty_layout(&[types]).into(),
            MirType::UserDefined(UserDefinedType {
                constructor: TypeConstructor::Sum(ref variants),
            }) => {
                let layouts: Vec<_> = variants
                    .iter()
                    .map(|types| self.compund_ty_layout(&[&[self.program.lib_std.ty_int], types]))
                    .collect();
                let size = layouts.iter().fold(8, |size, layout| size.max(layout.size));
                let align = layouts
                    .iter()
                    .fold(1, |align, layout| align.max(layout.align));

                TyLayout::Sum {
                    layouts: Slice::allocate_slice(&layouts, self.arena),
                    size,
                    align,
                }
            }
            MirType::Unknown => unreachable!(),
            MirType::None => SingleLayout::primitive(0, 1).into(),
        };

        let global_id = self.declare_ty_layout_global(&layout);
        self.ty_layouts
            .insert(ty_ref, (self.arena.alloc(layout), global_id));
    }

    fn calc_ty_layouts(&mut self) {
        let types: Vec<_> = self.program.types.left_values().copied().collect();
        for ty in types {
            self.calc_ty_layout(ty);
        }
    }

    fn declare_functions(&mut self) {
        for (&func_ref, &function) in &self.program.functions {
            let params: Vec<_> = function
                .params
                .iter()
                .copied()
                .chain(
                    function
                        .continuations
                        .iter()
                        .map(|(&param, &param_ty)| (param, param_ty))
                        .sorted_by_key(|&(param, _)| param),
                )
                .map(|(param, param_ty)| {
                    (param, ty_for(param_ty, &self.triple, &self.program.lib_std))
                })
                .collect();

            let mut sig = Signature::new(CallConv::Tail);
            for &(_, param_ty) in &params {
                sig.params.push(AbiParam::new(param_ty));
            }
            sig.returns.push(AbiParam::new(types::I64));

            let id = self
                .module
                .declare_function(&function.name, Linkage::Local, &sig)
                .unwrap();
            self.functions.insert(func_ref, (id, sig));
        }
    }

    fn compile_module(&mut self, func_ctx: &mut FunctionBuilderContext) {
        self.calc_ty_layouts();

        self.declare_functions();

        let functions: Vec<_> = self
            .program
            .functions
            .iter()
            .map(|(&func_ref, &func)| (func_ref, func))
            .collect();
        for (func_ref, function) in functions {
            self.function(function, func_ref, func_ctx);
        }
    }
}

impl<'arena, 'a> Compiler<'arena, 'a, ObjectModule> {
    fn compile_library(mut self) -> ObjectProduct {
        self.compile_module(&mut FunctionBuilderContext::new());

        self.module.finish()
    }

    fn compile_binary(mut self) -> ObjectProduct {
        let mut func_ctx = FunctionBuilderContext::new();

        self.compile_module(&mut func_ctx);

        let c_int = self.c_int_ty();

        let mut signature = self.module.make_signature();
        signature.returns.push(AbiParam::new(c_int));

        let main = self
            .module
            .declare_function("main", Linkage::Export, &signature)
            .unwrap();
        let name = UserFuncName::User(UserExternalName::new(1, 0));
        let mut function = Function::with_name_signature(name, signature);
        let mut builder = FunctionBuilder::new(&mut function, &mut func_ctx);

        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);

        let init = self
            .module
            .declare_func_in_func(self.runtime.init, builder.func);
        let results = builder.ins().call(init, &[]);
        debug_assert_eq!(builder.inst_results(results).len(), 0);

        let entry_point = self.functions[&self.program.entry_point()].0;
        let entry_point = self.module.declare_func_in_func(entry_point, builder.func);

        let termination_ref = self.program.lib_std.fn_termination;
        let termination = self.functions[&termination_ref].0;
        let termination = self.module.declare_func_in_func(termination, builder.func);
        let termination_addr = builder.ins().func_addr(ptr_ty(&self.triple), termination);
        let result = builder.ins().call(entry_point, &[termination_addr]);
        let rvals = builder.inst_results(result);
        debug_assert_eq!(rvals.len(), 1);
        let rval = rvals[0];

        let rval = builder.ins().ireduce(c_int, rval);
        builder.ins().return_(&[rval]);

        builder.finalize();

        self.context.clear();
        self.context.func = function;
        self.module
            .define_function(main, &mut self.context)
            .unwrap();

        self.module.finish()
    }
}

#[allow(clippy::missing_panics_doc)]
pub fn compile(program: Program, binary: bool) -> ObjectProduct {
    let mut flags = settings::builder();
    flags.enable("preserve_frame_pointers").unwrap();
    flags.enable("is_pic").unwrap();
    let isa = isa::lookup(target_lexicon::HOST)
        .unwrap()
        .finish(Flags::new(flags))
        .unwrap();
    let mut builder =
        ObjectBuilder::new(isa, program.name.clone(), default_libcall_names()).unwrap();
    if cfg!(debug_assertions) {
        builder.per_function_section(true);
    }

    let module = ObjectModule::new(builder);

    let arena = Bump::new();
    let tmp = &arena;
    let compiler = Compiler::new(program, module, &tmp);
    if binary {
        compiler.compile_binary()
    } else {
        compiler.compile_library()
    }
}
