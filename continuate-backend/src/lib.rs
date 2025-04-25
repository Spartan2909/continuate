mod function;
use function::FunctionCompilerBuilder;
use function::FunctionRuntime;

mod linked_list;
use linked_list::LinkedList;

use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::rc::Rc;

use bumpalo::Bump;

use continuate_ir::common::FuncRef;
use continuate_ir::mid_level_ir::Function as MirFunction;
use continuate_ir::mid_level_ir::FunctionTy;
use continuate_ir::mid_level_ir::Program;
use continuate_ir::mid_level_ir::Type as MirType;
use continuate_ir::mid_level_ir::UserDefinedType;

use continuate_rt::layout::SingleLayout;
use continuate_rt::layout::TyLayout;
use continuate_rt::slice::Slice;

use cranelift::codegen::ir::entities::Value;
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
use cranelift::module::default_libcall_names;
use cranelift::module::DataDescription;
use cranelift::module::DataId;
use cranelift::module::FuncId;
use cranelift::module::Linkage;
use cranelift::module::Module;
use cranelift::object::ObjectBuilder;
use cranelift::object::ObjectModule;
use cranelift::object::ObjectProduct;

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

    /// `fn()`
    cleanup: FuncId,
}

impl Runtime {
    fn new<M: Module + ?Sized>(module: &mut M) -> Runtime {
        let ptr_ty = Type::triple_pointer_type(module.isa().triple());

        let mut alloc_gc_sig = module.make_signature();
        alloc_gc_sig.params.push(AbiParam::new(ptr_ty));
        alloc_gc_sig.returns.push(AbiParam::new(ptr_ty));
        let alloc_gc = pretty_unwrap(module.declare_function(
            "cont_rt_alloc_gc",
            Linkage::Import,
            &alloc_gc_sig,
        ));

        let mut alloc_string_sig = module.make_signature();
        alloc_string_sig.params.push(AbiParam::new(ptr_ty));
        alloc_string_sig.returns.push(AbiParam::new(ptr_ty));
        let alloc_string = pretty_unwrap(module.declare_function(
            "cont_rt_alloc_string",
            Linkage::Import,
            &alloc_string_sig,
        ));

        let mut mark_unmark_root_sig = module.make_signature();
        mark_unmark_root_sig.params.push(AbiParam::new(types::I64));
        let mark_root = pretty_unwrap(module.declare_function(
            "cont_rt_mark_root",
            Linkage::Import,
            &mark_unmark_root_sig,
        ));
        let unmark_root = pretty_unwrap(module.declare_function(
            "cont_rt_unmark_root",
            Linkage::Import,
            &mark_unmark_root_sig,
        ));

        let init = pretty_unwrap(module.declare_function(
            "cont_rt_init",
            Linkage::Import,
            &module.make_signature(),
        ));

        let cleanup = pretty_unwrap(module.declare_function(
            "cont_rt_cleanup",
            Linkage::Import,
            &module.make_signature(),
        ));

        Runtime {
            alloc_gc,
            alloc_string,
            mark_root,
            unmark_root,
            init,
            cleanup,
        }
    }
}

const fn u64_as_endianness(value: u64, endianness: Endianness) -> [u8; 8] {
    match endianness {
        Endianness::Big => value.to_be_bytes(),
        Endianness::Little => value.to_le_bytes(),
    }
}

fn pretty_unwrap<T, E: fmt::Display>(res: Result<T, E>) -> T {
    match res {
        Ok(val) => val,
        Err(error) => panic!("{error}"),
    }
}

enum Callable {
    Static(FuncRef),
    Dynamic(Value),
}

fn ptr_ty(triple: &Triple) -> Type {
    Type::triple_pointer_type(triple)
}

fn fat_ptr_ty(triple: &Triple) -> Type {
    Type::int(ptr_ty(triple).bits() as u16 * 2).unwrap()
}

fn fat_ptr(
    thin_ptr: Value,
    metadata: Value,
    triple: &Triple,
    builder: &mut FunctionBuilder,
) -> Value {
    let fat_ptr_ty = fat_ptr_ty(triple);

    let rotation_places = i64::from(ptr_ty(triple).bits());
    let fat_ptr = builder.ins().uextend(fat_ptr_ty, thin_ptr);
    let fat_ptr = builder.ins().rotl_imm(fat_ptr, rotation_places);
    let metadata = builder.ins().uextend(fat_ptr_ty, metadata);
    builder.ins().bor(fat_ptr, metadata)
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

fn declare_static<M: Module + ?Sized>(
    contents: Box<[u8]>,
    align: Option<u64>,
    module: &mut M,
    data_description: &mut DataDescription,
) -> Option<DataId> {
    if contents.is_empty() {
        return None;
    }

    let global = pretty_unwrap(module.declare_anonymous_data(false, false));
    data_description.clear();
    data_description.define(contents);
    data_description.align = align;
    pretty_unwrap(module.define_data(global, data_description));

    Some(global)
}

fn dangling_static_ptr<M: Module + ?Sized>(
    align: Option<u64>,
    module: &mut M,
    data_description: &mut DataDescription,
    triple: &Triple,
) -> DataId {
    let ptr = pretty_unwrap(module.declare_anonymous_data(false, false));
    data_description.clear();
    let mut contents = Vec::with_capacity(ptr_ty(triple).bytes() as usize);
    int_as_target_usize(align.unwrap_or(1), &mut contents, triple);
    data_description.define(contents.into_boxed_slice());
    pretty_unwrap(module.define_data(ptr, data_description));
    ptr
}

fn ty_for(ty: &MirType, triple: &Triple) -> Type {
    if *ty == MirType::Int {
        types::I64
    } else if *ty == MirType::Float {
        types::F64
    } else if *ty == MirType::Bool {
        types::I8
    } else if *ty == MirType::String || ty.as_function().is_some() {
        fat_ptr_ty(triple)
    } else {
        ptr_ty(triple)
    }
}

fn ty_ref_size_align_ptr(ty: &MirType) -> (u64, u64, bool) {
    match ty {
        MirType::Bool => (1, 1, false),
        MirType::Int | MirType::Float => (8, 8, false),
        MirType::Array(_, _) | MirType::Tuple(_) | MirType::UserDefined(_) => (8, 8, true),
        MirType::String | MirType::Function(_) => (16, 8, true),
        MirType::Unknown => unreachable!(),
        MirType::None => (0, 1, false),
    }
}

fn signature_from_function_ty(function_ty: &FunctionTy, triple: &Triple) -> Signature {
    let mut signature = Signature::new(CallConv::Tail);
    signature.params.push(AbiParam::new(ptr_ty(triple)));
    signature.params.extend(
        function_ty
            .params
            .iter()
            .map(|param_ty| AbiParam::new(ty_for(param_ty, triple))),
    );
    signature.params.extend(
        function_ty
            .continuations
            .iter()
            .sorted_by_key(|&(&param, _)| param)
            .map(|(_, param_ty)| AbiParam::new(ty_for(param_ty, triple))),
    );
    signature.returns.push(AbiParam::new(types::I64));
    signature
}

struct Compiler<'arena, M: ?Sized> {
    program: Program,
    contexts: LinkedList<Context>,
    data_description: DataDescription,
    triple: Triple,
    runtime: Runtime,
    functions: HashMap<FuncRef, (FuncId, Signature)>,
    ty_layouts: HashMap<Rc<MirType>, (TyLayout<'arena>, DataId)>,
    builder_contexts: LinkedList<FunctionBuilderContext>,
    arena: &'arena Bump,
    module: M,
}

impl<'arena, M: Module> Compiler<'arena, M> {
    fn new(program: Program, mut module: M, arena: &'arena Bump) -> Compiler<'arena, M> {
        let triple = module.isa().triple().clone();
        let runtime = Runtime::new(&mut module);
        Compiler {
            program,
            module,
            contexts: LinkedList::new(Context::new),
            data_description: DataDescription::new(),
            triple,
            runtime,
            functions: HashMap::new(),
            ty_layouts: HashMap::new(),
            arena,
            builder_contexts: LinkedList::new(FunctionBuilderContext::new),
        }
    }
}

impl<'arena, M: Module + ?Sized> Compiler<'arena, M> {
    #[tracing::instrument(skip(self))]
    fn c_int_ty(&self) -> Type {
        Type::int(self.triple.data_model().unwrap().int_size().bits().into()).unwrap()
    }

    #[tracing::instrument(skip_all)]
    fn function(&mut self, mir_function: &MirFunction, func_ref: FuncRef) {
        let name = &mir_function.name;
        info!("compiling function '{name}'");

        let params: Vec<_> = mir_function
            .params
            .iter()
            .cloned()
            .chain(
                mir_function
                    .continuations
                    .iter()
                    .map(|(&param, param_ty)| (param, Rc::clone(param_ty)))
                    .sorted_by_key(|&(param, _)| param),
            )
            .collect();

        let (func_id, ref sig) = self.functions[&func_ref];

        let name = UserFuncName::User(UserExternalName::new(2, func_ref.into()));
        let mut function = Function::with_name_signature(name, sig.clone());
        let mut func_ctx = self.builder_contexts.get();
        let mut builder = FunctionBuilder::new(&mut function, &mut func_ctx);

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

        let function_compiler = FunctionCompilerBuilder {
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
            contexts: &self.contexts,
            builder_contexts: &self.builder_contexts,
        }
        .build();

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

        let mut context = self.contexts.get();
        context.clear();
        context.want_disasm = cfg!(debug_assertions);
        context.func = function;
        pretty_unwrap(self.module.define_function(func_id, &mut context));
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

        let layout_global = pretty_unwrap(self.module.declare_anonymous_data(false, false));
        self.data_description.clear();
        self.data_description.define(contents.into_boxed_slice());

        let gc_pointer_locations = self
            .module
            .declare_data_in_data(gc_pointer_locations, &mut self.data_description);
        self.data_description
            .write_data_addr(offset, gc_pointer_locations, 0);

        pretty_unwrap(
            self.module
                .define_data(layout_global, &self.data_description),
        );

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

                let variant_layouts =
                    pretty_unwrap(self.module.declare_anonymous_data(false, false));
                self.data_description.clear();
                self.data_description.define(contents.into_boxed_slice());
                for (offset, data_id) in relocs {
                    let data = self
                        .module
                        .declare_data_in_data(data_id, &mut self.data_description);
                    self.data_description.write_data_addr(offset, data, 0);
                }
                pretty_unwrap(
                    self.module
                        .define_data(variant_layouts, &self.data_description),
                );

                let layout = pretty_unwrap(self.module.declare_anonymous_data(false, false));
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

                pretty_unwrap(self.module.define_data(layout, &self.data_description));

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

    fn compound_ty_layout(&self, types: &[&[Rc<MirType>]]) -> SingleLayout<'arena> {
        let mut size = 0;
        let mut align = 1;
        let mut field_locations = Vec::with_capacity(types.len());
        let mut gc_pointer_locations = Vec::with_capacity(types.len());
        for ty in types.iter().copied().flatten() {
            let (field_size, field_align, ptr) = ty_ref_size_align_ptr(ty);
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
            field_locations: Slice::new(self.arena.alloc_slice_copy(&field_locations)),
            gc_pointer_locations: Slice::new(self.arena.alloc_slice_copy(&gc_pointer_locations)),
        }
    }

    fn calc_ty_layout(&mut self, ty: Rc<MirType>) {
        let layout = match *ty {
            MirType::Bool => SingleLayout::primitive(1, 1).into(),
            MirType::Int | MirType::Float | MirType::Function(_) => {
                SingleLayout::primitive(8, 8).into()
            }
            MirType::String => TyLayout::String,
            MirType::Array(ref elem_ty, len) => {
                let (elem_size, elem_align, ptr) = ty_ref_size_align_ptr(elem_ty);
                let field_locations: Vec<_> =
                    (0..elem_size * len).step_by(elem_size as usize).collect();
                let field_locations = Slice::new(self.arena.alloc_slice_copy(&field_locations));
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
            | MirType::UserDefined(UserDefinedType::Product(ref types)) => {
                self.compound_ty_layout(&[types]).into()
            }
            MirType::UserDefined(UserDefinedType::Sum(ref variants)) => {
                let layouts: Vec<_> = variants
                    .iter()
                    .map(|types| self.compound_ty_layout(&[&[Rc::new(MirType::Int)], types]))
                    .collect();
                let size = layouts.iter().fold(8, |size, layout| size.max(layout.size));
                let align = layouts
                    .iter()
                    .fold(1, |align, layout| align.max(layout.align));

                TyLayout::Sum {
                    layouts: Slice::new(self.arena.alloc_slice_copy(&layouts)),
                    size,
                    align,
                }
            }
            MirType::Unknown => unreachable!(),
            MirType::None => SingleLayout::primitive(0, 1).into(),
        };

        let global_id = self.declare_ty_layout_global(&layout);
        self.ty_layouts.insert(ty, (layout, global_id));
    }

    fn calc_ty_layouts(&mut self) {
        let types: Vec<_> = self.program.types.iter().cloned().collect();
        for ty in types {
            self.calc_ty_layout(ty);
        }
    }

    fn declare_functions(&mut self) {
        for (&func_ref, function) in &self.program.functions {
            let function_ty = self.program.signatures[&func_ref].as_function().unwrap();
            let sig = signature_from_function_ty(function_ty, &self.triple);

            let id = pretty_unwrap(self.module.declare_function(
                &function.name,
                Linkage::Local,
                &sig,
            ));
            self.functions.insert(func_ref, (id, sig));
        }
    }

    fn compile_module(&mut self) {
        self.calc_ty_layouts();

        self.declare_functions();

        let functions = mem::take(&mut self.program.functions);
        for (func_ref, function) in functions {
            self.function(&function, func_ref);
        }
    }
}

impl Compiler<'_, ObjectModule> {
    fn compile_library(mut self) -> ObjectProduct {
        self.compile_module();

        self.module.finish()
    }

    fn compile_binary(mut self) -> ObjectProduct {
        self.compile_module();

        let c_int = self.c_int_ty();

        let mut signature = self.module.make_signature();
        signature.returns.push(AbiParam::new(c_int));

        let main = pretty_unwrap(
            self.module
                .declare_function("main", Linkage::Export, &signature),
        );
        let name = UserFuncName::User(UserExternalName::new(1, 0));
        let mut function = Function::with_name_signature(name, signature);
        let mut func_ctx = self.builder_contexts.get();
        let mut builder = FunctionBuilder::new(&mut function, &mut func_ctx);

        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);

        let init = self
            .module
            .declare_func_in_func(self.runtime.init, builder.func);
        let results = builder.ins().call(init, &[]);
        debug_assert_eq!(builder.inst_results(results).len(), 0);

        let entry_point = self.functions[&FuncRef::ENTRY_POINT].0;
        let entry_point = self.module.declare_func_in_func(entry_point, builder.func);

        let termination_ref = self.program.lib_std.fn_termination;
        let termination = self.functions[&termination_ref].0;
        let termination = self.module.declare_func_in_func(termination, builder.func);
        let termination_addr = builder.ins().func_addr(ptr_ty(&self.triple), termination);
        let metadata = builder.ins().iconst(ptr_ty(&self.triple), 0);
        let termination = fat_ptr(termination_addr, metadata, &self.triple, &mut builder);
        let zero = builder.ins().iconst(ptr_ty(&self.triple), 0);

        let result = builder.ins().call(entry_point, &[zero, termination]);
        let rvals = builder.inst_results(result);
        debug_assert_eq!(rvals.len(), 1);
        let rval = rvals[0];

        let cleanup = self
            .module
            .declare_func_in_func(self.runtime.cleanup, builder.func);
        let results = builder.ins().call(cleanup, &[]);
        debug_assert_eq!(builder.inst_results(results).len(), 0);

        let rval = builder.ins().ireduce(c_int, rval);
        builder.ins().return_(&[rval]);

        builder.finalize();

        let mut context = self.contexts.get();
        context.clear();
        context.func = function;
        pretty_unwrap(self.module.define_function(main, &mut context));

        self.module.finish()
    }
}

#[allow(clippy::missing_panics_doc)]
pub fn compile(program: Program, binary: bool) -> ObjectProduct {
    let mut flags = settings::builder();
    flags.enable("preserve_frame_pointers").unwrap();
    flags.enable("is_pic").unwrap();
    flags.enable("enable_llvm_abi_extensions").unwrap();
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
    let compiler = Compiler::new(program, module, &arena);
    if binary {
        compiler.compile_binary()
    } else {
        compiler.compile_library()
    }
}
