mod function;
use function::{FunctionCompilerBuilder, FunctionRuntime};

#[cfg(feature = "jit")]
pub mod jit;

#[cfg(feature = "object")]
pub mod object;

mod storage;
use storage::Storage;

use std::{collections::HashMap, mem, sync::Arc};

use bumpalo::Bump;

use continuate_ir::{
    common::FuncRef,
    mid_level_ir::{
        Function as MirFunction, FunctionTy, Program, Type as MirType, UserDefinedType,
    },
};

use continuate_rt::{
    layout::{SingleLayout, TyLayout},
    slice::Slice,
};

use cranelift::{
    codegen::{
        Context,
        binemit::CodeOffset,
        ir::{
            AbiParam, Function, InstBuilder, Signature, StackSlotData, StackSlotKind, Type,
            UserExternalName, UserFuncName, UserStackMap, entities::Value, types,
        },
        isa::CallConv,
        settings::{self, Flags, FlagsOrIsa},
        verify_function,
    },
    frontend::{FunctionBuilder, FunctionBuilderContext},
    module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError, ModuleRelocTarget},
};

use itertools::Itertools;

use tracing::{info, warn};

use target_lexicon::{Endianness, PointerWidth, Triple};

struct BoxedModuleError(Box<ModuleError>);

impl From<ModuleError> for BoxedModuleError {
    fn from(value: ModuleError) -> Self {
        BoxedModuleError(Box::new(value))
    }
}

impl From<BoxedModuleError> for ModuleError {
    #[inline]
    fn from(value: BoxedModuleError) -> Self {
        *value.0
    }
}

type ModuleResult<T, E = BoxedModuleError> = Result<T, E>;

fn gc_wrapper<M: Module + ?Sized>(
    inner: FuncId,
    name: &str,
    sig: Signature,
    module: &mut M,
) -> ModuleResult<FuncId> {
    let ptr_ty = Type::triple_pointer_type(module.isa().triple());

    // sig.params.push(AbiParam::new(ptr_ty));
    let wrapper = module.declare_function(name, Linkage::Local, &sig)?;

    let mut func = Function::new();
    func.signature = sig;
    let inner = module.declare_func_in_func(inner, &mut func);
    let mut func_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut func, &mut func_ctx);

    let block = builder.create_block();
    builder.switch_to_block(block);
    builder.seal_block(block);
    builder.append_block_params_for_function_params(block);
    let mut block_params = builder.block_params(block).to_vec();
    let stack_ptr = block_params.pop().unwrap();

    let data = StackSlotData {
        kind: StackSlotKind::ExplicitSlot,
        size: ptr_ty.bytes() * 2,
        align_shift: ptr_ty.bytes() as u8,
        key: None,
    };
    let ss = builder.create_sized_stack_slot(data);
    let ret_addr = builder.ins().get_return_address(ptr_ty);
    builder.ins().stack_store(ret_addr, ss, 0);
    builder
        .ins()
        .stack_store(stack_ptr, ss, ptr_ty.bytes().cast_signed());
    let ss_addr = builder.ins().stack_addr(ptr_ty, ss, 0);
    block_params.push(ss_addr);
    let ret = builder.ins().call(inner, &block_params);
    let ret_values = builder.inst_results(ret).to_vec();
    builder.ins().return_(&ret_values);

    builder.finalize();

    let mut ctx = Context::new();
    ctx.func = func;
    module.define_function(wrapper, &mut ctx)?;
    Ok(wrapper)
}

struct Runtime {
    /// `fn(ty_layout: &TyLayout, *const stack) -> *mut ()`
    alloc_gc: FuncId,

    /// `fn(len: usize, *const stack) -> *mut ()`
    alloc_string: FuncId,
}

impl Runtime {
    fn new<M: Module + ?Sized>(module: &mut M) -> ModuleResult<Runtime> {
        let ptr_ty = Type::triple_pointer_type(module.isa().triple());

        let mut alloc_gc_sig = module.make_signature();
        alloc_gc_sig.params.push(AbiParam::new(ptr_ty));
        alloc_gc_sig.params.push(AbiParam::new(ptr_ty));
        alloc_gc_sig.returns.push(AbiParam::new(ptr_ty));
        let alloc_gc_inner =
            module.declare_function("cont_rt_alloc_gc", Linkage::Import, &alloc_gc_sig)?;
        let alloc_gc = gc_wrapper(alloc_gc_inner, "alloc_gc", alloc_gc_sig.clone(), module)?;

        let alloc_string_inner =
            module.declare_function("cont_rt_alloc_string", Linkage::Import, &alloc_gc_sig)?;
        let alloc_string = gc_wrapper(alloc_string_inner, "alloc_string", alloc_gc_sig, module)?;

        Ok(Runtime {
            alloc_gc,
            alloc_string,
        })
    }
}

const fn u64_as_endianness(value: u64, endianness: Endianness) -> [u8; 8] {
    match endianness {
        Endianness::Big => value.to_be_bytes(),
        Endianness::Little => value.to_le_bytes(),
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
) -> ModuleResult<Option<DataId>> {
    if contents.is_empty() {
        return Ok(None);
    }

    let global = module.declare_anonymous_data(false, false)?;
    data_description.clear();
    data_description.define(contents);
    data_description.align = align;
    module.define_data(global, data_description)?;

    Ok(Some(global))
}

fn dangling_static_ptr<M: Module + ?Sized>(
    align: Option<u64>,
    module: &mut M,
    data_description: &mut DataDescription,
    triple: &Triple,
) -> ModuleResult<DataId> {
    let ptr = module.declare_anonymous_data(false, false)?;
    data_description.clear();
    let mut contents = Vec::with_capacity(ptr_ty(triple).bytes() as usize);
    int_as_target_usize(align.unwrap_or(1), &mut contents, triple);
    data_description.define(contents.into_boxed_slice());
    module.define_data(ptr, data_description)?;
    Ok(ptr)
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

fn ty_ref_size_align_ptr(ty: &MirType, triple: &Triple) -> (u64, u64, bool) {
    let ptr_size = triple.pointer_width().unwrap().bytes();
    match ty {
        MirType::Bool => (1, 1, false),
        MirType::Int | MirType::Float => (8, 8, false),
        MirType::Array(_, _) | MirType::Tuple(_) | MirType::UserDefined(_) => {
            (ptr_size.into(), ptr_size.into(), true)
        }
        MirType::String | MirType::Function(_) => ((ptr_size * 2).into(), ptr_size.into(), true),
        MirType::Unknown => unreachable!(),
        MirType::None => (0, 1, false),
    }
}

fn signature_from_function_ty(function_ty: &FunctionTy, triple: &Triple) -> Signature {
    let mut signature = Signature::new(CallConv::Tail);
    signature.params.push(AbiParam::new(ptr_ty(triple)));
    signature.params.extend(
        function_ty
            .positional_params
            .iter()
            .map(|param_ty| AbiParam::new(ty_for(param_ty, triple))),
    );
    signature.params.extend(
        function_ty
            .named_params
            .iter()
            .sorted_by_key(|&(&param, _)| param)
            .map(|(_, param_ty)| AbiParam::new(ty_for(param_ty, triple))),
    );
    signature.returns.push(AbiParam::new(types::I64));
    signature
}

struct Compiler<'arena, M: ?Sized> {
    program: Program,
    contexts: Storage<Context>,
    data_description: DataDescription,
    triple: Triple,
    runtime: Runtime,
    functions: HashMap<FuncRef, (FuncId, Signature)>,
    ty_layouts: HashMap<Arc<MirType>, (TyLayout<'arena>, DataId)>,
    builder_contexts: Storage<FunctionBuilderContext>,
    arena: &'arena Bump,
    stack_maps: HashMap<FuncId, Vec<(CodeOffset, UserStackMap)>>,
    module: M,
}

impl<'arena, M: Module> Compiler<'arena, M> {
    fn new(
        program: Program,
        mut module: M,
        arena: &'arena Bump,
    ) -> ModuleResult<Compiler<'arena, M>> {
        let triple = module.isa().triple().clone();
        let runtime = Runtime::new(&mut module)?;
        Ok(Compiler {
            program,
            module,
            contexts: Storage::new(Context::new),
            data_description: DataDescription::new(),
            triple,
            runtime,
            functions: HashMap::new(),
            ty_layouts: HashMap::new(),
            arena,
            stack_maps: HashMap::new(),
            builder_contexts: Storage::new(FunctionBuilderContext::new),
        })
    }
}

impl<'arena, M: Module + ?Sized> Compiler<'arena, M> {
    #[tracing::instrument(skip_all)]
    fn function(&mut self, mir_function: &MirFunction, func_ref: FuncRef) -> ModuleResult<()> {
        let name = &mir_function.name;
        info!("compiling function '{name}'");

        let params: Vec<_> = mir_function
            .positional_params
            .iter()
            .cloned()
            .chain(
                mir_function
                    .named_params
                    .iter()
                    .map(|(&param, param_ty)| (param, Arc::clone(param_ty)))
                    .sorted_by_key(|&(param, _)| param),
            )
            .collect();

        let (func_id, ref sig) = self.functions[&func_ref];

        let name = UserFuncName::User(UserExternalName::new(2, func_ref.to_u32()));
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

        function_compiler.compile()?;

        builder.seal_all_blocks();
        builder.finalize();
        drop(func_ctx);

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
        self.module.define_function(func_id, &mut context)?;
        let mut cc = context.take_compiled_code().unwrap();
        drop(context);
        self.stack_maps.insert(
            func_id,
            cc.buffer
                .take_user_stack_maps()
                .into_iter()
                .map(|(o, _, m)| (o, m))
                .collect(),
        );

        Ok(())
    }

    fn append_single_layout_global(
        &mut self,
        layout: &SingleLayout,
        contents: &mut Vec<u8>,
    ) -> ModuleResult<(u32, DataId)> {
        let gc_pointer_locations = declare_static(
            layout.field_locations.as_byte_slice().as_slice().into(),
            Some(8),
            &mut self.module,
            &mut self.data_description,
        )?;

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

        Ok((
            (mem::offset_of!(SingleLayout, gc_pointer_locations) + offset) as u32,
            gc_pointer_locations.map_or_else(
                || {
                    dangling_static_ptr(
                        Some(8),
                        &mut self.module,
                        &mut self.data_description,
                        &self.triple,
                    )
                },
                Ok,
            )?,
        ))
    }

    fn declare_single_layout_global(
        &mut self,
        layout: &SingleLayout,
        mut contents: Vec<u8>,
    ) -> ModuleResult<DataId> {
        let (offset, gc_pointer_locations) =
            self.append_single_layout_global(layout, &mut contents)?;

        let layout_global = self.module.declare_anonymous_data(false, false)?;
        self.data_description.clear();
        self.data_description.define(contents.into_boxed_slice());

        let gc_pointer_locations = self
            .module
            .declare_data_in_data(gc_pointer_locations, &mut self.data_description);
        self.data_description
            .write_data_addr(offset, gc_pointer_locations, 0);

        self.module
            .define_data(layout_global, &self.data_description)?;

        Ok(layout_global)
    }

    fn declare_ty_layout_global(&mut self, layout: &TyLayout) -> ModuleResult<DataId> {
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
                    relocs.push(self.append_single_layout_global(layout, &mut contents)?);
                }

                let variant_layouts = self.module.declare_anonymous_data(false, false)?;
                self.data_description.clear();
                self.data_description.define(contents.into_boxed_slice());
                for (offset, data_id) in relocs {
                    let data = self
                        .module
                        .declare_data_in_data(data_id, &mut self.data_description);
                    self.data_description.write_data_addr(offset, data, 0);
                }

                self.module
                    .define_data(variant_layouts, &self.data_description)?;

                let layout = self.module.declare_anonymous_data(false, false)?;
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

                self.module.define_data(layout, &self.data_description)?;

                Ok(layout)
            }
            TyLayout::String => Ok(declare_static(
                [2].into(),
                None,
                &mut self.module,
                &mut self.data_description,
            )?
            .unwrap()),
        }
    }

    fn compound_ty_layout(&self, types: &[&[Arc<MirType>]]) -> SingleLayout<'arena> {
        let mut size = 0;
        let mut align = 1;
        let mut field_locations = Vec::with_capacity(types.len());
        let mut gc_pointer_locations = Vec::with_capacity(types.len());
        for ty in types.iter().copied().flatten() {
            let (field_size, field_align, ptr) = ty_ref_size_align_ptr(ty, &self.triple);
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

    fn calc_ty_layout(&mut self, ty: Arc<MirType>) -> ModuleResult<()> {
        let layout = match *ty {
            MirType::Bool => SingleLayout::primitive(1, 1).into(),
            MirType::Int | MirType::Float | MirType::Function(_) => {
                SingleLayout::primitive(8, 8).into()
            }
            MirType::String => TyLayout::String,
            MirType::Array(ref elem_ty, len) => {
                let (elem_size, elem_align, ptr) = ty_ref_size_align_ptr(elem_ty, &self.triple);
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
                    .map(|types| self.compound_ty_layout(&[&[Arc::new(MirType::Int)], types]))
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

        let global_id = self.declare_ty_layout_global(&layout)?;
        self.ty_layouts.insert(ty, (layout, global_id));
        Ok(())
    }

    fn calc_ty_layouts(&mut self) -> ModuleResult<()> {
        let types: Vec<_> = self.program.types.iter().cloned().collect();
        for ty in types {
            self.calc_ty_layout(ty)?;
        }
        Ok(())
    }

    fn declare_functions(&mut self) -> ModuleResult<()> {
        for (&func_ref, function) in &self.program.functions {
            let function_ty = self.program.signatures[&func_ref].as_function().unwrap();
            let sig = signature_from_function_ty(function_ty, &self.triple);

            let id = self
                .module
                .declare_function(&function.name, Linkage::Local, &sig)?;
            self.functions.insert(func_ref, (id, sig));
        }
        Ok(())
    }

    fn create_stack_maps(&mut self) -> ModuleResult<DataId> {
        let mut relocs = Vec::with_capacity(self.stack_maps.len());
        let mut data = Vec::new();
        self.data_description.clear();
        for (fun, stack_maps) in &self.stack_maps {
            if stack_maps.is_empty() {
                continue;
            }

            for (offset, map) in stack_maps {
                relocs.push((*fun, *offset, data.len()));
                let entries = map.entries().collect_vec();
                data.extend_from_slice(&(entries.len() as u64).to_le_bytes());
                for (ty, offset) in entries {
                    data.extend_from_slice(&offset.to_le_bytes());
                    data.extend_from_slice(&ty.bytes().to_le_bytes());
                }
            }
        }
        self.data_description.define(data.into_boxed_slice());
        self.data_description.set_used(true);
        self.data_description.set_align(64);

        let stack_maps = self.module.declare_anonymous_data(false, false)?;
        self.module
            .define_data(stack_maps, &self.data_description)?;

        self.data_description.clear();

        let ptr_ty = ptr_ty(&self.triple);
        self.data_description
            .define_zeroinit(relocs.len() * ptr_ty.bytes() as usize * 2);
        let table = self
            .module
            .declare_data_in_data(stack_maps, &mut self.data_description);
        for (i, (fun, code_offset, table_offset)) in relocs.iter().enumerate() {
            let i = i as u32 * ptr_ty.bytes() * 2;
            let fun = self
                .data_description
                .import_function(ModuleRelocTarget::FunctionOffset(*fun, *code_offset));
            self.data_description.write_function_addr(i, fun);
            self.data_description
                .write_data_addr(i + ptr_ty.bytes(), table, *table_offset as i64);
        }
        self.data_description.set_align(64);

        let stack_map_map =
            self.module
                .declare_data("cont_stack_maps", Linkage::Export, false, false)?;
        self.module
            .define_data(stack_map_map, &self.data_description)?;

        Ok(stack_map_map)
    }

    fn compile_module(&mut self) -> ModuleResult<DataId> {
        self.calc_ty_layouts()?;

        self.declare_functions()?;

        let functions = mem::take(&mut self.program.functions);
        for (func_ref, function) in functions {
            self.function(&function, func_ref)?;
        }

        self.create_stack_maps()
    }
}

fn call_entry_point<M: Module + ?Sized>(
    entry_point: FuncId,
    termination: FuncId,
    triple: &Triple,
    builder: &mut FunctionBuilder,
    module: &mut M,
) -> Value {
    let entry_point = module.declare_func_in_func(entry_point, builder.func);

    let termination = module.declare_func_in_func(termination, builder.func);
    let termination_addr = builder.ins().func_addr(ptr_ty(triple), termination);
    let metadata = builder.ins().iconst(ptr_ty(triple), 0);
    let termination = fat_ptr(metadata, termination_addr, triple, builder);
    let zero = builder.ins().iconst(ptr_ty(triple), 0);

    let result = builder.ins().call(entry_point, &[zero, termination]);
    let rvals = builder.inst_results(result);
    rvals[0]
}

const fn flags() -> &'static [(&'static str, &'static str)] {
    &[
        ("preserve_frame_pointers", "true"),
        ("is_pic", "true"),
        ("enable_llvm_abi_extensions", "true"),
    ]
}
