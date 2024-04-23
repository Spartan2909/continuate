use std::collections::HashMap;
use std::mem;

use continuate_arena::Arena;

use continuate_ir::common::FuncRef;
use continuate_ir::common::Literal;
use continuate_ir::common::TypeRef;
use continuate_ir::low_level_ir::BlockId;
use continuate_ir::low_level_ir::Expr;
use continuate_ir::low_level_ir::Function as LirFunction;
use continuate_ir::low_level_ir::Program;
use continuate_ir::low_level_ir::Type as LirType;
use continuate_ir::low_level_ir::TypeConstructor;
use continuate_ir::low_level_ir::UserDefinedType;

use continuate_rt_common::SingleLayout;
use continuate_rt_common::Slice;
use continuate_rt_common::TyLayout;

use cranelift::codegen::ir::entities::Value;
use cranelift::codegen::ir::types;
use cranelift::codegen::ir::AbiParam;
use cranelift::codegen::ir::Block;
use cranelift::codegen::ir::Function;
use cranelift::codegen::ir::InstBuilder;
use cranelift::codegen::ir::Signature;
use cranelift::codegen::ir::StackSlotData;
use cranelift::codegen::ir::StackSlotKind;
use cranelift::codegen::ir::Type;
use cranelift::codegen::ir::UserFuncName;
use cranelift::codegen::isa;
use cranelift::codegen::settings;
use cranelift::codegen::settings::Flags;
use cranelift::codegen::verify_function;
use cranelift::codegen::Context;
use cranelift::frontend::FunctionBuilder;
use cranelift::frontend::FunctionBuilderContext;
use cranelift::frontend::Variable;

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

use target_lexicon::Endianness;
use target_lexicon::PointerWidth;
use target_lexicon::Triple;

struct Runtime {
    /// `fn(ty_layout: &'static TyLayout<'static>, variant: usize) -> *mut ()`
    alloc_gc: FuncId,
}

impl Runtime {
    fn new(module: &mut ObjectModule) -> Runtime {
        let ptr_ty = Type::triple_pointer_type(module.isa().triple());

        let mut alloc_gc_sig = module.make_signature();
        alloc_gc_sig
            .params
            .extend([ptr_ty, ptr_ty].into_iter().map(AbiParam::new));
        alloc_gc_sig.returns.push(AbiParam::new(ptr_ty));
        let alloc_gc = module
            .declare_function("@rt_alloc_gc", Linkage::Import, &alloc_gc_sig)
            .unwrap();

        Runtime { alloc_gc }
    }
}

const fn u64_as_endianness(value: u64, endianness: Endianness) -> [u8; 8] {
    match endianness {
        Endianness::Big => value.to_be_bytes(),
        Endianness::Little => value.to_le_bytes(),
    }
}

struct Compiler<'arena, 'a> {
    program: Program<'a>,
    module: ObjectModule,
    context: Context,
    data_description: DataDescription,
    triple: Triple,
    runtime: Runtime,
    functions: HashMap<FuncRef, (FuncId, Signature)>,
    ty_layouts: HashMap<TypeRef, (&'arena TyLayout<'arena>, DataId)>,
    arena: &'arena Arena<'arena>,
}

impl<'arena, 'a> Compiler<'arena, 'a> {
    fn new(
        program: Program<'a>,
        mut module: ObjectModule,
        arena: &'arena Arena<'arena>,
    ) -> Compiler<'arena, 'a> {
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

    fn ptr_ty(&self) -> Type {
        Type::triple_pointer_type(&self.triple)
    }

    fn fat_ptr_ty(&self) -> Type {
        Type::int(self.ptr_ty().bits() as u16).unwrap()
    }

    fn ty_for(&self, ty: TypeRef) -> Type {
        if ty == self.program.lib_std.ty_int {
            types::I64
        } else if ty == self.program.lib_std.ty_float {
            types::F64
        } else if ty == self.program.lib_std.ty_bool {
            types::I8
        } else if ty == self.program.lib_std.ty_string {
            types::I128
        } else {
            self.ptr_ty()
        }
    }

    fn fat_ptr(&self, thin_ptr: Value, size: Value, builder: &mut FunctionBuilder) -> Value {
        let fat_ptr_ty = self.fat_ptr_ty();

        let rotation_places = builder
            .ins()
            .iconst(types::I32, i64::from(self.ptr_ty().bits()));
        let fat_ptr = builder.ins().uextend(fat_ptr_ty, thin_ptr);
        let fat_ptr = builder.ins().rotl(fat_ptr, rotation_places);
        let size = builder.ins().uextend(fat_ptr_ty, size);
        builder.ins().bor(fat_ptr, size)
    }

    fn alloc_gc(
        &mut self,
        ty: TypeRef,
        variant: Option<usize>,
        builder: &mut FunctionBuilder,
    ) -> Value {
        let alloc_gc = self
            .module
            .declare_func_in_func(self.runtime.alloc_gc, builder.func);

        let ty_layout = self.ty_layouts[&ty].1;
        let ty_layout = self.module.declare_data_in_func(ty_layout, builder.func);
        let ty_layout = builder.ins().global_value(self.ptr_ty(), ty_layout);

        let variant = variant.unwrap_or(usize::MAX);
        let variant = builder.ins().iconst(self.ptr_ty(), variant as i64);

        let call_result = builder.ins().call(alloc_gc, &[ty_layout, variant]);
        let values = builder.inst_results(call_result);
        debug_assert_eq!(values.len(), 1);

        values[0]
    }

    fn expr_literal_string(&mut self, string: &str, builder: &mut FunctionBuilder) -> Value {
        let global_string_ref = self.declare_static(string.as_bytes().into(), None);

        let dest_ptr = self.alloc_gc(self.program.lib_std.ty_string, None, builder);

        let gv = self
            .module
            .declare_data_in_func(global_string_ref, builder.func);
        let src_ptr = builder.ins().global_value(self.ptr_ty(), gv);

        let size = builder.ins().iconst(self.ptr_ty(), string.len() as i64);

        builder.call_memcpy(self.module.target_config(), dest_ptr, src_ptr, size);

        self.fat_ptr(dest_ptr, size, builder)
    }

    fn expr_function(&mut self, func_ref: FuncRef, builder: &mut FunctionBuilder) -> Value {
        let func_id = self.functions[&func_ref].0;
        let func_ref = self.module.declare_func_in_func(func_id, builder.func);
        builder.ins().func_addr(self.ptr_ty(), func_ref)
    }

    fn expr_tuple(
        &mut self,
        ty: TypeRef,
        values: &[&Expr],
        builder: &mut FunctionBuilder,
        block_map: &HashMap<BlockId, Block>,
    ) -> Value {
        let layout = self.ty_layouts[&ty].0;
        let layout = layout.as_single().unwrap();
        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: layout.size.try_into().unwrap(),
        };
        let stack_slot = builder.create_sized_stack_slot(stack_slot_data);

        for (&field_location, &field) in layout.field_locations.iter().zip(values) {
            let field = self.expr(field, builder, block_map);
            builder
                .ins()
                .stack_store(field, stack_slot, i32::try_from(field_location).unwrap());
        }

        let dest_ptr = self.alloc_gc(ty, None, builder);

        let src_ptr = builder.ins().stack_addr(self.ptr_ty(), stack_slot, 0);

        let size = builder.ins().iconst(self.ptr_ty(), layout.size as i64);

        builder.call_memcpy(self.module.target_config(), dest_ptr, src_ptr, size);

        dest_ptr
    }

    fn expr(
        &mut self,
        expr: &Expr,
        builder: &mut FunctionBuilder,
        block_map: &HashMap<BlockId, Block>,
    ) -> Value {
        match *expr {
            Expr::Literal(Literal::Int(n)) => builder.ins().iconst(types::I64, n),
            Expr::Literal(Literal::Float(n)) => builder.ins().f64const(n),
            Expr::Literal(Literal::String(ref string)) => self.expr_literal_string(string, builder),
            Expr::Ident(ident) => builder.use_var(Variable::from_u32(ident.into())),
            Expr::Function(func_ref) => self.expr_function(func_ref, builder),
            Expr::Tuple { ty, ref values } => self.expr_tuple(ty, values, builder, block_map),
            _ => todo!(),
        }
    }

    fn function(
        &mut self,
        lir_function: &LirFunction,
        func_ref: FuncRef,
        func_ctx: &mut FunctionBuilderContext,
    ) {
        self.context.clear();

        let params: Vec<_> = lir_function
            .params
            .iter()
            .copied()
            .chain(
                lir_function
                    .continuations
                    .iter()
                    .map(|(&param, &param_ty)| (param, param_ty))
                    .sorted_by_key(|&(param, _)| param),
            )
            .map(|(param, param_ty)| (param, self.ty_for(param_ty)))
            .collect();

        let (func_id, ref sig) = self.functions[&func_ref];

        let mut function = Function::with_name_signature(UserFuncName::default(), sig.clone());
        let mut builder = FunctionBuilder::new(&mut function, func_ctx);

        for &(param, param_ty) in &params {
            builder.declare_var(Variable::from_u32(param.into()), param_ty);
        }

        let block_map: HashMap<_, _> = lir_function
            .blocks
            .keys()
            .map(|&id| (id, builder.create_block()))
            .collect();

        builder.append_block_params_for_function_params(block_map[&LirFunction::entry_point()]);

        for (&block_id, block) in &lir_function.blocks {
            builder.switch_to_block(block_map[&block_id]);

            for &expr in &block.exprs {
                self.expr(expr, &mut builder, &block_map);
            }
        }

        builder.seal_all_blocks();
        builder.finalize();

        let flags = Flags::new(settings::builder());
        if let Err(errors) = verify_function(&function, &flags) {
            panic!("{errors}");
        }

        self.module
            .define_function(func_id, &mut self.context)
            .unwrap();
    }

    fn compund_ty_layout(&self, types: &[TypeRef]) -> SingleLayout<'arena> {
        let mut size = 0;
        let mut align = 1;
        let mut field_locations = Vec::with_capacity(types.len());
        let mut gc_pointer_locations = Vec::with_capacity(types.len());
        for &ty in types {
            let (field_size, field_align, ptr) = self.ty_ref_size_align_ptr(ty);
            let misalignment = size % align;
            if misalignment != 0 {
                size += align - misalignment;
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

    fn ty_ref_size_align_ptr(&self, ty: TypeRef) -> (u64, u64, bool) {
        match **self.program.types.get_by_left(&ty).unwrap() {
            _ if ty == self.program.lib_std.ty_bool => (1, 1, false),
            LirType::Int | LirType::Float => (8, 8, false),
            LirType::Array(_, _)
            | LirType::Tuple(_)
            | LirType::Function(_)
            | LirType::UserDefined(_) => (8, 8, true),
            LirType::String => (16, 8, true),
            LirType::Unknown => unreachable!(),
            LirType::None => (0, 1, false),
        }
    }

    fn declare_const(&mut self, contents: Box<[u8]>, align: Option<u64>) -> Option<DataId> {
        if contents.is_empty() {
            return None;
        }

        let global = self.module.declare_anonymous_data(false, false).unwrap();
        self.data_description.clear();
        self.data_description.define(contents);
        self.data_description.align = align;
        self.module
            .define_data(global, &self.data_description)
            .unwrap();

        Some(global)
    }

    fn int_as_target_usize<T: Into<u64>>(&self, i: T, sink: &mut Vec<u8>) {
        let i: u64 = i.into();
        match (
            self.triple.endianness().unwrap(),
            self.triple.pointer_width().unwrap(),
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

    fn pointer_to_global(&mut self, data_id: DataId, align: Option<u64>) -> DataId {
        let align = align.unwrap_or(1);
        let ptr = self.module.declare_anonymous_data(false, false).unwrap();
        self.data_description.clear();
        let mut contents = Vec::with_capacity(8);
        self.int_as_target_usize(align, &mut contents);
        self.data_description.define(contents.into_boxed_slice());
        let gv = self
            .module
            .declare_data_in_data(data_id, &mut self.data_description);
        self.data_description.write_data_addr(0, gv, 0);
        self.module
            .define_data(ptr, &self.data_description)
            .unwrap();

        ptr
    }

    fn dangling_static_ptr(&mut self, align: Option<u64>) -> DataId {
        let ptr = self.module.declare_anonymous_data(false, false).unwrap();
        self.data_description.clear();
        let mut contents = Vec::with_capacity(self.ptr_ty().bytes() as usize);
        self.int_as_target_usize(align.unwrap_or(1), &mut contents);
        self.data_description.define(contents.into_boxed_slice());
        self.module
            .define_data(ptr, &self.data_description)
            .unwrap();
        ptr
    }

    fn declare_static(&mut self, contents: Box<[u8]>, align: Option<u64>) -> DataId {
        let global = self.declare_const(contents, align);
        let dangling = self.dangling_static_ptr(align);
        global.map_or(dangling, |global| self.pointer_to_global(global, align))
    }

    fn append_single_layout_global(
        &mut self,
        layout: &SingleLayout,
        contents: &mut Vec<u8>,
    ) -> (u32, DataId) {
        let gc_pointer_locations = self.declare_const(
            layout.field_locations.as_byte_slice().as_slice().into(),
            Some(8),
        );

        let endianness = self.triple.endianness().unwrap();
        let offset = contents.len();

        contents.extend(u64_as_endianness(layout.size, endianness));
        contents.extend(u64_as_endianness(layout.align, endianness));
        self.int_as_target_usize(8u64, contents); // field_locations.ptr
        self.int_as_target_usize(0u64, contents); // field_locations.len
        self.int_as_target_usize(8u64, contents); // gc_pointer_locations.ptr
        self.int_as_target_usize(layout.gc_pointer_locations.len() as u64, contents);

        (
            (mem::offset_of!(SingleLayout, gc_pointer_locations) + offset) as u32,
            gc_pointer_locations.unwrap_or_else(|| self.dangling_static_ptr(Some(8))),
        )
    }

    /// Returns the global by value.
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
                let contents = vec![0; self.ptr_ty().bytes() as usize];
                let layout = self.declare_single_layout_global(layout, contents);
                self.pointer_to_global(layout, Some(8))
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

                let ptr_size = self.ptr_ty().bytes();
                let mut contents = vec![1];
                contents.extend(vec![0; ptr_size as usize - 1]);
                self.int_as_target_usize(8u64, &mut contents); // layouts.ptr
                self.int_as_target_usize(layouts.len() as u64, &mut contents);

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

                self.pointer_to_global(layout, Some(8))
            }
        }
    }

    fn calc_ty_layout(&mut self, ty_ref: TypeRef) {
        let ty = *self.program.types.get_by_left(&ty_ref).unwrap();
        let layout: TyLayout<'arena> = match *ty {
            _ if ty_ref == self.program.lib_std.ty_bool => SingleLayout::primitive(1, 1).into(),
            LirType::Int | LirType::Float | LirType::Function(_) => {
                SingleLayout::primitive(8, 8).into()
            }
            LirType::String => SingleLayout::primitive(16, 8).into(),
            LirType::Array(elem_ty, len) => {
                let (elem_size, elem_align, ptr) = self.ty_ref_size_align_ptr(elem_ty);
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
            LirType::Tuple(ref types)
            | LirType::UserDefined(UserDefinedType {
                constructor: TypeConstructor::Product(ref types),
            }) => self.compund_ty_layout(types).into(),
            LirType::UserDefined(UserDefinedType {
                constructor: TypeConstructor::Sum(ref variants),
            }) => {
                let layouts: Vec<_> = variants
                    .iter()
                    .map(|types| self.compund_ty_layout(types))
                    .collect();
                let size = layouts.iter().fold(0, |size, layout| size.max(layout.size));
                let align = layouts
                    .iter()
                    .fold(1, |align, layout| align.max(layout.align));

                TyLayout::Sum {
                    layouts: Slice::allocate_slice(&layouts, self.arena),
                    size,
                    align,
                }
            }
            LirType::Unknown => unreachable!(),
            LirType::None => SingleLayout::primitive(0, 1).into(),
        };

        let global_id = self.declare_ty_layout_global(&layout);
        self.ty_layouts
            .insert(ty_ref, (self.arena.allocate(layout), global_id));
    }

    fn compile(mut self) -> ObjectProduct {
        let types: Vec<_> = self.program.types.left_values().copied().collect();
        for ty in types {
            self.calc_ty_layout(ty);
        }

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
                .map(|(param, param_ty)| (param, self.ty_for(param_ty)))
                .collect();

            let mut sig = self.module.make_signature();
            for &(_, param_ty) in &params {
                sig.params.push(AbiParam::new(param_ty));
            }

            let id = self
                .module
                .declare_function(&function.name, Linkage::Export, &sig)
                .unwrap();
            self.functions.insert(func_ref, (id, sig));
        }

        let functions: Vec<_> = self
            .program
            .functions
            .iter()
            .map(|(&func_ref, &func)| (func_ref, func))
            .collect();
        let mut func_ctx = FunctionBuilderContext::new();
        for (func_ref, function) in functions {
            self.function(function, func_ref, &mut func_ctx);
        }
        self.module.finish()
    }
}

#[allow(clippy::missing_panics_doc)]
pub fn compile(program: Program) -> ObjectProduct {
    let isa = isa::lookup(target_lexicon::HOST)
        .unwrap()
        .finish(Flags::new(settings::builder()))
        .unwrap();
    let module = ObjectModule::new(
        ObjectBuilder::new(isa, program.name.clone(), default_libcall_names()).unwrap(),
    );

    let arena = Arena::new();
    Compiler::new(program, module, &arena).compile()
}
