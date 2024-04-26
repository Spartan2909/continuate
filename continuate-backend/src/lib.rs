use std::collections::HashMap;
use std::mem;

use continuate_arena::Arena;

use continuate_ir::common::BinaryOp;
use continuate_ir::common::FuncRef;
use continuate_ir::common::Ident;
use continuate_ir::common::Intrinsic;
use continuate_ir::common::Literal;
use continuate_ir::common::TypeRef;
use continuate_ir::common::UnaryOp;
use continuate_ir::lib_std::StdLib;
use continuate_ir::mid_level_ir::BlockId;
use continuate_ir::mid_level_ir::Expr;
use continuate_ir::mid_level_ir::Function as MirFunction;
use continuate_ir::mid_level_ir::FunctionTy;
use continuate_ir::mid_level_ir::Program;
use continuate_ir::mid_level_ir::Type as MirType;
use continuate_ir::mid_level_ir::TypeConstructor;
use continuate_ir::mid_level_ir::UserDefinedType;

use continuate_rt_common::SingleLayout;
use continuate_rt_common::Slice;
use continuate_rt_common::TyLayout;

use cranelift::codegen::ir;
use cranelift::codegen::ir::condcodes::FloatCC;
use cranelift::codegen::ir::condcodes::IntCC;
use cranelift::codegen::ir::entities::Value;
use cranelift::codegen::ir::types;
use cranelift::codegen::ir::AbiParam;
use cranelift::codegen::ir::Block;
use cranelift::codegen::ir::Function;
use cranelift::codegen::ir::InstBuilder;
use cranelift::codegen::ir::MemFlags;
use cranelift::codegen::ir::Signature;
use cranelift::codegen::ir::StackSlotData;
use cranelift::codegen::ir::StackSlotKind;
use cranelift::codegen::ir::TrapCode;
use cranelift::codegen::ir::Type;
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
use cranelift::frontend::Switch;
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

use log::warn;

use target_lexicon::CallingConvention;
use target_lexicon::Endianness;
use target_lexicon::PointerWidth;
use target_lexicon::Triple;

struct Runtime {
    /// `fn(ty_layout: &'static TyLayout<'static>, variant: usize) -> *mut ()`
    alloc_gc: FuncId,

    /// `fn(i64)`
    exit: FuncId,
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
            .declare_function("cont_rt_alloc_gc", Linkage::Import, &alloc_gc_sig)
            .unwrap();

        let mut exit_sig = module.make_signature();
        exit_sig.params.push(AbiParam::new(types::I64));
        let exit = module
            .declare_function("cont_rt_exit", Linkage::Import, &exit_sig)
            .unwrap();

        Runtime { alloc_gc, exit }
    }
}

const fn u64_as_endianness(value: u64, endianness: Endianness) -> [u8; 8] {
    match endianness {
        Endianness::Big => value.to_be_bytes(),
        Endianness::Little => value.to_le_bytes(),
    }
}

macro_rules! match_ty {
    { ($scrutinee:expr)
        $( $ty:expr $( , $alternative:expr )* => $expr:expr ),* $(,)?
    } => {
        match $scrutinee {
            $( _scrutinee if _scrutinee == $ty $( || _scrutinee == $alternative )* => $expr, )*
            _ => unreachable!(),
        }
    };
}

enum Callable {
    FuncRef(FuncRef),
    Variable(Ident),
}

fn ptr_ty(triple: &Triple) -> Type {
    Type::triple_pointer_type(triple)
}

fn fat_ptr_ty(triple: &Triple) -> Type {
    Type::int(ptr_ty(triple).bits() as u16).unwrap()
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

fn declare_const(
    contents: Box<[u8]>,
    align: Option<u64>,
    module: &mut ObjectModule,
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

fn dangling_static_ptr(
    align: Option<u64>,
    module: &mut ObjectModule,
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

fn pointer_to_global(
    data_id: DataId,
    align: Option<u64>,
    module: &mut ObjectModule,
    data_description: &mut DataDescription,
    triple: &Triple,
) -> DataId {
    let align = align.unwrap_or(1);
    let ptr = module.declare_anonymous_data(false, false).unwrap();
    data_description.clear();
    let mut contents = Vec::with_capacity(8);
    int_as_target_usize(align, &mut contents, triple);
    data_description.define(contents.into_boxed_slice());
    let gv = module.declare_data_in_data(data_id, data_description);
    data_description.write_data_addr(0, gv, 0);
    module.define_data(ptr, data_description).unwrap();

    ptr
}

fn declare_static(
    contents: Box<[u8]>,
    align: Option<u64>,
    module: &mut ObjectModule,
    data_description: &mut DataDescription,
    triple: &Triple,
) -> DataId {
    let global = declare_const(contents, align, module, data_description);
    let dangling = dangling_static_ptr(align, module, data_description, triple);
    global.map_or(dangling, |global| {
        pointer_to_global(global, align, module, data_description, triple)
    })
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
    signature
}

struct FunctionCompiler<'arena, 'function, 'builder> {
    program: &'function Program<'function>,
    module: &'function mut ObjectModule,
    data_description: &'function mut DataDescription,
    triple: &'function Triple,
    runtime: &'function Runtime,
    functions: &'function HashMap<FuncRef, (FuncId, Signature)>,
    ty_layouts: &'function HashMap<TypeRef, (&'arena TyLayout<'arena>, DataId)>,
    builder: &'function mut FunctionBuilder<'builder>,
    block_map: &'function HashMap<BlockId, Block>,
    mir_function: &'function MirFunction<'function>,
    params: &'function [(Ident, Type)],
}

impl<'arena, 'function, 'builder> FunctionCompiler<'arena, 'function, 'builder> {
    fn cranelift_endianness(&self) -> ir::Endianness {
        use ir::Endianness as E;
        match self.triple.endianness().unwrap() {
            Endianness::Big => E::Big,
            Endianness::Little => E::Little,
        }
    }

    fn fat_ptr(&mut self, thin_ptr: Value, size: Value) -> Value {
        let fat_ptr_ty = fat_ptr_ty(self.triple);

        let rotation_places = self
            .builder
            .ins()
            .iconst(types::I32, i64::from(ptr_ty(self.triple).bits()));
        let fat_ptr = self.builder.ins().uextend(fat_ptr_ty, thin_ptr);
        let fat_ptr = self.builder.ins().rotl(fat_ptr, rotation_places);
        let size = self.builder.ins().uextend(fat_ptr_ty, size);
        self.builder.ins().bor(fat_ptr, size)
    }

    fn alloc_gc(&mut self, ty: TypeRef, variant: Option<usize>) -> Value {
        let alloc_gc = self
            .module
            .declare_func_in_func(self.runtime.alloc_gc, self.builder.func);

        let ty_layout = self.ty_layouts[&ty].1;
        let ty_layout = self
            .module
            .declare_data_in_func(ty_layout, self.builder.func);
        let ty_layout = self
            .builder
            .ins()
            .global_value(ptr_ty(self.triple), ty_layout);

        let variant = variant.unwrap_or(usize::MAX);
        let variant = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), variant as i64);

        let call_result = self.builder.ins().call(alloc_gc, &[ty_layout, variant]);
        let values = self.builder.inst_results(call_result);
        debug_assert_eq!(values.len(), 1);

        values[0]
    }

    fn expr_literal(&mut self, literal: &Literal) -> Value {
        match *literal {
            Literal::Int(n) => self.builder.ins().iconst(types::I64, n),
            Literal::Float(n) => self.builder.ins().f64const(n),
            Literal::String(ref string) => self.expr_literal_string(string),
        }
    }

    fn expr_literal_string(&mut self, string: &str) -> Value {
        let global_string_ref = declare_static(
            string.as_bytes().into(),
            None,
            self.module,
            self.data_description,
            self.triple,
        );

        let dest_ptr = self.alloc_gc(self.program.lib_std.ty_string, None);

        let gv = self
            .module
            .declare_data_in_func(global_string_ref, self.builder.func);
        let src_ptr = self.builder.ins().global_value(ptr_ty(self.triple), gv);

        let size = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), string.len() as i64);

        self.builder
            .call_memcpy(self.module.target_config(), dest_ptr, src_ptr, size);

        self.fat_ptr(dest_ptr, size)
    }

    fn expr_function(&mut self, func_ref: FuncRef) -> Value {
        let func_id = self.functions[&func_ref].0;
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        self.builder.ins().func_addr(ptr_ty(self.triple), func_ref)
    }

    fn compound_ty(
        &mut self,
        ty: TypeRef,
        layout: &SingleLayout,
        values: &[&Expr],
    ) -> Option<Value> {
        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: layout.size.try_into().unwrap(),
        };
        let stack_slot = self.builder.create_sized_stack_slot(stack_slot_data);

        for (&field_location, &field) in layout.field_locations.iter().zip(values) {
            let field = self.expr(field)?;
            self.builder.ins().stack_store(
                field,
                stack_slot,
                i32::try_from(field_location).unwrap(),
            );
        }

        let dest_ptr = self.alloc_gc(ty, None);

        let src_ptr = self
            .builder
            .ins()
            .stack_addr(ptr_ty(self.triple), stack_slot, 0);

        let size = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), layout.size as i64);

        self.builder
            .call_memcpy(self.module.target_config(), dest_ptr, src_ptr, size);

        Some(dest_ptr)
    }

    fn expr_tuple(&mut self, ty: TypeRef, values: &[&Expr]) -> Option<Value> {
        let layout = self.ty_layouts[&ty].0.as_single().unwrap();
        self.compound_ty(ty, layout, values)
    }

    fn expr_constructor(
        &mut self,
        ty: TypeRef,
        index: Option<usize>,
        fields: &[&Expr],
    ) -> Option<Value> {
        let layout = self.ty_layouts[&ty].0;
        let layout = if let Some(index) = index {
            &layout.as_sum().unwrap()[index]
        } else {
            layout.as_single().unwrap()
        };
        self.compound_ty(ty, layout, fields)
    }

    fn expr_array(&mut self, ty: TypeRef, values: &[&Expr], value_ty: TypeRef) -> Option<Value> {
        let (value_size, _, _) = ty_ref_size_align_ptr(value_ty, self.program);
        let size = value_size * values.len() as u64;

        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: size.try_into().unwrap(),
        };
        let stack_slot = self.builder.create_sized_stack_slot(stack_slot_data);

        let mut offset = 0;
        let value_size = i32::try_from(value_size).unwrap();
        for &value in values {
            let value = self.expr(value)?;
            self.builder.ins().stack_store(value, stack_slot, offset);
            offset += value_size;
        }

        let dest_ptr = self.alloc_gc(ty, None);

        let src_ptr = self
            .builder
            .ins()
            .stack_addr(ptr_ty(self.triple), stack_slot, 0);

        let size = self.builder.ins().iconst(ptr_ty(self.triple), size as i64);

        self.builder
            .call_memcpy(self.module.target_config(), dest_ptr, src_ptr, size);

        Some(dest_ptr)
    }

    fn field_information(
        &self,
        object_ty: TypeRef,
        object_variant: Option<usize>,
        field: usize,
    ) -> (&'arena SingleLayout<'arena>, TypeRef) {
        let constructor = &self
            .program
            .types
            .get_by_left(&object_ty)
            .unwrap()
            .as_user_defined()
            .unwrap()
            .constructor;
        match (self.ty_layouts[&object_ty].0, object_variant, constructor) {
            (TyLayout::Single(layout), None, TypeConstructor::Product(fields)) => {
                (layout, fields[field])
            }
            (TyLayout::Sum { layouts, .. }, Some(variant), TypeConstructor::Sum(variants)) => {
                (&layouts[variant], variants[variant][field])
            }
            _ => unreachable!(),
        }
    }

    fn expr_get(
        &mut self,
        object: &Expr,
        object_ty: TypeRef,
        object_variant: Option<usize>,
        field: usize,
    ) -> Option<Value> {
        let object = self.expr(object)?;
        let (layout, field_ty) = self.field_information(object_ty, object_variant, field);
        let field_ty = ty_for(field_ty, self.triple, &self.program.lib_std);
        let endianness = self.cranelift_endianness();
        Some(
            self.builder.ins().load(
                field_ty,
                MemFlags::new()
                    .with_endianness(endianness)
                    .with_aligned()
                    .with_heap()
                    .with_notrap(),
                object,
                layout.field_locations[field] as i32,
            ),
        )
    }

    fn expr_set(
        &mut self,
        object: &Expr,
        object_ty: TypeRef,
        object_variant: Option<usize>,
        field: usize,
        value: &Expr,
    ) -> Option<Value> {
        let object = self.expr(object)?;
        let layout = self.field_information(object_ty, object_variant, field).0;
        let value = self.expr(value)?;
        let endianness = self.cranelift_endianness();
        self.builder.ins().store(
            MemFlags::new()
                .with_endianness(endianness)
                .with_aligned()
                .with_heap()
                .with_notrap(),
            value,
            object,
            layout.field_locations[field] as i32,
        );
        Some(value)
    }

    fn simple_callee<'a, 'b>(
        callee: &'b Expr<'a>,
    ) -> Result<(Callable, HashMap<Ident, &'a Expr<'a>>), &'b Expr<'a>> {
        match *callee {
            Expr::Ident(ident) => Ok((Callable::Variable(ident), HashMap::new())),
            Expr::Function(func_ref) => Ok((Callable::FuncRef(func_ref), HashMap::new())),
            Expr::ContApplication(callee, ref continuations) => {
                let (callable, mut new_continuations) = Self::simple_callee(callee)?;
                new_continuations.extend(continuations);
                Ok((callable, new_continuations))
            }
            _ => Err(callee),
        }
    }

    fn expr_call(&mut self, callee: &Expr, params: &[&Expr]) -> Option<Value> {
        let (callable, continuations) = match Self::simple_callee(callee) {
            Ok(callee) => callee,
            Err(expr) => todo!("{expr:?} is not a supported callee"),
        };

        let params: Option<Vec<_>> = params.iter().map(|&expr| self.expr(expr)).collect();
        let mut params = params?;

        let continuations: Option<Vec<_>> = continuations
            .into_iter()
            .sorted_unstable_by_key(|&(ident, _)| ident)
            .map(|(_, expr)| self.expr(expr))
            .collect();
        params.append(&mut continuations?);

        match callable {
            Callable::FuncRef(func_ref) => {
                let func_id = self.functions[&func_ref].0;
                let func = self.module.declare_func_in_func(func_id, self.builder.func);

                self.builder.ins().return_call(func, &params);
            }
            Callable::Variable(ident) => {
                let ident_ty = self.mir_function.type_of_var(ident).unwrap();
                let ident_ty = self
                    .program
                    .types
                    .get_by_left(&ident_ty)
                    .unwrap()
                    .as_function()
                    .unwrap();
                let signature =
                    signature_from_function_ty(ident_ty, CallConv::Tail, self.triple, self.program);
                let sig_ref = self.builder.import_signature(signature);

                let callee = self.builder.use_var(Variable::from_u32(ident.into()));
                self.builder
                    .ins()
                    .return_call_indirect(sig_ref, callee, &params);
            }
        }

        None
    }

    fn expr_unary(
        &mut self,
        operator: UnaryOp,
        operand: &Expr,
        operand_ty: TypeRef,
    ) -> Option<Value> {
        let operand = self.expr(operand)?;
        let operand_ty = ty_for(operand_ty, self.triple, &self.program.lib_std);
        match operator {
            UnaryOp::Neg if operand_ty == types::F64 => Some(self.builder.ins().ineg(operand)),
            UnaryOp::Neg if operand_ty == types::I64 => Some(self.builder.ins().fneg(operand)),
            UnaryOp::Neg => unreachable!(),
        }
    }

    #[allow(clippy::cognitive_complexity)]
    #[allow(clippy::too_many_arguments)]
    fn expr_binary(
        &mut self,
        left: &Expr,
        left_ty: TypeRef,
        operator: BinaryOp,
        right: &Expr,
        right_ty: TypeRef,
    ) -> Option<Value> {
        debug_assert_eq!(left_ty, right_ty);
        let left = self.expr(left)?;
        let left_ty = ty_for(left_ty, self.triple, &self.program.lib_std);
        let right = self.expr(right)?;
        let value = match operator {
            BinaryOp::Add => match_ty! { (left_ty)
                types::I64 => self.builder.ins().iadd(left, right),
                types::F64 => self.builder.ins().fadd(left, right),
            },
            BinaryOp::Sub => match_ty! { (left_ty)
                types::I64 => self.builder.ins().isub(left, right),
                types::F64 => self.builder.ins().isub(left, right),
            },
            BinaryOp::Mul => match_ty! { (left_ty)
                types::I64 => self.builder.ins().imul(left, right),
                types::F64 => self.builder.ins().fmul(left, right),
            },
            BinaryOp::Div => match_ty! { (left_ty)
                types::I64 => self.builder.ins().sdiv(left, right),
                types::F64 => self.builder.ins().fdiv(left, right),
            },
            BinaryOp::Rem => match_ty! { (left_ty)
                types::I64 => self.builder.ins().srem(left, right),
                types::F64 => self.builder.ins().srem(left, right),
            },
            BinaryOp::Eq => match_ty! { (left_ty)
                types::I64, fat_ptr_ty(self.triple) => self.builder.ins().icmp(IntCC::Equal, left, right),
                types::F64 => self.builder.ins().fcmp(FloatCC::Equal, left, right),
            },
            BinaryOp::Ne => match_ty! { (left_ty)
                types::I64, fat_ptr_ty(self.triple) => self.builder.ins().icmp(IntCC::NotEqual, left, right),
                types::F64 => self.builder.ins().fcmp(FloatCC::NotEqual, left, right),
            },
            BinaryOp::Lt => match_ty! { (left_ty)
                types::I64, fat_ptr_ty(self.triple) => self.builder.ins().icmp(IntCC::SignedLessThan, left, right),
                types::F64 => self.builder.ins().fcmp(FloatCC::LessThan, left, right),
            },
            BinaryOp::Le => match_ty! { (left_ty)
                types::I64, fat_ptr_ty(self.triple) => self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, left, right),
                types::F64 => self.builder.ins().fcmp(FloatCC::LessThanOrEqual, left, right),
            },
            BinaryOp::Gt => match_ty! { (left_ty)
                types::I64, fat_ptr_ty(self.triple) => self.builder.ins().icmp(IntCC::SignedGreaterThan, left, right),
                types::F64 => self.builder.ins().fcmp(FloatCC::GreaterThan, left, right),
            },
            BinaryOp::Ge => match_ty! { (left_ty)
                types::I64, fat_ptr_ty(self.triple) => self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left, right),
                types::F64 => self.builder.ins().fcmp(FloatCC::GreaterThanOrEqual, left, right),
            },
        };
        Some(value)
    }

    fn expr_assign(&mut self, ident: Ident, expr: &Expr) -> Option<Value> {
        let value = self.expr(expr)?;
        self.builder
            .def_var(Variable::from_u32(ident.into()), value);
        Some(value)
    }

    fn expr_switch(
        &mut self,
        scrutinee: &Expr,
        arms: &HashMap<i64, BlockId>,
        otherwise: BlockId,
    ) -> Option<Value> {
        let scrutinee = self.expr(scrutinee)?;
        let mut switch = Switch::new();
        for (&val, &block_id) in arms {
            switch.set_entry(val as u128, self.block_map[&block_id]);
        }
        switch.emit(self.builder, scrutinee, self.block_map[&otherwise]);
        None
    }

    fn expr_goto(&mut self, block_id: BlockId) -> Option<Value> {
        self.builder.switch_to_block(self.block_map[&block_id]);
        None
    }

    fn expr_intrinsic(
        &mut self,
        intrinsic: Intrinsic,
        value: &Expr,
        value_ty: TypeRef,
    ) -> Option<Value> {
        let value = self.expr(value)?;
        match intrinsic {
            Intrinsic::Discriminant => {
                if value_ty == self.program.lib_std.ty_bool {
                    Some(self.builder.ins().sextend(types::I64, value))
                } else if matches!(
                    self.program.types.get_by_left(&value_ty).unwrap(),
                    MirType::UserDefined(UserDefinedType {
                        constructor: TypeConstructor::Sum(_)
                    })
                ) {
                    let endianness = self.cranelift_endianness();
                    Some(
                        self.builder.ins().load(
                            ptr_ty(self.triple),
                            MemFlags::new()
                                .with_endianness(endianness)
                                .with_aligned()
                                .with_heap()
                                .with_notrap(),
                            value,
                            -(ptr_ty(self.triple).bytes() as i32),
                        ),
                    )
                } else {
                    Some(self.builder.ins().iconst(ptr_ty(self.triple), 0))
                }
            }
            Intrinsic::Terminate => {
                let exit = self
                    .module
                    .declare_func_in_func(self.runtime.exit, self.builder.func);
                self.builder.ins().call(exit, &[value]);
                self.builder.ins().trap(TrapCode::UnreachableCodeReached);
                None
            }
        }
    }

    fn expr(&mut self, expr: &Expr) -> Option<Value> {
        match *expr {
            Expr::Literal(ref literal) => Some(self.expr_literal(literal)),
            Expr::Ident(ident) => Some(self.builder.use_var(Variable::from_u32(ident.into()))),
            Expr::Function(func_ref) => Some(self.expr_function(func_ref)),
            Expr::Tuple { ty, ref values } => self.expr_tuple(ty, values),
            Expr::Constructor {
                ty,
                index,
                ref fields,
            } => self.expr_constructor(ty, index, fields),
            Expr::Array {
                ty,
                ref values,
                value_ty,
            } => self.expr_array(ty, values, value_ty),
            Expr::Get {
                object,
                object_ty,
                object_variant,
                field,
            } => self.expr_get(object, object_ty, object_variant, field),
            Expr::Set {
                object,
                object_ty,
                object_variant,
                field,
                value,
            } => self.expr_set(object, object_ty, object_variant, field, value),
            Expr::Call(callee, ref params) => self.expr_call(callee, params),
            Expr::ContApplication(_, _) => todo!(),
            Expr::Unary {
                operator,
                operand,
                operand_ty,
            } => self.expr_unary(operator, operand, operand_ty),
            Expr::Binary {
                left,
                left_ty,
                operator,
                right,
                right_ty,
            } => self.expr_binary(left, left_ty, operator, right, right_ty),
            Expr::Assign { ident, expr } => self.expr_assign(ident, expr),
            Expr::Switch {
                scrutinee,
                ref arms,
                otherwise,
            } => self.expr_switch(scrutinee, arms, otherwise),
            Expr::Goto(block_id) => self.expr_goto(block_id),
            Expr::Closure { .. } => todo!(),
            Expr::Intrinsic {
                intrinsic,
                value,
                value_ty,
            } => self.expr_intrinsic(intrinsic, value, value_ty),
            Expr::Unreachable => {
                self.builder.ins().trap(TrapCode::UnreachableCodeReached);
                None
            }
        }
    }

    /// This method does not finalise or verify the function, or define it in the module.
    fn compile(mut self) {
        for &(param, param_ty) in self.params {
            self.builder
                .declare_var(Variable::from_u32(param.into()), param_ty);
        }

        let entry_point = self.block_map[&MirFunction::entry_point()];
        self.builder
            .append_block_params_for_function_params(entry_point);
        self.builder.switch_to_block(entry_point);
        for (i, &(param, _)) in self.params.iter().enumerate() {
            let param_value = self.builder.block_params(entry_point)[i];
            self.builder
                .def_var(Variable::from_u32(param.into()), param_value);
        }

        for (&var, &(var_ty, ref initialiser)) in &self.mir_function.declarations {
            self.builder.declare_var(
                Variable::from_u32(var.into()),
                ty_for(var_ty, self.triple, &self.program.lib_std),
            );

            if let Some(initialiser) = initialiser {
                let value = self.expr_literal(initialiser);

                self.builder.def_var(Variable::from_u32(var.into()), value);
            }
        }

        for (&block_id, block) in &self.mir_function.blocks {
            self.builder.switch_to_block(self.block_map[&block_id]);

            for &expr in &block.exprs {
                self.expr(expr);
            }
        }
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

    fn c_int_ty(&self) -> Type {
        if self.triple.default_calling_convention() == Ok(CallingConvention::AppleAarch64) {
            warn!("Apple ARM support is potentially incomplete");
            types::I32
        } else {
            Type::int(self.triple.data_model().unwrap().int_size().bits().into()).unwrap()
        }
    }

    fn function(
        &mut self,
        mir_function: &MirFunction,
        func_ref: FuncRef,
        func_ctx: &mut FunctionBuilderContext,
    ) {
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
            .map(|(param, param_ty)| (param, ty_for(param_ty, &self.triple, &self.program.lib_std)))
            .collect();

        let (func_id, ref sig) = self.functions[&func_ref];

        let mut function = Function::with_name_signature(UserFuncName::default(), sig.clone());
        let mut builder = FunctionBuilder::new(&mut function, func_ctx);

        let block_map: HashMap<_, _> = mir_function
            .blocks
            .keys()
            .map(|&id| (id, builder.create_block()))
            .collect();

        let function_compiler = FunctionCompiler {
            program: &self.program,
            module: &mut self.module,
            data_description: &mut self.data_description,
            triple: &self.triple,
            runtime: &self.runtime,
            functions: &self.functions,
            ty_layouts: &self.ty_layouts,
            builder: &mut builder,
            block_map: &block_map,
            mir_function,
            params: &params,
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

    fn compund_ty_layout(&self, types: &[TypeRef]) -> SingleLayout<'arena> {
        let mut size = 0;
        let mut align = 1;
        let mut field_locations = Vec::with_capacity(types.len());
        let mut gc_pointer_locations = Vec::with_capacity(types.len());
        for &ty in types {
            let (field_size, field_align, ptr) = ty_ref_size_align_ptr(ty, &self.program);
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

    fn append_single_layout_global(
        &mut self,
        layout: &SingleLayout,
        contents: &mut Vec<u8>,
    ) -> (u32, DataId) {
        let gc_pointer_locations = declare_const(
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
                let contents = vec![0; ptr_ty(&self.triple).bytes() as usize];
                let layout = self.declare_single_layout_global(layout, contents);
                pointer_to_global(
                    layout,
                    Some(8),
                    &mut self.module,
                    &mut self.data_description,
                    &self.triple,
                )
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

                pointer_to_global(
                    layout,
                    Some(8),
                    &mut self.module,
                    &mut self.data_description,
                    &self.triple,
                )
            }
        }
    }

    fn calc_ty_layout(&mut self, ty_ref: TypeRef) {
        let ty = *self.program.types.get_by_left(&ty_ref).unwrap();
        let layout: TyLayout<'arena> = match *ty {
            _ if ty_ref == self.program.lib_std.ty_bool => SingleLayout::primitive(1, 1).into(),
            MirType::Int | MirType::Float | MirType::Function(_) => {
                SingleLayout::primitive(8, 8).into()
            }
            MirType::String => SingleLayout::primitive(16, 8).into(),
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
            }) => self.compund_ty_layout(types).into(),
            MirType::UserDefined(UserDefinedType {
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
            MirType::Unknown => unreachable!(),
            MirType::None => SingleLayout::primitive(0, 1).into(),
        };

        let global_id = self.declare_ty_layout_global(&layout);
        self.ty_layouts
            .insert(ty_ref, (self.arena.allocate(layout), global_id));
    }

    fn compile(mut self, binary: bool) -> ObjectProduct {
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
                .map(|(param, param_ty)| {
                    (param, ty_for(param_ty, &self.triple, &self.program.lib_std))
                })
                .collect();

            let mut sig = Signature::new(CallConv::Tail);
            for &(_, param_ty) in &params {
                sig.params.push(AbiParam::new(param_ty));
            }

            let id = self
                .module
                .declare_function(&function.name, Linkage::Local, &sig)
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

        if binary {
            let c_int = self.c_int_ty();

            let mut signature = self.module.make_signature();
            signature.returns.push(AbiParam::new(c_int));

            let main = self
                .module
                .declare_function("main", Linkage::Export, &signature)
                .unwrap();
            let mut function = Function::with_name_signature(UserFuncName::default(), signature);
            let mut builder = FunctionBuilder::new(&mut function, &mut func_ctx);

            let block = builder.create_block();
            builder.switch_to_block(block);
            builder.seal_block(block);

            let entry_point = self.functions[&self.program.entry_point()].0;
            let entry_point = self.module.declare_func_in_func(entry_point, builder.func);

            let termination_ref = self.program.lib_std.fn_termination;
            let termination = self.functions[&termination_ref].0;
            let termination = self.module.declare_func_in_func(termination, builder.func);
            let termination_addr = builder.ins().func_addr(ptr_ty(&self.triple), termination);
            builder.ins().call(entry_point, &[termination_addr]);

            let rval = builder.ins().iconst(c_int, 0);
            builder.ins().return_(&[rval]);

            builder.finalize();

            self.context.clear();
            self.context.func = function;
            self.module
                .define_function(main, &mut self.context)
                .unwrap();
        }

        self.module.finish()
    }
}

#[allow(clippy::missing_panics_doc)]
pub fn compile(program: Program, binary: bool) -> ObjectProduct {
    let mut flags = settings::builder();
    flags.enable("preserve_frame_pointers").unwrap();
    let isa = isa::lookup(target_lexicon::HOST)
        .unwrap()
        .finish(Flags::new(flags))
        .unwrap();
    let module = ObjectModule::new(
        ObjectBuilder::new(isa, program.name.clone(), default_libcall_names()).unwrap(),
    );

    let arena = Arena::new();
    Compiler::new(program, module, &arena).compile(binary)
}
