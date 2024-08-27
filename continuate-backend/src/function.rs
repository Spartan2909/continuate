use super::dangling_static_ptr;
use super::declare_static;
use super::fat_ptr_ty;
use super::ptr_ty;
use super::signature_from_function_ty;
use super::ty_for;
use super::ty_ref_size_align_ptr;
use super::Callable;

use std::collections::HashMap;
use std::iter;

use continuate_ir::common::BinaryOp;
use continuate_ir::common::FuncRef;
use continuate_ir::common::Ident;
use continuate_ir::common::Intrinsic;
use continuate_ir::common::Literal;
use continuate_ir::common::TypeRef;
use continuate_ir::common::UnaryOp;
use continuate_ir::mid_level_ir::BlockId;
use continuate_ir::mid_level_ir::Expr;
use continuate_ir::mid_level_ir::Function as MirFunction;
use continuate_ir::mid_level_ir::FunctionTy;
use continuate_ir::mid_level_ir::Program;
use continuate_ir::mid_level_ir::Type as MirType;
use continuate_ir::mid_level_ir::TypeConstructor;
use continuate_ir::mid_level_ir::UserDefinedType;
// use continuate_ir::HashMap;

use continuate_common::SingleLayout;
use continuate_common::TyLayout;

use cranelift::codegen::ir;
use cranelift::codegen::ir::condcodes::FloatCC;
use cranelift::codegen::ir::condcodes::IntCC;
use cranelift::codegen::ir::entities::Value;
use cranelift::codegen::ir::types;
use cranelift::codegen::ir::AliasRegion;
use cranelift::codegen::ir::Block;
use cranelift::codegen::ir::InstBuilder;
use cranelift::codegen::ir::MemFlags;
use cranelift::codegen::ir::Signature;
use cranelift::codegen::ir::StackSlotData;
use cranelift::codegen::ir::StackSlotKind;
use cranelift::codegen::ir::TrapCode;
use cranelift::codegen::isa::CallConv;
use cranelift::codegen::packed_option::ReservedValue;
use cranelift::frontend::FunctionBuilder;
use cranelift::frontend::Switch;
use cranelift::frontend::Variable;

use cranelift_module::DataDescription;
use cranelift_module::DataId;
use cranelift_module::FuncId;
use cranelift_module::Module;

use itertools::Itertools as _;

use target_lexicon::Endianness;
use target_lexicon::Triple;

pub(super) struct FunctionRuntime {
    /// `fn(ty_layout: &'static TyLayout<'static>) -> *mut ()`
    pub(super) alloc_gc: ir::FuncRef,

    /// `fn(len: usize) -> *mut ()`
    pub(super) alloc_string: ir::FuncRef,

    /// `fn(ptr: *const ())`
    pub(super) mark_root: ir::FuncRef,

    /// `fn(ptr: *const ())`
    pub(super) unmark_root: ir::FuncRef,
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

pub(super) struct FunctionCompiler<'arena, 'function, 'builder, M> {
    pub(super) program: &'function Program<'function>,
    pub(super) module: &'function mut M,
    pub(super) data_description: &'function mut DataDescription,
    pub(super) triple: &'function Triple,
    pub(super) functions: &'function HashMap<FuncRef, (FuncId, Signature)>,
    pub(super) ty_layouts: &'function HashMap<TypeRef, (&'arena TyLayout<'arena>, DataId)>,
    pub(super) builder: &'function mut FunctionBuilder<'builder>,
    pub(super) block_map: &'function HashMap<BlockId, Block>,
    pub(super) mir_function: &'function MirFunction<'function>,
    pub(super) params: &'function [(Ident, TypeRef)],
    pub(super) function_runtime: FunctionRuntime,
    pub(super) vars: HashMap<Ident, (TypeRef, bool)>,
    pub(super) temp_roots: Vec<Value>,
}

impl<'arena, 'function, 'builder, M: Module> FunctionCompiler<'arena, 'function, 'builder, M> {
    fn cranelift_endianness(&self) -> ir::Endianness {
        use ir::Endianness as E;
        match self.triple.endianness().unwrap() {
            Endianness::Big => E::Big,
            Endianness::Little => E::Little,
        }
    }

    fn fat_ptr(&mut self, thin_ptr: Value, metadata: Value) -> Value {
        super::fat_ptr(thin_ptr, metadata, self.triple, self.builder)
    }

    fn fat_ptr_addr(&mut self, fat_ptr: Value) -> Value {
        let rotation_places = i64::from(ptr_ty(self.triple).bits());
        let thin_ptr = self.builder.ins().rotr_imm(fat_ptr, rotation_places);
        self.builder.ins().ireduce(ptr_ty(self.triple), thin_ptr)
    }

    fn fat_ptr_meta(&mut self, fat_ptr: Value) -> Value {
        self.builder.ins().ireduce(ptr_ty(self.triple), fat_ptr)
    }

    fn value_ptr(&mut self, value: Value, ty: TypeRef) -> Option<Value> {
        if !self.program.is_primitive(ty) {
            Some(value)
        } else if ty == self.program.lib_std.ty_string {
            let str_ptr = self.fat_ptr_addr(value);
            Some(str_ptr)
        } else {
            None
        }
    }

    fn clear_temp_roots(&mut self) {
        for &temp_root in &self.temp_roots {
            self.builder
                .ins()
                .call(self.function_runtime.unmark_root, &[temp_root]);
        }

        self.temp_roots.clear();
    }

    fn alloc_gc(&mut self, ty: TypeRef) -> Value {
        let ty_layout = self.ty_layouts[&ty].1;
        let ty_layout = self
            .module
            .declare_data_in_func(ty_layout, self.builder.func);
        let ty_layout = self
            .builder
            .ins()
            .global_value(ptr_ty(self.triple), ty_layout);

        let call_result = self
            .builder
            .ins()
            .call(self.function_runtime.alloc_gc, &[ty_layout]);
        let values = self.builder.inst_results(call_result);
        debug_assert_eq!(values.len(), 1);

        self.temp_roots.push(values[0]);

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
        let mut contents = Vec::with_capacity(string.len() + 1);
        contents.extend(string.as_bytes().iter().copied());
        contents.push(0);

        let global_string_ref = declare_static(
            contents.into_boxed_slice(),
            None,
            self.module,
            self.data_description,
        )
        .unwrap_or_else(|| {
            dangling_static_ptr(None, self.module, self.data_description, self.triple)
        });

        let len = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), string.len() as i64 + 1);
        let call_result = self
            .builder
            .ins()
            .call(self.function_runtime.alloc_string, &[len]);
        let values = self.builder.inst_results(call_result);
        debug_assert_eq!(values.len(), 1);

        let dest_ptr = values[0];

        let gv = self
            .module
            .declare_data_in_func(global_string_ref, self.builder.func);
        let src_ptr = self.builder.ins().global_value(ptr_ty(self.triple), gv);

        let size = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), string.len() as i64 + 1);

        self.builder
            .call_memcpy(self.module.target_config(), dest_ptr, src_ptr, size);

        self.temp_roots.push(dest_ptr);

        let size = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), string.len() as i64);

        self.fat_ptr(dest_ptr, size)
    }

    fn expr_function(&mut self, func_ref: FuncRef) -> Value {
        let func_id = self.functions[&func_ref].0;
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        let function_ptr = self.builder.ins().func_addr(ptr_ty(self.triple), func_ref);
        let metadata = self.builder.ins().iconst(ptr_ty(self.triple), 0);
        self.fat_ptr(function_ptr, metadata)
    }

    fn compound_ty(
        &mut self,
        ty: TypeRef,
        layout: &SingleLayout,
        values: &[&[Expr]],
    ) -> Option<Value> {
        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: layout.size.try_into().unwrap(),
            align_shift: 3,
        };
        let stack_slot = self.builder.create_sized_stack_slot(stack_slot_data);

        for (&field_location, field) in layout
            .field_locations
            .iter()
            .zip(values.iter().copied().flatten())
        {
            let field = self.expr(field)?;
            self.builder.ins().stack_store(
                field,
                stack_slot,
                i32::try_from(field_location).unwrap(),
            );
        }

        let dest_ptr = self.alloc_gc(ty);

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

    fn expr_tuple(&mut self, ty: TypeRef, values: &[Expr]) -> Option<Value> {
        let layout = self.ty_layouts[&ty].0.as_single().unwrap();
        self.compound_ty(ty, layout, &[values])
    }

    fn expr_constructor(
        &mut self,
        ty: TypeRef,
        index: Option<usize>,
        fields: &[Expr],
    ) -> Option<Value> {
        let layout = self.ty_layouts[&ty].0;
        if let Some(index) = index {
            let layout = &layout.as_sum().unwrap()[index];
            self.compound_ty(
                ty,
                layout,
                &[&[Expr::Literal(Literal::Int(index as i64))], fields],
            )
        } else {
            let layout = layout.as_single().unwrap();
            self.compound_ty(ty, layout, &[fields])
        }
    }

    fn expr_array(&mut self, ty: TypeRef, values: &[Expr], value_ty: TypeRef) -> Option<Value> {
        let (value_size, _, _) = ty_ref_size_align_ptr(value_ty, self.program);
        let size = value_size * values.len() as u64;

        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: size.try_into().unwrap(),
            align_shift: 3,
        };
        let stack_slot = self.builder.create_sized_stack_slot(stack_slot_data);

        let mut offset = 0;
        let value_size = i32::try_from(value_size).unwrap();
        for value in values {
            let value = self.expr(value)?;
            self.builder.ins().stack_store(value, stack_slot, offset);
            offset += value_size;
        }

        let dest_ptr = self.alloc_gc(ty);

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
        let field_ty = ty_for(field_ty, self.triple, self.program);
        let endianness = self.cranelift_endianness();
        Some(
            self.builder.ins().load(
                field_ty,
                MemFlags::new()
                    .with_endianness(endianness)
                    .with_aligned()
                    .with_alias_region(Some(AliasRegion::Heap))
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
                .with_alias_region(Some(AliasRegion::Heap))
                .with_notrap(),
            value,
            object,
            layout.field_locations[field] as i32,
        );
        self.clear_temp_roots();
        Some(value)
    }

    fn callable<'a>(
        &mut self,
        callee: &'a Expr<'a>,
    ) -> Option<(Callable, HashMap<Ident, &'a Expr<'a>>)> {
        match *callee {
            Expr::Function(func_ref) => Some((Callable::Static(func_ref), HashMap::new())),
            Expr::ContApplication(callee, ref continuations) => {
                let (callable, mut new_continuations) = self.callable(callee)?;
                new_continuations.extend(continuations.iter().map(|(&ident, expr)| (ident, expr)));
                Some((callable, new_continuations))
            }
            _ => Some((Callable::Dynamic(self.expr(callee)?), HashMap::new())),
        }
    }

    fn expr_call(&mut self, callee: &Expr, callee_ty: &FunctionTy, args: &[Expr]) -> Option<Value> {
        let (callable, continuations) = self.callable(callee)?;

        let args: Option<Vec<_>> = iter::once(Some(Value::reserved_value()))
            .chain(args.iter().map(|expr| self.expr(expr)))
            .collect();
        let mut args = args?;

        let continuations: Option<Vec<_>> = continuations
            .into_iter()
            .sorted_unstable_by_key(|&(ident, _)| ident)
            .map(|(_, expr)| self.expr(expr))
            .collect();
        args.append(&mut continuations?);

        let vars: Vec<_> = self
            .vars
            .iter()
            .filter_map(|(&var, &(var_ty, initialised))| {
                if initialised {
                    Some((var, var_ty))
                } else {
                    None
                }
            })
            .collect();
        for (var, var_ty) in vars {
            let value = self.builder.use_var(Variable::from_u32(var.into()));
            if let Some(ptr) = self.value_ptr(value, var_ty) {
                self.builder
                    .ins()
                    .call(self.function_runtime.unmark_root, &[ptr]);
            }
        }

        match callable {
            Callable::Static(func_ref) => {
                let func_id = self.functions[&func_ref].0;
                let func = self.module.declare_func_in_func(func_id, self.builder.func);
                args[0] = self.builder.ins().iconst(ptr_ty(self.triple), 0);

                self.builder.ins().return_call(func, &args);
            }
            Callable::Dynamic(callee) => {
                let signature = signature_from_function_ty(
                    callee_ty,
                    CallConv::Tail,
                    self.triple,
                    self.program,
                );
                let sig_ref = self.builder.import_signature(signature);

                let function_ptr = self.fat_ptr_addr(callee);

                args[0] = self.fat_ptr_meta(callee);

                self.builder
                    .ins()
                    .return_call_indirect(sig_ref, function_ptr, &args);
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
        let operand_ty = ty_for(operand_ty, self.triple, self.program);
        match operator {
            UnaryOp::Neg if operand_ty == types::F64 => Some(self.builder.ins().ineg(operand)),
            UnaryOp::Neg if operand_ty == types::I64 => Some(self.builder.ins().fneg(operand)),
            UnaryOp::Not if operand_ty == types::I8 => {
                Some(self.builder.ins().bxor_imm(operand, 1))
            }
            UnaryOp::Neg | UnaryOp::Not => unreachable!(),
        }
    }

    #[allow(clippy::cognitive_complexity)]
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
        let left_ty = ty_for(left_ty, self.triple, self.program);
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
        let (var_ty, initialised_ref) = self.vars.get_mut(&ident).unwrap();
        let (var_ty, initialised) = (*var_ty, *initialised_ref);
        *initialised_ref = true;

        if initialised {
            let value = self.builder.use_var(Variable::from_u32(ident.into()));
            if let Some(ptr) = self.value_ptr(value, var_ty) {
                self.builder
                    .ins()
                    .call(self.function_runtime.unmark_root, &[ptr]);
            }
        }

        let value = self.expr(expr)?;
        self.builder
            .def_var(Variable::from_u32(ident.into()), value);

        self.clear_temp_roots();

        if let Some(ptr) = self.value_ptr(value, var_ty) {
            self.builder
                .ins()
                .call(self.function_runtime.mark_root, &[ptr]);
        }

        Some(value)
    }

    fn expr_switch<I>(&mut self, scrutinee: &Expr, arms: I, otherwise: BlockId) -> Option<Value>
    where
        I: IntoIterator<Item = (i64, BlockId)>,
    {
        let scrutinee = self.expr(scrutinee)?;
        let mut switch = Switch::new();
        for (val, block_id) in arms {
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
                                .with_alias_region(Some(AliasRegion::Heap))
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
                self.builder.ins().return_(&[value]);
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
            Expr::Call {
                callee,
                callee_ty,
                ref args,
            } => self.expr_call(callee, callee_ty, args),
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
            } => self.expr_switch(
                scrutinee,
                arms.iter()
                    .map(|(&discriminant, &block)| (discriminant, block)),
                otherwise,
            ),
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
    pub(super) fn compile(mut self) {
        for &(param, param_ty) in self.params {
            self.builder.declare_var(
                Variable::from_u32(param.into()),
                ty_for(param_ty, self.triple, self.program),
            );
            self.vars.insert(param, (param_ty, true));
        }

        let entry_point = self.block_map[&MirFunction::entry_point()];
        self.builder
            .append_block_params_for_function_params(entry_point);
        self.builder.switch_to_block(entry_point);
        for (i, &(param, _)) in self.params.iter().enumerate() {
            let param_value = self.builder.block_params(entry_point)[i + 1];
            self.builder
                .def_var(Variable::from_u32(param.into()), param_value);
        }

        for (&var, &(var_ty, ref initialiser)) in &self.mir_function.declarations {
            self.builder.declare_var(
                Variable::from_u32(var.into()),
                ty_for(var_ty, self.triple, self.program),
            );

            if let Some(initialiser) = initialiser {
                let value = self.expr_literal(initialiser);

                self.builder.def_var(Variable::from_u32(var.into()), value);
            }

            self.vars.insert(var, (var_ty, initialiser.is_some()));
        }

        for (&block_id, block) in &self.mir_function.blocks {
            self.builder.switch_to_block(self.block_map[&block_id]);

            for expr in &block.exprs {
                self.expr(expr);
            }
        }
    }
}
