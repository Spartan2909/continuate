use crate::linked_list::LinkedList;

use super::dangling_static_ptr;
use super::declare_static;
use super::fat_ptr;
use super::fat_ptr_ty;
use super::ptr_ty;
use super::signature_from_function_ty;
use super::ty_for;
use super::ty_ref_size_align_ptr;
use super::Callable;

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::iter;
use std::rc::Rc;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering;

use continuate_ir::common::BinaryOp;
use continuate_ir::common::FuncRef;
use continuate_ir::common::Ident;
use continuate_ir::common::Intrinsic;
use continuate_ir::common::Literal;
use continuate_ir::common::UnaryOp;
use continuate_ir::mid_level_ir::BlockId;
use continuate_ir::mid_level_ir::Expr;
use continuate_ir::mid_level_ir::ExprArray;
use continuate_ir::mid_level_ir::ExprAssign;
use continuate_ir::mid_level_ir::ExprBinary;
use continuate_ir::mid_level_ir::ExprCall;
use continuate_ir::mid_level_ir::ExprClosure;
use continuate_ir::mid_level_ir::ExprConstructor;
use continuate_ir::mid_level_ir::ExprContApplication;
use continuate_ir::mid_level_ir::ExprGet;
use continuate_ir::mid_level_ir::ExprIntrinsic;
use continuate_ir::mid_level_ir::ExprSet;
use continuate_ir::mid_level_ir::ExprSwitch;
use continuate_ir::mid_level_ir::ExprTuple;
use continuate_ir::mid_level_ir::ExprUnary;
use continuate_ir::mid_level_ir::Function as MirFunction;
use continuate_ir::mid_level_ir::FunctionTy;
use continuate_ir::mid_level_ir::Type as MirType;
use continuate_ir::mid_level_ir::UserDefinedType;

use continuate_common::SingleLayout;
use continuate_common::TyLayout;

use cranelift::codegen::ir;
use cranelift::codegen::ir::condcodes::FloatCC;
use cranelift::codegen::ir::condcodes::IntCC;
use cranelift::codegen::ir::entities::Value;
use cranelift::codegen::ir::types;
use cranelift::codegen::ir::AliasRegion;
use cranelift::codegen::ir::Block;
use cranelift::codegen::ir::Function;
use cranelift::codegen::ir::InstBuilder;
use cranelift::codegen::ir::MemFlags;
use cranelift::codegen::ir::Signature;
use cranelift::codegen::ir::StackSlotData;
use cranelift::codegen::ir::StackSlotKind;
use cranelift::codegen::ir::TrapCode;
use cranelift::codegen::ir::UserExternalName;
use cranelift::codegen::packed_option::ReservedValue;
use cranelift::codegen::Context;
use cranelift::frontend::FunctionBuilder;
use cranelift::frontend::Switch;
use cranelift::frontend::Variable;

use cranelift::prelude::FunctionBuilderContext;
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

pub(super) struct FunctionCompiler<'arena, 'function, 'builder, M: ?Sized> {
    pub(super) module: &'function mut M,
    pub(super) data_description: &'function mut DataDescription,
    pub(super) triple: &'function Triple,
    pub(super) functions: &'function HashMap<FuncRef, (FuncId, Signature)>,
    pub(super) ty_layouts: &'function HashMap<Rc<MirType>, (&'arena TyLayout<'arena>, DataId)>,
    pub(super) builder: &'function mut FunctionBuilder<'builder>,
    pub(super) block_map: &'function HashMap<BlockId, Block>,
    pub(super) mir_function: &'function MirFunction,
    pub(super) params: &'function [(Ident, Rc<MirType>)],
    pub(super) function_runtime: FunctionRuntime,
    pub(super) contexts: &'function LinkedList<Context>,
    pub(super) builder_contexts: &'function LinkedList<FunctionBuilderContext>,
    pub(super) vars: HashMap<Ident, (&'function MirType, bool)>,
    pub(super) temp_roots: Vec<Value>,
    pub(super) variables: HashMap<Ident, Variable>,
}

fn fat_ptr_addr(fat_ptr: Value, builder: &mut FunctionBuilder, triple: &Triple) -> Value {
    let rotation_places = i64::from(ptr_ty(triple).bits());
    let thin_ptr = builder.ins().rotr_imm(fat_ptr, rotation_places);
    builder.ins().ireduce(ptr_ty(triple), thin_ptr)
}

fn fat_ptr_meta(fat_ptr: Value, builder: &mut FunctionBuilder, triple: &Triple) -> Value {
    builder.ins().ireduce(ptr_ty(triple), fat_ptr)
}

fn get(
    endianness: cranelift::codegen::ir::Endianness,
    builder: &mut FunctionBuilder,
    triple: &Triple,
    object: Value,
    field: usize,
    layout: &SingleLayout,
    field_ty: &MirType,
) -> Value {
    let field_ty = ty_for(field_ty, triple);
    builder.ins().load(
        field_ty,
        MemFlags::new()
            .with_endianness(endianness)
            .with_aligned()
            .with_alias_region(Some(AliasRegion::Heap))
            .with_notrap(),
        object,
        layout.field_locations[field] as i32,
    )
}

impl<'arena, M: Module + ?Sized> FunctionCompiler<'arena, '_, '_, M> {
    fn variable(&mut self, ident: Ident) -> Variable {
        static NEXT: AtomicU32 = AtomicU32::new(0);

        match self.variables.entry(ident) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let variable = NEXT.fetch_add(1, Ordering::Relaxed);
                assert_ne!(variable, u32::MAX, "variable overflow");
                entry.insert(Variable::from_u32(variable));
                Variable::from_u32(variable)
            }
        }
    }

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

    fn value_ptr(&mut self, value: Value, ty: &MirType) -> Option<Value> {
        if !ty.is_primitive() {
            Some(value)
        } else if *ty == MirType::String {
            let str_ptr = fat_ptr_addr(value, self.builder, self.triple);
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

    fn alloc_gc(&mut self, ty: &MirType) -> Value {
        let ty_layout = self.ty_layouts[ty].1;
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

    fn closure<'a>(
        &mut self,
        func_ref: cranelift::codegen::ir::entities::FuncRef,
        captures: impl IntoIterator<Item = &'a Expr>,
        storage_ty: &MirType,
    ) -> Option<Value> {
        let layout = self
            .ty_layouts
            .get(storage_ty)
            .unwrap()
            .0
            .as_single()
            .unwrap();
        let storage = self.compound_ty(storage_ty, layout, captures)?;
        let function_ptr = self.builder.ins().func_addr(ptr_ty(self.triple), func_ref);
        Some(fat_ptr(function_ptr, storage, self.triple, self.builder))
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

    fn compound_ty<'a>(
        &mut self,
        ty: &MirType,
        layout: &SingleLayout,
        values: impl IntoIterator<Item = &'a Expr>,
    ) -> Option<Value> {
        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: layout.size.try_into().unwrap(),
            align_shift: 3,
        };
        let stack_slot = self.builder.create_sized_stack_slot(stack_slot_data);

        for (&field_location, field) in layout.field_locations.iter().zip(values) {
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

    fn expr_tuple(&mut self, expr: &ExprTuple) -> Option<Value> {
        let layout = self.ty_layouts[&expr.ty].0.as_single().unwrap();
        self.compound_ty(&expr.ty, layout, &expr.values)
    }

    fn expr_constructor(&mut self, expr: &ExprConstructor) -> Option<Value> {
        let layout = self.ty_layouts[&expr.ty].0;
        if let Some(index) = expr.index {
            let layout = &layout.as_sum().unwrap()[index];
            self.compound_ty(
                &expr.ty,
                layout,
                iter::once(&Expr::Literal(Literal::Int(index as i64))).chain(&expr.fields),
            )
        } else {
            let layout = layout.as_single().unwrap();
            self.compound_ty(&expr.ty, layout, &expr.fields)
        }
    }

    fn expr_array(&mut self, expr: &ExprArray) -> Option<Value> {
        let (value_size, _, _) = ty_ref_size_align_ptr(&expr.value_ty);
        let size = value_size * expr.values.len() as u64;

        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: size.try_into().unwrap(),
            align_shift: 3,
        };
        let stack_slot = self.builder.create_sized_stack_slot(stack_slot_data);

        let mut offset = 0;
        let value_size = i32::try_from(value_size).unwrap();
        for value in &expr.values {
            let value = self.expr(value)?;
            self.builder.ins().stack_store(value, stack_slot, offset);
            offset += value_size;
        }

        let dest_ptr = self.alloc_gc(&expr.ty);

        let src_ptr = self
            .builder
            .ins()
            .stack_addr(ptr_ty(self.triple), stack_slot, 0);

        let size = self.builder.ins().iconst(ptr_ty(self.triple), size as i64);

        self.builder
            .call_memcpy(self.module.target_config(), dest_ptr, src_ptr, size);

        Some(dest_ptr)
    }

    fn field_information<'a>(
        &self,
        object_ty: &'a MirType,
        object_variant: Option<usize>,
        field: usize,
    ) -> (&'arena SingleLayout<'arena>, &'a MirType) {
        let ty = object_ty.as_user_defined().unwrap();
        match (self.ty_layouts[object_ty].0, object_variant, ty) {
            (TyLayout::Single(ref layout), None, UserDefinedType::Product(fields)) => {
                (layout, &fields[field])
            }
            (TyLayout::Sum { layouts, .. }, Some(variant), UserDefinedType::Sum(variants)) => {
                (&layouts[variant], &variants[variant][field])
            }
            _ => unreachable!(),
        }
    }

    fn expr_get(&mut self, expr: &ExprGet) -> Option<Value> {
        let object = self.expr(&expr.object)?;
        let (layout, field_ty) =
            self.field_information(&expr.object_ty, expr.object_variant, expr.field);
        Some(get(
            self.cranelift_endianness(),
            self.builder,
            self.triple,
            object,
            expr.field,
            layout,
            field_ty,
        ))
    }

    fn expr_set(&mut self, expr: &ExprSet) -> Option<Value> {
        let object = self.expr(&expr.object)?;
        let layout = self
            .field_information(&expr.object_ty, expr.object_variant, expr.field)
            .0;
        let value = self.expr(&expr.value)?;
        let endianness = self.cranelift_endianness();
        self.builder.ins().store(
            MemFlags::new()
                .with_endianness(endianness)
                .with_aligned()
                .with_alias_region(Some(AliasRegion::Heap))
                .with_notrap(),
            value,
            object,
            layout.field_locations[expr.field] as i32,
        );
        self.clear_temp_roots();
        Some(value)
    }

    fn callable(&mut self, callee: &Expr) -> Option<Callable> {
        match *callee {
            Expr::Function(func_ref) => Some(Callable::Static(func_ref)),
            _ => Some(Callable::Dynamic(self.expr(callee)?)),
        }
    }

    fn expr_call(&mut self, expr: &ExprCall) -> Option<Value> {
        let callable = self.callable(&expr.callee)?;

        let args: Option<Vec<_>> = iter::once(Some(Value::reserved_value()))
            .chain(
                expr.args
                    .iter()
                    .map(|(ident, expr)| (*ident, self.expr(expr)))
                    .sorted_by_key(|(ident, _)| *ident)
                    .map(|(_, value)| value),
            )
            .collect();
        let mut args = args?;

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
            let var = self.variable(var);
            let value = self.builder.use_var(var);
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
                let signature =
                    signature_from_function_ty(expr.callee_ty.as_function().unwrap(), self.triple);
                let sig_ref = self.builder.import_signature(signature);

                let function_ptr = fat_ptr_addr(callee, self.builder, self.triple);

                args[0] = fat_ptr_meta(callee, self.builder, self.triple);

                self.builder
                    .ins()
                    .return_call_indirect(sig_ref, function_ptr, &args);
            }
        }

        None
    }

    fn application_function(
        &mut self,
        ty: &FunctionTy,
        storage_ty: &MirType,
        callee_ty: &MirType,
        continuations: impl IntoIterator<Item = Ident>,
    ) -> FuncId {
        let signature = signature_from_function_ty(ty, self.triple);
        let func_id = self.module.declare_anonymous_function(&signature).unwrap();

        let mut function = Function::with_name_signature(
            ir::UserFuncName::User(UserExternalName::new(2, 0)),
            signature,
        );
        let mut func_ctx = self.builder_contexts.get();
        let mut builder = FunctionBuilder::new(&mut function, &mut func_ctx);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.append_block_params_for_function_params(block);
        let storage = builder.block_params(block)[0];

        let (layout, field_ty) = self.field_information(storage_ty, None, 0);
        let callee = get(
            self.cranelift_endianness(),
            &mut builder,
            self.triple,
            storage,
            0,
            layout,
            field_ty,
        );

        let params = ty
            .params
            .iter()
            .map(|_| None)
            .chain(ty.continuations.keys().map(|ident| Some(*ident)))
            .sorted()
            .collect_vec();
        let mut args: Vec<_> = builder
            .block_params(block)
            .iter()
            .skip(1)
            .enumerate()
            .map(|(i, value)| (*value, params[i]))
            .collect();
        args.extend(continuations.into_iter().enumerate().map(|(field, ident)| {
            let (layout, field_ty) = self.field_information(storage_ty, None, field + 1);
            (
                get(
                    self.cranelift_endianness(),
                    &mut builder,
                    self.triple,
                    storage,
                    field + 1,
                    layout,
                    field_ty,
                ),
                Some(ident),
            )
        }));
        args.sort_unstable_by_key(|(_, ident)| *ident);
        let args = iter::once(fat_ptr_meta(callee, &mut builder, self.triple))
            .chain(args.into_iter().map(|(value, _)| value))
            .collect_vec();

        let signature = signature_from_function_ty(callee_ty.as_function().unwrap(), self.triple);
        let sig_ref = builder.import_signature(signature);

        let callee = fat_ptr_addr(callee, &mut builder, self.triple);
        builder.ins().return_call_indirect(sig_ref, callee, &args);

        let mut context = self.contexts.get();
        context.clear();
        context.want_disasm = cfg!(debug_assertions);
        context.func = function;
        self.module.define_function(func_id, &mut context).unwrap();
        func_id
    }

    fn expr_cont_application(&mut self, expr: &ExprContApplication) -> Option<Value> {
        let func_id = self.application_function(
            expr.result_ty.as_function().unwrap(),
            &expr.storage_ty,
            &expr.callee_ty,
            expr.continuations
                .iter()
                .map(|(ident, _)| *ident)
                .sorted_unstable(),
        );
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);

        self.closure(
            func_ref,
            iter::once(&*expr.callee).chain(expr.continuations.iter().map(|(_, expr)| expr)),
            &expr.storage_ty,
        )
    }

    fn expr_unary(&mut self, expr: &ExprUnary) -> Option<Value> {
        let operand = self.expr(&expr.operand)?;
        let operand_ty = ty_for(&expr.operand_ty, self.triple);
        match expr.operator {
            UnaryOp::Neg if operand_ty == types::F64 => Some(self.builder.ins().ineg(operand)),
            UnaryOp::Neg if operand_ty == types::I64 => Some(self.builder.ins().fneg(operand)),
            UnaryOp::Not if operand_ty == types::I8 => {
                Some(self.builder.ins().bxor_imm(operand, 1))
            }
            UnaryOp::Neg | UnaryOp::Not => unreachable!(),
        }
    }

    #[allow(clippy::cognitive_complexity)]
    fn expr_binary(&mut self, expr: &ExprBinary) -> Option<Value> {
        debug_assert_eq!(expr.left_ty, expr.right_ty);
        let left = self.expr(&expr.left)?;
        let left_ty = ty_for(&expr.left_ty, self.triple);
        let right = self.expr(&expr.right)?;
        let value = match expr.operator {
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

    fn expr_assign(&mut self, expr: &ExprAssign) -> Option<Value> {
        let (var_ty, initialised_ref) = self.vars.get_mut(&expr.ident).unwrap();
        let (var_ty, initialised) = (*var_ty, *initialised_ref);
        *initialised_ref = true;

        if initialised {
            let var = self.variable(expr.ident);
            let value = self.builder.use_var(var);
            if let Some(ptr) = self.value_ptr(value, var_ty) {
                self.builder
                    .ins()
                    .call(self.function_runtime.unmark_root, &[ptr]);
            }
        }

        let value = self.expr(&expr.expr)?;
        let var = self.variable(expr.ident);
        self.builder.def_var(var, value);

        self.clear_temp_roots();

        if let Some(ptr) = self.value_ptr(value, var_ty) {
            self.builder
                .ins()
                .call(self.function_runtime.mark_root, &[ptr]);
        }

        Some(value)
    }

    fn expr_switch(&mut self, expr: &ExprSwitch) -> Option<Value> {
        let scrutinee = self.expr(&expr.scrutinee)?;
        let mut switch = Switch::new();
        for (&val, block_id) in &expr.arms {
            switch.set_entry(val as u128, self.block_map[block_id]);
        }
        switch.emit(self.builder, scrutinee, self.block_map[&expr.otherwise]);
        None
    }

    fn expr_goto(&mut self, block_id: BlockId) -> Option<Value> {
        self.builder.switch_to_block(self.block_map[&block_id]);
        None
    }

    fn expr_closure(&mut self, expr: &ExprClosure) -> Option<Value> {
        let captures: Vec<_> = expr
            .captures
            .iter()
            .copied()
            .sorted_unstable()
            .map(Expr::Ident)
            .collect();
        let func_id = self.functions[&expr.func_ref].0;
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        self.closure(func_ref, &captures, &expr.storage_ty)
    }

    fn expr_intrinsic(&mut self, expr: &ExprIntrinsic) -> Option<Value> {
        let value = self.expr(&expr.value)?;
        match expr.intrinsic {
            Intrinsic::Discriminant => {
                if *expr.value_ty == MirType::Bool {
                    Some(self.builder.ins().sextend(types::I64, value))
                } else if matches!(
                    *expr.value_ty,
                    MirType::UserDefined(UserDefinedType::Sum(_))
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
            Intrinsic::Unreachable => {
                self.builder.ins().trap(TrapCode::unwrap_user(1));
                None
            }
        }
    }

    fn expr(&mut self, expr: &Expr) -> Option<Value> {
        match expr {
            Expr::Literal(literal) => Some(self.expr_literal(literal)),
            Expr::Ident(ident) => {
                let var = self.variable(*ident);
                Some(self.builder.use_var(var))
            }
            Expr::Function(func_ref) => Some(self.expr_function(*func_ref)),
            Expr::Tuple(expr) => self.expr_tuple(expr),
            Expr::Constructor(expr) => self.expr_constructor(expr),
            Expr::Array(expr) => self.expr_array(expr),
            Expr::Get(expr) => self.expr_get(expr),
            Expr::Set(expr) => self.expr_set(expr),
            Expr::Call(expr) => self.expr_call(expr),
            Expr::ContApplication(expr) => self.expr_cont_application(expr),
            Expr::Unary(expr) => self.expr_unary(expr),
            Expr::Binary(expr) => self.expr_binary(expr),
            Expr::Assign(expr) => self.expr_assign(expr),
            Expr::Switch(expr) => self.expr_switch(expr),
            Expr::Goto(block_id) => self.expr_goto(*block_id),
            Expr::Closure(expr) => self.expr_closure(expr),
            Expr::Intrinsic(expr) => self.expr_intrinsic(expr),
        }
    }

    /// This method does not finalise or verify the function, or define it in the module.
    pub(super) fn compile(mut self) {
        for (param, param_ty) in self.params {
            let var = self.variable(*param);
            self.builder.declare_var(var, ty_for(param_ty, self.triple));
            self.vars.insert(*param, (param_ty, true));
        }

        let entry_point = self.block_map[&MirFunction::entry_point()];
        self.builder
            .append_block_params_for_function_params(entry_point);
        self.builder.switch_to_block(entry_point);
        for (i, &(param, _)) in self.params.iter().enumerate() {
            let param_value = self.builder.block_params(entry_point)[i + 1];
            let var = self.variable(param);
            self.builder.def_var(var, param_value);
        }

        for (&ident, (var_ty, initialiser)) in &self.mir_function.declarations {
            let var = self.variable(ident);
            self.builder.declare_var(var, ty_for(var_ty, self.triple));

            if let Some(initialiser) = initialiser {
                let value = self.expr_literal(initialiser);

                self.builder.def_var(var, value);
            }

            self.vars.insert(ident, (var_ty, initialiser.is_some()));
        }

        if let Some(captures) = &self.mir_function.captures {
            let storage = self.builder.block_params(entry_point)[0];
            for (i, &ident) in captures.captures.iter().enumerate() {
                let (layout, field_ty) = self.field_information(&captures.storage_ty, None, i);
                let value = get(
                    self.cranelift_endianness(),
                    self.builder,
                    self.triple,
                    storage,
                    i,
                    layout,
                    field_ty,
                );
                let var = self.variable(ident);
                self.builder.def_var(var, value);
            }
        }

        for (&block_id, block) in &self.mir_function.blocks {
            self.builder.switch_to_block(self.block_map[&block_id]);

            for expr in &block.exprs {
                self.expr(expr);
            }
        }
    }
}
