use crate::{
    BoxedModuleError, Callable, ModuleResult, dangling_static_ptr, declare_static, fat_ptr_ty,
    ptr_ty, signature_from_function_ty, storage::Storage, ty_for, ty_ref_size_align_ptr,
};

use std::{collections::HashMap, iter, sync::Arc};

use continuate_ir::{
    common::{BinaryOp, FuncRef, Ident, Intrinsic, Literal, UnaryOp},
    mid_level_ir::{
        BlockId, Expr, ExprApplication, ExprArray, ExprAssign, ExprBinary, ExprCall, ExprClosure,
        ExprConstructor, ExprFunction, ExprGet, ExprGoto, ExprIdent, ExprIntrinsic, ExprLiteral,
        ExprSet, ExprSwitch, ExprTuple, ExprUnary, Function as MirFunction, FunctionTy,
        Type as MirType, UserDefinedType,
    },
};

use continuate_rt::layout::{SingleLayout, TyLayout};

use cranelift::{
    codegen::{
        Context,
        ir::{
            self, AliasRegion, Block, Function, InstBuilder, MemFlags, Signature, StackSlotData,
            StackSlotKind, TrapCode, UserExternalName,
            condcodes::{FloatCC, IntCC},
            entities::Value,
            types,
        },
        packed_option::ReservedValue,
    },
    frontend::{FunctionBuilder, FunctionBuilderContext, Switch, Variable},
    module::{DataDescription, DataId, FuncId, Module},
};

use itertools::Itertools as _;

use target_lexicon::Triple;

pub(super) struct FunctionRuntime {
    /// `fn(ty_layout: &'static TyLayout<'static>, &StackMap, *const stack) -> *mut ()`
    pub(super) alloc_gc: ir::FuncRef,

    /// `fn(len: usize, &StackMap, *const stack) -> *mut ()`
    pub(super) alloc_string: ir::FuncRef,
}

macro_rules! match_ty {
    { ($scrutinee:expr_2021)
        $( $ty:expr_2021 $( , $alternative:expr_2021 )* => $expr:expr_2021 ),* $(,)?
    } => {
        match $scrutinee {
            $( _scrutinee if _scrutinee == $ty $( || _scrutinee == $alternative )* => $expr, )*
            _ => unreachable!(),
        }
    };
}

enum ExprError {
    Module(BoxedModuleError),
    NoValue,
}

impl From<BoxedModuleError> for ExprError {
    fn from(value: BoxedModuleError) -> Self {
        ExprError::Module(value)
    }
}

type Result<T, E = ExprError> = std::result::Result<T, E>;

pub(super) struct FunctionCompilerBuilder<'function, 'builder, M: ?Sized> {
    pub(super) module: &'function mut M,
    pub(super) data_description: &'function mut DataDescription,
    pub(super) triple: &'function Triple,
    pub(super) functions: &'function HashMap<FuncRef, (FuncId, Signature)>,
    pub(super) ty_layouts: &'function HashMap<Arc<MirType>, (TyLayout<'function>, DataId)>,
    pub(super) builder: &'function mut FunctionBuilder<'builder>,
    pub(super) block_map: &'function HashMap<BlockId, Block>,
    pub(super) mir_function: &'function MirFunction,
    pub(super) params: &'function [(Ident, Arc<MirType>)],
    pub(super) function_runtime: FunctionRuntime,
    pub(super) contexts: &'function Storage<Context>,
    pub(super) builder_contexts: &'function Storage<FunctionBuilderContext>,
}

impl<'function, 'builder, M: ?Sized> FunctionCompilerBuilder<'function, 'builder, M> {
    pub(super) fn build(self) -> FunctionCompiler<'function, 'builder, M> {
        FunctionCompiler {
            module: self.module,
            data_description: self.data_description,
            triple: self.triple,
            functions: self.functions,
            ty_layouts: self.ty_layouts,
            builder: self.builder,
            block_map: self.block_map,
            mir_function: self.mir_function,
            params: self.params,
            function_runtime: self.function_runtime,
            contexts: self.contexts,
            builder_contexts: self.builder_contexts,
            vars: HashMap::new(),
            variables: HashMap::new(),
        }
    }
}

pub(super) struct FunctionCompiler<'function, 'builder, M: ?Sized> {
    module: &'function mut M,
    data_description: &'function mut DataDescription,
    triple: &'function Triple,
    functions: &'function HashMap<FuncRef, (FuncId, Signature)>,
    ty_layouts: &'function HashMap<Arc<MirType>, (TyLayout<'function>, DataId)>,
    builder: &'function mut FunctionBuilder<'builder>,
    block_map: &'function HashMap<BlockId, Block>,
    mir_function: &'function MirFunction,
    params: &'function [(Ident, Arc<MirType>)],
    function_runtime: FunctionRuntime,
    contexts: &'function Storage<Context>,
    builder_contexts: &'function Storage<FunctionBuilderContext>,
    vars: HashMap<Ident, (&'function MirType, bool)>,
    variables: HashMap<Ident, Variable>,
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
            .with_aligned()
            .with_alias_region(Some(AliasRegion::Heap))
            .with_notrap(),
        object,
        layout.field_locations[field] as i32,
    )
}

const fn is_ptr(ty: &MirType) -> bool {
    match ty {
        MirType::Bool | MirType::Int | MirType::Float | MirType::Unknown | MirType::None => false,
        MirType::String
        | MirType::Array(_, _)
        | MirType::Tuple(_)
        | MirType::Function(_)
        | MirType::UserDefined(_) => true,
    }
}

impl<'function, M: Module + ?Sized> FunctionCompiler<'function, '_, M> {
    fn fat_ptr(&mut self, thin_ptr: Value, metadata: Value) -> Value {
        crate::fat_ptr(thin_ptr, metadata, self.triple, self.builder)
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

        let sp = self.builder.ins().get_stack_pointer(ptr_ty(self.triple));
        let call_result = self
            .builder
            .ins()
            .call(self.function_runtime.alloc_gc, &[ty_layout, sp]);
        let values = self.builder.inst_results(call_result);
        let value = values[0];

        self.builder.declare_value_needs_stack_map(value);

        value
    }

    fn closure<'a>(
        &mut self,
        func_ref: cranelift::codegen::ir::entities::FuncRef,
        captures: impl IntoIterator<Item = &'a Expr>,
        storage_ty: &MirType,
    ) -> Result<Value> {
        let layout = self
            .ty_layouts
            .get(storage_ty)
            .unwrap()
            .0
            .as_single()
            .unwrap();
        let storage = self.compound_ty(storage_ty, layout, captures)?;
        let function_ptr = self.builder.ins().func_addr(ptr_ty(self.triple), func_ref);
        let value = self.fat_ptr(storage, function_ptr);
        self.builder.declare_value_needs_stack_map(value);
        Ok(value)
    }

    fn literal(&mut self, literal: &Literal) -> ModuleResult<Value> {
        match *literal {
            Literal::Int(n) => Ok(self.builder.ins().iconst(types::I64, n)),
            Literal::Float(n) => Ok(self.builder.ins().f64const(n)),
            Literal::String(ref string) => self.expr_literal_string(string),
        }
    }

    fn expr_literal(&mut self, expr: &ExprLiteral) -> Result<Value> {
        Ok(self.literal(&expr.literal)?)
    }

    fn expr_literal_string(&mut self, string: &str) -> ModuleResult<Value> {
        let mut contents = Vec::with_capacity(string.len() + 1);
        contents.extend(string.as_bytes().iter().copied());
        contents.push(0);

        let global_string_ref = declare_static(
            contents.into_boxed_slice(),
            None,
            self.module,
            self.data_description,
        )?
        .map_or_else(
            || dangling_static_ptr(None, self.module, self.data_description, self.triple),
            Ok,
        )?;

        let len = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), string.len() as i64 + 1);
        let sp = self.builder.ins().get_stack_pointer(ptr_ty(self.triple));
        let call_result = self
            .builder
            .ins()
            .call(self.function_runtime.alloc_string, &[len, sp]);
        let values = self.builder.inst_results(call_result);

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

        let size = self
            .builder
            .ins()
            .iconst(ptr_ty(self.triple), string.len() as i64);

        let value = self.fat_ptr(dest_ptr, size);

        self.builder.declare_value_needs_stack_map(value);

        Ok(value)
    }

    fn expr_function(&mut self, expr: &ExprFunction) -> Value {
        let func_id = self.functions[&expr.function].0;
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        let function_ptr = self.builder.ins().func_addr(ptr_ty(self.triple), func_ref);
        let metadata = self.builder.ins().iconst(ptr_ty(self.triple), 0);
        self.fat_ptr(metadata, function_ptr)
    }

    fn compound_ty<'a>(
        &mut self,
        ty: &MirType,
        layout: &SingleLayout,
        values: impl IntoIterator<Item = &'a Expr>,
    ) -> Result<Value> {
        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: layout.size.try_into().unwrap(),
            align_shift: 3,
            key: None,
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

        Ok(dest_ptr)
    }

    fn expr_tuple(&mut self, expr: &ExprTuple) -> Result<Value> {
        let layout = self.ty_layouts[&expr.ty].0.as_single().unwrap();
        self.compound_ty(&expr.ty, layout, &expr.values)
    }

    fn expr_constructor(&mut self, expr: &ExprConstructor) -> Result<Value> {
        let layout = self.ty_layouts[&expr.ty].0;
        if let Some(index) = expr.index {
            let layout = &layout.as_sum().unwrap()[index];
            self.compound_ty(
                &expr.ty,
                layout,
                iter::once(&Expr::Literal(ExprLiteral {
                    literal: Literal::Int(index as i64),
                }))
                .chain(&expr.fields),
            )
        } else {
            let layout = layout.as_single().unwrap();
            self.compound_ty(&expr.ty, layout, &expr.fields)
        }
    }

    fn expr_array(&mut self, expr: &ExprArray) -> Result<Value> {
        let (value_size, _, _) = ty_ref_size_align_ptr(&expr.value_ty, self.triple);
        let size = value_size * expr.values.len() as u64;

        let stack_slot_data = StackSlotData {
            kind: StackSlotKind::ExplicitSlot,
            size: size.try_into().unwrap(),
            align_shift: 3,
            key: None,
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

        Ok(dest_ptr)
    }

    fn field_information<'a>(
        &self,
        object_ty: &'a MirType,
        object_variant: Option<usize>,
        field: usize,
    ) -> (SingleLayout<'function>, &'a MirType) {
        let ty = object_ty.as_user_defined().unwrap();
        match (self.ty_layouts[object_ty].0, object_variant, ty) {
            (TyLayout::Single(layout), None, UserDefinedType::Product(fields)) => {
                (layout, &fields[field])
            }
            (TyLayout::Sum { layouts, .. }, Some(variant), UserDefinedType::Sum(variants)) => {
                (layouts[variant], &variants[variant][field])
            }
            _ => unreachable!(),
        }
    }

    fn expr_get(&mut self, expr: &ExprGet) -> Result<Value> {
        let object = self.expr(&expr.object)?;
        let (layout, field_ty) =
            self.field_information(&expr.object_ty, expr.object_variant, expr.field);
        Ok(get(
            self.builder,
            self.triple,
            object,
            expr.field,
            &layout,
            field_ty,
        ))
    }

    fn expr_set(&mut self, expr: &ExprSet) -> Result<Value> {
        let object = self.expr(&expr.object)?;
        let layout = self
            .field_information(&expr.object_ty, expr.object_variant, expr.field)
            .0;
        let value = self.expr(&expr.value)?;
        self.builder.ins().store(
            MemFlags::new()
                .with_aligned()
                .with_alias_region(Some(AliasRegion::Heap))
                .with_notrap(),
            value,
            object,
            layout.field_locations[expr.field] as i32,
        );
        Ok(value)
    }

    fn callable(&mut self, callee: &Expr) -> Result<Callable> {
        match callee {
            Expr::Function(expr) => Ok(Callable::Static(expr.function)),
            _ => Ok(Callable::Dynamic(self.expr(callee)?)),
        }
    }

    fn expr_call(&mut self, expr: &ExprCall) -> Result<Value> {
        let callable = self.callable(&expr.callee)?;

        let positional: Vec<_> = expr.positional.iter().map(|e| self.expr(e)).collect();
        let args: Result<Vec<_>> = iter::once(Ok(Value::reserved_value()))
            .chain(positional)
            // we need to execute the exprs *then* sort
            .chain(
                expr.named
                    .iter()
                    .map(|(i, e)| (*i, self.expr(e)))
                    .sorted_by_key(|x| x.0)
                    .map(|x| x.1),
            )
            .collect();
        let mut args = args?;

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

                let function_ptr = fat_ptr_meta(callee, self.builder, self.triple);

                args[0] = fat_ptr_addr(callee, self.builder, self.triple);

                self.builder
                    .ins()
                    .return_call_indirect(sig_ref, function_ptr, &args);
            }
        }

        Err(ExprError::NoValue)
    }

    fn application_function(
        &mut self,
        ty: &FunctionTy,
        storage_ty: &MirType,
        callee_ty: &MirType,
        positional: usize,
        named: impl IntoIterator<Item = Ident>,
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
        let callee = get(&mut builder, self.triple, storage, 0, &layout, field_ty);

        let params = ty
            .positional_params
            .iter()
            .map(|_| None)
            .chain(ty.named_params.keys().map(|ident| Some(*ident)))
            .sorted()
            .collect_vec();
        let mut args = builder
            .block_params(block)
            .iter()
            .skip(1)
            .enumerate()
            .map(|(i, value)| (*value, params[i]))
            .collect_vec();
        args.extend(
            iter::repeat_n(None, positional)
                .chain(named.into_iter().map(Some))
                .enumerate()
                .map(|(field, ident)| {
                    let (layout, field_ty) = self.field_information(storage_ty, None, field + 1);
                    (
                        get(
                            &mut builder,
                            self.triple,
                            storage,
                            field + 1,
                            &layout,
                            field_ty,
                        ),
                        ident,
                    )
                }),
        );
        args.sort_by_key(|(_, ident)| *ident);
        let args = iter::once(fat_ptr_addr(callee, &mut builder, self.triple))
            .chain(args.into_iter().map(|(value, _)| value))
            .collect_vec();

        let signature = signature_from_function_ty(callee_ty.as_function().unwrap(), self.triple);
        let sig_ref = builder.import_signature(signature);

        let callee = fat_ptr_meta(callee, &mut builder, self.triple);
        builder.ins().return_call_indirect(sig_ref, callee, &args);

        let mut context = self.contexts.get();
        context.clear();
        context.want_disasm = cfg!(debug_assertions);
        context.func = function;
        self.module.define_function(func_id, &mut context).unwrap();
        func_id
    }

    fn expr_application(&mut self, expr: &ExprApplication) -> Result<Value> {
        let func_id = self.application_function(
            expr.result_ty.as_function().unwrap(),
            &expr.storage_ty,
            &expr.callee_ty,
            expr.positional.len(),
            expr.named.iter().map(|(ident, _)| *ident).sorted_unstable(),
        );
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);

        self.closure(
            func_ref,
            iter::once(&*expr.callee)
                .chain(&expr.positional)
                .chain(expr.named.iter().map(|(_, expr)| expr)),
            &expr.storage_ty,
        )
    }

    fn expr_unary(&mut self, expr: &ExprUnary) -> Result<Value> {
        let operand = self.expr(&expr.operand)?;
        let operand_ty = ty_for(&expr.operand_ty, self.triple);
        match expr.operator {
            UnaryOp::Neg if operand_ty == types::F64 => Ok(self.builder.ins().ineg(operand)),
            UnaryOp::Neg if operand_ty == types::I64 => Ok(self.builder.ins().fneg(operand)),
            UnaryOp::Not if operand_ty == types::I8 => Ok(self.builder.ins().bxor_imm(operand, 1)),
            UnaryOp::Neg | UnaryOp::Not => unreachable!(),
        }
    }

    #[expect(clippy::cognitive_complexity, reason = "this is abstracted by macros")]
    fn expr_binary(&mut self, expr: &ExprBinary) -> Result<Value> {
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
        Ok(value)
    }

    fn expr_assign(&mut self, expr: &ExprAssign) -> Result<Value> {
        let (_, initialised) = self.vars.get_mut(&expr.ident).unwrap();
        *initialised = true;

        let value = self.expr(&expr.expr)?;
        let var = self.variables[&expr.ident];
        self.builder.def_var(var, value);

        Ok(value)
    }

    fn expr_switch(&mut self, expr: &ExprSwitch) -> Result<Value> {
        let scrutinee = self.expr(&expr.scrutinee)?;
        let mut switch = Switch::new();
        for (&val, block_id) in &expr.arms {
            switch.set_entry(val as u128, self.block_map[block_id]);
        }
        switch.emit(self.builder, scrutinee, self.block_map[&expr.otherwise]);
        Err(ExprError::NoValue)
    }

    fn expr_goto(&mut self, expr: &ExprGoto) -> Result<Value> {
        self.builder.switch_to_block(self.block_map[&expr.block]);
        Err(ExprError::NoValue)
    }

    fn expr_closure(&mut self, expr: &ExprClosure) -> Result<Value> {
        let captures: Vec<_> = expr
            .captures
            .iter()
            .copied()
            .sorted_unstable()
            .map(|ident| Expr::Ident(ExprIdent { ident }))
            .collect();
        let func_id = self.functions[&expr.func_ref].0;
        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);
        self.closure(func_ref, &captures, &expr.storage_ty)
    }

    fn expr_intrinsic(&mut self, expr: &ExprIntrinsic) -> Result<Value> {
        let values: Result<Vec<_>> = expr
            .values
            .iter()
            .map(|(expr, ty)| Ok((self.expr(expr)?, &**ty)))
            .collect();
        let values = values?;
        match expr.intrinsic {
            Intrinsic::Discriminant => {
                let (value, ty) = values[0];
                if *ty == MirType::Bool {
                    Ok(self.builder.ins().sextend(types::I64, value))
                } else if matches!(ty, MirType::UserDefined(UserDefinedType::Sum(_))) {
                    Ok(self.builder.ins().load(
                        ptr_ty(self.triple),
                        MemFlags::new()
                            .with_aligned()
                            .with_alias_region(Some(AliasRegion::Heap))
                            .with_notrap(),
                        value,
                        -(ptr_ty(self.triple).bytes() as i32),
                    ))
                } else {
                    Ok(self.builder.ins().iconst(ptr_ty(self.triple), 0))
                }
            }
            Intrinsic::Terminate => {
                self.builder.ins().return_(&[values[0].0]);
                Err(ExprError::NoValue)
            }
            Intrinsic::Unreachable => {
                self.builder.ins().trap(TrapCode::unwrap_user(1));
                Err(ExprError::NoValue)
            }
        }
    }

    fn expr(&mut self, expr: &Expr) -> Result<Value> {
        match expr {
            Expr::Literal(expr) => self.expr_literal(expr),
            Expr::Ident(expr) => {
                let var = self.variables[&expr.ident];
                Ok(self.builder.use_var(var))
            }
            Expr::Function(expr) => Ok(self.expr_function(expr)),
            Expr::Tuple(expr) => self.expr_tuple(expr),
            Expr::Constructor(expr) => self.expr_constructor(expr),
            Expr::Array(expr) => self.expr_array(expr),
            Expr::Get(expr) => self.expr_get(expr),
            Expr::Set(expr) => self.expr_set(expr),
            Expr::Call(expr) => self.expr_call(expr),
            Expr::Application(expr) => self.expr_application(expr),
            Expr::Unary(expr) => self.expr_unary(expr),
            Expr::Binary(expr) => self.expr_binary(expr),
            Expr::Assign(expr) => self.expr_assign(expr),
            Expr::Switch(expr) => self.expr_switch(expr),
            Expr::Goto(expr) => self.expr_goto(expr),
            Expr::Closure(expr) => self.expr_closure(expr),
            Expr::Intrinsic(expr) => self.expr_intrinsic(expr),
        }
    }

    /// This method does not finalise or verify the function, or define it in the module.
    pub(super) fn compile(mut self) -> ModuleResult<()> {
        for (param, param_ty) in self.params {
            let var = self.builder.declare_var(ty_for(param_ty, self.triple));
            if is_ptr(param_ty) {
                self.builder.declare_var_needs_stack_map(var);
            }
            self.variables.insert(*param, var);
            self.vars.insert(*param, (param_ty, true));
        }

        let entry_point = self.block_map[&MirFunction::entry_point()];
        self.builder
            .append_block_params_for_function_params(entry_point);
        self.builder.switch_to_block(entry_point);
        for (i, &(param, _)) in self.params.iter().enumerate() {
            let param_value = self.builder.block_params(entry_point)[i + 1];
            let var = self.variables[&param];
            self.builder.def_var(var, param_value);
        }

        for (&ident, (var_ty, initialiser)) in &self.mir_function.declarations {
            let var = self.builder.declare_var(ty_for(var_ty, self.triple));
            self.variables.insert(ident, var);
            if is_ptr(var_ty) {
                self.builder.declare_var_needs_stack_map(var);
            }

            if let Some(initialiser) = initialiser {
                let value = self.literal(initialiser)?;

                self.builder.def_var(var, value);
            }

            self.vars.insert(ident, (var_ty, initialiser.is_some()));
        }

        if let Some(captures) = &self.mir_function.captures {
            let storage = self.builder.block_params(entry_point)[0];
            for (i, &ident) in captures.captures.iter().enumerate() {
                let (layout, field_ty) = self.field_information(&captures.storage_ty, None, i);
                let value = get(self.builder, self.triple, storage, i, &layout, field_ty);
                let var = self.variables[&ident];
                self.builder.def_var(var, value);
            }
        }

        for (&block_id, block) in &self.mir_function.blocks {
            self.builder.switch_to_block(self.block_map[&block_id]);

            for expr in &block.exprs {
                if let Err(ExprError::Module(e)) = self.expr(expr) {
                    return Err(e);
                }
            }
        }

        Ok(())
    }
}
