use crate::common::BinaryOp;
use crate::common::Ident;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::common::UnaryOp;
use crate::high_level_ir::Block as HirBlock;
use crate::high_level_ir::Expr as HirExpr;
use crate::high_level_ir::Function as HirFunction;
use crate::high_level_ir::FunctionTy as HirFunctionTy;
use crate::high_level_ir::Program as HirProgram;
use crate::high_level_ir::Type as HirType;
use crate::high_level_ir::TypeConstructor as HirTypeConstructor;
use crate::high_level_ir::UserDefinedType as HirUserDefinedType;
use crate::low_level_ir::Block;
use crate::low_level_ir::Expr;
use crate::low_level_ir::Function;
use crate::low_level_ir::Program;
use crate::low_level_ir::Type;
use crate::low_level_ir::TypeConstructor;
use crate::low_level_ir::UserDefinedType;

use std::collections::HashMap;

use continuate_arena::Arena;

use continuate_error::Result;

fn user_defined_ty(ty: &HirUserDefinedType) -> UserDefinedType {
    let constructor = match &ty.constructor {
        HirTypeConstructor::Product(fields) => TypeConstructor::Product(fields.clone()),
        HirTypeConstructor::Sum(variants) => TypeConstructor::Sum(variants.clone()),
    };
    UserDefinedType { constructor }
}

fn lower_ty(ty: &HirType) -> Type {
    match *ty {
        HirType::Int => Type::Int,
        HirType::Float => Type::Float,
        HirType::String => Type::String,
        HirType::Array(ty, len) => Type::Array(ty, len),
        HirType::Tuple(ref types) => Type::Tuple(types.clone()),
        HirType::Function(HirFunctionTy {
            ref params,
            ref continuations,
        }) => Type::function(params.clone(), continuations.clone()),
        HirType::UserDefined(ref ty) => Type::UserDefined(user_defined_ty(ty)),
    }
}

struct ExprGet<'arena> {
    object: Expr<'arena>,
    object_variant: Option<usize>,
    field: usize,
}

struct Lowerer<'arena> {
    arena: &'arena Arena<'arena>,
    program: Program<'arena>,
    environment: HashMap<Ident, TypeRef>,
    ty_bool: TypeRef,
}

impl<'arena> Lowerer<'arena> {
    fn expr_list(
        &mut self,
        exprs: &[&HirExpr],
        function: &mut Function<'arena>,
    ) -> Result<Vec<(Expr<'arena>, TypeRef)>> {
        exprs.iter().map(|expr| self.expr(expr, function)).collect()
    }

    fn expr_block(
        &mut self,
        exprs: &[&HirExpr],
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let exprs = self.expr_list(exprs, function)?;
        let block_ty = exprs.last().map_or_else(
            || self.program.insert_type(Type::Tuple(vec![]), self.arena).0,
            |(_, ty)| *ty,
        );
        Ok((
            Expr::Block(
                exprs
                    .into_iter()
                    .map(|(expr, _)| &*self.arena.allocate(expr))
                    .collect(),
            ),
            block_ty,
        ))
    }

    fn expr_tuple(
        &mut self,
        elements: &[&HirExpr],
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let elements = self.expr_list(elements, function)?;
        let types = elements.iter().map(|(_, ty)| *ty).collect();
        let values = elements
            .into_iter()
            .map(|(expr, _)| &*self.arena.allocate(expr))
            .collect();
        let expr = Expr::Tuple(values);
        let ty = Type::Tuple(types);
        let ty = self.program.insert_type(ty, self.arena).0;
        Ok((expr, ty))
    }

    fn expr_constructor(
        &mut self,
        ty: TypeRef,
        index: Option<usize>,
        fields: &[&HirExpr],
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let fields = self.expr_list(fields, function)?;
        let user_defined = *self.program.types.get_by_left(&ty).unwrap();
        let user_defined = user_defined
            .as_user_defined()
            .ok_or(format!("cannot construct {user_defined:?}"))?;
        let ty_fields = match (&user_defined.constructor, index) {
            (TypeConstructor::Product(ty_fields), None) => ty_fields,
            (TypeConstructor::Sum(variants), Some(index)) => &variants[index],
            _ => unreachable!(),
        };

        if fields.len() != ty_fields.len() {
            Err("incorrect number of fields")?;
        }

        for ((_, given_field_ty), field_ty) in fields.iter().zip(ty_fields) {
            let given_field_ty = *self.program.types.get_by_left(given_field_ty).unwrap();
            let field_ty = *self.program.types.get_by_left(field_ty).unwrap();
            given_field_ty.unify(field_ty, &mut self.program, self.arena)?;
        }

        let fields = fields
            .into_iter()
            .map(|(expr, _)| &*self.arena.allocate(expr))
            .collect();
        let expr = Expr::Constructor { ty, index, fields };
        Ok((expr, ty))
    }

    fn expr_array(
        &mut self,
        array: &[&HirExpr],
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let array = self.expr_list(array, function)?;
        let mut array_ty = self.program.insert_type(Type::Unknown, self.arena).1;
        for (_, ty) in &array {
            let ty = *self.program.types.get_by_left(ty).unwrap();
            array_ty = array_ty.unify(ty, &mut self.program, self.arena)?;
        }
        let array_ty = *self.program.types.get_by_right(array_ty).unwrap();
        let array = array
            .into_iter()
            .map(|(expr, _)| &*self.arena.allocate(expr))
            .collect();
        Ok((Expr::Array(array), array_ty))
    }

    fn expr_get(
        &mut self,
        object: &HirExpr,
        object_variant: Option<usize>,
        field: usize,
        function: &mut Function<'arena>,
    ) -> Result<(ExprGet<'arena>, TypeRef)> {
        let (object, object_ty) = self.expr(object, function)?;
        let user_defined = *self.program.types.get_by_left(&object_ty).unwrap();
        let user_defined = user_defined
            .as_user_defined()
            .ok_or(format!("cannot access field of {user_defined:?}"))?;
        let field_ty = match (&user_defined.constructor, object_variant) {
            (TypeConstructor::Product(ty_fields), None) => ty_fields[field],
            (TypeConstructor::Sum(variants), Some(index)) => variants[index][field],
            _ => unreachable!(),
        };
        let expr = ExprGet {
            object,
            object_variant,
            field,
        };
        Ok((expr, field_ty))
    }

    fn expr_set(
        &mut self,
        object: &HirExpr,
        object_variant: Option<usize>,
        field: usize,
        value: &HirExpr,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (expr, field_ty) = self.expr_get(object, object_variant, field, function)?;
        let ExprGet {
            object,
            object_variant,
            field,
        } = expr;

        let (value, value_ty) = self.expr(value, function)?;

        let field_ty = *self.program.types.get_by_left(&field_ty).unwrap();
        let value_ty = *self.program.types.get_by_left(&value_ty).unwrap();
        let ty = field_ty.unify(value_ty, &mut self.program, self.arena)?;
        let ty_ref = *self.program.types.get_by_right(ty).unwrap();
        let expr = Expr::Set {
            object: self.arena.allocate(object),
            object_variant,
            field,
            value: self.arena.allocate(value),
        };
        Ok((expr, ty_ref))
    }

    fn expr_call(
        &mut self,
        callee: &HirExpr,
        params: &[&HirExpr],
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (callee, callee_ty) = self.expr(callee, function)?;
        let params = self.expr_list(params, function)?;
        let callee_ty = *self.program.types.get_by_left(&callee_ty).unwrap();
        let callee_ty = callee_ty
            .as_function()
            .ok_or(format!("cannot call {callee_ty:?}"))?;

        if !callee_ty.continuations.is_empty() {
            Err("cannot call function with outstanding continuations")?;
        }

        if callee_ty.params.len() != params.len() {
            Err("incorrect number of parameters")?;
        }

        for (formal, (_, actual)) in callee_ty.params.iter().zip(params.iter()) {
            let formal = *self.program.types.get_by_left(formal).unwrap();
            let actual = *self.program.types.get_by_left(actual).unwrap();
            formal.unify(actual, &mut self.program, self.arena)?;
        }

        let params = params
            .into_iter()
            .map(|(expr, _)| &*self.arena.allocate(expr))
            .collect();
        let expr = Expr::Call(self.arena.allocate(callee), params);
        let (ty, _) = self.program.insert_type(Type::None, self.arena);
        Ok((expr, ty))
    }

    fn expr_cont_application(
        &mut self,
        callee: &HirExpr,
        continuations: &HashMap<Ident, &HirExpr>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (callee, callee_ty) = self.expr(callee, function)?;
        let callee_ty = *self.program.types.get_by_left(&callee_ty).unwrap();
        let callee_ty = callee_ty
            .as_function()
            .ok_or(format!("cannot apply continuations to {callee_ty:?}"))?;

        let mut outstanding_continuations = callee_ty.continuations.clone();
        let mut new_continuations = HashMap::with_capacity(continuations.len());
        for (&ident, &expr) in continuations {
            let (expr, ty) = self.expr(expr, function)?;
            let expr = &*self.arena.allocate(expr);

            let cont_ty = callee_ty
                .continuations
                .get(&ident)
                .ok_or("unexpected continuation")?;
            let cont_ty = *self.program.types.get_by_left(cont_ty).unwrap();
            self.program.types.get_by_left(&ty).unwrap().unify(
                cont_ty,
                &mut self.program,
                self.arena,
            )?;

            outstanding_continuations.remove(&ident);
            new_continuations.insert(ident, expr);
        }

        let expr = Expr::ContApplication(self.arena.allocate(callee), new_continuations);
        let ty = Type::function(callee_ty.params.clone(), outstanding_continuations);
        let (ty, _) = self.program.insert_type(ty, self.arena);

        Ok((expr, ty))
    }

    fn expr_unary(
        &mut self,
        operator: UnaryOp,
        operand: &HirExpr,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (operand, input_ty_ref) = self.expr(operand, function)?;
        let input_ty = *self.program.types.get_by_left(&input_ty_ref).unwrap();
        let output_ty = match (operator, input_ty) {
            (UnaryOp::Neg, Type::Int | Type::Float) => input_ty_ref,
            _ => Err(format!("cannot apply {operator:?} to {input_ty:?}"))?,
        };
        let expr = Expr::Unary(operator, self.arena.allocate(operand));
        Ok((expr, output_ty))
    }

    fn expr_binary(
        &mut self,
        left: &HirExpr,
        operator: BinaryOp,
        right: &HirExpr,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (left, left_ty_ref) = self.expr(left, function)?;
        let left_ty = *self.program.types.get_by_left(&left_ty_ref).unwrap();
        let (right, right_ty_ref) = self.expr(right, function)?;
        let right_ty = *self.program.types.get_by_left(&right_ty_ref).unwrap();

        let output_ty = match (left_ty, operator, right_ty) {
            (
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Add,
                r @ (Type::Int | Type::Float | Type::String),
            )
            | (
                l @ (Type::Int | Type::Float),
                BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem,
                r @ (Type::Int | Type::Float),
            ) if l == r => left_ty_ref,
            (
                l @ (Type::Int | Type::Float),
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
                r @ (Type::Int | Type::Float),
            ) if l == r => self.ty_bool,
            (l, BinaryOp::Eq | BinaryOp::Ne, r) if l == r => self.ty_bool,
            _ => Err(format!(
                "cannot apply {operator:?} to {left_ty:?} and {right_ty:?}"
            ))?,
        };

        let expr = Expr::Binary(
            self.arena.allocate(left),
            operator,
            self.arena.allocate(right),
        );
        Ok((expr, output_ty))
    }

    fn expr_declare(
        &mut self,
        ident: Ident,
        ty: TypeRef,
        expr: &HirExpr,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (expr, expr_ty) = self.expr(expr, function)?;
        let expr_ty = *self.program.types.get_by_left(&expr_ty).unwrap();
        let slot_ty = *self.program.types.get_by_left(&ty).unwrap();
        let ty = expr_ty.unify(slot_ty, &mut self.program, self.arena)?;
        let ty = *self.program.types.get_by_right(ty).unwrap();

        function.declarations.insert(ident, (ty, None));
        let expr = Expr::Assign {
            ident,
            expr: self.arena.allocate(expr),
        };
        Ok((expr, ty))
    }

    fn expr_assign(
        &mut self,
        ident: Ident,
        expr: &HirExpr,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (expr, expr_ty) = self.expr(expr, function)?;
        let expr_ty = *self.program.types.get_by_left(&expr_ty).unwrap();
        let slot_ty = self.environment[&ident];
        let slot_ty = *self.program.types.get_by_left(&slot_ty).unwrap();
        let ty = expr_ty.unify(slot_ty, &mut self.program, self.arena)?;
        let ty = *self.program.types.get_by_right(ty).unwrap();

        function.declarations.insert(ident, (ty, None));
        let expr = Expr::Assign {
            ident,
            expr: self.arena.allocate(expr),
        };
        Ok((expr, ty))
    }

    fn expr(
        &mut self,
        expr: &HirExpr,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        match *expr {
            HirExpr::Literal(ref lit) => {
                let ty = match lit {
                    Literal::Int(_) => Type::Int,
                    Literal::Float(_) => Type::Float,
                    Literal::String(_) => Type::String,
                };
                Ok((
                    Expr::Literal(lit.clone()),
                    self.program.insert_type(ty, self.arena).0,
                ))
            }
            HirExpr::Ident(ident) => Ok((Expr::Ident(ident), self.environment[&ident])),
            HirExpr::Function(func_ref) => {
                Ok((Expr::Function(func_ref), self.program.signatures[&func_ref]))
            }
            HirExpr::Block(ref exprs) => self.expr_block(exprs, function),
            HirExpr::Tuple(ref elements) => self.expr_tuple(elements, function),
            HirExpr::Constructor {
                ty,
                index,
                ref fields,
            } => self.expr_constructor(ty, index, fields, function),
            HirExpr::Array(ref array) => self.expr_array(array, function),
            HirExpr::Get {
                object,
                object_variant,
                field,
            } => {
                let (expr, ty) = self.expr_get(object, object_variant, field, function)?;
                Ok((
                    Expr::Get {
                        object: self.arena.allocate(expr.object),
                        object_variant: expr.object_variant,
                        field: expr.field,
                    },
                    ty,
                ))
            }
            HirExpr::Set {
                object,
                object_variant,
                field,
                value,
            } => self.expr_set(object, object_variant, field, value, function),
            HirExpr::Call(callee, ref params) => self.expr_call(callee, params, function),
            HirExpr::ContApplication(callee, ref continuations) => {
                self.expr_cont_application(callee, continuations, function)
            }
            HirExpr::Unary(operator, operand) => self.expr_unary(operator, operand, function),
            HirExpr::Binary(left, operator, right) => {
                self.expr_binary(left, operator, right, function)
            }
            HirExpr::Declare { ident, ty, expr } => self.expr_declare(ident, ty, expr, function),
            HirExpr::Assign { ident, expr } => self.expr_assign(ident, expr, function),
            HirExpr::Goto(block_id) => Ok((
                Expr::Goto(block_id),
                self.program.insert_type(Type::None, self.arena).0,
            )),
            HirExpr::Unreachable => Ok((
                Expr::Unreachable,
                self.program.insert_type(Type::None, self.arena).0,
            )),
            ref expr => todo!("{expr:#?}"),
        }
    }

    fn block(
        &mut self,
        block: &HirBlock,
        function: &mut Function<'arena>,
    ) -> Result<Block<'arena>> {
        let (expr, _) = self.expr(block.expr, function)?;
        Ok(Block {
            expr: self.arena.allocate(expr),
        })
    }

    fn function(
        &mut self,
        function: &HirFunction,
        environment: &HashMap<Ident, TypeRef>,
    ) -> Result<Function<'arena>> {
        let mut lir_function = Function::new();
        lir_function.params.clone_from(&function.params);
        lir_function
            .continuations
            .clone_from(&function.continuations);

        lir_function.next_block = function.next_block;

        self.environment.clone_from(environment);
        for (&param, &ty) in lir_function
            .params
            .iter()
            .map(|(param, ty)| (param, ty))
            .chain(&lir_function.continuations)
        {
            self.environment.insert(param, ty);
        }

        if let Some(intrinsic) = function.intrinsic {
            lir_function.intrinsic = Some(intrinsic);
            return Ok(lir_function);
        }

        for (&block_id, block) in &function.blocks {
            let block = self.block(block, &mut lir_function)?;
            lir_function.blocks.insert(block_id, block);
        }

        Ok(lir_function)
    }

    fn lower(arena: &'arena Arena<'arena>, program: &HirProgram) -> Result<Program<'arena>> {
        let mut lowerer = Lowerer {
            arena,
            program: Program::new(program, arena),
            environment: HashMap::new(),
            ty_bool: program.lib_std().ty_bool,
        };

        for (&type_ref, &ty) in &program.types {
            let ty = lowerer.arena.allocate(lower_ty(ty));
            lowerer.program.types.insert(type_ref, ty);
        }

        lowerer.program.signatures.clone_from(&program.signatures);

        for (&func_ref, &function) in &program.functions {
            if !function.captures.is_empty() {
                continue;
            }
            let function = lowerer
                .arena
                .allocate(lowerer.function(function, &HashMap::new())?);
            lowerer.program.functions.insert(func_ref, function);
        }

        Ok(lowerer.program)
    }
}

/// ## Errors
///
/// Returns an error if there is a type error in the program.
pub fn lower<'arena>(
    program: &HirProgram,
    arena: &'arena Arena<'arena>,
) -> Result<Program<'arena>> {
    Lowerer::lower(arena, program)
}
