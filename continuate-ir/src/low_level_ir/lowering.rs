use crate::common::BinaryOp;
use crate::common::Ident;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::common::UnaryOp;
use crate::high_level_ir::Expr as HirExpr;
use crate::high_level_ir::Function as HirFunction;
use crate::high_level_ir::FunctionTy as HirFunctionTy;
use crate::high_level_ir::Pattern;
use crate::high_level_ir::Program as HirProgram;
use crate::high_level_ir::Type as HirType;
use crate::high_level_ir::TypeConstructor as HirTypeConstructor;
use crate::high_level_ir::UserDefinedType as HirUserDefinedType;
use crate::low_level_ir::Block;
use crate::low_level_ir::BlockId;
use crate::low_level_ir::Expr;
use crate::low_level_ir::Function;
use crate::low_level_ir::Program;
use crate::low_level_ir::Type;
use crate::low_level_ir::TypeConstructor;
use crate::low_level_ir::UserDefinedType;

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::mem;

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

enum ArmData<'arena> {
    Variant {
        ty: &'arena Type,
        variant: usize,
        exhaustive: bool,
        block: BlockId,
    },
    Otherwise,
    None,
}

struct Lowerer<'arena> {
    arena: &'arena Arena<'arena>,
    program: Program<'arena>,
    environment: HashMap<Ident, TypeRef>,
    ty_bool: TypeRef,
    current_block: BlockId,
}

impl<'arena> Lowerer<'arena> {
    fn expr_list(
        &mut self,
        exprs: &[&HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<Vec<(Expr<'arena>, TypeRef)>> {
        exprs
            .iter()
            .map(|expr| self.expr(expr, block, function))
            .collect()
    }

    fn expr_block(
        &mut self,
        exprs: &[&HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let mut exprs: Vec<_> = self.expr_list(exprs, block, function)?;
        let (last_expr, block_ty) = exprs.pop().unwrap_or_else(|| {
            let ty = self.program.insert_type(Type::Tuple(vec![]), self.arena).0;
            (Expr::Tuple(vec![]), ty)
        });
        let exprs = exprs.into_iter().map(|(expr, _)| self.arena.allocate(expr));
        for expr in exprs {
            block.exprs.push(expr);
        }
        Ok((last_expr, block_ty))
    }

    fn expr_tuple(
        &mut self,
        elements: &[&HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let elements = self.expr_list(elements, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let fields = self.expr_list(fields, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let array = self.expr_list(array, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(ExprGet<'arena>, TypeRef)> {
        let (object, object_ty) = self.expr(object, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (expr, field_ty) = self.expr_get(object, object_variant, field, block, function)?;
        let ExprGet {
            object,
            object_variant,
            field,
        } = expr;

        let (value, value_ty) = self.expr(value, block, function)?;

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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (callee, callee_ty) = self.expr(callee, block, function)?;
        let params = self.expr_list(params, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (callee, callee_ty) = self.expr(callee, block, function)?;
        let callee_ty = *self.program.types.get_by_left(&callee_ty).unwrap();
        let callee_ty = callee_ty
            .as_function()
            .ok_or(format!("cannot apply continuations to {callee_ty:?}"))?;

        let mut outstanding_continuations = callee_ty.continuations.clone();
        let mut new_continuations = HashMap::with_capacity(continuations.len());
        for (&ident, &expr) in continuations {
            let (expr, ty) = self.expr(expr, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (operand, input_ty_ref) = self.expr(operand, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (left, left_ty_ref) = self.expr(left, block, function)?;
        let left_ty = *self.program.types.get_by_left(&left_ty_ref).unwrap();
        let (right, right_ty_ref) = self.expr(right, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (expr, expr_ty) = self.expr(expr, block, function)?;
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
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (expr, expr_ty) = self.expr(expr, block, function)?;
        let expr_ty = *self.program.types.get_by_left(&expr_ty).unwrap();
        let slot_ty = self.environment[&ident];
        let slot_ty = *self.program.types.get_by_left(&slot_ty).unwrap();
        let ty = expr_ty.unify(slot_ty, &mut self.program, self.arena)?;
        let ty = *self.program.types.get_by_right(ty).unwrap();

        let expr = Expr::Assign {
            ident,
            expr: self.arena.allocate(expr),
        };
        Ok((expr, ty))
    }

    fn match_arm(
        &mut self,
        scrutinee: (&'arena Expr<'arena>, TypeRef),
        arm_pat: &Pattern,
        arm: &HirExpr,
        otherwise: BlockId,
        next_id: BlockId,
        function: &mut Function<'arena>,
    ) -> Result<ArmData<'arena>> {
        let mut arm_block = Block::new();
        let mut arm_block_id = function.block();
        let (scrutinee, scrutinee_ty_ref) = scrutinee;

        let arm_data = match *arm_pat {
            Pattern::Wildcard => {
                arm_block_id = otherwise;
                ArmData::Otherwise
            }
            Pattern::Ident(ident) => {
                let binding = Expr::Assign {
                    ident,
                    expr: scrutinee,
                };
                function
                    .declarations
                    .insert(ident, (scrutinee_ty_ref, None));
                arm_block.exprs.push(self.arena.allocate(binding));
                arm_block_id = otherwise;
                ArmData::Otherwise
            }
            Pattern::Destructure {
                ty,
                variant,
                ref fields,
            } => {
                let ty = *self.program.types.get_by_left(&ty).unwrap();
                for (field, ident) in fields
                    .iter()
                    .enumerate()
                    .filter_map(|(field, pattern)| Some((field, pattern.as_ident()?)))
                {
                    let field_ty = ty.field(variant, field).unwrap();
                    let get = Expr::Get {
                        object: scrutinee,
                        object_variant: variant,
                        field,
                    };
                    let binding = Expr::Assign {
                        ident,
                        expr: self.arena.allocate(get),
                    };
                    function.declarations.insert(ident, (field_ty, None));
                    arm_block.exprs.push(self.arena.allocate(binding));
                }
                // TODO: Handle sub-destructures.
                if let Some(variant) = variant {
                    ArmData::Variant {
                        ty,
                        variant,
                        exhaustive: true,
                        block: arm_block_id,
                    }
                } else {
                    ArmData::None
                }
            }
        };
        let (arm, arm_ty) = self.expr(arm, &mut arm_block, function)?;
        arm_block.exprs.push(self.arena.allocate(arm));
        let goto = Expr::Goto(next_id);
        arm_block.exprs.push(self.arena.allocate(goto));

        let arm_ty = *self.program.types.get_by_left(&arm_ty).unwrap();
        arm_ty.unify(
            self.program.insert_type(Type::None, self.arena).1,
            &mut self.program,
            self.arena,
        )?;

        function.blocks.insert(arm_block_id, arm_block);

        Ok(arm_data)
    }

    fn expr_match(
        &mut self,
        scrutinee: &HirExpr,
        arms: &[(Pattern, &HirExpr)],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (scrutinee, scrutinee_ty_ref) = self.expr(scrutinee, block, function)?;
        let scrutinee = self.arena.allocate(scrutinee);
        let mut scrutinee_ty = *self.program.types.get_by_left(&scrutinee_ty_ref).unwrap();

        let mut discriminants = Vec::new();
        let otherwise = function.block();
        let mut has_wildcard = false;

        let next_id = function.block();

        for (arm_pat, arm) in arms {
            let arm_data = self.match_arm(
                (scrutinee, scrutinee_ty_ref),
                arm_pat,
                arm,
                otherwise,
                next_id,
                function,
            )?;
            match arm_data {
                ArmData::Otherwise => {
                    has_wildcard = true;
                    break;
                }
                ArmData::Variant {
                    ty,
                    variant,
                    exhaustive,
                    block,
                } => {
                    scrutinee_ty = scrutinee_ty.unify(ty, &mut self.program, self.arena)?;
                    discriminants.push((variant, exhaustive, block));
                }
                ArmData::None => {}
            }
        }

        if let Some(variants) = scrutinee_ty.variants() {
            let mut exhaustive = true;
            let mut last = false;
            for &(discriminant, variant_exhaustive, _) in &discriminants {
                if discriminant == variants {
                    last = true;
                }
                exhaustive &= variant_exhaustive;
            }
            if !(exhaustive && last || has_wildcard) {
                Err("non-exhaustive match")?;
            }
        }

        let current_block = mem::replace(block, Block::new());
        function.blocks.insert(self.current_block, current_block);
        self.current_block = next_id;

        let scrutinee = if discriminants.is_empty() {
            &*scrutinee
        } else {
            let discriminant = Expr::Function(self.program.lib_std.fn_discriminant);
            self.arena.allocate(Expr::Call(
                self.arena.allocate(discriminant),
                vec![scrutinee],
            ))
        };

        if let Entry::Vacant(entry) = function.blocks.entry(otherwise) {
            let mut otherwise_block = Block::new();
            otherwise_block
                .exprs
                .push(self.arena.allocate(Expr::Unreachable));
            entry.insert(otherwise_block);
        }
        let expr = Expr::Switch {
            scrutinee,
            arms: discriminants
                .iter()
                .map(|&(variant, _, block)| (variant as i64, block))
                .collect(),
            otherwise,
        };

        Ok((expr, self.program.insert_type(Type::None, self.arena).0))
    }

    fn expr(
        &mut self,
        expr: &HirExpr,
        block: &mut Block<'arena>,
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
            HirExpr::Block(ref exprs) => self.expr_block(exprs, block, function),
            HirExpr::Tuple(ref elements) => self.expr_tuple(elements, block, function),
            HirExpr::Constructor {
                ty,
                index,
                ref fields,
            } => self.expr_constructor(ty, index, fields, block, function),
            HirExpr::Array(ref array) => self.expr_array(array, block, function),
            HirExpr::Get {
                object,
                object_variant,
                field,
            } => {
                let (expr, ty) = self.expr_get(object, object_variant, field, block, function)?;
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
            } => self.expr_set(object, object_variant, field, value, block, function),
            HirExpr::Call(callee, ref params) => self.expr_call(callee, params, block, function),
            HirExpr::ContApplication(callee, ref continuations) => {
                self.expr_cont_application(callee, continuations, block, function)
            }
            HirExpr::Unary(operator, operand) => {
                self.expr_unary(operator, operand, block, function)
            }
            HirExpr::Binary(left, operator, right) => {
                self.expr_binary(left, operator, right, block, function)
            }
            HirExpr::Declare { ident, ty, expr } => {
                self.expr_declare(ident, ty, expr, block, function)
            }
            HirExpr::Assign { ident, expr } => self.expr_assign(ident, expr, block, function),
            HirExpr::Match {
                scrutinee,
                ref arms,
            } => self.expr_match(scrutinee, arms, block, function),
            HirExpr::Unreachable => Ok((
                Expr::Unreachable,
                self.program.insert_type(Type::None, self.arena).0,
            )),
            ref expr => todo!("{expr:#?}"),
        }
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

        self.current_block = Function::entry_point();

        let mut block = Block::new();
        let (body, body_ty) = self.expr_block(&function.body, &mut block, &mut lir_function)?;
        block.exprs.push(self.arena.allocate(body));
        lir_function.blocks.insert(self.current_block, block);
        let (_, ty_none) = self.program.insert_type(Type::None, self.arena);
        self.program.types.get_by_left(&body_ty).unwrap().unify(
            ty_none,
            &mut self.program,
            self.arena,
        )?;

        Ok(lir_function)
    }

    fn lower(arena: &'arena Arena<'arena>, program: &HirProgram) -> Result<Program<'arena>> {
        let mut lowerer = Lowerer {
            arena,
            program: Program::new(program, arena),
            environment: HashMap::new(),
            ty_bool: program.lib_std().ty_bool,
            current_block: Function::entry_point(),
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
