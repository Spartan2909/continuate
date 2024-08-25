use crate::collect_into;
use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
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
use crate::mid_level_ir::Block;
use crate::mid_level_ir::BlockId;
use crate::mid_level_ir::Expr;
use crate::mid_level_ir::Function;
use crate::mid_level_ir::Program;
use crate::mid_level_ir::Type;
use crate::mid_level_ir::TypeConstructor;
use crate::mid_level_ir::UserDefinedType;
use crate::try_collect_into;
use crate::HashMap;
use crate::Vec;

use std::cmp::Ordering;
use std::iter;
use std::mem;

use bumpalo::Bump;

use continuate_error::Result;

use hashbrown::hash_map::Entry;

use itertools::Itertools as _;

struct ExprGet<'arena> {
    object: Expr<'arena>,
    object_ty: TypeRef,
    field: usize,
}

enum ArmData<'arena> {
    Variant {
        ty: &'arena Type<'arena>,
        variant: MatchVariant,
    },
    Wildcard,
    None,
}

struct MatchVariant {
    variant: usize,
    exhaustive: bool,
    block: BlockId,
}

struct Lowerer<'a, 'arena> {
    arena: &'arena Bump,
    program: Program<'arena>,
    environment: HashMap<'arena, Ident, TypeRef>,
    ty_bool: TypeRef,
    current_block: BlockId,
    hir_program: &'a HirProgram<'a>,
}

impl<'a, 'arena> Lowerer<'a, 'arena> {
    fn user_defined_ty(&self, ty: &HirUserDefinedType) -> UserDefinedType<'arena> {
        let constructor = match &ty.constructor {
            HirTypeConstructor::Product(fields) => {
                let mut new_fields = Vec::with_capacity_in(fields.len(), self.arena);
                new_fields.extend_from_slice(fields);
                TypeConstructor::Product(new_fields)
            }
            HirTypeConstructor::Sum(variants) => {
                let mut new_variants = Vec::with_capacity_in(variants.len(), self.arena);
                for variant in variants {
                    let mut new_variant = Vec::with_capacity_in(variant.len(), self.arena);
                    new_variant.extend_from_slice(variant);
                    new_variants.push(new_variant);
                }
                TypeConstructor::Sum(new_variants)
            }
        };
        UserDefinedType { constructor }
    }

    fn lower_ty(&self, ty: &HirType) -> Type<'arena> {
        match *ty {
            HirType::Int => Type::Int,
            HirType::Float => Type::Float,
            HirType::String => Type::String,
            HirType::Array(ty, len) => Type::Array(ty, len),
            HirType::Tuple(ref types) => {
                Type::Tuple(collect_into(types.iter().copied(), Vec::new_in(self.arena)))
            }
            HirType::Function(HirFunctionTy {
                ref params,
                ref continuations,
            }) => Type::function(
                collect_into(params.iter().copied(), Vec::new_in(self.arena)),
                collect_into(
                    continuations.iter().map(|(&ident, &ty)| (ident, ty)),
                    HashMap::new_in(self.arena),
                ),
            ),
            HirType::UserDefined(ref ty) => Type::UserDefined(self.user_defined_ty(ty)),
        }
    }

    fn expr_list(
        &mut self,
        exprs: &[HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<Vec<'arena, (Expr<'arena>, TypeRef)>> {
        let initial = Vec::new_in(self.arena);
        try_collect_into(
            exprs.iter().map(|expr| self.expr(expr, block, function)),
            initial,
        )
    }

    fn expr_block(
        &mut self,
        exprs: &[HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let mut exprs = self.expr_list(exprs, block, function)?;
        let (last_expr, block_ty) = exprs.pop().unwrap_or_else(|| {
            let ty = self
                .program
                .insert_type(Type::Tuple(Vec::new_in(self.arena)), self.arena)
                .0;
            (
                Expr::Tuple {
                    ty,
                    values: Vec::new_in(self.arena),
                },
                ty,
            )
        });
        for (expr, _) in exprs {
            block.exprs.push(expr);
        }
        Ok((last_expr, block_ty))
    }

    fn expr_tuple(
        &mut self,
        elements: &[HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let elements = self.expr_list(elements, block, function)?;

        let types = collect_into(elements.iter().map(|(_, ty)| *ty), Vec::new_in(self.arena));
        let ty = Type::Tuple(types);
        let ty = self.program.insert_type(ty, self.arena).0;

        let mut values = Vec::with_capacity_in(elements.len(), self.arena);
        values.extend(elements.into_iter().map(|(expr, _)| expr));
        let expr = Expr::Tuple { ty, values };
        Ok((expr, ty))
    }

    fn expr_constructor(
        &mut self,
        ty: TypeRef,
        index: Option<usize>,
        fields: &[HirExpr],
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

        let mut new_fields = Vec::with_capacity_in(fields.len(), self.arena);
        new_fields.extend(fields.into_iter().map(|(expr, _)| expr));
        let expr = Expr::Constructor {
            ty,
            index,
            fields: new_fields,
        };
        Ok((expr, ty))
    }

    fn expr_array(
        &mut self,
        array: &[HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let array = self.expr_list(array, block, function)?;
        let mut value_ty = self.program.insert_type(Type::Unknown, self.arena).1;
        for (_, ty) in &array {
            let ty = *self.program.types.get_by_left(ty).unwrap();
            value_ty = value_ty.unify(ty, &mut self.program, self.arena)?;
        }
        let value_ty = *self.program.types.get_by_right(value_ty).unwrap();
        let array_ty = self
            .program
            .insert_type(Type::Array(value_ty, array.len() as u64), self.arena)
            .0;
        let mut values = Vec::with_capacity_in(array.len(), self.arena);
        values.extend(array.into_iter().map(|(expr, _)| expr));
        Ok((
            Expr::Array {
                ty: array_ty,
                values,
                value_ty,
            },
            array_ty,
        ))
    }

    fn expr_get(
        &mut self,
        object: &HirExpr,
        field: usize,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(ExprGet<'arena>, TypeRef)> {
        let (object, object_ty) = self.expr(object, block, function)?;
        let user_defined = *self.program.types.get_by_left(&object_ty).unwrap();
        let user_defined = user_defined
            .as_user_defined()
            .ok_or(format!("cannot access field of {user_defined:?}"))?;
        let TypeConstructor::Product(ty_fields) = &user_defined.constructor else {
            return Err("cannot access field of sum".into());
        };
        let expr = ExprGet {
            object,
            object_ty,
            field,
        };
        Ok((expr, ty_fields[field]))
    }

    fn expr_set(
        &mut self,
        object: &HirExpr,
        field: usize,
        value: &HirExpr,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (expr, field_ty) = self.expr_get(object, field, block, function)?;
        let ExprGet {
            object,
            object_ty,
            field,
        } = expr;

        let (value, value_ty) = self.expr(value, block, function)?;

        let field_ty = *self.program.types.get_by_left(&field_ty).unwrap();
        let value_ty = *self.program.types.get_by_left(&value_ty).unwrap();
        let ty = field_ty.unify(value_ty, &mut self.program, self.arena)?;
        let ty_ref = *self.program.types.get_by_right(ty).unwrap();
        let expr = Expr::Set {
            object: self.arena.alloc(object),
            object_ty,
            object_variant: None,
            field,
            value: self.arena.alloc(value),
        };
        Ok((expr, ty_ref))
    }

    fn expr_call(
        &mut self,
        callee: &HirExpr,
        params: &[HirExpr],
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

        let mut new_params = Vec::with_capacity_in(params.len(), self.arena);
        new_params.extend(params.into_iter().map(|(expr, _)| expr));
        let expr = Expr::Call(self.arena.alloc(callee), new_params);
        let (ty, _) = self.program.insert_type(Type::None, self.arena);
        Ok((expr, ty))
    }

    fn expr_cont_application(
        &mut self,
        callee: &HirExpr,
        continuations: &HashMap<Ident, HirExpr>,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (callee, callee_ty) = self.expr(callee, block, function)?;
        let callee_ty = *self.program.types.get_by_left(&callee_ty).unwrap();
        let callee_ty = callee_ty
            .as_function()
            .ok_or(format!("cannot apply continuations to {callee_ty:?}"))?;

        let mut outstanding_continuations = callee_ty.continuations.clone();
        let mut new_continuations = HashMap::with_capacity_in(continuations.len(), self.arena);
        for (&ident, expr) in continuations {
            let (expr, ty) = self.expr(expr, block, function)?;

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

        let expr = Expr::ContApplication(self.arena.alloc(callee), new_continuations);
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
            (UnaryOp::Not, _) if input_ty_ref == self.program.lib_std.ty_bool => input_ty_ref,
            _ => Err(format!("cannot apply {operator:?} to {input_ty:?}"))?,
        };
        let expr = Expr::Unary {
            operator,
            operand: self.arena.alloc(operand),
            operand_ty: input_ty_ref,
        };
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
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
                r @ (Type::Int | Type::Float | Type::String),
            ) if l == r => self.ty_bool,
            (l, BinaryOp::Eq | BinaryOp::Ne, r) if l == r => self.ty_bool,
            _ => Err(format!(
                "cannot apply {operator:?} to {left_ty:?} and {right_ty:?}"
            ))?,
        };

        let expr = Expr::Binary {
            left: self.arena.alloc(left),
            left_ty: left_ty_ref,
            operator,
            right: self.arena.alloc(right),
            right_ty: right_ty_ref,
        };
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
        self.environment.insert(ident, ty);
        let expr = Expr::Assign {
            ident,
            expr: self.arena.alloc(expr),
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
            expr: self.arena.alloc(expr),
        };
        Ok((expr, ty))
    }

    fn order_patterns<'b, 'c>(
        fields: &'b [Pattern<'c>],
    ) -> impl Iterator<Item = (usize, &'b Pattern<'c>)> {
        fields
            .iter()
            .enumerate()
            .sorted_unstable_by(|&(_, l), &(_, r)| {
                #[allow(clippy::match_same_arms)] // Arm order matters
                match (l, r) {
                    (x, y) if x == y => Ordering::Equal,
                    (Pattern::Wildcard, _) => Ordering::Less,
                    (Pattern::Ident(_), Pattern::Wildcard) => Ordering::Greater,
                    (Pattern::Ident(_), _) => Ordering::Less,
                    (Pattern::Destructure { .. }, _) => Ordering::Greater,
                }
            })
    }

    fn pattern(
        &mut self,
        scrutinee: (&'arena Expr<'arena>, TypeRef),
        arm_pat: &Pattern,
        arm_block: &mut Block<'arena>,
        arm_block_id: BlockId,
        otherwise: BlockId,
        function: &mut Function<'arena>,
    ) -> Result<ArmData<'arena>> {
        let (scrutinee, scrutinee_ty_ref) = scrutinee;
        let scrutinee_ty = *self.program.types.get_by_left(&scrutinee_ty_ref).unwrap();

        let arm_data = match *arm_pat {
            Pattern::Wildcard => ArmData::Wildcard,
            Pattern::Ident(ident) => {
                let binding = Expr::Assign {
                    ident,
                    expr: scrutinee,
                };
                function
                    .declarations
                    .insert(ident, (scrutinee_ty_ref, None));
                arm_block.exprs.push(binding);
                ArmData::Wildcard
            }
            Pattern::Destructure {
                ty,
                variant,
                ref fields,
            } => {
                let ty = *self.program.types.get_by_left(&ty).unwrap();
                let mut exhaustive = true;
                for (field, pattern) in Self::order_patterns(fields) {
                    let get = Expr::Get {
                        object: scrutinee,
                        object_ty: scrutinee_ty_ref,
                        object_variant: variant,
                        field,
                    };
                    let get = self.arena.alloc(get);
                    let field_ty_ref = scrutinee_ty.field(variant, field).unwrap();
                    let field_ty = *self.program.types.get_by_left(&field_ty_ref).unwrap();
                    let mut new_block = Block::new(self.arena);
                    let new_block_id = function.block();
                    match self.pattern(
                        (get, field_ty_ref),
                        pattern,
                        &mut new_block,
                        new_block_id,
                        otherwise,
                        function,
                    )? {
                        ArmData::None | ArmData::Wildcard => {
                            arm_block.exprs.append(&mut new_block.exprs);
                        }
                        ArmData::Variant {
                            ty: switch_ty,
                            variant:
                                MatchVariant {
                                    variant,
                                    exhaustive: _,
                                    block: switch_arm_id,
                                },
                        } => {
                            switch_ty.unify(field_ty, &mut self.program, self.arena)?;
                            let discriminant = Expr::Intrinsic {
                                intrinsic: Intrinsic::Discriminant,
                                value: get,
                                value_ty: field_ty_ref,
                            };
                            let arms = iter::once((variant as i64, switch_arm_id));
                            let switch = Expr::Switch {
                                scrutinee: self.arena.alloc(discriminant),
                                arms: collect_into(arms, HashMap::new_in(self.arena)),
                                otherwise,
                            };
                            arm_block.exprs.push(switch);
                            function.blocks.insert(switch_arm_id, new_block);
                            exhaustive = false;
                        }
                    }
                }
                if let Some(variant) = variant {
                    ArmData::Variant {
                        ty,
                        variant: MatchVariant {
                            variant,
                            exhaustive,
                            block: arm_block_id,
                        },
                    }
                } else {
                    ArmData::None
                }
            }
        };
        Ok(arm_data)
    }

    fn expr_match(
        &mut self,
        scrutinee: &HirExpr,
        arms: &[(Pattern, HirExpr)],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (scrutinee, scrutinee_ty_ref) = self.expr(scrutinee, block, function)?;
        let scrutinee = &*self.arena.alloc(scrutinee);
        let mut scrutinee_ty = *self.program.types.get_by_left(&scrutinee_ty_ref).unwrap();

        let mut discriminants = vec![];
        let otherwise = function.block();
        let mut has_wildcard = false;
        let next_id = function.block();

        for (arm_pat, arm) in arms {
            let mut arm_block = Block::new(self.arena);
            let mut arm_block_id = function.block();

            let arm_data = self.pattern(
                (scrutinee, scrutinee_ty_ref),
                arm_pat,
                &mut arm_block,
                arm_block_id,
                otherwise,
                function,
            )?;

            match arm_data {
                ArmData::Wildcard => {
                    has_wildcard = true;
                    arm_block_id = otherwise;
                }
                ArmData::Variant { ty, variant } => {
                    scrutinee_ty = scrutinee_ty.unify(ty, &mut self.program, self.arena)?;
                    discriminants.push(variant);
                }
                ArmData::None => {}
            }

            let (arm, arm_ty) = self.expr(arm, &mut arm_block, function)?;
            arm_block.exprs.push(arm);
            let goto = Expr::Goto(next_id);
            arm_block.exprs.push(goto);

            let arm_ty = *self.program.types.get_by_left(&arm_ty).unwrap();
            arm_ty.unify(
                self.program.insert_type(Type::None, self.arena).1,
                &mut self.program,
                self.arena,
            )?;

            function.blocks.insert(arm_block_id, arm_block);

            if has_wildcard {
                break;
            }
        }

        if !has_wildcard {
            if let Some(variants) = scrutinee_ty.variants() {
                let mut exhaustive = true;
                let mut last = false;
                for &MatchVariant {
                    variant,
                    exhaustive: variant_exhaustive,
                    block: _,
                } in &discriminants
                {
                    if variant == variants {
                        last = true;
                    }
                    exhaustive &= variant_exhaustive;
                }
                if !(exhaustive && last) {
                    Err("non-exhaustive match")?;
                }
            }
        }

        let current_block = mem::replace(block, Block::new(self.arena));
        function.blocks.insert(self.current_block, current_block);
        self.current_block = next_id;

        let scrutinee = if discriminants.is_empty() {
            scrutinee
        } else {
            self.arena.alloc(Expr::Intrinsic {
                intrinsic: Intrinsic::Discriminant,
                value: scrutinee,
                value_ty: scrutinee_ty_ref,
            })
        };

        if let Entry::Vacant(entry) = function.blocks.entry(otherwise) {
            let mut otherwise_block = Block::new(self.arena);
            otherwise_block.exprs.push(Expr::Unreachable);
            entry.insert(otherwise_block);
        }
        let expr = Expr::Switch {
            scrutinee,
            arms: collect_into(
                discriminants.iter().map(
                    |&MatchVariant {
                         variant,
                         exhaustive: _,
                         block,
                     }| (variant as i64, block),
                ),
                HashMap::new_in(self.arena),
            ),
            otherwise,
        };

        Ok((expr, self.program.insert_type(Type::None, self.arena).0))
    }

    fn expr_closure(&mut self, func_ref: FuncRef) -> Result<(Expr<'arena>, TypeRef)> {
        let func = &self.hir_program.functions[&func_ref];
        let captures = collect_into(
            func.captures
                .iter()
                .map(|&ident| (ident, self.environment[&ident])),
            HashMap::new_in(self.arena),
        );

        let func = self.function(func, captures.clone())?;
        self.program
            .functions
            .insert(func_ref, self.arena.alloc(func));

        let expr = Expr::Closure { func_ref, captures };
        let ty = self.program.signatures[&func_ref];
        Ok((expr, ty))
    }

    fn expr_intrinsic(
        &mut self,
        intrinsic: Intrinsic,
        value: &HirExpr,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Result<(Expr<'arena>, TypeRef)> {
        let (value, value_ty) = self.expr(value, block, function)?;
        let output_ty = match intrinsic {
            Intrinsic::Discriminant => self.program.lib_std.ty_int,
            Intrinsic::Terminate => self.program.insert_type(Type::None, self.arena).0,
        };
        Ok((
            Expr::Intrinsic {
                intrinsic,
                value: self.arena.alloc(value),
                value_ty,
            },
            output_ty,
        ))
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
            HirExpr::Get { object, field } => {
                let (expr, ty) = self.expr_get(object, field, block, function)?;
                Ok((
                    Expr::Get {
                        object: self.arena.alloc(expr.object),
                        object_ty: expr.object_ty,
                        object_variant: None,
                        field: expr.field,
                    },
                    ty,
                ))
            }
            HirExpr::Set {
                object,
                field,
                value,
            } => self.expr_set(object, field, value, block, function),
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
            HirExpr::Closure { func } => self.expr_closure(func),
            HirExpr::Intrinsic { intrinsic, value } => {
                self.expr_intrinsic(intrinsic, value, block, function)
            }
            HirExpr::Unreachable => Ok((
                Expr::Unreachable,
                self.program.insert_type(Type::None, self.arena).0,
            )),
        }
    }

    fn function<'b, 'c>(
        &mut self,
        function: &'b HirFunction<'c>,
        captures: HashMap<'arena, Ident, TypeRef>,
    ) -> Result<Function<'arena>> {
        let mut mir_function = Function::new(function.name.clone(), self.arena);
        mir_function.params.reserve(function.params.len());
        for &param in &function.params {
            mir_function.params.push(param);
        }
        mir_function
            .continuations
            .reserve(function.continuations.len());
        for (&param, &ty) in &function.continuations {
            mir_function.continuations.insert(param, ty);
        }

        self.environment.clone_from(&captures);
        mir_function.captures = captures;

        for (&param, &ty) in mir_function
            .params
            .iter()
            .map(|(param, ty)| (param, ty))
            .chain(&mir_function.continuations)
        {
            self.environment.insert(param, ty);
        }

        self.current_block = Function::entry_point();

        let mut block = Block::new(self.arena);
        let (body, body_ty) = self.expr_block(&function.body, &mut block, &mut mir_function)?;
        block.exprs.push(body);
        mir_function.blocks.insert(self.current_block, block);
        let (_, ty_none) = self.program.insert_type(Type::None, self.arena);
        self.program.types.get_by_left(&body_ty).unwrap().unify(
            ty_none,
            &mut self.program,
            self.arena,
        )?;

        Ok(mir_function)
    }

    fn lower(arena: &'arena Bump, program: &'a HirProgram<'a>) -> Result<Program<'arena>> {
        let mut lowerer = Lowerer {
            arena,
            program: Program::new(program, arena),
            environment: HashMap::new_in(arena),
            ty_bool: program.lib_std().ty_bool,
            current_block: Function::entry_point(),
            hir_program: program,
        };

        for (&type_ref, &ty) in &program.types {
            let ty = lowerer.arena.alloc(lowerer.lower_ty(ty));
            lowerer.program.types.insert(type_ref, ty);
        }

        for (&function, &signature) in &program.signatures {
            lowerer.program.signatures.insert(function, signature);
        }

        for (&func_ref, function) in &program.functions {
            if !function.captures.is_empty() {
                continue;
            }
            let function = lowerer
                .arena
                .alloc(lowerer.function(function, HashMap::new_in(arena))?);
            lowerer.program.functions.insert(func_ref, function);
        }

        Ok(lowerer.program)
    }
}

/// ## Errors
///
/// Returns an error if there is a type error in the program.
pub fn lower<'a, 'arena>(
    program: &'a HirProgram<'a>,
    arena: &'arena Bump,
) -> Result<Program<'arena>> {
    Lowerer::lower(arena, program)
}
