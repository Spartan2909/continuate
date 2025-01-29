use std::mem;

use crate::collect_into;
use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::common::UnaryOp;
use crate::high_level_ir::Expr;
use crate::high_level_ir::Function;
use crate::high_level_ir::FunctionTy;
use crate::high_level_ir::Pattern;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;
use crate::high_level_ir::TypeConstructor;
use crate::high_level_ir::UserDefinedType;
use crate::try_collect_into;
use crate::HashMap;
use crate::HashSet;
use crate::Vec;

use bumpalo::Bump;

use continuate_error::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)]
enum Exhaustive<'arena> {
    Exhaustive,
    ExhaustiveVariants(HashSet<'arena, usize>),
    NonExhaustive,
}

impl<'arena> Exhaustive<'arena> {
    fn finalise(self) -> Exhaustive<'arena> {
        if matches!(self, Exhaustive::Exhaustive) {
            Exhaustive::Exhaustive
        } else {
            Exhaustive::NonExhaustive
        }
    }

    fn intersect(self, other: Exhaustive<'arena>, arena: &'arena Bump) -> Exhaustive<'arena> {
        match (self, other) {
            (Exhaustive::Exhaustive, Exhaustive::Exhaustive) => Exhaustive::Exhaustive,
            (Exhaustive::Exhaustive, Exhaustive::ExhaustiveVariants(variants))
            | (Exhaustive::ExhaustiveVariants(variants), Exhaustive::Exhaustive) => {
                Exhaustive::ExhaustiveVariants(variants)
            }
            (
                Exhaustive::ExhaustiveVariants(self_variants),
                Exhaustive::ExhaustiveVariants(other_variants),
            ) => Exhaustive::ExhaustiveVariants(collect_into(
                self_variants.intersection(&other_variants).copied(),
                HashSet::new_in(arena),
            )),
            _ => Exhaustive::NonExhaustive,
        }
    }

    fn union(self, other: Exhaustive<'arena>, arena: &'arena Bump) -> Exhaustive<'arena> {
        match (self, other) {
            (Exhaustive::Exhaustive, _) | (_, Exhaustive::Exhaustive) => Exhaustive::Exhaustive,
            (
                Exhaustive::ExhaustiveVariants(self_variants),
                Exhaustive::ExhaustiveVariants(other_variants),
            ) => Exhaustive::ExhaustiveVariants(collect_into(
                self_variants.union(&other_variants),
                HashSet::new_in(arena),
            )),
            (Exhaustive::ExhaustiveVariants(variants), Exhaustive::NonExhaustive)
            | (Exhaustive::NonExhaustive, Exhaustive::ExhaustiveVariants(variants)) => {
                Exhaustive::ExhaustiveVariants(variants)
            }
            (Exhaustive::NonExhaustive, Exhaustive::NonExhaustive) => Exhaustive::NonExhaustive,
        }
    }
}

struct TypeCk<'a, 'arena> {
    program: &'a mut Program<'arena>,
    environment: HashMap<'arena, Ident, TypeRef>,
    arena: &'arena Bump,
    closures: Vec<'arena, (FuncRef, HashMap<'arena, Ident, TypeRef>)>,
}

impl<'a, 'arena> TypeCk<'a, 'arena> {
    fn exprs(&mut self, exprs: &mut [Expr<'arena>]) -> Result<Vec<'arena, TypeRef>> {
        let vec = Vec::new_in(self.arena);
        let types = try_collect_into(exprs.iter_mut().map(|expr| self.expr(expr)), vec)?;
        Ok(types)
    }

    fn expr_literal(&self, literal: &Literal) -> TypeRef {
        match *literal {
            Literal::Int(_) => self.program.lib_std().ty_int,
            Literal::Float(_) => self.program.lib_std().ty_float,
            Literal::String(_) => self.program.lib_std().ty_string,
        }
    }

    fn expr_ident(&self, ident: Ident) -> Result<TypeRef> {
        self.environment
            .get(&ident)
            .copied()
            .ok_or_else(|| format!("cannot find {ident:?}").into())
    }

    fn expr_block(&mut self, exprs: &mut [Expr<'arena>], ty: TypeRef) -> Result<TypeRef> {
        let Some((tail, block)) = exprs.split_last_mut() else {
            return Ok(self
                .program
                .insert_type(Type::Tuple(Vec::new_in(self.arena)), self.arena)
                .0);
        };

        for expr in block {
            self.expr(expr)?;
        }

        let block_ty_ref = self.expr(tail)?;
        let block_ty = self.program.types.get_by_left(&block_ty_ref).unwrap();
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let unified = block_ty.unify(ty, self.program, self.arena)?;
        Ok(*self.program.types.get_by_right(unified).unwrap())
    }

    fn expr_tuple(&mut self, exprs: &mut [Expr<'arena>], ty: TypeRef) -> Result<TypeRef> {
        let types = self.exprs(exprs)?;
        let result_ty = self.program.insert_type(Type::Tuple(types), self.arena).1;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let result_ty = result_ty.unify(ty, self.program, self.arena)?;

        Ok(*self.program.types.get_by_right(result_ty).unwrap())
    }

    fn expr_constructor(
        &mut self,
        ty: TypeRef,
        index: Option<usize>,
        fields: &mut [Expr<'arena>],
    ) -> Result<TypeRef> {
        let fields = self.exprs(fields)?;
        let user_defined = self.program.types.get_by_left(&ty).unwrap();
        let user_defined = user_defined
            .as_user_defined()
            .ok_or_else(|| format!("cannot construct {user_defined:?}"))?;
        let ty_fields = match (&user_defined.constructor, index) {
            (TypeConstructor::Product(ty_fields), None) => ty_fields,
            (TypeConstructor::Sum(variants), Some(index)) => &variants[index],
            _ => unreachable!(),
        };

        if fields.len() != ty_fields.len() {
            Err("incorrect number of fields")?;
        }

        for (given_field_ty, field_ty) in fields.iter().zip(ty_fields) {
            let given_field_ty = *self.program.types.get_by_left(given_field_ty).unwrap();
            let field_ty = *self.program.types.get_by_left(field_ty).unwrap();
            given_field_ty.unify(field_ty, self.program, self.arena)?;
        }

        Ok(ty)
    }

    fn expr_array(&mut self, exprs: &mut [Expr<'arena>], ty: &mut TypeRef) -> Result<TypeRef> {
        let elem_ty = self.exprs(exprs)?.into_iter().try_fold(*ty, |acc, ty| {
            let acc = self.program.types.get_by_left(&acc).unwrap();
            let ty = self.program.types.get_by_left(&ty).unwrap();
            let ty = ty.unify(acc, self.program, self.arena)?;
            Result::Ok(*self.program.types.get_by_right(ty).unwrap())
        })?;
        *ty = elem_ty;
        let ty = self
            .program
            .insert_type(Type::Array(elem_ty, exprs.len() as u64), self.arena);
        Ok(ty.0)
    }

    fn expr_get(
        &mut self,
        object: &mut Expr<'arena>,
        object_ty: TypeRef,
        field: usize,
    ) -> Result<TypeRef> {
        let object_ty = *self.program.types.get_by_left(&object_ty).unwrap();
        let found_ty = self.expr(object)?;
        let found_ty = self.program.types.get_by_left(&found_ty).unwrap();
        let object_ty = found_ty.unify(object_ty, self.program, self.arena)?;
        let Type::UserDefined(UserDefinedType {
            constructor: TypeConstructor::Product(fields),
        }) = object_ty
        else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };

        Ok(fields[field])
    }

    fn expr_set(
        &mut self,
        object: &mut Expr<'arena>,
        object_ty: &mut TypeRef,
        field: usize,
        value: &mut Expr<'arena>,
        value_ty: &mut TypeRef,
    ) -> Result<TypeRef> {
        let ty = *self.program.types.get_by_left(object_ty).unwrap();
        let found_ty = self.expr(object)?;
        let found_ty = self.program.types.get_by_left(&found_ty).unwrap();
        let ty = found_ty.unify(ty, self.program, self.arena)?;
        *object_ty = *self.program.types.get_by_right(ty).unwrap();

        let Type::UserDefined(UserDefinedType {
            constructor: TypeConstructor::Product(fields),
        }) = ty
        else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };

        let field_ty = fields[field];
        let field_ty = *self.program.types.get_by_left(&field_ty).unwrap();

        let ty = self.expr(value)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let ty = ty.unify(field_ty, self.program, self.arena)?;
        let ty = *self.program.types.get_by_right(ty).unwrap();
        *value_ty = ty;
        Ok(ty)
    }

    fn expr_call(
        &mut self,
        callee: &mut Expr<'arena>,
        callee_ty: &mut TypeRef,
        args: &mut [Expr<'arena>],
    ) -> Result<TypeRef> {
        let ty = self.expr(callee)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let expected_ty = self.program.types.get_by_left(callee_ty).unwrap();
        let ty = ty.unify(expected_ty, self.program, self.arena)?;
        *callee_ty = *self.program.types.get_by_right(ty).unwrap();
        let Type::Function(FunctionTy {
            params,
            continuations,
        }) = ty
        else {
            Err("{ty:?} is not a function")?
        };

        if !continuations.is_empty() {
            Err("cannot call a function with remaining continuations")?;
        }

        if args.len() != params.len() {
            Err(format!(
                "incorrect number of arguments (expected {}, got {})",
                params.len(),
                args.len()
            ))?;
        }

        for (param, arg) in params.iter().zip(args) {
            let arg = self.expr(arg)?;
            let arg = self.program.types.get_by_left(&arg).unwrap();
            let param = self.program.types.get_by_left(param).unwrap();
            arg.unify(param, self.program, self.arena)?;
        }

        Ok(self.program.insert_type(Type::None, self.arena).0)
    }

    fn expr_cont_application(
        &mut self,
        callee: &mut Expr<'arena>,
        callee_ty: &mut TypeRef,
        continuations: &mut HashMap<Ident, Expr<'arena>>,
    ) -> Result<TypeRef> {
        let ty = self.expr(callee)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let expected_ty = self.program.types.get_by_left(callee_ty).unwrap();
        let ty = ty.unify(expected_ty, self.program, self.arena)?;
        *callee_ty = *self.program.types.get_by_right(ty).unwrap();
        let Type::Function(FunctionTy {
            params,
            continuations: ty_continuations,
        }) = ty
        else {
            Err("{ty:?} is not a function")?
        };

        let mut ty_continuations = ty_continuations.clone();
        for (ident, cont) in continuations {
            let cont = self.expr(cont)?;
            let cont = self.program.types.get_by_left(&cont).unwrap();
            let expected = ty_continuations
                .remove(ident)
                .ok_or_else(|| format!("no such continuation {ident:?}"))?;
            let expected = self.program.types.get_by_left(&expected).unwrap();
            cont.unify(expected, self.program, self.arena)?;
        }

        let ty = Type::function(params.clone(), ty_continuations);
        Ok(self.program.insert_type(ty, self.arena).0)
    }

    fn expr_unary(
        &mut self,
        op: UnaryOp,
        right: &mut Expr<'arena>,
        right_ty: &mut TypeRef,
    ) -> Result<TypeRef> {
        let expected = *self.program.types.get_by_left(right_ty).unwrap();
        let right = self.expr(right)?;
        let right = self.program.types.get_by_left(&right).unwrap();
        let right = right.unify(expected, self.program, self.arena)?;
        let right_ref = *self.program.types.get_by_right(right).unwrap();
        *right_ty = right_ref;
        match (op, right) {
            (UnaryOp::Neg, Type::Int | Type::Float) => Ok(right_ref),
            (UnaryOp::Not, _) if right_ref == self.program.lib_std().ty_bool => Ok(right_ref),
            _ => Err(format!("invalid use of {op:?}"))?,
        }
    }

    fn expr_binary(
        &mut self,
        left: &mut Expr<'arena>,
        left_ty: &mut TypeRef,
        op: BinaryOp,
        right: &mut Expr<'arena>,
        right_ty: &mut TypeRef,
    ) -> Result<TypeRef> {
        let expected = *self.program.types.get_by_left(left_ty).unwrap();
        let left = self.expr(left)?;
        let left = self.program.types.get_by_left(&left).unwrap();
        let left = left.unify(expected, self.program, self.arena)?;
        *left_ty = *self.program.types.get_by_right(left).unwrap();

        let expected = *self.program.types.get_by_left(right_ty).unwrap();
        let right = self.expr(right)?;
        let right = self.program.types.get_by_left(&right).unwrap();
        let right = right.unify(expected, self.program, self.arena)?;
        *right_ty = *self.program.types.get_by_right(right).unwrap();

        match (left, op, right) {
            (
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Add,
                r @ (Type::Int | Type::Float | Type::String),
            )
            | (
                l @ (Type::Int | Type::Float),
                BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem,
                r @ (Type::Int | Type::Float),
            ) if l == r => Ok(*left_ty),
            (
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
                r @ (Type::Int | Type::Float | Type::String),
            ) if l == r => Ok(self.program.lib_std().ty_bool),
            (l, BinaryOp::Eq | BinaryOp::Ne, r) if l == r => Ok(self.program.lib_std().ty_bool),
            _ => Err(format!("cannot apply {op:?} to {left_ty:?} and {right_ty:?}").into()),
        }
    }

    fn expr_declare(
        &mut self,
        ident: Ident,
        ty: &mut TypeRef,
        expr: &mut Expr<'arena>,
    ) -> Result<TypeRef> {
        let expr_ty = self.expr(expr)?;
        let expr_ty = self.program.types.get_by_left(&expr_ty).unwrap();
        let expected = self.program.types.get_by_left(ty).unwrap();
        let expr_ty = expr_ty.unify(expected, self.program, self.arena)?;
        *ty = *self.program.types.get_by_right(expr_ty).unwrap();
        self.environment.insert(ident, *ty);
        Ok(*ty)
    }

    fn expr_assign(&mut self, ident: Ident, expr: &mut Expr<'arena>) -> Result<TypeRef> {
        let expected = self.environment.get(&ident).unwrap();
        let expected = *self.program.types.get_by_left(expected).unwrap();
        let ty = self.expr(expr)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let ty = ty.unify(expected, self.program, self.arena)?;
        Ok(*self.program.types.get_by_right(ty).unwrap())
    }

    fn pattern(&mut self, expr_ty: TypeRef, pattern: &Pattern) -> Result<Exhaustive<'arena>> {
        match *pattern {
            Pattern::Wildcard => Ok(Exhaustive::Exhaustive),
            Pattern::Ident(ident) => {
                self.environment.insert(ident, expr_ty);
                Ok(Exhaustive::Exhaustive)
            }
            Pattern::Destructure {
                ty,
                variant,
                ref fields,
            } => {
                let expr_ty = self.program.types.get_by_left(&expr_ty).unwrap();
                let ty = self.program.types.get_by_left(&ty).unwrap();
                let ty = expr_ty.unify(ty, self.program, self.arena)?;
                let field_tys = match (&ty.as_user_defined().unwrap().constructor, variant) {
                    (TypeConstructor::Product(fields), None) => fields,
                    (TypeConstructor::Sum(variants), Some(variant)) => &variants[variant],
                    _ => unreachable!(),
                };
                let exhaustive = fields.iter().zip(field_tys).try_fold(
                    Exhaustive::Exhaustive,
                    |acc, (pat, &field_ty)| {
                        Result::Ok(
                            self.pattern(field_ty, pat)?
                                .finalise()
                                .intersect(acc, self.arena),
                        )
                    },
                )?;
                match (variant, exhaustive) {
                    (Some(variant), Exhaustive::Exhaustive) => {
                        let mut variants = HashSet::with_capacity_in(1, self.arena);
                        variants.insert(variant);
                        Ok(Exhaustive::ExhaustiveVariants(variants))
                    }
                    (None, Exhaustive::Exhaustive) => Ok(Exhaustive::Exhaustive),
                    _ => Ok(Exhaustive::NonExhaustive),
                }
            }
        }
    }

    fn expr_match(
        &mut self,
        expr: &mut Expr<'arena>,
        arms: &mut [(Pattern<'arena>, Expr<'arena>)],
    ) -> Result<TypeRef> {
        let expr_ty = self.expr(expr)?;
        let mut exhaustive = Exhaustive::Exhaustive;
        let mut output_ty = self.program.insert_type(Type::Unknown, self.arena).1;
        for (pat, expr) in arms {
            exhaustive = exhaustive.union(self.pattern(expr_ty, pat)?, self.arena);
            let expr_ty = self.expr(expr)?;
            let expr_ty = self.program.types.get_by_left(&expr_ty).unwrap();
            output_ty = expr_ty.unify(output_ty, self.program, self.arena)?;
        }
        Ok(*self.program.types.get_by_right(output_ty).unwrap())
    }

    fn expr_closure(
        &mut self,
        func: FuncRef,
        captures: &mut Option<HashMap<'arena, Ident, TypeRef>>,
    ) -> TypeRef {
        let actual_func = self.program.functions.get(&func).unwrap();
        let new_captures = collect_into(
            actual_func
                .captures
                .iter()
                .map(|&ident| (ident, self.environment[&ident])),
            HashMap::new_in(self.arena),
        );
        {
            let mut captures = HashMap::new_in(self.arena);
            captures.clone_from(&new_captures);
            self.closures.push((func, captures));
        }
        *captures = Some(new_captures);
        self.program.signatures[&func]
    }

    fn expr_intrinsic(
        &mut self,
        intrinsic: Intrinsic,
        value: &mut Expr<'arena>,
        value_ty: &mut TypeRef,
    ) -> Result<TypeRef> {
        let ty = self.expr(value)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let expected = self.program.types.get_by_left(value_ty).unwrap();
        let ty = ty.unify(expected, self.program, self.arena)?;
        *value_ty = *self.program.types.get_by_right(ty).unwrap();
        match intrinsic {
            Intrinsic::Discriminant => Ok(self.program.lib_std().ty_int),
            Intrinsic::Terminate => Ok(self.program.insert_type(Type::None, self.arena).0),
        }
    }

    fn expr(&mut self, expr: &mut Expr<'arena>) -> Result<TypeRef> {
        match *expr {
            Expr::Literal(ref literal) => Ok(self.expr_literal(literal)),
            Expr::Ident(ident) => self.expr_ident(ident),
            Expr::Function(func_ref) => Ok(self.program.signatures[&func_ref]),
            Expr::Block(ref mut exprs, ref mut ty) => {
                let checked_ty = self.expr_block(exprs, *ty)?;
                *ty = checked_ty;
                Ok(checked_ty)
            }
            Expr::Tuple(ref mut exprs, ref mut ty) => {
                let checked_ty = self.expr_tuple(exprs, *ty)?;
                *ty = checked_ty;
                Ok(checked_ty)
            }
            Expr::Constructor {
                ty,
                index,
                ref mut fields,
            } => self.expr_constructor(ty, index, fields),
            Expr::Array {
                ref mut exprs,
                ref mut ty,
            } => self.expr_array(exprs, ty),
            Expr::Get {
                ref mut object,
                object_ty,
                field,
            } => self.expr_get(object, object_ty, field),
            Expr::Set {
                ref mut object,
                ref mut object_ty,
                field,
                ref mut value,
                ref mut value_ty,
            } => self.expr_set(object, object_ty, field, value, value_ty),
            Expr::Call {
                ref mut callee,
                ref mut callee_ty,
                ref mut args,
            } => self.expr_call(callee, callee_ty, args),
            Expr::ContApplication {
                ref mut callee,
                ref mut callee_ty,
                ref mut continuations,
            } => self.expr_cont_application(callee, callee_ty, continuations),
            Expr::Unary {
                op,
                ref mut right,
                ref mut right_ty,
            } => self.expr_unary(op, right, right_ty),
            Expr::Binary {
                ref mut left,
                ref mut left_ty,
                op,
                ref mut right,
                ref mut right_ty,
            } => self.expr_binary(left, left_ty, op, right, right_ty),
            Expr::Declare {
                ident,
                ref mut ty,
                ref mut expr,
            } => self.expr_declare(ident, ty, expr),
            Expr::Assign {
                ident,
                ref mut expr,
            } => self.expr_assign(ident, expr),
            Expr::Match {
                ref mut scrutinee,
                ref mut arms,
            } => self.expr_match(scrutinee, arms),
            Expr::Closure {
                func,
                ref mut captures,
            } => Ok(self.expr_closure(func, captures)),
            Expr::Intrinsic {
                intrinsic,
                ref mut value,
                ref mut value_ty,
            } => self.expr_intrinsic(intrinsic, value, value_ty),
            Expr::Unreachable => Ok(self.program.insert_type(Type::None, self.arena).0),
        }
    }

    fn function(
        &mut self,
        function: &mut Function<'arena>,
        captures: HashMap<'arena, Ident, TypeRef>,
    ) -> Result<()> {
        self.environment = captures;

        for (&param, &ty) in function
            .params
            .iter()
            .map(|(param, ty)| (param, ty))
            .chain(&function.continuations)
        {
            self.environment.insert(param, ty);
        }

        for expr in &mut function.body {
            self.expr(expr)?;
        }

        Ok(())
    }

    fn typeck(mut self) -> Result<()> {
        let functions = collect_into(
            self.program.functions.keys().copied(),
            Vec::new_in(self.arena),
        );

        for func_ref in functions {
            let mut function = self.program.functions.remove(&func_ref).unwrap();
            if !function.captures.is_empty() {
                self.program.functions.insert(func_ref, function);
                continue;
            }

            self.function(&mut function, HashMap::new_in(self.arena))?;

            self.program.functions.insert(func_ref, function);
        }

        for (func_ref, captures) in mem::replace(&mut self.closures, Vec::new_in(self.arena)) {
            let mut function = self.program.functions.remove(&func_ref).unwrap();
            self.function(&mut function, captures)?;
            self.program.functions.insert(func_ref, function);
        }

        Ok(())
    }

    fn new(arena: &'arena Bump, program: &'a mut Program<'arena>) -> TypeCk<'a, 'arena> {
        TypeCk {
            program,
            environment: HashMap::new_in(arena),
            arena,
            closures: Vec::new_in(arena),
        }
    }
}

/// ## Errors
///
/// Returns an error if `program` contains a type error.
pub fn typeck<'arena>(arena: &'arena Bump, program: &mut Program<'arena>) -> Result<()> {
    TypeCk::new(arena, program).typeck()
}
