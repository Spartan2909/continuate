use std::mem;

use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::common::UnaryOp;
use crate::high_level_ir::Expr;
use crate::high_level_ir::ExprArray;
use crate::high_level_ir::ExprAssign;
use crate::high_level_ir::ExprBinary;
use crate::high_level_ir::ExprBlock;
use crate::high_level_ir::ExprCall;
use crate::high_level_ir::ExprClosure;
use crate::high_level_ir::ExprConstructor;
use crate::high_level_ir::ExprContApplication;
use crate::high_level_ir::ExprDeclare;
use crate::high_level_ir::ExprGet;
use crate::high_level_ir::ExprIntrinsic;
use crate::high_level_ir::ExprMatch;
use crate::high_level_ir::ExprSet;
use crate::high_level_ir::ExprTuple;
use crate::high_level_ir::ExprUnary;
use crate::high_level_ir::Function;
use crate::high_level_ir::FunctionTy;
use crate::high_level_ir::Pattern;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;
use crate::high_level_ir::TypeConstructor;
use crate::high_level_ir::UserDefinedType;

use bumpalo::Bump;

use continuate_error::Result;

use continuate_utils::collect_into;
use continuate_utils::try_collect_into;
use continuate_utils::HashMap;
use continuate_utils::HashSet;
use continuate_utils::Vec;

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

    fn block(&mut self, exprs: &mut [Expr<'arena>], ty: TypeRef) -> Result<TypeRef> {
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

    fn expr_block(&mut self, expr: &mut ExprBlock<'arena>) -> Result<TypeRef> {
        expr.ty = self.block(&mut expr.exprs, expr.ty)?;
        Ok(expr.ty)
    }

    fn expr_tuple(&mut self, expr: &mut ExprTuple<'arena>) -> Result<TypeRef> {
        let types = self.exprs(&mut expr.exprs)?;
        let result_ty = self.program.insert_type(Type::Tuple(types), self.arena).1;
        let ty = self.program.types.get_by_left(&expr.ty).unwrap();
        let result_ty = result_ty.unify(ty, self.program, self.arena)?;
        expr.ty = *self.program.types.get_by_right(result_ty).unwrap();
        Ok(expr.ty)
    }

    fn expr_constructor(&mut self, expr: &mut ExprConstructor<'arena>) -> Result<TypeRef> {
        let fields = self.exprs(&mut expr.fields)?;
        let user_defined = self.program.types.get_by_left(&expr.ty).unwrap();
        let user_defined = user_defined
            .as_user_defined()
            .ok_or_else(|| format!("cannot construct {user_defined:?}"))?;
        let ty_fields = match (&user_defined.constructor, expr.index) {
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

        Ok(expr.ty)
    }

    fn expr_array(&mut self, expr: &mut ExprArray<'arena>) -> Result<TypeRef> {
        let elem_ty = self
            .exprs(&mut expr.exprs)?
            .into_iter()
            .try_fold(expr.ty, |acc, ty| {
                let acc = self.program.types.get_by_left(&acc).unwrap();
                let ty = self.program.types.get_by_left(&ty).unwrap();
                let ty = ty.unify(acc, self.program, self.arena)?;
                Result::Ok(*self.program.types.get_by_right(ty).unwrap())
            })?;
        expr.element_ty = elem_ty;
        expr.ty = self
            .program
            .insert_type(Type::Array(elem_ty, expr.exprs.len() as u64), self.arena)
            .0;
        Ok(expr.ty)
    }

    fn expr_get(&mut self, expr: &mut ExprGet<'arena>) -> Result<TypeRef> {
        let object_ty = *self.program.types.get_by_left(&expr.object_ty).unwrap();
        let found_ty = self.expr(&mut expr.object)?;
        let found_ty = self.program.types.get_by_left(&found_ty).unwrap();
        let object_ty = found_ty.unify(object_ty, self.program, self.arena)?;
        let Type::UserDefined(UserDefinedType {
            constructor: TypeConstructor::Product(fields),
        }) = object_ty
        else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };

        Ok(fields[expr.field])
    }

    fn expr_set(&mut self, expr: &mut ExprSet<'arena>) -> Result<TypeRef> {
        let ty = *self.program.types.get_by_left(&expr.object_ty).unwrap();
        let found_ty = self.expr(&mut expr.object)?;
        let found_ty = self.program.types.get_by_left(&found_ty).unwrap();
        let ty = found_ty.unify(ty, self.program, self.arena)?;
        expr.object_ty = *self.program.types.get_by_right(ty).unwrap();

        let Type::UserDefined(UserDefinedType {
            constructor: TypeConstructor::Product(fields),
        }) = ty
        else {
            Err(format!("cannot take field of {:?}", expr.object_ty))?
        };

        let field_ty = fields[expr.field];
        let field_ty = *self.program.types.get_by_left(&field_ty).unwrap();

        let ty = self.expr(&mut expr.value)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let ty = ty.unify(field_ty, self.program, self.arena)?;
        let ty = *self.program.types.get_by_right(ty).unwrap();
        expr.value_ty = ty;
        Ok(ty)
    }

    fn expr_call(&mut self, expr: &mut ExprCall<'arena>) -> Result<TypeRef> {
        let ty = self.expr(&mut expr.callee)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let expected_ty = self.program.types.get_by_left(&expr.callee_ty).unwrap();
        let ty = ty.unify(expected_ty, self.program, self.arena)?;
        expr.callee_ty = *self.program.types.get_by_right(ty).unwrap();
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

        if expr.args.len() != params.len() {
            Err(format!(
                "incorrect number of arguments (expected {}, got {})",
                params.len(),
                expr.args.len()
            ))?;
        }

        for (param, arg) in params.iter().zip(&mut expr.args) {
            let arg = self.expr(arg)?;
            let arg = self.program.types.get_by_left(&arg).unwrap();
            let param = self.program.types.get_by_left(param).unwrap();
            arg.unify(param, self.program, self.arena)?;
        }

        Ok(self.program.insert_type(Type::None, self.arena).0)
    }

    fn expr_cont_application(&mut self, expr: &mut ExprContApplication<'arena>) -> Result<TypeRef> {
        let ty = self.expr(&mut expr.callee)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let expected_ty = self.program.types.get_by_left(&expr.callee_ty).unwrap();
        let ty = ty.unify(expected_ty, self.program, self.arena)?;
        expr.callee_ty = *self.program.types.get_by_right(ty).unwrap();
        let Type::Function(FunctionTy {
            params,
            continuations: ty_continuations,
        }) = ty
        else {
            Err("{ty:?} is not a function")?
        };

        let mut ty_continuations = ty_continuations.clone();
        for (ident, cont) in &mut expr.continuations {
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

    fn expr_unary(&mut self, expr: &mut ExprUnary<'arena>) -> Result<TypeRef> {
        let expected = *self.program.types.get_by_left(&expr.right_ty).unwrap();
        let right = self.expr(&mut expr.right)?;
        let right = self.program.types.get_by_left(&right).unwrap();
        let right = right.unify(expected, self.program, self.arena)?;
        let right_ref = *self.program.types.get_by_right(right).unwrap();
        expr.right_ty = right_ref;
        match (expr.op, right) {
            (UnaryOp::Neg, Type::Int | Type::Float) => Ok(right_ref),
            (UnaryOp::Not, _) if right_ref == self.program.lib_std().ty_bool => Ok(right_ref),
            _ => Err(format!("invalid use of {:?}", expr.op))?,
        }
    }

    fn expr_binary(&mut self, expr: &mut ExprBinary<'arena>) -> Result<TypeRef> {
        let expected = *self.program.types.get_by_left(&expr.left_ty).unwrap();
        let left = self.expr(&mut expr.left)?;
        let left = self.program.types.get_by_left(&left).unwrap();
        let left = left.unify(expected, self.program, self.arena)?;
        expr.left_ty = *self.program.types.get_by_right(left).unwrap();

        let expected = *self.program.types.get_by_left(&expr.right_ty).unwrap();
        let right = self.expr(&mut expr.right)?;
        let right = self.program.types.get_by_left(&right).unwrap();
        let right = right.unify(expected, self.program, self.arena)?;
        expr.right_ty = *self.program.types.get_by_right(right).unwrap();

        match (left, expr.op, right) {
            (
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Add,
                r @ (Type::Int | Type::Float | Type::String),
            )
            | (
                l @ (Type::Int | Type::Float),
                BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem,
                r @ (Type::Int | Type::Float),
            ) if l == r => Ok(expr.left_ty),
            (
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
                r @ (Type::Int | Type::Float | Type::String),
            ) if l == r => Ok(self.program.lib_std().ty_bool),
            (l, BinaryOp::Eq | BinaryOp::Ne, r) if l == r => Ok(self.program.lib_std().ty_bool),
            _ => Err(format!(
                "cannot apply {:?} to {:?} and {:?}",
                expr.op, expr.left_ty, expr.right_ty
            )
            .into()),
        }
    }

    fn expr_declare(&mut self, expr: &mut ExprDeclare<'arena>) -> Result<TypeRef> {
        let expr_ty = self.expr(&mut expr.expr)?;
        let expr_ty = self.program.types.get_by_left(&expr_ty).unwrap();
        let expected = self.program.types.get_by_left(&expr.ty).unwrap();
        let expr_ty = expr_ty.unify(expected, self.program, self.arena)?;
        expr.ty = *self.program.types.get_by_right(expr_ty).unwrap();
        self.environment.insert(expr.ident, expr.ty);
        Ok(expr.ty)
    }

    fn expr_assign(&mut self, expr: &mut ExprAssign<'arena>) -> Result<TypeRef> {
        let expected = self.environment.get(&expr.ident).unwrap();
        let expected = *self.program.types.get_by_left(expected).unwrap();
        let ty = self.expr(&mut expr.expr)?;
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

    fn expr_match(&mut self, expr: &mut ExprMatch<'arena>) -> Result<TypeRef> {
        let expr_ty = self.expr(&mut expr.scrutinee)?;
        expr.scrutinee_ty = expr_ty;
        let mut exhaustive = Exhaustive::Exhaustive;
        let mut output_ty = self.program.insert_type(Type::Unknown, self.arena).1;
        for (pat, expr) in &mut expr.arms {
            exhaustive = exhaustive.union(self.pattern(expr_ty, pat)?, self.arena);
            let expr_ty = self.expr(expr)?;
            let expr_ty = self.program.types.get_by_left(&expr_ty).unwrap();
            output_ty = expr_ty.unify(output_ty, self.program, self.arena)?;
        }
        expr.ty = *self.program.types.get_by_right(output_ty).unwrap();
        Ok(expr.ty)
    }

    fn expr_closure(&mut self, expr: &mut ExprClosure<'arena>) -> TypeRef {
        let actual_func = self.program.functions.get(&expr.func).unwrap();
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
            self.closures.push((expr.func, captures));
        }
        expr.captures = Some(new_captures);
        self.program.signatures[&expr.func]
    }

    fn expr_intrinsic(&mut self, expr: &mut ExprIntrinsic<'arena>) -> Result<TypeRef> {
        let ty = self.expr(&mut expr.value)?;
        let ty = self.program.types.get_by_left(&ty).unwrap();
        let expected = self.program.types.get_by_left(&expr.value_ty).unwrap();
        let ty = ty.unify(expected, self.program, self.arena)?;
        expr.value_ty = *self.program.types.get_by_right(ty).unwrap();
        match expr.intrinsic {
            Intrinsic::Discriminant => Ok(self.program.lib_std().ty_int),
            Intrinsic::Terminate => Ok(self.program.insert_type(Type::None, self.arena).0),
        }
    }

    fn expr(&mut self, expr: &mut Expr<'arena>) -> Result<TypeRef> {
        match expr {
            Expr::Literal(literal) => Ok(self.expr_literal(literal)),
            Expr::Ident(ident) => self.expr_ident(*ident),
            Expr::Function(func_ref) => Ok(self.program.signatures[func_ref]),
            Expr::Block(expr) => {
                let checked_ty = self.expr_block(expr)?;
                expr.ty = checked_ty;
                Ok(checked_ty)
            }
            Expr::Tuple(expr) => {
                let checked_ty = self.expr_tuple(expr)?;
                expr.ty = checked_ty;
                Ok(checked_ty)
            }
            Expr::Constructor(expr) => self.expr_constructor(expr),
            Expr::Array(expr) => self.expr_array(expr),
            Expr::Get(expr) => self.expr_get(expr),
            Expr::Set(expr) => self.expr_set(expr),
            Expr::Call(expr) => self.expr_call(expr),
            Expr::ContApplication(expr) => self.expr_cont_application(expr),
            Expr::Unary(expr) => self.expr_unary(expr),
            Expr::Binary(expr) => self.expr_binary(expr),
            Expr::Declare(expr) => self.expr_declare(expr),
            Expr::Assign(expr) => self.expr_assign(expr),
            Expr::Match(expr) => self.expr_match(expr),
            Expr::Closure(expr) => Ok(self.expr_closure(expr)),
            Expr::Intrinsic(expr) => self.expr_intrinsic(expr),
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

        let ty_none = self.program.insert_type(Type::None, self.arena).0;
        self.block(&mut function.body, ty_none)?;

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
