use std::mem;

use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::UnaryOp;
use crate::high_level_ir::DestructureFields;
use crate::high_level_ir::Expr;
use crate::high_level_ir::ExprArray;
use crate::high_level_ir::ExprAssign;
use crate::high_level_ir::ExprBinary;
use crate::high_level_ir::ExprBlock;
use crate::high_level_ir::ExprCall;
use crate::high_level_ir::ExprClosure;
use crate::high_level_ir::ExprConstructor;
use crate::high_level_ir::ExprConstructorFields;
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
use crate::high_level_ir::UserDefinedType;
use crate::high_level_ir::UserDefinedTypeFields;

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
                HashSet::new_in(arena),
                self_variants.intersection(&other_variants).copied(),
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
                HashSet::new_in(arena),
                self_variants.union(&other_variants),
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
    environment: HashMap<'arena, Ident, &'arena Type<'arena>>,
    arena: &'arena Bump,
    closures: Vec<'arena, (FuncRef, HashMap<'arena, Ident, &'arena Type<'arena>>)>,
}

impl<'a, 'arena> TypeCk<'a, 'arena> {
    fn exprs<'b, I: IntoIterator<Item = &'b mut Expr<'arena>>>(
        &mut self,
        exprs: I,
    ) -> Result<Vec<'arena, &'arena Type<'arena>>>
    where
        'arena: 'b,
    {
        try_collect_into(
            Vec::new_in(self.arena),
            exprs.into_iter().map(|expr| self.expr(expr)),
        )
    }

    fn expr_literal(&mut self, literal: &Literal) -> &'arena Type<'arena> {
        match *literal {
            Literal::Int(_) => self.program.insert_type(Type::Int, self.arena),
            Literal::Float(_) => self.program.insert_type(Type::Float, self.arena),
            Literal::String(_) => self.program.insert_type(Type::String, self.arena),
        }
    }

    fn expr_ident(&self, ident: Ident) -> Result<&'arena Type<'arena>> {
        self.environment
            .get(&ident)
            .copied()
            .ok_or_else(|| format!("cannot find {ident:?}").into())
    }

    fn block(
        &mut self,
        exprs: &mut [Expr<'arena>],
        ty: &'arena Type<'arena>,
    ) -> Result<&'arena Type<'arena>> {
        let Some((tail, block)) = exprs.split_last_mut() else {
            return Ok(self
                .program
                .insert_type(Type::Tuple(Vec::new_in(self.arena)), self.arena));
        };

        for expr in block {
            self.expr(expr)?;
        }

        let block_ty = self.expr(tail)?;
        block_ty.unify(ty, self.program, self.arena)
    }

    fn expr_block(&mut self, expr: &mut ExprBlock<'arena>) -> Result<&'arena Type<'arena>> {
        expr.ty = self.block(&mut expr.exprs, expr.ty)?;
        Ok(expr.ty)
    }

    fn expr_tuple(&mut self, expr: &mut ExprTuple<'arena>) -> Result<&'arena Type<'arena>> {
        let types = self.exprs(&mut expr.exprs)?;
        let result_ty = self.program.insert_type(Type::Tuple(types), self.arena);
        expr.ty = result_ty.unify(expr.ty, self.program, self.arena)?;
        Ok(expr.ty)
    }

    fn expr_constructor(
        &mut self,
        expr: &mut ExprConstructor<'arena>,
    ) -> Result<&'arena Type<'arena>> {
        let ty = expr.ty;
        let user_defined = ty
            .as_user_defined()
            .ok_or_else(|| format!("cannot construct {:?}", expr.ty))?;
        let ty_fields = match (
            &self.program.user_defined_types[&user_defined],
            &expr.variant,
        ) {
            (UserDefinedType::Product(ty_fields), None) => ty_fields,
            (UserDefinedType::Sum(variants), Some(variant)) => variants
                .iter()
                .find(|(name, _)| name == variant)
                .map(|(_, variant)| variant)
                .ok_or_else(|| format!("type {:?} has no variant '{variant}'", expr.ty))?,
            _ => unreachable!(),
        };

        match (&mut expr.fields, ty_fields) {
            (
                ExprConstructorFields::Named(expr_fields),
                UserDefinedTypeFields::Named(ty_fields),
            ) => {
                let mut used_fields = HashSet::new_in(self.arena);
                for (field, expr) in expr_fields {
                    if used_fields.contains(field) {
                        Err(format!("field {field} specified twice"))?;
                    }

                    let (field, ty_field) = ty_fields
                        .iter()
                        .find(|(name, _)| name == field)
                        .ok_or_else(|| format!("type {ty:?} has no field '{field}"))?;
                    self.expr(expr)?.unify(ty_field, self.program, self.arena)?;
                    used_fields.insert(field);
                }
                for (field, _) in ty_fields {
                    if !used_fields.contains(field) {
                        Err(format!("missing field '{field}'"))?;
                    }
                }
            }
            (
                ExprConstructorFields::Anonymous(expr_fields),
                UserDefinedTypeFields::Anonymous(ty_fields),
            ) => {
                let expr_field_tys = self.exprs(expr_fields)?;
                for (expr_ty, field_ty) in expr_field_tys.iter().zip(ty_fields) {
                    expr_ty.unify(field_ty, self.program, self.arena)?;
                }
            }
            (ExprConstructorFields::Unit, UserDefinedTypeFields::Unit) => {}
            _ => Err("incompatible field styles")?,
        }

        Ok(expr.ty)
    }

    fn expr_array(&mut self, expr: &mut ExprArray<'arena>) -> Result<&'arena Type<'arena>> {
        let elem_ty = self
            .exprs(&mut expr.exprs)?
            .into_iter()
            .try_fold(expr.ty, |acc, ty| ty.unify(acc, self.program, self.arena))?;
        expr.element_ty = elem_ty;
        expr.ty = self
            .program
            .insert_type(Type::Array(elem_ty, expr.exprs.len() as u64), self.arena);
        Ok(expr.ty)
    }

    fn expr_get(&mut self, expr: &mut ExprGet<'arena>) -> Result<&'arena Type<'arena>> {
        let found_ty = self.expr(&mut expr.object)?;
        let object_ty = found_ty.unify(expr.object_ty, self.program, self.arena)?;
        let Type::UserDefined(ty) = object_ty else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };
        let UserDefinedType::Product(fields) = self.program.user_defined_types[ty] else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };

        Ok(fields
            .get(&expr.field)
            .ok_or_else(|| format!("{object_ty:?} has no field '{}'", expr.field))?)
    }

    fn expr_set(&mut self, expr: &mut ExprSet<'arena>) -> Result<&'arena Type<'arena>> {
        let found_ty = self.expr(&mut expr.object)?;
        let ty = found_ty.unify(expr.object_ty, self.program, self.arena)?;
        expr.object_ty = ty;

        let Type::UserDefined(object_ty) = ty else {
            Err(format!("cannot take field of {ty:?}"))?
        };
        let UserDefinedType::Product(fields) = self.program.user_defined_types[object_ty] else {
            Err(format!("cannot take field of {ty:?}"))?
        };

        let field_ty = fields
            .get(&expr.field)
            .ok_or_else(|| format!("{object_ty:?} has no field '{}'", expr.field))?;

        let ty = self.expr(&mut expr.value)?;
        let ty = ty.unify(field_ty, self.program, self.arena)?;
        expr.value_ty = ty;
        Ok(ty)
    }

    fn expr_call(&mut self, expr: &mut ExprCall<'arena>) -> Result<&'arena Type<'arena>> {
        let ty = self.expr(&mut expr.callee)?;
        let ty = ty.unify(expr.callee_ty, self.program, self.arena)?;
        expr.callee_ty = ty;
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
            arg.unify(param, self.program, self.arena)?;
        }

        Ok(self.program.insert_type(Type::None, self.arena))
    }

    fn expr_cont_application(
        &mut self,
        expr: &mut ExprContApplication<'arena>,
    ) -> Result<&'arena Type<'arena>> {
        let ty = self.expr(&mut expr.callee)?;
        let ty = ty.unify(expr.callee_ty, self.program, self.arena)?;
        expr.callee_ty = ty;
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
            let expected = ty_continuations
                .remove(ident)
                .ok_or_else(|| format!("no such continuation {ident:?}"))?;
            cont.unify(expected, self.program, self.arena)?;
        }

        let ty = Type::function(params.clone(), ty_continuations);
        expr.result_ty = self.program.insert_type(ty, self.arena);
        Ok(expr.result_ty)
    }

    fn expr_unary(&mut self, expr: &mut ExprUnary<'arena>) -> Result<&'arena Type<'arena>> {
        let right = self.expr(&mut expr.right)?;
        let right = right.unify(expr.right_ty, self.program, self.arena)?;
        expr.right_ty = right;
        match (expr.op, right) {
            (UnaryOp::Neg, Type::Int | Type::Float) | (UnaryOp::Not, Type::Bool) => Ok(right),
            _ => Err(format!("invalid use of {:?}", expr.op))?,
        }
    }

    fn expr_binary(&mut self, expr: &mut ExprBinary<'arena>) -> Result<&'arena Type<'arena>> {
        let left = self.expr(&mut expr.left)?;
        let left = left.unify(expr.left_ty, self.program, self.arena)?;
        expr.left_ty = left;

        let right = self.expr(&mut expr.right)?;
        let right = right.unify(expr.right_ty, self.program, self.arena)?;
        expr.right_ty = right;

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
            ) if l == r => Ok(self.program.insert_type(Type::Bool, self.arena)),
            (l, BinaryOp::Eq | BinaryOp::Ne, r) if l == r => {
                Ok(self.program.insert_type(Type::Bool, self.arena))
            }
            _ => Err(format!(
                "cannot apply {:?} to {:?} and {:?}",
                expr.op, expr.left_ty, expr.right_ty
            )
            .into()),
        }
    }

    fn expr_declare(&mut self, expr: &mut ExprDeclare<'arena>) -> Result<&'arena Type<'arena>> {
        let expr_ty = self.expr(&mut expr.expr)?;
        let expr_ty = expr_ty.unify(expr.ty, self.program, self.arena)?;
        expr.ty = expr_ty;
        self.environment.insert(expr.ident, expr.ty);
        Ok(expr.ty)
    }

    fn expr_assign(&mut self, expr: &mut ExprAssign<'arena>) -> Result<&'arena Type<'arena>> {
        let expected = *self.environment.get(&expr.ident).unwrap();
        let ty = self.expr(&mut expr.expr)?;
        ty.unify(expected, self.program, self.arena)
    }

    fn pattern(
        &mut self,
        expr_ty: &'arena Type<'arena>,
        pattern: &Pattern<'arena>,
    ) -> Result<Exhaustive<'arena>> {
        match *pattern {
            Pattern::Wildcard => Ok(Exhaustive::Exhaustive),
            Pattern::Ident(ident) => {
                self.environment.insert(ident, expr_ty);
                Ok(Exhaustive::Exhaustive)
            }
            Pattern::Destructure {
                ty,
                ref variant,
                ref fields,
            } => {
                let ty = expr_ty.unify(ty, self.program, self.arena)?;
                let user_defined = &self.program.user_defined_types[&ty.as_user_defined().unwrap()];
                let field_tys = match (user_defined, variant) {
                    (UserDefinedType::Product(fields), None) => fields,
                    (UserDefinedType::Sum(variants), Some(variant)) => variants
                        .iter()
                        .find(|(name, _)| name == variant)
                        .map(|(_, variant)| variant)
                        .ok_or_else(|| format!("{ty:?} has no variant '{variant}'"))?,
                    (UserDefinedType::Product(_), Some(variant)) => {
                        Err(format!("{ty:?} has no variant '{variant}'"))?
                    }
                    (UserDefinedType::Sum(_), None) => Err(format!("{ty:?} does not have fields"))?,
                };

                let exhaustive = match (fields, field_tys) {
                    (DestructureFields::Named(fields), UserDefinedTypeFields::Named(field_tys)) => {
                        let mut used_fields = HashSet::new_in(self.arena);
                        let mut exhaustive = Exhaustive::Exhaustive;
                        for (field, pat) in fields {
                            let (_, field_ty) = field_tys
                                .iter()
                                .find(|(name, _)| name == field)
                                .ok_or_else(|| format!("type {ty:?} has no field '{field}'"))?;
                            exhaustive = self
                                .pattern(field_ty, pat)?
                                .finalise()
                                .intersect(exhaustive, self.arena);
                            used_fields.insert(field);
                        }
                        for (field, _) in field_tys {
                            if !used_fields.contains(field) {
                                Err(format!("missing field '{field}'"))?;
                            }
                        }
                        exhaustive
                    }
                    (
                        DestructureFields::Anonymous(fields),
                        UserDefinedTypeFields::Anonymous(field_tys),
                    ) => fields.iter().zip(field_tys).try_fold(
                        Exhaustive::Exhaustive,
                        |acc, (pat, &field_ty)| {
                            Result::Ok(
                                self.pattern(field_ty, pat)?
                                    .finalise()
                                    .intersect(acc, self.arena),
                            )
                        },
                    )?,
                    (DestructureFields::Unit, UserDefinedTypeFields::Unit) => {
                        Exhaustive::Exhaustive
                    }
                    _ => return Err("mismatched field types".into()),
                };

                match (variant, exhaustive) {
                    (Some(variant), Exhaustive::Exhaustive) => {
                        let user_defined =
                            &self.program.user_defined_types[&ty.as_user_defined().unwrap()];
                        let variants = user_defined.as_sum().unwrap();
                        let (variant, _) = variants
                            .iter()
                            .enumerate()
                            .find(|(_, (name, _))| name == variant)
                            .unwrap();
                        let mut found_variants = HashSet::with_capacity_in(1, self.arena);
                        found_variants.insert(variant);
                        Ok(Exhaustive::ExhaustiveVariants(found_variants))
                    }
                    (None, Exhaustive::Exhaustive) => Ok(Exhaustive::Exhaustive),
                    _ => Ok(Exhaustive::NonExhaustive),
                }
            }
        }
    }

    fn expr_match(&mut self, expr: &mut ExprMatch<'arena>) -> Result<&'arena Type<'arena>> {
        let expr_ty = self.expr(&mut expr.scrutinee)?;
        expr.scrutinee_ty = expr_ty;
        let mut exhaustive = Exhaustive::Exhaustive;
        let mut output_ty = self.program.insert_type(Type::Unknown, self.arena);
        for (pat, expr) in &mut expr.arms {
            exhaustive = exhaustive.union(self.pattern(expr_ty, pat)?, self.arena);
            let expr_ty = self.expr(expr)?;
            output_ty = expr_ty.unify(output_ty, self.program, self.arena)?;
        }
        expr.ty = output_ty;
        Ok(expr.ty)
    }

    fn expr_closure(&mut self, expr: &mut ExprClosure<'arena>) -> &'arena Type<'arena> {
        let actual_func = self.program.functions.get(&expr.func).unwrap();
        let new_captures = collect_into(
            HashMap::new_in(self.arena),
            actual_func
                .captures
                .iter()
                .map(|&ident| (ident, self.environment[&ident])),
        );
        {
            let mut captures = HashMap::new_in(self.arena);
            captures.clone_from(&new_captures);
            self.closures.push((expr.func, captures));
        }
        expr.captures = Some(new_captures);
        self.program.signatures[&expr.func]
    }

    fn expr_intrinsic(&mut self, expr: &mut ExprIntrinsic<'arena>) -> Result<&'arena Type<'arena>> {
        let ty = self.expr(&mut expr.value)?;
        let ty = ty.unify(expr.value_ty, self.program, self.arena)?;
        expr.value_ty = ty;
        match expr.intrinsic {
            Intrinsic::Discriminant => Ok(self.program.insert_type(Type::Int, self.arena)),
            Intrinsic::Terminate | Intrinsic::Unreachable => {
                Ok(self.program.insert_type(Type::None, self.arena))
            }
        }
    }

    fn expr(&mut self, expr: &mut Expr<'arena>) -> Result<&'arena Type<'arena>> {
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
        }
    }

    fn function(
        &mut self,
        function: &mut Function<'arena>,
        captures: HashMap<'arena, Ident, &'arena Type<'arena>>,
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

        let ty_none = self.program.insert_type(Type::None, self.arena);
        self.block(&mut function.body, ty_none)?;

        Ok(())
    }

    fn typeck(mut self) -> Result<()> {
        let functions = collect_into(
            Vec::new_in(self.arena),
            self.program.functions.keys().copied(),
        );

        for &func_ref in &functions {
            let function = &self.program.functions[&func_ref];
            let params = collect_into(
                Vec::new_in(self.arena),
                function.params.iter().map(|(_, ty)| *ty),
            );
            let continuations = collect_into(
                HashMap::new_in(self.arena),
                function.continuations.iter().map(|(&name, &ty)| (name, ty)),
            );
            let ty = self
                .program
                .insert_type(Type::function(params, continuations), self.arena);
            self.program.signatures.insert(func_ref, ty);
        }

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
