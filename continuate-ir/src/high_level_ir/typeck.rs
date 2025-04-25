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
use crate::high_level_ir::Typed;
use crate::high_level_ir::TypedExpr;
use crate::high_level_ir::TypedExprArray;
use crate::high_level_ir::TypedExprAssign;
use crate::high_level_ir::TypedExprBinary;
use crate::high_level_ir::TypedExprBlock;
use crate::high_level_ir::TypedExprCall;
use crate::high_level_ir::TypedExprClosure;
use crate::high_level_ir::TypedExprConstructor;
use crate::high_level_ir::TypedExprConstructorFields;
use crate::high_level_ir::TypedExprContApplication;
use crate::high_level_ir::TypedExprDeclare;
use crate::high_level_ir::TypedExprGet;
use crate::high_level_ir::TypedExprIntrinsic;
use crate::high_level_ir::TypedExprMatch;
use crate::high_level_ir::TypedExprSet;
use crate::high_level_ir::TypedExprTuple;
use crate::high_level_ir::TypedExprUnary;
use crate::high_level_ir::UserDefinedType;
use crate::high_level_ir::UserDefinedTypeFields;

use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use continuate_error::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)]
enum Exhaustive {
    Exhaustive,
    ExhaustiveVariants(HashSet<usize>),
    NonExhaustive,
}

impl Exhaustive {
    fn finalise(self, num_variants: Option<usize>) -> Exhaustive {
        match (self, num_variants) {
            (Exhaustive::Exhaustive, _) => Exhaustive::Exhaustive,
            (Exhaustive::ExhaustiveVariants(variants), Some(num_variants))
                if variants.len() == num_variants =>
            {
                Exhaustive::Exhaustive
            }
            _ => Exhaustive::NonExhaustive,
        }
    }

    fn intersect(self, other: Exhaustive) -> Exhaustive {
        match (self, other) {
            (Exhaustive::Exhaustive, Exhaustive::Exhaustive) => Exhaustive::Exhaustive,
            (Exhaustive::Exhaustive, Exhaustive::ExhaustiveVariants(variants))
            | (Exhaustive::ExhaustiveVariants(variants), Exhaustive::Exhaustive) => {
                Exhaustive::ExhaustiveVariants(variants)
            }
            (
                Exhaustive::ExhaustiveVariants(self_variants),
                Exhaustive::ExhaustiveVariants(other_variants),
            ) => Exhaustive::ExhaustiveVariants(
                self_variants
                    .intersection(&other_variants)
                    .copied()
                    .collect(),
            ),
            _ => Exhaustive::NonExhaustive,
        }
    }

    fn union(self, other: Exhaustive) -> Exhaustive {
        match (self, other) {
            (Exhaustive::Exhaustive, _) | (_, Exhaustive::Exhaustive) => Exhaustive::Exhaustive,
            (
                Exhaustive::ExhaustiveVariants(self_variants),
                Exhaustive::ExhaustiveVariants(other_variants),
            ) => Exhaustive::ExhaustiveVariants(
                self_variants.union(&other_variants).copied().collect(),
            ),
            (Exhaustive::ExhaustiveVariants(variants), Exhaustive::NonExhaustive)
            | (Exhaustive::NonExhaustive, Exhaustive::ExhaustiveVariants(variants)) => {
                Exhaustive::ExhaustiveVariants(variants)
            }
            (Exhaustive::NonExhaustive, Exhaustive::NonExhaustive) => Exhaustive::NonExhaustive,
        }
    }
}

struct TypeCk<'a> {
    program: &'a Program<Expr>,
    typed_program: Program<TypedExpr>,
    environment: HashMap<Ident, Rc<Type>>,
    closures: Vec<(FuncRef, HashMap<Ident, Rc<Type>>)>,
}

impl<'a> TypeCk<'a> {
    fn exprs<'b, I: IntoIterator<Item = &'b Expr>>(
        &mut self,
        exprs: I,
    ) -> Result<Vec<Typed<TypedExpr>>> {
        exprs.into_iter().map(|expr| self.expr(expr)).collect()
    }

    fn expr_literal(&mut self, literal: Literal) -> Typed<TypedExpr> {
        let ty = match literal {
            Literal::Int(_) => self.typed_program.insert_type(Type::Int),
            Literal::Float(_) => self.typed_program.insert_type(Type::Float),
            Literal::String(_) => self.typed_program.insert_type(Type::String),
        };
        Typed::new(TypedExpr::Literal(literal), ty)
    }

    fn expr_ident(&self, ident: Ident) -> Result<Typed<TypedExpr>> {
        let ty = self
            .environment
            .get(&ident)
            .cloned()
            .ok_or_else(|| format!("cannot find {ident:?}"))?;
        Ok(Typed::new(TypedExpr::Ident(ident), ty))
    }

    fn expr_function(&self, func_ref: FuncRef) -> Typed<TypedExpr> {
        let ty = Rc::clone(&self.typed_program.signatures[&func_ref]);
        Typed::new(TypedExpr::Function(func_ref), ty)
    }

    fn block(&mut self, exprs: &[Expr]) -> Result<Typed<Vec<TypedExpr>>> {
        let Some((tail, block)) = exprs.split_last() else {
            let ty = self.typed_program.insert_type(Type::Tuple(Vec::new()));
            return Ok(Typed::new(vec![], Rc::clone(&ty)));
        };

        let block: Result<Vec<_>> = block
            .iter()
            .map(|expr| Ok(self.expr(expr)?.value))
            .collect();
        let mut block = block?;

        let tail = self.expr(tail)?;
        block.push(tail.value);
        Ok(Typed::new(block, tail.ty))
    }

    fn expr_block(&mut self, expr: &ExprBlock) -> Result<Typed<TypedExpr>> {
        self.block(&expr.exprs).map(|exprs| {
            Typed::new(
                TypedExpr::Block(Typed::new(
                    TypedExprBlock { exprs: exprs.value },
                    Rc::clone(&exprs.ty),
                )),
                exprs.ty,
            )
        })
    }

    fn expr_tuple(&mut self, expr: &ExprTuple) -> Result<Typed<TypedExpr>> {
        let exprs = self.exprs(&expr.exprs)?;
        let ty = self.typed_program.insert_type(Type::Tuple(
            exprs.iter().map(|expr| Rc::clone(&expr.ty)).collect(),
        ));
        Ok(Typed::new(
            TypedExpr::Tuple(Typed::new(
                TypedExprTuple {
                    exprs: exprs.into_iter().map(|expr| expr.value).collect(),
                },
                Rc::clone(&ty),
            )),
            ty,
        ))
    }

    fn expr_constructor(&mut self, expr: &ExprConstructor) -> Result<Typed<TypedExpr>> {
        let ty = Rc::clone(&expr.ty);
        let user_defined = ty
            .as_user_defined()
            .ok_or_else(|| format!("cannot construct {:?}", expr.ty))?;
        let ty_fields = match (
            &*self.program.user_defined_types[&user_defined],
            &expr.variant,
        ) {
            (UserDefinedType::Product(ty_fields), None) => ty_fields.clone(),
            (UserDefinedType::Sum(variants), Some(variant)) => variants
                .iter()
                .find(|(name, _)| name == variant)
                .map(|(_, variant)| variant.clone())
                .ok_or_else(|| format!("type {:?} has no variant '{variant}'", expr.ty))?,
            _ => unreachable!(),
        };

        let fields = match (&expr.fields, ty_fields) {
            (
                ExprConstructorFields::Named(expr_fields),
                UserDefinedTypeFields::Named(ty_fields),
            ) => {
                let mut fields = Vec::new();
                for (field, expr) in expr_fields {
                    if fields.iter().any(|(f, _)| f == field) {
                        Err(format!("field {field} specified twice"))?;
                    }

                    let (field, ty_field) = ty_fields
                        .iter()
                        .find(|(name, _)| name == field)
                        .ok_or_else(|| format!("type {ty:?} has no field '{field}"))?;
                    let ty_field = Rc::clone(ty_field);
                    let expr = self.expr(expr)?;
                    expr.ty.unify(&ty_field, &mut self.typed_program)?;
                    fields.push((field.clone(), expr.value));
                }
                for (field, _) in &ty_fields {
                    if !fields.iter().any(|(f, _)| f == field) {
                        Err(format!("missing field '{field}'"))?;
                    }
                }
                TypedExprConstructorFields::Named(fields)
            }
            (
                ExprConstructorFields::Anonymous(expr_fields),
                UserDefinedTypeFields::Anonymous(ty_fields),
            ) => {
                let expr_fields = self.exprs(expr_fields)?;
                if expr_fields.len() != ty_fields.len() {
                    Err("incorrect number of fields")?;
                }
                for (expr, field_ty) in expr_fields.iter().zip(ty_fields) {
                    expr.ty.unify(&field_ty, &mut self.typed_program)?;
                }
                TypedExprConstructorFields::Anonymous(
                    expr_fields.into_iter().map(|expr| expr.value).collect(),
                )
            }
            (ExprConstructorFields::Unit, UserDefinedTypeFields::Unit) => {
                TypedExprConstructorFields::Unit
            }
            _ => Err("incompatible field styles")?,
        };

        let expr = TypedExprConstructor {
            ty: Rc::clone(&ty),
            variant: expr.variant.clone(),
            fields,
        };

        Ok(Typed::new(TypedExpr::Constructor(expr), ty))
    }

    fn expr_array(&mut self, expr: &ExprArray) -> Result<Typed<TypedExpr>> {
        let exprs = self.exprs(&expr.exprs)?;
        let element_ty = exprs
            .iter()
            .try_fold(self.typed_program.insert_type(Type::Unknown), |acc, val| {
                val.ty.unify(&acc, &mut self.typed_program)
            })?;
        let ty = self
            .typed_program
            .insert_type(Type::Array(Rc::clone(&element_ty), exprs.len() as u64));
        let expr = TypedExpr::Array(TypedExprArray {
            exprs: exprs.into_iter().map(|expr| expr.value).collect(),
            element_ty,
        });
        Ok(Typed::new(expr, ty))
    }

    fn expr_get(&mut self, expr: &ExprGet) -> Result<Typed<TypedExpr>> {
        let (object, object_ty) = self.expr(&expr.object)?.into_value_ty();
        let Type::UserDefined(ty) = *object_ty else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };
        let UserDefinedType::Product(fields) = &*self.program.user_defined_types[&ty] else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };

        let field_ty = fields
            .get(&expr.field)
            .cloned()
            .ok_or_else(|| format!("{object_ty:?} has no field '{}'", &expr.field))?;
        let expr = TypedExpr::Get(TypedExprGet {
            object: Typed::new(Box::new(object), object_ty),
            field: expr.field.clone(),
        });

        Ok(Typed::new(expr, field_ty))
    }

    fn expr_set(&mut self, expr: &ExprSet) -> Result<Typed<TypedExpr>> {
        let (object, object_ty) = self.expr(&expr.object)?.into_value_ty();

        let Type::UserDefined(ty) = &*object_ty else {
            Err(format!("cannot take field of {object_ty:?}"))?
        };
        let UserDefinedType::Product(fields) = &*self.program.user_defined_types[ty] else {
            Err(format!("cannot take field of {ty:?}"))?
        };

        let field_ty = fields
            .get(&expr.field)
            .cloned()
            .ok_or_else(|| format!("{object_ty:?} has no field '{}'", expr.field))?;

        let (value, value_ty) = self.expr(&expr.value)?.into_value_ty();

        value_ty.unify(&field_ty, &mut self.typed_program)?;

        let expr = TypedExpr::Set(TypedExprSet {
            object: Typed::new(Box::new(object), object_ty),
            field: expr.field.clone(),
            value: Typed::new(Box::new(value), Rc::clone(&value_ty)),
        });
        Ok(Typed::new(expr, value_ty))
    }

    fn expr_call(&mut self, expr: &ExprCall) -> Result<Typed<TypedExpr>> {
        let callee = self.expr(&expr.callee)?;
        let Type::Function(FunctionTy {
            params,
            continuations,
        }) = &*callee.ty
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

        let args: Result<Vec<_>> = params
            .iter()
            .zip(&expr.args)
            .map(|(param, arg)| {
                let arg = self.expr(arg)?;
                arg.ty.unify(param, &mut self.typed_program)?;
                Ok(arg.value)
            })
            .collect();

        let expr = TypedExprCall {
            callee: Typed::boxed(callee),
            args: args?,
        };

        Ok(Typed::new(
            TypedExpr::Call(expr),
            self.typed_program.insert_type(Type::None),
        ))
    }

    fn expr_cont_application(&mut self, expr: &ExprContApplication) -> Result<Typed<TypedExpr>> {
        let callee = self.expr(&expr.callee)?;
        let Type::Function(FunctionTy {
            params,
            continuations: ty_continuations,
        }) = &*callee.ty
        else {
            Err("{ty:?} is not a function")?
        };

        let mut ty_continuations = ty_continuations.clone();
        let mut continuations = Vec::with_capacity(expr.continuations.len());
        for (ident, cont) in &expr.continuations {
            let cont = self.expr(cont)?;
            let expected = ty_continuations
                .remove(ident)
                .ok_or_else(|| format!("no such continuation {ident:?}"))?;
            cont.ty.unify(&expected, &mut self.typed_program)?;
            continuations.push((*ident, cont.value));
        }

        let ty = Type::function(params.clone(), ty_continuations);
        let ty = self.typed_program.insert_type(ty);
        let expr = Typed::new(
            TypedExprContApplication {
                callee: Typed::boxed(callee),
                continuations,
            },
            Rc::clone(&ty),
        );
        Ok(Typed::new(TypedExpr::ContApplication(expr), ty))
    }

    fn expr_unary(&mut self, expr: &ExprUnary) -> Result<Typed<TypedExpr>> {
        let right = self.expr(&expr.right)?;
        let ty = match (expr.op, &*right.ty) {
            (UnaryOp::Neg, Type::Int | Type::Float) | (UnaryOp::Not, Type::Bool) => {
                Result::Ok(Rc::clone(&right.ty))
            }
            _ => Err(format!("invalid use of {:?}", expr.op))?,
        }?;
        let expr = TypedExprUnary {
            op: expr.op,
            right: Typed::boxed(right),
        };
        Ok(Typed::new(TypedExpr::Unary(expr), ty))
    }

    fn expr_binary(&mut self, expr: &ExprBinary) -> Result<Typed<TypedExpr>> {
        let left = self.expr(&expr.left)?;

        let right = self.expr(&expr.right)?;

        let ty = match (&*left.ty, expr.op, &*right.ty) {
            (
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Add,
                r @ (Type::Int | Type::Float | Type::String),
            )
            | (
                l @ (Type::Int | Type::Float),
                BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem,
                r @ (Type::Int | Type::Float),
            ) if l == r => Ok(Rc::clone(&left.ty)),
            (
                l @ (Type::Int | Type::Float | Type::String),
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge,
                r @ (Type::Int | Type::Float | Type::String),
            ) if l == r => Ok(self.typed_program.insert_type(Type::Bool)),
            (l, BinaryOp::Eq | BinaryOp::Ne, r) if l == r => {
                Ok(self.typed_program.insert_type(Type::Bool))
            }
            _ => Err(format!(
                "cannot apply {:?} to {:?} and {:?}",
                expr.op, left.ty, right.ty
            )),
        }?;

        let expr = TypedExprBinary {
            left: Typed::boxed(left),
            op: expr.op,
            right: Typed::boxed(right),
        };
        Ok(Typed::new(TypedExpr::Binary(expr), ty))
    }

    fn expr_declare(&mut self, expr: &ExprDeclare) -> Result<Typed<TypedExpr>> {
        let typed_expr = self.expr(&expr.expr)?;
        let ty = if let Some(ty) = &expr.ty {
            typed_expr.ty.unify(ty, &mut self.typed_program)?
        } else {
            Rc::clone(&typed_expr.ty)
        };
        self.environment.insert(expr.ident, Rc::clone(&ty));
        let expr = TypedExprDeclare {
            ident: expr.ident,
            ty: Rc::clone(&ty),
            expr: Box::new(typed_expr.value),
        };
        Ok(Typed::new(TypedExpr::Declare(expr), ty))
    }

    fn expr_assign(&mut self, expr: &ExprAssign) -> Result<Typed<TypedExpr>> {
        let typed_expr = self.expr(&expr.expr)?;
        let expected = self.environment.get(&expr.ident).unwrap();
        let ty = typed_expr.ty.unify(expected, &mut self.typed_program)?;
        let expr = TypedExprAssign {
            ident: expr.ident,
            expr: Box::new(typed_expr.value),
        };
        Ok(Typed::new(TypedExpr::Assign(expr), ty))
    }

    fn pattern(&mut self, expr_ty: Rc<Type>, pattern: &Pattern) -> Result<Exhaustive> {
        match *pattern {
            Pattern::Wildcard => Ok(Exhaustive::Exhaustive),
            Pattern::Ident(ident) => {
                self.environment.insert(ident, expr_ty);
                Ok(Exhaustive::Exhaustive)
            }
            Pattern::Destructure {
                ref ty,
                ref variant,
                ref fields,
            } => {
                let ty = expr_ty.unify(ty, &mut self.typed_program)?;
                let user_defined =
                    Rc::clone(&self.program.user_defined_types[&ty.as_user_defined().unwrap()]);
                let field_tys = match (&*user_defined, variant) {
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
                        let mut used_fields = HashSet::new();
                        let mut exhaustive = Exhaustive::Exhaustive;
                        for (field, pat) in fields {
                            let (_, field_ty) = field_tys
                                .iter()
                                .find(|(name, _)| name == field)
                                .ok_or_else(|| format!("type {ty:?} has no field '{field}'"))?;
                            exhaustive = self
                                .pattern(Rc::clone(field_ty), pat)?
                                .finalise(None)
                                .intersect(exhaustive);
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
                        |acc, (pat, field_ty)| {
                            Result::Ok(
                                self.pattern(Rc::clone(field_ty), pat)?
                                    .finalise(None)
                                    .intersect(acc),
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
                        let mut found_variants = HashSet::with_capacity(1);
                        found_variants.insert(variant);
                        Ok(Exhaustive::ExhaustiveVariants(found_variants))
                    }
                    (None, Exhaustive::Exhaustive) => Ok(Exhaustive::Exhaustive),
                    _ => Ok(Exhaustive::NonExhaustive),
                }
            }
        }
    }

    fn expr_match(&mut self, expr: &ExprMatch) -> Result<Typed<TypedExpr>> {
        let scrutinee = self.expr(&expr.scrutinee)?;
        let (exhaustive, output_ty, arms) = expr.arms.iter().try_fold(
            (
                Exhaustive::Exhaustive,
                self.typed_program.insert_type(Type::Unknown),
                vec![],
            ),
            |(exhaustive, output_ty, mut arms), (pat, expr)| {
                let expr = self.expr(expr)?;
                let output_ty = expr.ty.unify(&output_ty, &mut self.typed_program)?;
                let arm_exhaustive = self.pattern(expr.ty, pat)?;
                arms.push((pat.clone(), expr.value));
                Result::Ok((exhaustive.union(arm_exhaustive), output_ty, arms))
            },
        )?;
        if exhaustive.finalise(None) != Exhaustive::Exhaustive {
            Err("non-exhaustive match")?;
        }
        let expr = Typed::new(
            TypedExprMatch {
                scrutinee: Typed::boxed(scrutinee),
                arms,
            },
            Rc::clone(&output_ty),
        );
        Ok(Typed::new(TypedExpr::Match(expr), output_ty))
    }

    fn expr_closure(&mut self, expr: &ExprClosure) -> Typed<TypedExpr> {
        let actual_func = self.program.functions.get(&expr.func).unwrap();
        let captures: HashMap<_, _> = actual_func
            .captures
            .iter()
            .map(|&ident| (ident, Rc::clone(&self.environment[&ident])))
            .collect();
        self.closures.push((expr.func, captures.clone()));
        let ty = Rc::clone(&self.program.signatures[&expr.func]);
        let expr = TypedExprClosure {
            func: expr.func,
            captures,
        };
        Typed::new(TypedExpr::Closure(expr), ty)
    }

    fn expr_intrinsic(&mut self, expr: &ExprIntrinsic) -> Result<Typed<TypedExpr>> {
        let values = self.exprs(&expr.values)?;
        let ty = match expr.intrinsic {
            Intrinsic::Discriminant => self.typed_program.insert_type(Type::Int),
            Intrinsic::Terminate | Intrinsic::Unreachable => {
                self.typed_program.insert_type(Type::None)
            }
        };
        let expr = TypedExprIntrinsic {
            intrinsic: expr.intrinsic,
            values,
        };
        Ok(Typed::new(TypedExpr::Intrinsic(expr), ty))
    }

    fn expr(&mut self, expr: &Expr) -> Result<Typed<TypedExpr>> {
        match expr {
            Expr::Literal(literal) => Ok(self.expr_literal(literal.clone())),
            Expr::Ident(ident) => self.expr_ident(*ident),
            Expr::Function(func_ref) => Ok(self.expr_function(*func_ref)),
            Expr::Block(expr) => self.expr_block(expr),
            Expr::Tuple(expr) => self.expr_tuple(expr),
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
        function: &Function<Expr>,
        captures: HashMap<Ident, Rc<Type>>,
    ) -> Result<Function<TypedExpr>> {
        self.environment = captures;

        for (&param, ty) in function
            .params
            .iter()
            .map(|(param, ty)| (param, ty))
            .chain(&function.continuations)
        {
            self.environment.insert(param, Rc::clone(ty));
        }

        let ty_none = self.typed_program.insert_type(Type::None);
        let (body, body_ty) = self.block(&function.body)?.into_value_ty();
        body_ty.unify(&ty_none, &mut self.typed_program)?;

        Ok(Function::clone_metadata(function, body))
    }

    fn typeck(mut self) -> Result<Program<TypedExpr>> {
        for (&func_ref, function) in &self.program.functions {
            let params = function
                .params
                .iter()
                .map(|(_, ty)| Rc::clone(ty))
                .collect();
            let continuations = function
                .continuations
                .iter()
                .map(|(&name, ty)| (name, Rc::clone(ty)))
                .collect();
            let ty = self
                .typed_program
                .insert_type(Type::function(params, continuations));
            self.typed_program.signatures.insert(func_ref, ty);
        }

        for (&func_ref, function) in &self.program.functions {
            if !function.captures.is_empty() {
                continue;
            }

            let function = self.function(function, HashMap::new())?;

            self.typed_program.functions.insert(func_ref, function);
        }

        for (func_ref, captures) in mem::take(&mut self.closures) {
            let function = self.program.functions.get(&func_ref).unwrap();
            let function = self.function(function, captures)?;
            self.typed_program.functions.insert(func_ref, function);
        }

        Ok(self.typed_program)
    }

    fn new(program: &'a Program<Expr>) -> TypeCk<'a> {
        TypeCk {
            program,
            typed_program: Program::clone_metadata(program),
            environment: HashMap::new(),
            closures: Vec::new(),
        }
    }
}

/// ## Errors
///
/// Returns an error if `program` contains a type error.
pub fn typeck(program: &Program<Expr>) -> Result<Program<TypedExpr>> {
    TypeCk::new(program).typeck()
}
