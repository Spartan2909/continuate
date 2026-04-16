use crate::{
    common::{Ident, Intrinsic, UserDefinedTyRef},
    high_level_ir as hir, mid_level_ir as mir,
};

type HirTy = Arc<hir::Type>;

type HirExpr = hir::Expr<HirTy>;

use std::{
    collections::{HashMap, hash_map::Entry},
    iter, mem, slice,
    sync::Arc,
};

use itertools::Itertools as _;

enum ArmData {
    Variant(MatchVariant),
    Wildcard,
    None,
}

struct MatchVariant {
    variant: usize,
    block: mir::BlockId,
}

fn field_index(ty: &hir::UserDefinedType, field: &str) -> Option<usize> {
    let fields = ty.as_product()?;
    match fields {
        hir::UserDefinedTypeFields::Named(fields) => {
            fields.iter().position(|(name, _)| name == field)
        }
        hir::UserDefinedTypeFields::Anonymous(_) => field.parse().ok(),
        hir::UserDefinedTypeFields::Unit => None,
    }
}

struct Lowerer<'a> {
    program: mir::Program,
    environment: HashMap<Ident, Arc<mir::Type>>,
    current_block: mir::BlockId,
    hir_program: &'a hir::Program<HirTy>,
    types: HashMap<&'a hir::Type, Arc<mir::Type>>,
}

impl<'a> Lowerer<'a> {
    fn user_defined_ty(&mut self, ty_ref: UserDefinedTyRef) -> mir::UserDefinedType {
        let ty = &self.hir_program.user_defined_types[&ty_ref];
        match &**ty {
            hir::UserDefinedType::Product(fields) => {
                let mut new_fields = Vec::with_capacity(fields.len());
                new_fields.extend(fields.iter().map(|field| self.lower_ty(field)));
                mir::UserDefinedType::Product(new_fields)
            }
            hir::UserDefinedType::Sum(variants) => {
                let mut new_variants = Vec::with_capacity(variants.len());
                for (_, variant) in variants {
                    let mut new_variant = Vec::with_capacity(variant.len());
                    new_variant.extend(variant.iter().map(|field| self.lower_ty(field)));
                    new_variants.push(new_variant);
                }
                mir::UserDefinedType::Sum(new_variants)
            }
        }
    }

    fn lower_ty(&mut self, hir_ty: &'a hir::Type) -> Arc<mir::Type> {
        if let Some(ty) = self.types.get(hir_ty) {
            return Arc::clone(ty);
        }

        let ty = match *hir_ty {
            hir::Type::Bool => mir::Type::Bool,
            hir::Type::Int => mir::Type::Int,
            hir::Type::Float => mir::Type::Float,
            hir::Type::String => mir::Type::String,
            hir::Type::Array(ref ty, len) => mir::Type::Array(self.lower_ty(ty), len),
            hir::Type::Tuple(ref types) => {
                mir::Type::Tuple(types.iter().map(|ty| self.lower_ty(ty)).collect())
            }
            hir::Type::Function(hir::FunctionTy {
                ref positional_params,
                ref named_params,
            }) => mir::Type::function(
                positional_params
                    .iter()
                    .map(|ty| self.lower_ty(ty))
                    .collect(),
                named_params
                    .iter()
                    .map(|(&ident, ty)| (ident, self.lower_ty(ty)))
                    .collect(),
            ),
            hir::Type::UserDefined(ty) => mir::Type::UserDefined(self.user_defined_ty(ty)),
            hir::Type::Unknown => unreachable!(),
            hir::Type::None => mir::Type::None,
        };
        let ty = self.program.insert_type(ty);
        self.types.insert(hir_ty, Arc::clone(&ty));
        ty
    }

    fn expr_list(
        &mut self,
        exprs: impl IntoIterator<Item = &'a HirExpr>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> Vec<mir::Expr> {
        exprs
            .into_iter()
            .map(|expr| self.expr(expr, block, function))
            .collect()
    }

    fn block(
        &mut self,
        exprs: &'a [HirExpr],
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let mut exprs = self.expr_list(exprs, block, function);
        let last_expr = exprs.pop().unwrap_or_else(|| {
            let ty = self.program.insert_type(mir::Type::Tuple(Vec::new()));
            mir::Expr::Tuple(mir::ExprTuple {
                ty,
                values: Vec::new(),
            })
        });
        for expr in exprs {
            block.exprs.push(expr);
        }
        last_expr
    }

    fn expr_block(
        &mut self,
        expr: &'a hir::Typed<hir::ExprBlock<HirTy>>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        self.block(&expr.value.exprs, block, function)
    }

    fn expr_tuple(
        &mut self,
        expr: &'a hir::Typed<hir::ExprTuple<HirTy>>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let values = self.expr_list(&expr.value.exprs, block, function);

        mir::Expr::Tuple(mir::ExprTuple {
            ty: self.lower_ty(&expr.ty),
            values,
        })
    }

    fn expr_constructor(
        &mut self,
        expr: &'a hir::ExprConstructor<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let ty = &self.hir_program.user_defined_types[&expr.ty.as_user_defined().unwrap()];
        let fields = match &expr.fields {
            hir::ExprConstructorFields::Named(fields) => self.expr_list(
                fields
                    .iter()
                    .sorted_unstable_by(|(name_1, _), (name_2, _)| {
                        let fields = ty.fields(expr.variant.as_deref()).unwrap();
                        let index_1 = fields.index_of(name_1).unwrap();
                        let index_2 = fields.index_of(name_2).unwrap();
                        index_1.cmp(&index_2)
                    })
                    .map(|(_, field)| field),
                block,
                function,
            ),
            hir::ExprConstructorFields::Anonymous(fields) => {
                self.expr_list(fields, block, function)
            }
            hir::ExprConstructorFields::Unit => Vec::new(),
        };

        mir::Expr::Constructor(mir::ExprConstructor {
            ty: self.lower_ty(&expr.ty),
            index: expr.variant.as_ref().and_then(|variant| {
                ty.as_sum()
                    .unwrap()
                    .iter()
                    .position(|(name, _)| name == variant)
            }),
            fields,
        })
    }

    fn expr_array(
        &mut self,
        expr: &'a hir::Typed<hir::ExprArray<HirTy>>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let array = self.expr_list(&expr.value.exprs, block, function);
        let mut values = Vec::with_capacity(array.len());
        values.extend(array);
        let (value_ty, _) = expr.ty.as_array().unwrap();
        let value_ty = self.lower_ty(value_ty);
        let ty = self.program.insert_type(mir::Type::Array(
            Arc::clone(&value_ty),
            expr.value.exprs.len() as u64,
        ));
        mir::Expr::Array(mir::ExprArray {
            ty,
            values,
            value_ty,
        })
    }

    fn expr_get(
        &mut self,
        expr: &'a hir::ExprGet<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let object = self.expr(&expr.object, block, function);
        let user_defined = expr.object.ty.as_user_defined().unwrap();
        mir::Expr::Get(mir::ExprGet {
            object: Box::new(object),
            object_ty: self.lower_ty(&expr.object.ty),
            object_variant: None,
            field: field_index(
                &self.hir_program.user_defined_types[&user_defined],
                &expr.field,
            )
            .unwrap(),
        })
    }

    fn expr_set(
        &mut self,
        expr: &'a hir::ExprSet<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let object = self.expr(&expr.object, block, function);
        let user_defined = expr.object.ty.as_user_defined().unwrap();

        let value = self.expr(&expr.value, block, function);

        mir::Expr::Set(mir::ExprSet {
            object: Box::new(object),
            object_ty: self.lower_ty(&expr.object.ty),
            object_variant: None,
            field: field_index(
                &self.hir_program.user_defined_types[&user_defined],
                &expr.field,
            )
            .unwrap(),
            value: Box::new(value),
        })
    }

    fn expr_call(
        &mut self,
        expr: &'a hir::ExprCall<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let callee = self.expr(&expr.callee, block, function);
        let positional = self.expr_list(&expr.positional, block, function);
        let named = expr
            .named
            .iter()
            .map(|(i, e)| (*i, self.expr(e, block, function)))
            .collect();

        let callee_ty = self.lower_ty(&expr.callee.ty);
        mir::Expr::Call(mir::ExprCall {
            callee: Box::new(callee),
            callee_ty,
            positional,
            named,
        })
    }

    fn expr_application(
        &mut self,
        expr: &'a hir::Typed<hir::ExprApplication<HirTy>>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let callee = self.expr(&expr.callee, block, function);

        let new_positional = self.expr_list(&expr.positional, block, function);

        let mut new_named = Vec::with_capacity(expr.named.len());
        for (ident, expr) in &expr.named {
            let expr = self.expr(expr, block, function);
            new_named.push((*ident, expr));
        }

        let callee_ty = self.lower_ty(&expr.callee.ty);
        let callee_ty = callee_ty.as_function().unwrap();
        let storage_ty = mir::UserDefinedType::Product(
            iter::once(self.lower_ty(&expr.callee.ty))
                .chain(
                    callee_ty.positional_params[..expr.positional.len()]
                        .iter()
                        .cloned(),
                )
                .chain(
                    expr.named
                        .iter()
                        .sorted_unstable_by_key(|(ident, _)| *ident)
                        .map(|(ident, _)| Arc::clone(&callee_ty.named_params[ident])),
                )
                .collect(),
        );

        mir::Expr::Application(mir::ExprApplication {
            callee: Box::new(callee),
            callee_ty: self.lower_ty(&expr.callee.ty),
            positional: new_positional,
            named: new_named,
            result_ty: self.lower_ty(&expr.ty),
            storage_ty: self.program.insert_type(mir::Type::UserDefined(storage_ty)),
        })
    }

    fn expr_unary(
        &mut self,
        expr: &'a hir::ExprUnary<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let operand = self.expr(&expr.right, block, function);
        mir::Expr::Unary(mir::ExprUnary {
            operator: expr.op,
            operand: Box::new(operand),
            operand_ty: self.lower_ty(&expr.right.ty),
        })
    }

    fn expr_binary(
        &mut self,
        expr: &'a hir::ExprBinary<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let left = self.expr(&expr.left, block, function);
        let right = self.expr(&expr.right, block, function);

        mir::Expr::Binary(mir::ExprBinary {
            left: Box::new(left),
            left_ty: self.lower_ty(&expr.left.ty),
            operator: expr.op,
            right: Box::new(right),
            right_ty: self.lower_ty(&expr.right.ty),
        })
    }

    fn expr_declare(
        &mut self,
        expr: &'a hir::ExprDeclare<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let right = self.expr(&expr.expr, block, function);

        function
            .declarations
            .insert(expr.ident, (self.lower_ty(&expr.ty), None));
        mir::Expr::Assign(mir::ExprAssign {
            ident: expr.ident,
            expr: Box::new(right),
        })
    }

    fn expr_assign(
        &mut self,
        expr: &'a hir::ExprAssign<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let right = self.expr(&expr.expr, block, function);

        mir::Expr::Assign(mir::ExprAssign {
            ident: expr.ident,
            expr: Box::new(right),
        })
    }

    fn order_destructure_fields<'b>(
        fields: &'b hir::DestructureFields,
        ty: &'b hir::UserDefinedType,
        variant: Option<&str>,
    ) -> impl Iterator<Item = &'b hir::Pattern> + use<'b> {
        enum Iter<'a> {
            Named {
                fields: &'a [(String, hir::Pattern)],
                pos: usize,
                ty: &'a [(String, Arc<hir::Type>)],
            },
            Anonymous(slice::Iter<'a, hir::Pattern>),
        }

        impl<'a> Iterator for Iter<'a> {
            type Item = &'a hir::Pattern;

            fn next(&mut self) -> Option<Self::Item> {
                match *self {
                    Iter::Named {
                        fields,
                        ref mut pos,
                        ty,
                    } => {
                        if *pos > ty.len() {
                            return None;
                        }

                        let (name, _) = &ty[*pos];
                        *pos += 1;
                        fields
                            .iter()
                            .find(|(field, _)| field == name)
                            .map(|(_, pattern)| pattern)
                    }
                    Iter::Anonymous(ref mut iter) => iter.next(),
                }
            }
        }

        match fields {
            hir::DestructureFields::Named(fields) => Iter::Named {
                fields,
                pos: 0,
                ty: ty.fields(variant).unwrap().as_named().unwrap(),
            },
            hir::DestructureFields::Anonymous(fields) => Iter::Anonymous(fields.iter()),
            hir::DestructureFields::Unit => Iter::Anonymous([].iter()),
        }
    }

    fn pattern(
        &mut self,
        scrutinee: (&mir::Expr, Arc<mir::Type>),
        arm_pat: &hir::Pattern,
        arm_block: &mut mir::Block,
        arm_block_id: mir::BlockId,
        otherwise: mir::BlockId,
        function: &mut mir::Function,
    ) -> ArmData {
        let (scrutinee, scrutinee_ty) = scrutinee;

        match *arm_pat {
            hir::Pattern::Wildcard => ArmData::Wildcard,
            hir::Pattern::Ident(ident) => {
                let binding = mir::Expr::Assign(mir::ExprAssign {
                    ident,
                    expr: Box::new(scrutinee.clone()),
                });
                function.declarations.insert(ident, (scrutinee_ty, None));
                arm_block.exprs.push(binding);
                ArmData::Wildcard
            }
            hir::Pattern::Destructure {
                ref ty,
                ref variant,
                ref fields,
            } => {
                let ty = &self.hir_program.user_defined_types[&ty.as_user_defined().unwrap()];
                let variant_index = variant.as_ref().and_then(|variant| variant.parse().ok());
                for (field, pattern) in
                    Self::order_destructure_fields(fields, ty, variant.as_deref()).enumerate()
                {
                    let get = mir::Expr::Get(mir::ExprGet {
                        object: Box::new(scrutinee.clone()),
                        object_ty: Arc::clone(&scrutinee_ty),
                        object_variant: variant_index,
                        field,
                    });
                    let field_ty_ref = scrutinee_ty.field(variant_index, field).unwrap();
                    let mut new_block = mir::Block::new();
                    let new_block_id = function.block();
                    match self.pattern(
                        (&get, Arc::clone(&field_ty_ref)),
                        pattern,
                        &mut new_block,
                        new_block_id,
                        otherwise,
                        function,
                    ) {
                        ArmData::None | ArmData::Wildcard => {
                            arm_block.exprs.append(&mut new_block.exprs);
                        }
                        ArmData::Variant(MatchVariant {
                            variant,
                            block: switch_arm_id,
                        }) => {
                            let discriminant = mir::Expr::Intrinsic(mir::ExprIntrinsic {
                                intrinsic: Intrinsic::Discriminant,
                                values: vec![(get, field_ty_ref)],
                            });
                            let arms = iter::once((variant as i64, switch_arm_id));
                            let switch = mir::Expr::Switch(mir::ExprSwitch {
                                scrutinee: Box::new(discriminant),
                                arms: arms.collect(),
                                otherwise,
                            });
                            arm_block.exprs.push(switch);
                            function.blocks.insert(switch_arm_id, new_block);
                        }
                    }
                }
                if let Some(variant) = variant_index {
                    ArmData::Variant(MatchVariant {
                        variant,
                        block: arm_block_id,
                    })
                } else {
                    ArmData::None
                }
            }
        }
    }

    fn expr_match(
        &mut self,
        expr: &'a hir::ExprMatch<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        let scrutinee = self.expr(&expr.scrutinee, block, function);

        let mut discriminants = vec![];
        let otherwise = function.block();
        let next_id = function.block();

        for (arm_pat, arm) in &expr.arms {
            let mut arm_block = mir::Block::new();
            let mut arm_block_id = function.block();

            let scrutinee_ty = self.lower_ty(&expr.scrutinee.ty);
            let arm_data = self.pattern(
                (&scrutinee, scrutinee_ty),
                arm_pat,
                &mut arm_block,
                arm_block_id,
                otherwise,
                function,
            );

            let has_wildcard = match arm_data {
                ArmData::Wildcard => {
                    arm_block_id = otherwise;
                    true
                }
                ArmData::Variant(variant) => {
                    discriminants.push(variant);
                    false
                }
                ArmData::None => false,
            };

            let arm = self.expr(arm, &mut arm_block, function);
            arm_block.exprs.push(arm);
            let goto = mir::Expr::Goto(mir::ExprGoto { block: next_id });
            arm_block.exprs.push(goto);

            function.blocks.insert(arm_block_id, arm_block);

            if has_wildcard {
                break;
            }
        }

        let current_block = mem::replace(block, mir::Block::new());
        function.blocks.insert(self.current_block, current_block);
        self.current_block = next_id;

        let scrutinee = if discriminants.is_empty() {
            scrutinee
        } else {
            mir::Expr::Intrinsic(mir::ExprIntrinsic {
                intrinsic: Intrinsic::Discriminant,
                values: vec![(scrutinee.clone(), self.lower_ty(&expr.scrutinee.ty))],
            })
        };

        if let Entry::Vacant(entry) = function.blocks.entry(otherwise) {
            let mut otherwise_block = mir::Block::new();
            otherwise_block
                .exprs
                .push(mir::Expr::Intrinsic(mir::ExprIntrinsic {
                    intrinsic: Intrinsic::Unreachable,
                    values: vec![],
                }));
            entry.insert(otherwise_block);
        }
        mir::Expr::Switch(mir::ExprSwitch {
            scrutinee: Box::new(scrutinee),
            arms: discriminants
                .iter()
                .map(|&MatchVariant { variant, block }| (variant as i64, block))
                .collect(),
            otherwise,
        })
    }

    fn expr_closure(&mut self, expr: &hir::ExprClosure) -> mir::Expr {
        let func = &self.hir_program.functions[&expr.func];
        let captures: Vec<_> = func.captures.iter().copied().sorted_unstable().collect();

        let func = self.function(
            func,
            Some(
                &captures
                    .iter()
                    .map(|ident| (*ident, Arc::clone(&self.environment[ident])))
                    .collect_vec(),
            ),
        );
        self.program.functions.insert(expr.func, func);

        let storage_ty = mir::UserDefinedType::Product(
            captures
                .iter()
                .map(|ident| Arc::clone(&self.environment[ident]))
                .collect(),
        );

        let func_ref = expr.func;
        mir::Expr::Closure(mir::ExprClosure {
            func_ref,
            captures,
            storage_ty: self.program.insert_type(mir::Type::UserDefined(storage_ty)),
        })
    }

    fn expr_intrinsic(
        &mut self,
        expr: &'a hir::ExprIntrinsic<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        mir::Expr::Intrinsic(mir::ExprIntrinsic {
            intrinsic: expr.intrinsic,
            values: expr
                .values
                .iter()
                .map(|expr| (self.expr(expr, block, function), self.lower_ty(&expr.ty)))
                .collect(),
        })
    }

    fn expr(
        &mut self,
        expr: &'a hir::Expr<HirTy>,
        block: &mut mir::Block,
        function: &mut mir::Function,
    ) -> mir::Expr {
        match expr {
            hir::Expr::Literal(lit) => mir::Expr::Literal(mir::ExprLiteral {
                literal: lit.clone(),
            }),
            hir::Expr::Ident(ident) => mir::Expr::Ident(mir::ExprIdent {
                ident: ident.ident.value,
            }),
            hir::Expr::Function(func_ref) => mir::Expr::Function(mir::ExprFunction {
                function: *func_ref,
            }),
            hir::Expr::Block(expr) => self.expr_block(expr, block, function),
            hir::Expr::Tuple(expr) => self.expr_tuple(expr, block, function),
            hir::Expr::Constructor(expr) => self.expr_constructor(expr, block, function),
            hir::Expr::Array(expr) => self.expr_array(expr, block, function),
            hir::Expr::Get(expr) => self.expr_get(expr, block, function),
            hir::Expr::Set(expr) => self.expr_set(expr, block, function),
            hir::Expr::Call(expr) => self.expr_call(expr, block, function),
            hir::Expr::Application(expr) => self.expr_application(expr, block, function),
            hir::Expr::Unary(expr) => self.expr_unary(expr, block, function),
            hir::Expr::Binary(expr) => self.expr_binary(expr, block, function),
            hir::Expr::Declare(expr) => self.expr_declare(expr, block, function),
            hir::Expr::Assign(expr) => self.expr_assign(expr, block, function),
            hir::Expr::Match(expr) => self.expr_match(expr, block, function),
            hir::Expr::Closure(expr) => self.expr_closure(expr),
            hir::Expr::Intrinsic(expr) => self.expr_intrinsic(expr, block, function),
        }
    }

    fn captures(&mut self, captures: &[(Ident, Arc<mir::Type>)]) -> mir::ClosureCaptures {
        let storage_ty = mir::UserDefinedType::Product(
            captures
                .iter()
                .sorted_unstable_by_key(|(ident, _)| *ident)
                .map(|(_, ty)| Arc::clone(ty))
                .collect(),
        );
        mir::ClosureCaptures {
            captures: captures
                .iter()
                .map(|(ident, _)| *ident)
                .sorted_unstable()
                .collect(),

            storage_ty: self.program.insert_type(mir::Type::UserDefined(storage_ty)),
        }
    }

    fn function(
        &mut self,
        function: &'a hir::Function<HirTy>,
        captures: Option<&[(Ident, Arc<mir::Type>)]>,
    ) -> mir::Function {
        let mut mir_function = mir::Function::new(function.name.clone());
        mir_function
            .positional_params
            .reserve(function.positional.len());
        for (param, ty) in &function.positional {
            mir_function
                .positional_params
                .push((*param, self.lower_ty(ty)));
        }
        mir_function.named_params.reserve(function.named.len());
        for (&param, ty) in &function.named {
            mir_function.named_params.insert(param, self.lower_ty(ty));
        }

        self.environment.clear();

        if let Some(captures) = captures {
            self.environment
                .extend(captures.iter().map(|(ident, ty)| (*ident, Arc::clone(ty))));
            mir_function.declarations.extend(
                captures
                    .iter()
                    .map(|(ident, ty)| (*ident, (Arc::clone(ty), None))),
            );
            mir_function.captures = Some(self.captures(captures));
        }

        for (&param, ty) in mir_function
            .positional_params
            .iter()
            .map(|(param, ty)| (param, ty))
            .chain(&mir_function.named_params)
        {
            self.environment.insert(param, Arc::clone(ty));
        }

        self.current_block = mir::Function::entry_point();

        let mut block = mir::Block::new();
        let body = self.block(&function.body, &mut block, &mut mir_function);
        block.exprs.push(body);
        mir_function.blocks.insert(self.current_block, block);

        mir_function
    }

    fn lower(program: &'a hir::Program<HirTy>) -> mir::Program {
        let mut lowerer = Lowerer {
            program: mir::Program::new(program),
            environment: HashMap::new(),
            current_block: mir::Function::entry_point(),
            hir_program: program,
            types: HashMap::new(),
        };

        for (&function, signature) in &program.signatures {
            let signature = lowerer.lower_ty(signature);
            lowerer.program.signatures.insert(function, signature);
        }

        for (&func_ref, function) in &program.functions {
            if !function.captures.is_empty() {
                continue;
            }
            let function = lowerer.function(function, None);
            lowerer.program.functions.insert(func_ref, function);
        }

        lowerer.program
    }
}

#[inline]
pub fn lower(program: &hir::Program<HirTy>) -> mir::Program {
    Lowerer::lower(program)
}
