use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::UserDefinedTyRef;
use crate::high_level_ir::DestructureFields;
use crate::high_level_ir::Expr as HirExpr;
use crate::high_level_ir::ExprArray as HirExprArray;
use crate::high_level_ir::ExprAssign as HirExprAssign;
use crate::high_level_ir::ExprBinary as HirExprBinary;
use crate::high_level_ir::ExprBlock as HirExprBlock;
use crate::high_level_ir::ExprCall as HirExprCall;
use crate::high_level_ir::ExprClosure as HirExprClosure;
use crate::high_level_ir::ExprConstructor as HirExprConstructor;
use crate::high_level_ir::ExprConstructorFields;
use crate::high_level_ir::ExprContApplication as HirExprContApplication;
use crate::high_level_ir::ExprDeclare as HirExprDeclare;
use crate::high_level_ir::ExprGet as HirExprGet;
use crate::high_level_ir::ExprIntrinsic as HirExprIntrinsic;
use crate::high_level_ir::ExprMatch as HirExprMatch;
use crate::high_level_ir::ExprSet as HirExprSet;
use crate::high_level_ir::ExprTuple as HirExprTuple;
use crate::high_level_ir::ExprUnary as HirExprUnary;
use crate::high_level_ir::Function as HirFunction;
use crate::high_level_ir::FunctionTy as HirFunctionTy;
use crate::high_level_ir::Pattern;
use crate::high_level_ir::Program as HirProgram;
use crate::high_level_ir::Type as HirType;
use crate::high_level_ir::UserDefinedType as HirUserDefinedType;
use crate::high_level_ir::UserDefinedTypeFields;
use crate::mid_level_ir::Block;
use crate::mid_level_ir::BlockId;
use crate::mid_level_ir::ClosureCaptures;
use crate::mid_level_ir::Expr;
use crate::mid_level_ir::ExprArray;
use crate::mid_level_ir::ExprAssign;
use crate::mid_level_ir::ExprBinary;
use crate::mid_level_ir::ExprCall;
use crate::mid_level_ir::ExprClosure;
use crate::mid_level_ir::ExprConstructor;
use crate::mid_level_ir::ExprContApplication;
use crate::mid_level_ir::ExprGet;
use crate::mid_level_ir::ExprIntrinsic;
use crate::mid_level_ir::ExprSet;
use crate::mid_level_ir::ExprSwitch;
use crate::mid_level_ir::ExprTuple;
use crate::mid_level_ir::ExprUnary;
use crate::mid_level_ir::Function;
use crate::mid_level_ir::Program;
use crate::mid_level_ir::Type;
use crate::mid_level_ir::UserDefinedType;

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::iter;
use std::mem;
use std::rc::Rc;
use std::slice;

use itertools::Itertools as _;

enum ArmData {
    Variant(MatchVariant),
    Wildcard,
    None,
}

struct MatchVariant {
    variant: usize,
    block: BlockId,
}

fn field_index(ty: &HirUserDefinedType, field: &str) -> Option<usize> {
    let fields = ty.as_product()?;
    match fields {
        UserDefinedTypeFields::Named(fields) => fields.iter().position(|(name, _)| name == field),
        UserDefinedTypeFields::Anonymous(_) => field.parse().ok(),
        UserDefinedTypeFields::Unit => None,
    }
}

struct Lowerer<'a> {
    program: Program,
    environment: HashMap<Ident, Rc<Type>>,
    current_block: BlockId,
    hir_program: &'a HirProgram,
    types: HashMap<&'a HirType, Rc<Type>>,
}

impl<'a> Lowerer<'a> {
    fn user_defined_ty(&mut self, ty_ref: UserDefinedTyRef) -> UserDefinedType {
        let ty = &self.hir_program.user_defined_types[&ty_ref];
        match &**ty {
            HirUserDefinedType::Product(fields) => {
                let mut new_fields = Vec::with_capacity(fields.len());
                new_fields.extend(fields.iter().map(|field| self.lower_ty(field)));
                UserDefinedType::Product(new_fields)
            }
            HirUserDefinedType::Sum(variants) => {
                let mut new_variants = Vec::with_capacity(variants.len());
                for (_, variant) in variants {
                    let mut new_variant = Vec::with_capacity(variant.len());
                    new_variant.extend(variant.iter().map(|field| self.lower_ty(field)));
                    new_variants.push(new_variant);
                }
                UserDefinedType::Sum(new_variants)
            }
        }
    }

    fn lower_ty(&mut self, hir_ty: &'a HirType) -> Rc<Type> {
        if let Some(ty) = self.types.get(hir_ty) {
            return Rc::clone(ty);
        }

        let ty = match *hir_ty {
            HirType::Bool => Type::Bool,
            HirType::Int => Type::Int,
            HirType::Float => Type::Float,
            HirType::String => Type::String,
            HirType::Array(ref ty, len) => Type::Array(self.lower_ty(ty), len),
            HirType::Tuple(ref types) => {
                Type::Tuple(types.iter().map(|ty| self.lower_ty(ty)).collect())
            }
            HirType::Function(HirFunctionTy {
                ref params,
                ref continuations,
            }) => Type::function(
                params.iter().map(|ty| self.lower_ty(ty)).collect(),
                continuations
                    .iter()
                    .map(|(&ident, ty)| (ident, self.lower_ty(ty)))
                    .collect(),
            ),
            HirType::UserDefined(ty) => Type::UserDefined(self.user_defined_ty(ty)),
            HirType::Unknown => unreachable!(),
            HirType::None => Type::None,
        };
        let ty = self.program.insert_type(ty);
        self.types.insert(hir_ty, Rc::clone(&ty));
        ty
    }

    fn expr_list(
        &mut self,
        exprs: impl IntoIterator<Item = &'a HirExpr>,
        block: &mut Block,
        function: &mut Function,
    ) -> Vec<Expr> {
        exprs
            .into_iter()
            .map(|expr| self.expr(expr, block, function))
            .collect()
    }

    fn block(&mut self, exprs: &'a [HirExpr], block: &mut Block, function: &mut Function) -> Expr {
        let mut exprs = self.expr_list(exprs, block, function);
        let last_expr = exprs.pop().unwrap_or_else(|| {
            let ty = self.program.insert_type(Type::Tuple(Vec::new()));
            Expr::Tuple(ExprTuple {
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
        expr: &'a HirExprBlock,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        self.block(&expr.exprs, block, function)
    }

    fn expr_tuple(
        &mut self,
        expr: &'a HirExprTuple,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let values = self.expr_list(&expr.exprs, block, function);

        Expr::Tuple(ExprTuple {
            ty: self.lower_ty(&expr.ty),
            values,
        })
    }

    fn expr_constructor(
        &mut self,
        expr: &'a HirExprConstructor,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let ty = &self.hir_program.user_defined_types[&expr.ty.as_user_defined().unwrap()];
        let fields = match &expr.fields {
            ExprConstructorFields::Named(fields) => self.expr_list(
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
            ExprConstructorFields::Anonymous(fields) => self.expr_list(fields, block, function),
            ExprConstructorFields::Unit => Vec::new(),
        };

        Expr::Constructor(ExprConstructor {
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
        expr: &'a HirExprArray,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let array = self.expr_list(&expr.exprs, block, function);
        let mut values = Vec::with_capacity(array.len());
        values.extend(array);
        Expr::Array(ExprArray {
            ty: self.lower_ty(&expr.ty),
            values,
            value_ty: self.lower_ty(&expr.element_ty),
        })
    }

    fn expr_get(
        &mut self,
        expr: &'a HirExprGet,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let object = self.expr(&expr.object, block, function);
        let user_defined = expr.object_ty.as_user_defined().unwrap();
        Expr::Get(ExprGet {
            object: Box::new(object),
            object_ty: self.lower_ty(&expr.object_ty),
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
        expr: &'a HirExprSet,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let object = self.expr(&expr.object, block, function);
        let user_defined = expr.object_ty.as_user_defined().unwrap();

        let value = self.expr(&expr.value, block, function);

        Expr::Set(ExprSet {
            object: Box::new(object),
            object_ty: self.lower_ty(&expr.object_ty),
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
        expr: &'a HirExprCall,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let callee = self.expr(&expr.callee, block, function);
        let params = self.expr_list(&expr.args, block, function);

        let mut new_params = Vec::with_capacity(params.len());
        new_params.extend(params.into_iter().map(|expr| (None, expr)));
        let callee_ty = self.lower_ty(&expr.callee_ty);
        Expr::Call(ExprCall {
            callee: Box::new(callee),
            callee_ty,
            args: new_params,
        })
    }

    fn expr_cont_application(
        &mut self,
        expr: &'a HirExprContApplication,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let callee = self.expr(&expr.callee, block, function);

        let mut new_continuations = Vec::with_capacity(expr.continuations.len());
        for (ident, expr) in &expr.continuations {
            let expr = self.expr(expr, block, function);
            new_continuations.push((*ident, expr));
        }

        let callee_ty = self.lower_ty(&expr.callee_ty);
        let callee_ty = callee_ty.as_function().unwrap();
        let storage_ty = UserDefinedType::Product(
            iter::once(self.lower_ty(&expr.callee_ty))
                .chain(
                    expr.continuations
                        .iter()
                        .sorted_unstable_by_key(|(ident, _)| *ident)
                        .map(|(ident, _)| Rc::clone(&callee_ty.continuations[ident])),
                )
                .collect(),
        );

        Expr::ContApplication(ExprContApplication {
            callee: Box::new(callee),
            callee_ty: self.lower_ty(&expr.callee_ty),
            continuations: new_continuations,
            result_ty: self.lower_ty(&expr.result_ty),
            storage_ty: self.program.insert_type(Type::UserDefined(storage_ty)),
        })
    }

    fn expr_unary(
        &mut self,
        expr: &'a HirExprUnary,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let operand = self.expr(&expr.right, block, function);
        Expr::Unary(ExprUnary {
            operator: expr.op,
            operand: Box::new(operand),
            operand_ty: self.lower_ty(&expr.right_ty),
        })
    }

    fn expr_binary(
        &mut self,
        expr: &'a HirExprBinary,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let left = self.expr(&expr.left, block, function);
        let right = self.expr(&expr.right, block, function);

        Expr::Binary(ExprBinary {
            left: Box::new(left),
            left_ty: self.lower_ty(&expr.left_ty),
            operator: expr.op,
            right: Box::new(right),
            right_ty: self.lower_ty(&expr.right_ty),
        })
    }

    fn expr_declare(
        &mut self,
        expr: &'a HirExprDeclare,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let right = self.expr(&expr.expr, block, function);

        function
            .declarations
            .insert(expr.ident, (self.lower_ty(&expr.ty), None));
        Expr::Assign(ExprAssign {
            ident: expr.ident,
            expr: Box::new(right),
        })
    }

    fn expr_assign(
        &mut self,
        expr: &'a HirExprAssign,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let right = self.expr(&expr.expr, block, function);

        Expr::Assign(ExprAssign {
            ident: expr.ident,
            expr: Box::new(right),
        })
    }

    #[expect(
        clippy::iter_on_empty_collections,
        reason = "must be an empty slice to typecheck"
    )]
    fn order_destructure_fields<'b>(
        fields: &'b DestructureFields,
        ty: &'b HirUserDefinedType,
        variant: Option<&str>,
    ) -> impl Iterator<Item = &'b Pattern> {
        enum Iter<'a> {
            Named {
                fields: &'a [(String, Pattern)],
                pos: usize,
                ty: &'a [(String, Rc<HirType>)],
            },
            Anonymous(slice::Iter<'a, Pattern>),
        }

        impl<'a> Iterator for Iter<'a> {
            type Item = &'a Pattern;

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
            DestructureFields::Named(fields) => Iter::Named {
                fields,
                pos: 0,
                ty: ty.fields(variant).unwrap().as_named().unwrap(),
            },
            DestructureFields::Anonymous(fields) => Iter::Anonymous(fields.iter()),
            DestructureFields::Unit => Iter::Anonymous([].iter()),
        }
    }

    fn pattern(
        &mut self,
        scrutinee: (&Expr, Rc<Type>),
        arm_pat: &Pattern,
        arm_block: &mut Block,
        arm_block_id: BlockId,
        otherwise: BlockId,
        function: &mut Function,
    ) -> ArmData {
        let (scrutinee, scrutinee_ty) = scrutinee;

        match *arm_pat {
            Pattern::Wildcard => ArmData::Wildcard,
            Pattern::Ident(ident) => {
                let binding = Expr::Assign(ExprAssign {
                    ident,
                    expr: Box::new(scrutinee.clone()),
                });
                function.declarations.insert(ident, (scrutinee_ty, None));
                arm_block.exprs.push(binding);
                ArmData::Wildcard
            }
            Pattern::Destructure {
                ref ty,
                ref variant,
                ref fields,
            } => {
                let ty = &self.hir_program.user_defined_types[&ty.as_user_defined().unwrap()];
                let variant_index = variant.as_ref().and_then(|variant| variant.parse().ok());
                for (field, pattern) in
                    Self::order_destructure_fields(fields, ty, variant.as_deref()).enumerate()
                {
                    let get = Expr::Get(ExprGet {
                        object: Box::new(scrutinee.clone()),
                        object_ty: Rc::clone(&scrutinee_ty),
                        object_variant: variant_index,
                        field,
                    });
                    let get = Box::new(get);
                    let field_ty_ref = scrutinee_ty.field(variant_index, field).unwrap();
                    let mut new_block = Block::new();
                    let new_block_id = function.block();
                    match self.pattern(
                        (&get, Rc::clone(&field_ty_ref)),
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
                            let discriminant = Expr::Intrinsic(ExprIntrinsic {
                                intrinsic: Intrinsic::Discriminant,
                                value: get,
                                value_ty: field_ty_ref,
                            });
                            let arms = iter::once((variant as i64, switch_arm_id));
                            let switch = Expr::Switch(ExprSwitch {
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
        expr: &'a HirExprMatch,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let scrutinee = self.expr(&expr.scrutinee, block, function);

        let mut discriminants = vec![];
        let otherwise = function.block();
        let next_id = function.block();

        for (arm_pat, arm) in &expr.arms {
            let mut arm_block = Block::new();
            let mut arm_block_id = function.block();

            let scrutinee_ty = self.lower_ty(&expr.scrutinee_ty);
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
            let goto = Expr::Goto(next_id);
            arm_block.exprs.push(goto);

            function.blocks.insert(arm_block_id, arm_block);

            if has_wildcard {
                break;
            }
        }

        let current_block = mem::replace(block, Block::new());
        function.blocks.insert(self.current_block, current_block);
        self.current_block = next_id;

        let scrutinee = if discriminants.is_empty() {
            scrutinee
        } else {
            Expr::Intrinsic(ExprIntrinsic {
                intrinsic: Intrinsic::Discriminant,
                value: Box::new(scrutinee.clone()),
                value_ty: self.lower_ty(&expr.scrutinee_ty),
            })
        };

        if let Entry::Vacant(entry) = function.blocks.entry(otherwise) {
            let mut otherwise_block = Block::new();
            otherwise_block
                .exprs
                .push(Expr::unreachable(&mut self.program));
            entry.insert(otherwise_block);
        }
        Expr::Switch(ExprSwitch {
            scrutinee: Box::new(scrutinee),
            arms: discriminants
                .iter()
                .map(|&MatchVariant { variant, block }| (variant as i64, block))
                .collect(),
            otherwise,
        })
    }

    fn expr_closure(&mut self, expr: &HirExprClosure) -> Expr {
        let func = &self.hir_program.functions[&expr.func];
        let captures: Vec<_> = func.captures.iter().copied().sorted_unstable().collect();

        let func = self.function(
            func,
            Some(
                &captures
                    .iter()
                    .map(|ident| (*ident, Rc::clone(&self.environment[ident])))
                    .collect_vec(),
            ),
        );
        self.program.functions.insert(expr.func, func);

        let storage_ty = UserDefinedType::Product(
            captures
                .iter()
                .map(|ident| Rc::clone(&self.environment[ident]))
                .collect(),
        );

        let func_ref = expr.func;
        Expr::Closure(ExprClosure {
            func_ref,
            captures,
            storage_ty: self.program.insert_type(Type::UserDefined(storage_ty)),
        })
    }

    fn expr_intrinsic(
        &mut self,
        expr: &'a HirExprIntrinsic,
        block: &mut Block,
        function: &mut Function,
    ) -> Expr {
        let value = self.expr(&expr.value, block, function);
        Expr::Intrinsic(ExprIntrinsic {
            intrinsic: expr.intrinsic,
            value: Box::new(value),
            value_ty: self.lower_ty(&expr.value_ty),
        })
    }

    fn expr(&mut self, expr: &'a HirExpr, block: &mut Block, function: &mut Function) -> Expr {
        match expr {
            HirExpr::Literal(lit) => Expr::Literal(lit.clone()),
            HirExpr::Ident(ident) => Expr::Ident(*ident),
            HirExpr::Function(func_ref) => Expr::Function(*func_ref),
            HirExpr::Block(expr) => self.expr_block(expr, block, function),
            HirExpr::Tuple(expr) => self.expr_tuple(expr, block, function),
            HirExpr::Constructor(expr) => self.expr_constructor(expr, block, function),
            HirExpr::Array(expr) => self.expr_array(expr, block, function),
            HirExpr::Get(expr) => self.expr_get(expr, block, function),
            HirExpr::Set(expr) => self.expr_set(expr, block, function),
            HirExpr::Call(expr) => self.expr_call(expr, block, function),
            HirExpr::ContApplication(expr) => self.expr_cont_application(expr, block, function),
            HirExpr::Unary(expr) => self.expr_unary(expr, block, function),
            HirExpr::Binary(expr) => self.expr_binary(expr, block, function),
            HirExpr::Declare(expr) => self.expr_declare(expr, block, function),
            HirExpr::Assign(expr) => self.expr_assign(expr, block, function),
            HirExpr::Match(expr) => self.expr_match(expr, block, function),
            HirExpr::Closure(expr) => self.expr_closure(expr),
            HirExpr::Intrinsic(expr) => self.expr_intrinsic(expr, block, function),
        }
    }

    fn captures(&mut self, captures: &[(Ident, Rc<Type>)]) -> ClosureCaptures {
        let storage_ty = UserDefinedType::Product(
            captures
                .iter()
                .sorted_unstable_by_key(|(ident, _)| *ident)
                .map(|(_, ty)| Rc::clone(ty))
                .collect(),
        );
        ClosureCaptures {
            captures: captures
                .iter()
                .map(|(ident, _)| *ident)
                .sorted_unstable()
                .collect(),

            storage_ty: self.program.insert_type(Type::UserDefined(storage_ty)),
        }
    }

    fn function(
        &mut self,
        function: &'a HirFunction,
        captures: Option<&[(Ident, Rc<Type>)]>,
    ) -> Function {
        let mut mir_function = Function::new(function.name.clone());
        mir_function.params.reserve(function.params.len());
        for (param, ty) in &function.params {
            mir_function.params.push((*param, self.lower_ty(ty)));
        }
        mir_function
            .continuations
            .reserve(function.continuations.len());
        for (&param, ty) in &function.continuations {
            mir_function.continuations.insert(param, self.lower_ty(ty));
        }

        self.environment.clear();

        if let Some(captures) = captures {
            self.environment
                .extend(captures.iter().map(|(ident, ty)| (*ident, Rc::clone(ty))));
            mir_function.declarations.extend(
                captures
                    .iter()
                    .map(|(ident, ty)| (*ident, (Rc::clone(ty), None))),
            );
            mir_function.captures = Some(self.captures(captures));
        }

        for (&param, ty) in mir_function
            .params
            .iter()
            .map(|(param, ty)| (param, ty))
            .chain(&mir_function.continuations)
        {
            self.environment.insert(param, Rc::clone(ty));
        }

        self.current_block = Function::entry_point();

        let mut block = Block::new();
        let body = self.block(&function.body, &mut block, &mut mir_function);
        block.exprs.push(body);
        mir_function.blocks.insert(self.current_block, block);

        mir_function
    }

    fn lower(program: &'a HirProgram) -> Program {
        let mut lowerer = Lowerer {
            program: Program::new(program),
            environment: HashMap::new(),
            current_block: Function::entry_point(),
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

pub fn lower(program: &HirProgram) -> Program {
    Lowerer::lower(program)
}
