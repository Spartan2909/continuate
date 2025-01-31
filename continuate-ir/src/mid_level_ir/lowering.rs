use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::TypeRef;
use crate::high_level_ir::Expr as HirExpr;
use crate::high_level_ir::ExprArray as HirExprArray;
use crate::high_level_ir::ExprAssign as HirExprAssign;
use crate::high_level_ir::ExprBinary as HirExprBinary;
use crate::high_level_ir::ExprBlock as HirExprBlock;
use crate::high_level_ir::ExprCall as HirExprCall;
use crate::high_level_ir::ExprClosure as HirExprClosure;
use crate::high_level_ir::ExprConstructor as HirExprConstructor;
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

use std::cmp::Ordering;
use std::iter;
use std::mem;

use bumpalo::Bump;

use continuate_utils::collect_into;
use continuate_utils::HashMap;
use continuate_utils::Vec;

use hashbrown::hash_map::Entry;

use itertools::Itertools as _;

struct ExprGet<'arena> {
    object: Expr<'arena>,
    object_ty: TypeRef,
    field: usize,
}

enum ArmData {
    Variant(MatchVariant),
    Wildcard,
    None,
}

struct MatchVariant {
    variant: usize,
    block: BlockId,
}

struct Lowerer<'a, 'arena> {
    arena: &'arena Bump,
    program: Program<'arena>,
    environment: HashMap<'arena, Ident, TypeRef>,
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
            HirType::Unknown => unreachable!(),
            HirType::None => Type::None,
        }
    }

    fn expr_list(
        &mut self,
        exprs: &[HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Vec<'arena, Expr<'arena>> {
        let initial = Vec::new_in(self.arena);
        collect_into(
            exprs.iter().map(|expr| self.expr(expr, block, function)),
            initial,
        )
    }

    fn block(
        &mut self,
        exprs: &[HirExpr],
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let mut exprs = self.expr_list(exprs, block, function);
        let last_expr = exprs.pop().unwrap_or_else(|| {
            let ty = self
                .program
                .insert_type(Type::Tuple(Vec::new_in(self.arena)), self.arena)
                .0;
            Expr::Tuple {
                ty,
                values: Vec::new_in(self.arena),
            }
        });
        for expr in exprs {
            block.exprs.push(expr);
        }
        last_expr
    }

    fn expr_block(
        &mut self,
        expr: &HirExprBlock,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        self.block(&expr.exprs, block, function)
    }

    fn expr_tuple(
        &mut self,
        expr: &HirExprTuple,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let elements = self.expr_list(&expr.exprs, block, function);

        let mut values = Vec::with_capacity_in(elements.len(), self.arena);
        values.extend(elements);
        Expr::Tuple {
            ty: expr.ty,
            values,
        }
    }

    fn expr_constructor(
        &mut self,
        expr: &HirExprConstructor,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let fields = self.expr_list(&expr.fields, block, function);

        let mut new_fields = Vec::with_capacity_in(fields.len(), self.arena);
        new_fields.extend(fields);
        let ty = expr.ty;
        Expr::Constructor {
            ty,
            index: expr.index,
            fields: new_fields,
        }
    }

    fn expr_array(
        &mut self,
        expr: &HirExprArray,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let array = self.expr_list(&expr.exprs, block, function);
        let mut values = Vec::with_capacity_in(array.len(), self.arena);
        values.extend(array);
        Expr::Array {
            ty: expr.ty,
            values,
            value_ty: expr.element_ty,
        }
    }

    fn expr_get_impl(
        &mut self,
        object: &HirExpr,
        object_ty: TypeRef,
        field: usize,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> ExprGet<'arena> {
        let object = self.expr(object, block, function);
        ExprGet {
            object,
            object_ty,
            field,
        }
    }

    fn expr_get(
        &mut self,
        expr: &HirExprGet,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let ExprGet {
            object,
            object_ty,
            field,
        } = self.expr_get_impl(&expr.object, expr.object_ty, expr.field, block, function);
        Expr::Get {
            object: self.arena.alloc(object),
            object_ty,
            object_variant: None,
            field,
        }
    }

    fn expr_set(
        &mut self,
        expr: &HirExprSet,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let ExprGet {
            object,
            object_ty,
            field,
        } = self.expr_get_impl(&expr.object, expr.object_ty, expr.field, block, function);

        let value = self.expr(&expr.value, block, function);

        let expr = Expr::Set {
            object: self.arena.alloc(object),
            object_ty,
            object_variant: None,
            field,
            value: self.arena.alloc(value),
        };
        expr
    }

    fn expr_call(
        &mut self,
        expr: &HirExprCall,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let callee = self.expr(&expr.callee, block, function);
        let params = self.expr_list(&expr.args, block, function);

        let mut new_params = Vec::with_capacity_in(params.len(), self.arena);
        new_params.extend(params);
        let callee_ty = self
            .program
            .types
            .get_by_left(&expr.callee_ty)
            .unwrap()
            .as_function()
            .unwrap();
        let expr = Expr::Call {
            callee: self.arena.alloc(callee),
            callee_ty,
            args: new_params,
        };
        expr
    }

    fn expr_cont_application(
        &mut self,
        expr: &HirExprContApplication,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let callee = self.expr(&expr.callee, block, function);

        let mut new_continuations = HashMap::with_capacity_in(expr.continuations.len(), self.arena);
        for (&ident, expr) in &expr.continuations {
            let expr = self.expr(expr, block, function);
            new_continuations.insert(ident, expr);
        }

        let expr = Expr::ContApplication(self.arena.alloc(callee), new_continuations);
        expr
    }

    fn expr_unary(
        &mut self,
        expr: &HirExprUnary,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let operand = self.expr(&expr.right, block, function);
        let expr = Expr::Unary {
            operator: expr.op,
            operand: self.arena.alloc(operand),
            operand_ty: expr.right_ty,
        };
        expr
    }

    fn expr_binary(
        &mut self,
        expr: &HirExprBinary,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let left = self.expr(&expr.left, block, function);
        let right = self.expr(&expr.right, block, function);

        let expr = Expr::Binary {
            left: self.arena.alloc(left),
            left_ty: expr.left_ty,
            operator: expr.op,
            right: self.arena.alloc(right),
            right_ty: expr.right_ty,
        };
        expr
    }

    fn expr_declare(
        &mut self,
        expr: &HirExprDeclare,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let right = self.expr(&expr.expr, block, function);

        function.declarations.insert(expr.ident, (expr.ty, None));
        let expr = Expr::Assign {
            ident: expr.ident,
            expr: self.arena.alloc(right),
        };
        expr
    }

    fn expr_assign(
        &mut self,
        expr: &HirExprAssign,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let right = self.expr(&expr.expr, block, function);

        let expr = Expr::Assign {
            ident: expr.ident,
            expr: self.arena.alloc(right),
        };
        expr
    }

    fn order_patterns<'b>(
        fields: &'b [Pattern<'b>],
    ) -> impl Iterator<Item = (usize, &'b Pattern<'b>)> {
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
    ) -> ArmData {
        let (scrutinee, scrutinee_ty_ref) = scrutinee;
        let scrutinee_ty = *self.program.types.get_by_left(&scrutinee_ty_ref).unwrap();

        match *arm_pat {
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
                ty: _,
                variant,
                ref fields,
            } => {
                for (field, pattern) in Self::order_patterns(fields) {
                    let get = Expr::Get {
                        object: scrutinee,
                        object_ty: scrutinee_ty_ref,
                        object_variant: variant,
                        field,
                    };
                    let get = self.arena.alloc(get);
                    let field_ty_ref = scrutinee_ty.field(variant, field).unwrap();
                    let mut new_block = Block::new(self.arena);
                    let new_block_id = function.block();
                    match self.pattern(
                        (get, field_ty_ref),
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
                        }
                    }
                }
                if let Some(variant) = variant {
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
        expr: &HirExprMatch,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let scrutinee = self.expr(&expr.scrutinee, block, function);
        let scrutinee = &*self.arena.alloc(scrutinee);

        let mut discriminants = vec![];
        let otherwise = function.block();
        let next_id = function.block();

        for (arm_pat, arm) in &expr.arms {
            let mut arm_block = Block::new(self.arena);
            let mut arm_block_id = function.block();

            let arm_data = self.pattern(
                (scrutinee, expr.scrutinee_ty),
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

        let current_block = mem::replace(block, Block::new(self.arena));
        function.blocks.insert(self.current_block, current_block);
        self.current_block = next_id;

        let scrutinee = if discriminants.is_empty() {
            scrutinee
        } else {
            self.arena.alloc(Expr::Intrinsic {
                intrinsic: Intrinsic::Discriminant,
                value: scrutinee,
                value_ty: expr.scrutinee_ty,
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
                discriminants
                    .iter()
                    .map(|&MatchVariant { variant, block }| (variant as i64, block)),
                HashMap::new_in(self.arena),
            ),
            otherwise,
        };

        expr
    }

    fn expr_closure(&mut self, expr: &HirExprClosure) -> Expr<'arena> {
        let func = &self.hir_program.functions[&expr.func];
        let captures = collect_into(
            func.captures
                .iter()
                .map(|&ident| (ident, self.environment[&ident])),
            HashMap::new_in(self.arena),
        );

        let func = self.function(func, captures.clone());
        self.program
            .functions
            .insert(expr.func, self.arena.alloc(func));

        let func_ref = expr.func;
        Expr::Closure { func_ref, captures }
    }

    fn expr_intrinsic(
        &mut self,
        expr: &HirExprIntrinsic,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
        let value = self.expr(&expr.value, block, function);
        Expr::Intrinsic {
            intrinsic: expr.intrinsic,
            value: self.arena.alloc(value),
            value_ty: expr.value_ty,
        }
    }

    fn expr(
        &mut self,
        expr: &HirExpr,
        block: &mut Block<'arena>,
        function: &mut Function<'arena>,
    ) -> Expr<'arena> {
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
            HirExpr::Unreachable => Expr::Unreachable,
        }
    }

    fn function(
        &mut self,
        function: &HirFunction,
        captures: HashMap<'arena, Ident, TypeRef>,
    ) -> Function<'arena> {
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
        let body = self.block(&function.body, &mut block, &mut mir_function);
        block.exprs.push(body);
        mir_function.blocks.insert(self.current_block, block);

        mir_function
    }

    fn lower(arena: &'arena Bump, program: &'a HirProgram<'a>) -> Program<'arena> {
        let mut lowerer = Lowerer {
            arena,
            program: Program::new(program, arena),
            environment: HashMap::new_in(arena),
            current_block: Function::entry_point(),
            hir_program: program,
        };

        for (&type_ref, &ty) in &program.types {
            if *ty == HirType::Unknown {
                continue;
            }
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
                .alloc(lowerer.function(function, HashMap::new_in(arena)));
            lowerer.program.functions.insert(func_ref, function);
        }

        lowerer.program
    }
}

pub fn lower<'a, 'arena>(program: &'a HirProgram<'a>, arena: &'arena Bump) -> Program<'arena> {
    Lowerer::lower(arena, program)
}
