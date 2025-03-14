use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Literal;
use crate::common::UserDefinedTyRef;
use crate::high_level_ir::BinaryOp;
use crate::high_level_ir::DestructureFields;
use crate::high_level_ir::Expr;
use crate::high_level_ir::ExprArray;
use crate::high_level_ir::ExprAssign;
use crate::high_level_ir::ExprBinary;
use crate::high_level_ir::ExprBlock;
use crate::high_level_ir::ExprCall;
use crate::high_level_ir::ExprConstructor;
use crate::high_level_ir::ExprConstructorFields;
use crate::high_level_ir::ExprContApplication;
use crate::high_level_ir::ExprDeclare;
use crate::high_level_ir::ExprGet;
use crate::high_level_ir::ExprMatch;
use crate::high_level_ir::ExprSet;
use crate::high_level_ir::ExprTuple;
use crate::high_level_ir::ExprUnary;
use crate::high_level_ir::Function;
use crate::high_level_ir::Pattern;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;
use crate::high_level_ir::UnaryOp;
use crate::high_level_ir::UserDefinedType;
use crate::high_level_ir::UserDefinedTypeFields;

use std::iter;

use bumpalo::Bump;

use continuate_error::Span;

use continuate_frontend::BinaryOp as AstBinaryOp;
use continuate_frontend::Expr as AstExpr;
use continuate_frontend::Function as AstFunction;
use continuate_frontend::Ident as AstIdent;
use continuate_frontend::Item;
use continuate_frontend::Literal as AstLiteral;
use continuate_frontend::NameMap;
use continuate_frontend::Path as AstPath;
use continuate_frontend::Path;
use continuate_frontend::Pattern as AstPattern;
use continuate_frontend::Program as AstProgram;
use continuate_frontend::Type as AstType;
use continuate_frontend::UnaryOp as AstUnaryOp;
use continuate_frontend::UserDefinedTy as AstUserDefinedTy;
use continuate_frontend::UserDefinedTyFields as AstUserDefinedTyFields;

use continuate_utils::collect_into;
use continuate_utils::HashMap;
use continuate_utils::Vec;

struct Lowerer<'a, 'arena> {
    arena: &'arena Bump,
    program: Program<'arena>,
    ast: &'a AstProgram<'a>,
    user_defined_types: HashMap<'arena, Span, UserDefinedTyRef>,
    names: NameMap,
    idents: HashMap<'arena, Span, Ident>,
    functions: HashMap<'arena, Span, FuncRef>,
}

impl<'a, 'arena> Lowerer<'a, 'arena> {
    fn new(
        program_name: String,
        arena: &'arena Bump,
        ast: &'a AstProgram<'a>,
        names: NameMap,
    ) -> Lowerer<'a, 'arena> {
        Lowerer {
            arena,
            program: Program::new(program_name, arena),
            ast,
            user_defined_types: HashMap::new_in(arena),
            names,
            idents: HashMap::new_in(arena),
            functions: HashMap::new_in(arena),
        }
    }

    fn resolve_ty_path(&mut self, path: &Path) -> Option<&'arena Type<'arena>> {
        self.names
            .get_path(path)
            .and_then(|span| self.user_defined_types.get(&span))
            .map(|&ty| self.program.insert_type(Type::UserDefined(ty), self.arena))
    }

    fn resolve_fn_path(&self, path: &Path) -> Option<FuncRef> {
        self.names
            .get_path(path)
            .and_then(|span| self.functions.get(&span))
            .copied()
    }

    fn ident(&self, ident: &AstIdent) -> Option<Ident> {
        self.names
            .get_ident(ident)
            .and_then(|ident| self.idents.get(&ident))
            .copied()
    }

    fn ty(&mut self, ty: &AstType) -> &'arena Type<'arena> {
        match ty {
            AstType::Bool(_) => self.program.insert_type(Type::Bool, self.arena),
            AstType::Int(_) => self.program.insert_type(Type::Int, self.arena),
            AstType::Float(_) => self.program.insert_type(Type::Float, self.arena),
            AstType::String(_) => self.program.insert_type(Type::String, self.arena),
            AstType::Path(path) => self.resolve_ty_path(path).unwrap(),
            AstType::Tuple { items, span: _ } => {
                let ty = Type::Tuple(collect_into(
                    Vec::new_in(self.arena),
                    items.iter().map(|ty| self.ty(ty)),
                ));
                self.program.insert_type(ty, self.arena)
            }
            AstType::Function {
                params,
                continuations,
                span: _,
            } => {
                let ty = Type::function(
                    collect_into(Vec::new_in(self.arena), params.iter().map(|ty| self.ty(ty))),
                    collect_into(
                        HashMap::new_in(self.arena),
                        continuations.iter().map(|(name, ty)| {
                            (self.program.continuation_ident(name.string), self.ty(ty))
                        }),
                    ),
                );
                self.program.insert_type(ty, self.arena)
            }
        }
    }

    fn declare_ty(&mut self, ty: &AstUserDefinedTy) {
        self.user_defined_types
            .insert(ty.name().span, UserDefinedTyRef::new());
    }

    fn ty_fields(&mut self, fields: &AstUserDefinedTyFields) -> UserDefinedTypeFields<'arena> {
        match fields {
            AstUserDefinedTyFields::Named(fields) => UserDefinedTypeFields::Named(collect_into(
                Vec::new_in(self.arena),
                fields
                    .iter()
                    .map(|(ident, ty)| (ident.string.to_owned(), self.ty(ty))),
            )),
            AstUserDefinedTyFields::Anonymous(fields) => UserDefinedTypeFields::Anonymous(
                collect_into(Vec::new_in(self.arena), fields.iter().map(|ty| self.ty(ty))),
            ),
            AstUserDefinedTyFields::Unit => UserDefinedTypeFields::Unit,
        }
    }

    fn define_ty(&mut self, ty: &AstUserDefinedTy) {
        match ty {
            AstUserDefinedTy::Product {
                name,
                fields,
                span: _,
            } => {
                let ty = self
                    .arena
                    .alloc(UserDefinedType::Product(self.ty_fields(fields)));
                self.program
                    .user_defined_types
                    .insert(self.user_defined_types[&name.span], ty);
            }
            AstUserDefinedTy::Sum {
                name,
                variants,
                span: _,
            } => {
                let ty = UserDefinedType::Sum(collect_into(
                    Vec::new_in(self.arena),
                    variants
                        .iter()
                        .map(|(name, fields)| (name.string.to_owned(), self.ty_fields(fields))),
                ));
                self.program
                    .user_defined_types
                    .insert(self.user_defined_types[&name.span], self.arena.alloc(ty));
            }
        }
    }

    fn declare_fns(&mut self) {
        self.functions.extend(
            self.ast
                .items
                .iter()
                .filter_map(|item| Some(item.as_function()?.name.span))
                .zip(iter::repeat_with(FuncRef::new)),
        );
    }

    fn declare_idents(&mut self) {
        self.idents.extend(
            self.names
                .ident_definitions()
                .zip(iter::repeat_with(Ident::new)),
        );
    }

    fn expr_literal(literal: &AstLiteral) -> Expr<'arena> {
        match *literal {
            AstLiteral::Int(value, _) => Expr::Literal(Literal::Int(value)),
            AstLiteral::Float(value, _) => Expr::Literal(Literal::Float(value)),
            AstLiteral::String(value, _) => Expr::Literal(Literal::String(value.to_string())),
        }
    }

    fn expr_path(&self, path: &AstPath) -> Expr<'arena> {
        if let Some(ident) = path.as_ident() {
            if let Some(ident) = self.ident(ident) {
                return Expr::Ident(ident);
            }
        }

        Expr::Function(self.resolve_fn_path(path).unwrap())
    }

    fn expr_block(&mut self, exprs: &[AstExpr], tail: Option<&AstExpr>) -> Expr<'arena> {
        let mut result =
            Vec::with_capacity_in(exprs.len() + usize::from(tail.is_some()), self.arena);
        result.extend(exprs.iter().chain(tail).map(|expr| self.expr(expr)));
        Expr::Block(ExprBlock {
            exprs: result,
            ty: self.program.insert_type(Type::Unknown, self.arena),
        })
    }

    fn expr_tuple(&mut self, exprs: &[AstExpr]) -> Expr<'arena> {
        let mut result = Vec::with_capacity_in(exprs.len(), self.arena);
        result.extend(exprs.iter().map(|expr| self.expr(expr)));
        Expr::Tuple(ExprTuple {
            exprs: result,
            ty: self.program.insert_type(Type::Unknown, self.arena),
        })
    }

    #[allow(
        clippy::map_unwrap_or,
        reason = "required to satisfy the borrow checker"
    )]
    fn expr_named_constructor(
        &mut self,
        path: &AstPath,
        fields: &[(AstIdent, Option<AstExpr>)],
    ) -> Expr<'arena> {
        let ty = self.resolve_ty_path(path).unwrap();
        let mut result = Vec::with_capacity_in(fields.len(), self.arena);
        result.extend(fields.iter().map(|(ident, expr)| {
            (
                ident.string.to_string(),
                expr.as_ref()
                    .map(|expr| self.expr(expr))
                    .unwrap_or_else(|| Expr::Ident(self.ident(ident).unwrap())),
            )
        }));
        Expr::Constructor(ExprConstructor {
            ty,
            variant: None,
            fields: ExprConstructorFields::Named(result),
        })
    }

    fn expr_array(&mut self, exprs: &[AstExpr]) -> Expr<'arena> {
        let mut result = Vec::with_capacity_in(exprs.len(), self.arena);
        result.extend(exprs.iter().map(|expr| self.expr(expr)));
        let ty_unknown = self.program.insert_type(Type::Unknown, self.arena);
        Expr::Array(ExprArray {
            exprs: result,
            ty: ty_unknown,
            element_ty: ty_unknown,
        })
    }

    #[allow(
        clippy::map_unwrap_or,
        reason = "required to satisfy the borrow checker"
    )]
    fn pattern(&mut self, pattern: &AstPattern) -> Pattern<'arena> {
        match pattern {
            AstPattern::Wildcard(_) => Pattern::Wildcard,
            AstPattern::Ident(ident) => Pattern::Ident(self.ident(ident).unwrap()),
            AstPattern::NamedDestructure {
                ty,
                fields,
                brace_span: _,
            } => {
                let mut result = Vec::with_capacity_in(fields.len(), self.arena);
                result.extend(fields.iter().map(|(ident, pat)| {
                    (
                        ident.string.to_string(),
                        self.pattern(&pat.clone().unwrap_or(AstPattern::Ident(*ident))),
                    )
                }));
                Pattern::Destructure {
                    ty: self.resolve_ty_path(ty).unwrap(),
                    variant: None,
                    fields: DestructureFields::Named(result),
                }
            }
            AstPattern::AnonymousDestructure {
                ty,
                fields,
                paren_span: _,
            } => {
                let mut result = Vec::with_capacity_in(fields.len(), self.arena);
                result.extend(fields.iter().map(|pat| self.pattern(pat)));
                Pattern::Destructure {
                    ty: ty
                        .as_ref()
                        .map(|ty| self.resolve_ty_path(ty).unwrap())
                        .unwrap_or_else(|| self.program.insert_type(Type::Unknown, self.arena)),
                    variant: None,
                    fields: DestructureFields::Anonymous(result),
                }
            }
        }
    }

    fn expr_match(&mut self, scrutinee: &AstExpr, arms: &[(AstPattern, AstExpr)]) -> Expr<'arena> {
        let scrutinee = self.expr(scrutinee);
        let mut result = Vec::with_capacity_in(arms.len(), self.arena);
        result.extend(
            arms.iter()
                .map(|(pat, expr)| (self.pattern(pat), self.expr(expr))),
        );
        let ty_unknown = self.program.insert_type(Type::Unknown, self.arena);
        Expr::Match(ExprMatch {
            scrutinee: Box::new_in(scrutinee, self.arena),
            scrutinee_ty: ty_unknown,
            ty: ty_unknown,
            arms: result,
        })
    }

    fn expr_get(&mut self, object: &AstExpr, field: &AstIdent) -> Expr<'arena> {
        Expr::Get(ExprGet {
            object: Box::new_in(self.expr(object), self.arena),
            object_ty: self.program.insert_type(Type::Unknown, self.arena),
            field: field.string.to_string(),
        })
    }

    fn expr_set(&mut self, object: &AstExpr, field: &AstIdent, value: &AstExpr) -> Expr<'arena> {
        let ty_unknown = self.program.insert_type(Type::Unknown, self.arena);
        Expr::Set(ExprSet {
            object: Box::new_in(self.expr(object), self.arena),
            object_ty: ty_unknown,
            field: field.string.to_string(),
            value: Box::new_in(self.expr(value), self.arena),
            value_ty: ty_unknown,
        })
    }

    fn expr_call(&mut self, callee: &AstExpr, arguments: &[AstExpr]) -> Expr<'arena> {
        let mut result = Vec::with_capacity_in(arguments.len(), self.arena);
        result.extend(arguments.iter().map(|expr| self.expr(expr)));
        Expr::Call(ExprCall {
            callee: Box::new_in(self.expr(callee), self.arena),
            callee_ty: self.program.insert_type(Type::Unknown, self.arena),
            args: result,
        })
    }

    #[allow(
        clippy::map_unwrap_or,
        reason = "required to satisfy the borrow checker"
    )]
    fn expr_cont_application(
        &mut self,
        callee: &AstExpr,
        arguments: &[(AstIdent, Option<AstExpr>)],
    ) -> Expr<'arena> {
        let mut continuations = HashMap::with_capacity_in(arguments.len(), self.arena);
        continuations.extend(arguments.iter().map(|(ident, expr)| {
            (
                self.ident(ident).unwrap(),
                expr.as_ref()
                    .map(|expr| self.expr(expr))
                    .unwrap_or_else(|| Expr::Ident(self.ident(ident).unwrap())),
            )
        }));
        Expr::ContApplication(ExprContApplication {
            callee: Box::new_in(self.expr(callee), self.arena),
            callee_ty: self.program.insert_type(Type::Unknown, self.arena),
            continuations,
        })
    }

    fn expr_unary(&mut self, operator: &AstUnaryOp, operand: &AstExpr) -> Expr<'arena> {
        let op = match operator {
            AstUnaryOp::Neg(_) => UnaryOp::Neg,
            AstUnaryOp::Not(_) => UnaryOp::Not,
        };
        Expr::Unary(ExprUnary {
            op,
            right: Box::new_in(self.expr(operand), self.arena),
            right_ty: self.program.insert_type(Type::Unknown, self.arena),
        })
    }

    fn expr_binary(
        &mut self,
        left: &AstExpr,
        operator: &AstBinaryOp,
        right: &AstExpr,
    ) -> Expr<'arena> {
        let op = match operator {
            AstBinaryOp::Add(_) => BinaryOp::Add,
            AstBinaryOp::Sub(_) => BinaryOp::Sub,
            AstBinaryOp::Mul(_) => BinaryOp::Mul,
            AstBinaryOp::Div(_) => BinaryOp::Div,
            AstBinaryOp::Rem(_) => BinaryOp::Rem,
            AstBinaryOp::Eq(_) => BinaryOp::Eq,
            AstBinaryOp::Ne(_) => BinaryOp::Ne,
            AstBinaryOp::Lt(_) => BinaryOp::Lt,
            AstBinaryOp::Le(_) => BinaryOp::Le,
            AstBinaryOp::Gt(_) => BinaryOp::Gt,
            AstBinaryOp::Ge(_) => BinaryOp::Ge,
        };
        let ty_unknown = self.program.insert_type(Type::Unknown, self.arena);
        Expr::Binary(ExprBinary {
            left: Box::new_in(self.expr(left), self.arena),
            left_ty: ty_unknown,
            op,
            right: Box::new_in(self.expr(right), self.arena),
            right_ty: ty_unknown,
        })
    }

    fn expr_declare(
        &mut self,
        name: &AstIdent,
        ty: Option<&AstType>,
        value: &AstExpr,
    ) -> Expr<'arena> {
        let ty_unknown = self.program.insert_type(Type::Unknown, self.arena);
        Expr::Declare(ExprDeclare {
            ident: self.ident(name).unwrap(),
            ty: ty.map_or(ty_unknown, |ty| self.ty(ty)),
            expr: Box::new_in(self.expr(value), self.arena),
        })
    }

    fn expr_assign(&mut self, name: &AstIdent, value: &AstExpr) -> Expr<'arena> {
        Expr::Assign(ExprAssign {
            ident: self.ident(name).unwrap(),
            expr: Box::new_in(self.expr(value), self.arena),
        })
    }

    fn expr(&mut self, expr: &AstExpr) -> Expr<'arena> {
        match expr {
            AstExpr::Literal(literal) => Self::expr_literal(literal),
            AstExpr::Path(path) => self.expr_path(path),
            AstExpr::Block {
                exprs,
                tail,
                span: _,
            } => self.expr_block(exprs, tail.as_deref()),
            AstExpr::Tuple { exprs, span: _ } => self.expr_tuple(exprs),
            AstExpr::NamedConstructor {
                path,
                fields,
                brace_span: _,
            } => self.expr_named_constructor(path, fields),
            AstExpr::Array { exprs, span: _ } => self.expr_array(exprs),
            AstExpr::Match {
                scrutinee,
                arms,
                brace_span: _,
            } => self.expr_match(scrutinee, arms),
            AstExpr::Get { object, field } => self.expr_get(object, field),
            AstExpr::Set {
                object,
                field,
                value,
            } => self.expr_set(object, field, value),
            AstExpr::Call {
                callee,
                arguments,
                paren_span: _,
            } => self.expr_call(callee, arguments),
            AstExpr::ContApplication {
                callee,
                arguments,
                bracket_span: _,
            } => self.expr_cont_application(callee, arguments),
            AstExpr::Unary { operator, operand } => self.expr_unary(operator, operand),
            AstExpr::Binary {
                left,
                operator,
                right,
            } => self.expr_binary(left, operator, right),
            AstExpr::Declare {
                name,
                ty,
                value,
                span: _,
            } => self.expr_declare(name, ty.as_ref(), value),
            AstExpr::Assign { name, value } => self.expr_assign(name, value),
        }
    }

    fn define_fn(&mut self, fun: &AstFunction) {
        let mut ir_fun = Function::new(fun.name.string.to_string(), self.arena);

        let mut params = Vec::with_capacity_in(fun.params.len(), self.arena);
        params.extend(
            fun.params
                .iter()
                .map(|(name, ty)| (self.ident(name).unwrap(), self.ty(ty))),
        );
        ir_fun.params = params;

        let mut continuations = HashMap::with_capacity_in(fun.continuations.len(), self.arena);
        continuations.extend(
            fun.continuations
                .iter()
                .map(|(name, ty)| (self.ident(name).unwrap(), self.ty(ty))),
        );
        ir_fun.continuations = continuations;

        ir_fun
            .body
            .extend(fun.body.iter().map(|expr| self.expr(expr)));

        self.program
            .functions
            .insert(self.functions[&fun.name.span], ir_fun);
    }

    fn lower(mut self) -> Program<'arena> {
        for ty in self.ast.items.iter().filter_map(Item::as_user_defined_ty) {
            self.declare_ty(ty);
        }

        for ty in self.ast.items.iter().filter_map(Item::as_user_defined_ty) {
            self.define_ty(ty);
        }

        self.declare_fns();

        self.declare_idents();

        for fun in self.ast.items.iter().filter_map(Item::as_function) {
            self.define_fn(fun);
        }

        self.program
    }
}

pub fn lower<'arena>(
    ast: &AstProgram,
    names: NameMap,
    program_name: String,
    arena: &'arena Bump,
) -> Program<'arena> {
    Lowerer::new(program_name, arena, ast, names).lower()
}
