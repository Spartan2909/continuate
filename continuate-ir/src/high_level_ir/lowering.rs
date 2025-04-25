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

use std::collections::HashMap;
use std::iter;
use std::rc::Rc;

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

struct Lowerer<'a> {
    program: Program<Expr>,
    ast: &'a AstProgram<'a>,
    user_defined_types: HashMap<Span, UserDefinedTyRef>,
    names: NameMap,
    idents: HashMap<Span, Ident>,
    functions: HashMap<Span, FuncRef>,
}

impl<'a> Lowerer<'a> {
    fn new(program_name: String, ast: &'a AstProgram<'a>, names: NameMap) -> Lowerer<'a> {
        Lowerer {
            program: Program::new(program_name),
            ast,
            user_defined_types: HashMap::new(),
            names,
            idents: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    fn resolve_ty_path(&mut self, path: &Path) -> Option<Rc<Type>> {
        self.names
            .get_path(path)
            .and_then(|span| self.user_defined_types.get(&span))
            .map(|&ty| self.program.insert_type(Type::UserDefined(ty)))
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

    fn ty(&mut self, ty: &AstType) -> Rc<Type> {
        match ty {
            AstType::Bool(_) => self.program.insert_type(Type::Bool),
            AstType::Int(_) => self.program.insert_type(Type::Int),
            AstType::Float(_) => self.program.insert_type(Type::Float),
            AstType::String(_) => self.program.insert_type(Type::String),
            AstType::Path(path) => self.resolve_ty_path(path).unwrap(),
            AstType::Tuple { items, span: _ } => {
                let ty = Type::Tuple(items.iter().map(|ty| self.ty(ty)).collect());
                self.program.insert_type(ty)
            }
            AstType::Function {
                params,
                continuations,
                span: _,
            } => {
                let ty = Type::function(
                    params.iter().map(|ty| self.ty(ty)).collect(),
                    continuations
                        .iter()
                        .map(|(name, ty)| {
                            (
                                self.program.continuation_ident(name.string, name.span),
                                self.ty(ty),
                            )
                        })
                        .collect(),
                );
                self.program.insert_type(ty)
            }
        }
    }

    fn declare_ty(&mut self, ty: &AstUserDefinedTy) {
        self.user_defined_types
            .insert(ty.name().span, UserDefinedTyRef::new());
    }

    fn ty_fields(&mut self, fields: &AstUserDefinedTyFields) -> UserDefinedTypeFields {
        match fields {
            AstUserDefinedTyFields::Named(fields) => UserDefinedTypeFields::Named(
                fields
                    .iter()
                    .map(|(ident, ty)| (ident.string.to_owned(), self.ty(ty)))
                    .collect(),
            ),
            AstUserDefinedTyFields::Anonymous(fields) => {
                UserDefinedTypeFields::Anonymous(fields.iter().map(|ty| self.ty(ty)).collect())
            }
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
                let ty = Rc::new(UserDefinedType::Product(self.ty_fields(fields)));
                self.program
                    .user_defined_types
                    .insert(self.user_defined_types[&name.span], ty);
            }
            AstUserDefinedTy::Sum {
                name,
                variants,
                span: _,
            } => {
                let ty = UserDefinedType::Sum(
                    variants
                        .iter()
                        .map(|(name, fields)| (name.string.to_owned(), self.ty_fields(fields)))
                        .collect(),
                );
                self.program
                    .user_defined_types
                    .insert(self.user_defined_types[&name.span], Rc::new(ty));
            }
        }
    }

    fn declare_fns(&mut self) {
        let mut fn_main = None;
        self.functions.extend(
            self.ast
                .items
                .iter()
                .filter_map(|item| {
                    let name = item.as_function()?.name;
                    if name.string == "main" {
                        fn_main = Some(name.span);
                        None
                    } else {
                        Some(name.span)
                    }
                })
                .zip(iter::repeat_with(FuncRef::new)),
        );
        if let Some(fn_main) = fn_main {
            self.functions.insert(fn_main, FuncRef::ENTRY_POINT);
        }
    }

    fn declare_idents(&mut self) {
        self.idents
            .extend(self.names.ident_definitions().map(|ident| {
                if let Some(name) = &ident.continuation_name {
                    (
                        ident.span,
                        self.program.continuation_ident(name, ident.span),
                    )
                } else {
                    (ident.span, Ident::new(ident.span))
                }
            }));
    }

    fn expr_literal(literal: &AstLiteral) -> Expr {
        match *literal {
            AstLiteral::Int(value, _) => Expr::Literal(Literal::Int(value)),
            AstLiteral::Float(value, _) => Expr::Literal(Literal::Float(value)),
            AstLiteral::String(value, _) => Expr::Literal(Literal::String(value.to_string())),
        }
    }

    fn expr_path(&self, path: &AstPath) -> Expr {
        if let Some(ident) = path.as_ident() {
            if let Some(ident) = self.ident(ident) {
                return Expr::Ident(ident);
            }
        }

        Expr::Function(self.resolve_fn_path(path).unwrap())
    }

    fn expr_block(&mut self, exprs: &[AstExpr], tail: Option<&AstExpr>) -> Expr {
        let exprs = exprs
            .iter()
            .chain(tail)
            .map(|expr| self.expr(expr))
            .collect();
        Expr::Block(ExprBlock { exprs })
    }

    fn expr_tuple(&mut self, exprs: &[AstExpr]) -> Expr {
        let exprs = exprs.iter().map(|expr| self.expr(expr)).collect();
        Expr::Tuple(ExprTuple { exprs })
    }

    #[allow(
        clippy::map_unwrap_or,
        reason = "required to satisfy the borrow checker"
    )]
    fn expr_named_constructor(
        &mut self,
        path: &AstPath,
        fields: &[(AstIdent, Option<AstExpr>)],
    ) -> Expr {
        let ty = self.resolve_ty_path(path).unwrap();
        let fields = fields
            .iter()
            .map(|(ident, expr)| {
                (
                    ident.string.to_string(),
                    expr.as_ref()
                        .map(|expr| self.expr(expr))
                        .unwrap_or_else(|| Expr::Ident(self.ident(ident).unwrap())),
                )
            })
            .collect();
        Expr::Constructor(ExprConstructor {
            ty,
            variant: None,
            fields: ExprConstructorFields::Named(fields),
        })
    }

    fn expr_array(&mut self, exprs: &[AstExpr]) -> Expr {
        let exprs = exprs.iter().map(|expr| self.expr(expr)).collect();
        Expr::Array(ExprArray { exprs })
    }

    #[allow(
        clippy::map_unwrap_or,
        reason = "required to satisfy the borrow checker"
    )]
    fn pattern(&mut self, pattern: &AstPattern) -> Pattern {
        match pattern {
            AstPattern::Wildcard(_) => Pattern::Wildcard,
            AstPattern::Ident(ident) => Pattern::Ident(self.ident(ident).unwrap()),
            AstPattern::NamedDestructure {
                ty,
                fields,
                brace_span: _,
            } => {
                let fields = fields
                    .iter()
                    .map(|(ident, pat)| {
                        (
                            ident.string.to_string(),
                            self.pattern(&pat.clone().unwrap_or(AstPattern::Ident(*ident))),
                        )
                    })
                    .collect();
                Pattern::Destructure {
                    ty: self.resolve_ty_path(ty).unwrap(),
                    variant: None,
                    fields: DestructureFields::Named(fields),
                }
            }
            AstPattern::AnonymousDestructure {
                ty,
                fields,
                paren_span: _,
            } => {
                let fields = fields.iter().map(|pat| self.pattern(pat)).collect();
                Pattern::Destructure {
                    ty: ty
                        .as_ref()
                        .map(|ty| self.resolve_ty_path(ty).unwrap())
                        .unwrap_or_else(|| self.program.insert_type(Type::Unknown)),
                    variant: None,
                    fields: DestructureFields::Anonymous(fields),
                }
            }
        }
    }

    fn expr_match(&mut self, scrutinee: &AstExpr, arms: &[(AstPattern, AstExpr)]) -> Expr {
        let scrutinee = self.expr(scrutinee);
        let arms = arms
            .iter()
            .map(|(pat, expr)| (self.pattern(pat), self.expr(expr)))
            .collect();
        Expr::Match(ExprMatch {
            scrutinee: Box::new(scrutinee),
            arms,
        })
    }

    fn expr_get(&mut self, object: &AstExpr, field: &AstIdent) -> Expr {
        Expr::Get(ExprGet {
            object: Box::new(self.expr(object)),
            field: field.string.to_string(),
        })
    }

    fn expr_set(&mut self, object: &AstExpr, field: &AstIdent, value: &AstExpr) -> Expr {
        Expr::Set(ExprSet {
            object: Box::new(self.expr(object)),
            field: field.string.to_string(),
            value: Box::new(self.expr(value)),
        })
    }

    fn expr_call(&mut self, callee: &AstExpr, arguments: &[AstExpr]) -> Expr {
        let args = arguments.iter().map(|expr| self.expr(expr)).collect();
        Expr::Call(ExprCall {
            callee: Box::new(self.expr(callee)),
            args,
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
    ) -> Expr {
        let continuations = arguments
            .iter()
            .map(|(ident, expr)| {
                (
                    self.ident(ident).unwrap(),
                    expr.as_ref()
                        .map(|expr| self.expr(expr))
                        .unwrap_or_else(|| Expr::Ident(self.ident(ident).unwrap())),
                )
            })
            .collect();
        Expr::ContApplication(ExprContApplication {
            callee: Box::new(self.expr(callee)),
            continuations,
        })
    }

    fn expr_unary(&mut self, operator: &AstUnaryOp, operand: &AstExpr) -> Expr {
        let op = match operator {
            AstUnaryOp::Neg(_) => UnaryOp::Neg,
            AstUnaryOp::Not(_) => UnaryOp::Not,
        };
        Expr::Unary(ExprUnary {
            op,
            right: Box::new(self.expr(operand)),
        })
    }

    fn expr_binary(&mut self, left: &AstExpr, operator: &AstBinaryOp, right: &AstExpr) -> Expr {
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
        Expr::Binary(ExprBinary {
            left: Box::new(self.expr(left)),
            op,
            right: Box::new(self.expr(right)),
        })
    }

    fn expr_declare(&mut self, name: &AstIdent, ty: Option<&AstType>, value: &AstExpr) -> Expr {
        Expr::Declare(ExprDeclare {
            ident: self.ident(name).unwrap(),
            ty: ty.map(|ty| self.ty(ty)),
            expr: Box::new(self.expr(value)),
        })
    }

    fn expr_assign(&mut self, name: &AstIdent, value: &AstExpr) -> Expr {
        Expr::Assign(ExprAssign {
            ident: self.ident(name).unwrap(),
            expr: Box::new(self.expr(value)),
        })
    }

    fn expr(&mut self, expr: &AstExpr) -> Expr {
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
        let name = format!("{}::{}", self.program.name, fun.name.string);
        let mut ir_fun = Function::new(name);

        ir_fun.params = fun
            .params
            .iter()
            .map(|(name, ty)| (self.ident(name).unwrap(), self.ty(ty)))
            .collect();

        ir_fun.continuations = fun
            .continuations
            .iter()
            .map(|(name, ty)| (self.ident(name).unwrap(), self.ty(ty)))
            .collect();

        ir_fun
            .body
            .extend(fun.body.iter().map(|expr| self.expr(expr)));

        self.program
            .functions
            .insert(self.functions[&fun.name.span], ir_fun);
    }

    fn lower(mut self) -> Program<Expr> {
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

pub fn lower(ast: &AstProgram, names: NameMap, program_name: String) -> Program<Expr> {
    Lowerer::new(program_name, ast, names).lower()
}
