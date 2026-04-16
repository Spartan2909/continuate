use crate::{
    common::{FuncRef, Ident, Literal, UserDefinedTyRef},
    high_level_ir::{
        BinaryOp, DestructureFields, Expr, ExprArray, ExprAssign, ExprBinary, ExprBlock, ExprCall,
        ExprConstructor, ExprConstructorFields, ExprDeclare, ExprGet, ExprIdent, ExprMatch,
        ExprSet, ExprTuple, ExprUnary, Function, Pattern, Program, Type, UnaryOp, UserDefinedType,
        UserDefinedTypeFields,
    },
};

use std::{collections::HashMap, iter, sync::Arc};

use continuate_error::Span;

use continuate_frontend::{
    BinaryOp as AstBinaryOp, Expr as AstExpr, Function as AstFunction, Ident as AstIdent, Item,
    Literal as AstLiteral, NameMap, Path as AstPath, Path, Pattern as AstPattern,
    Program as AstProgram, Type as AstType, UnaryOp as AstUnaryOp,
    UserDefinedTy as AstUserDefinedTy, UserDefinedTyFields as AstUserDefinedTyFields,
};

struct Lowerer<'a> {
    program: Program<()>,
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

    fn resolve_ty_path(&mut self, path: &Path) -> Option<Arc<Type>> {
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

    fn ty(&mut self, ty: &AstType) -> Arc<Type> {
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
                positional,
                named,
                span: _,
            } => {
                let ty = Type::function(
                    positional.iter().map(|ty| self.ty(ty)).collect(),
                    named
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
                let ty = Arc::new(UserDefinedType::Product(self.ty_fields(fields)));
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
                    .insert(self.user_defined_types[&name.span], Arc::new(ty));
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

    fn expr_literal(literal: &AstLiteral) -> Expr<()> {
        match *literal {
            AstLiteral::Int(value, _) => Expr::Literal(Literal::Int(value)),
            AstLiteral::Float(value, _) => Expr::Literal(Literal::Float(value)),
            AstLiteral::String(value, _) => Expr::Literal(Literal::String(value.to_string())),
        }
    }

    fn expr_path(&self, path: &AstPath) -> Expr<()> {
        if let Some(ident) = path.as_ident()
            && let Some(ident) = self.ident(ident)
        {
            return Expr::Ident(ExprIdent { ident });
        }

        Expr::Function(self.resolve_fn_path(path).unwrap())
    }

    fn expr_block(&mut self, exprs: &[AstExpr], tail: Option<&AstExpr>) -> Expr<()> {
        let exprs = exprs
            .iter()
            .chain(tail)
            .map(|expr| self.expr(expr))
            .collect();
        Expr::Block(ExprBlock { exprs })
    }

    fn expr_tuple(&mut self, exprs: &[AstExpr]) -> Expr<()> {
        let exprs = exprs.iter().map(|expr| self.expr(expr)).collect();
        Expr::Tuple(ExprTuple { exprs })
    }

    #[expect(
        clippy::map_unwrap_or,
        reason = "required to satisfy the borrow checker"
    )]
    fn expr_named_constructor(
        &mut self,
        path: &AstPath,
        fields: &[(AstIdent, Option<AstExpr>)],
    ) -> Expr<()> {
        let ty = self.resolve_ty_path(path).unwrap();
        let fields = fields
            .iter()
            .map(|(ident, expr)| {
                (
                    ident.string.to_string(),
                    expr.as_ref()
                        .map(|expr| self.expr(expr))
                        .unwrap_or_else(|| {
                            Expr::Ident(ExprIdent {
                                ident: self.ident(ident).unwrap(),
                            })
                        }),
                )
            })
            .collect();
        Expr::Constructor(ExprConstructor {
            ty,
            variant: None,
            fields: ExprConstructorFields::Named(fields),
        })
    }

    fn expr_array(&mut self, exprs: &[AstExpr]) -> Expr<()> {
        let exprs = exprs.iter().map(|expr| self.expr(expr)).collect();
        Expr::Array(ExprArray { exprs })
    }

    #[expect(
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

    fn expr_match(&mut self, scrutinee: &AstExpr, arms: &[(AstPattern, AstExpr)]) -> Expr<()> {
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

    fn expr_get(&mut self, object: &AstExpr, field: &AstIdent) -> Expr<()> {
        Expr::Get(ExprGet {
            object: Box::new(self.expr(object)),
            field: field.string.to_string(),
        })
    }

    fn expr_set(&mut self, object: &AstExpr, field: &AstIdent, value: &AstExpr) -> Expr<()> {
        Expr::Set(ExprSet {
            object: Box::new(self.expr(object)),
            field: field.string.to_string(),
            value: Box::new(self.expr(value)),
        })
    }

    #[expect(
        clippy::map_unwrap_or,
        reason = "required to satisfy the borrow checker"
    )]
    fn expr_call(
        &mut self,
        callee: &AstExpr,
        positional: &[AstExpr],
        named: &[(AstIdent, Option<AstExpr>)],
    ) -> Expr<()> {
        let positional = positional.iter().map(|expr| self.expr(expr)).collect();
        let named = named
            .iter()
            .map(|(ident, expr)| {
                (
                    self.ident(ident).unwrap(),
                    expr.as_ref()
                        .map(|expr| self.expr(expr))
                        .unwrap_or_else(|| {
                            Expr::Ident(ExprIdent {
                                ident: self.ident(ident).unwrap(),
                            })
                        }),
                )
            })
            .collect();
        Expr::Call(ExprCall {
            callee: Box::new(self.expr(callee)),
            positional,
            named,
        })
    }

    fn expr_unary(&mut self, operator: &AstUnaryOp, operand: &AstExpr) -> Expr<()> {
        let op = match operator {
            AstUnaryOp::Neg(_) => UnaryOp::Neg,
            AstUnaryOp::Not(_) => UnaryOp::Not,
        };
        Expr::Unary(ExprUnary {
            op,
            right: Box::new(self.expr(operand)),
        })
    }

    fn expr_binary(&mut self, left: &AstExpr, operator: &AstBinaryOp, right: &AstExpr) -> Expr<()> {
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

    #[expect(clippy::map_unwrap_or, reason = "required by the borrow checker")]
    fn expr_declare(&mut self, name: &AstIdent, ty: Option<&AstType>, value: &AstExpr) -> Expr<()> {
        Expr::Declare(ExprDeclare {
            ident: self.ident(name).unwrap(),
            ty: ty
                .map(|ty| self.ty(ty))
                .unwrap_or_else(|| self.program.insert_type(Type::Unknown)),
            expr: Box::new(self.expr(value)),
        })
    }

    fn expr_assign(&mut self, name: &AstIdent, value: &AstExpr) -> Expr<()> {
        Expr::Assign(ExprAssign {
            ident: self.ident(name).unwrap(),
            expr: Box::new(self.expr(value)),
        })
    }

    fn expr(&mut self, expr: &AstExpr) -> Expr<()> {
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
                positional,
                named,
                paren_span: _,
            } => self.expr_call(callee, positional, named),
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

        ir_fun.positional = fun
            .positional
            .iter()
            .map(|(name, ty)| (self.ident(name).unwrap(), self.ty(ty)))
            .collect();

        ir_fun.named = fun
            .named
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

    fn lower(mut self) -> Program<()> {
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

#[inline]
pub fn lower(ast: &AstProgram, names: NameMap, program_name: String) -> Program<()> {
    Lowerer::new(program_name, ast, names).lower()
}
