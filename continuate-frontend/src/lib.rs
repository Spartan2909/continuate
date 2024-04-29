pub mod lexer;

use lexer::Ident;
use lexer::Literal;

use std::collections::HashMap;

use continuate_error::Span;

pub enum PathIdentSegment {
    Ident(Ident),
    Package(Span),
    Super(Span),
}

#[derive(Debug, Clone)]
pub struct PathSegment {
    pub ident: Ident,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Path {
    pub segments: Vec<PathSegment>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum Expr<'arena> {
    Literal(Literal),
    Ident(Ident),
    Block {
        exprs: Vec<Expr<'arena>>,
        span: Span,
    },
    Tuple {
        exprs: Vec<Expr<'arena>>,
        span: Span,
    },
    TupleConstructor {
        path: Path,
        fields: Vec<Expr<'arena>>,
        paren_span: Span,
    },
    NamedConstructor {
        path: Path,
        fields: Vec<(Ident, &'arena Expr<'arena>)>,
        brace_span: Span,
    },
    Array {
        exprs: Vec<Expr<'arena>>,
        span: Span,
    },

    Get {
        object: &'arena Expr<'arena>,
        field: Ident,
    },
    Set {
        object: &'arena Expr<'arena>,
        field: Ident,
        value: &'arena Expr<'arena>,
    },

    Call {
        callee: &'arena Expr<'arena>,
        arguments: Vec<Expr<'arena>>,
    },
    ContApplication {
        callee: &'arena Expr<'arena>,
        arguments: HashMap<Ident, Expr<'arena>>,
    },
}
