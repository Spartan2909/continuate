pub mod lexer;

use std::collections::HashMap;

use continuate_error::Span;

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64, Span),
    Float(f64, Span),
    String(String, Span),
}

#[derive(Debug, Clone)]
pub struct Ident {
    pub string: String,
    pub span: Span,
}

impl Ident {
    pub const fn new(string: String, span: Span) -> Ident {
        Ident { string, span }
    }
}

#[derive(Debug, Clone)]
pub enum PathIdentSegment {
    Ident(Ident),
    Package(Span),
    Super(Span),
}

#[derive(Debug, Clone)]
pub struct PathSegment {
    pub ident: PathIdentSegment,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Path {
    pub segments: Vec<PathSegment>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOp {
    Neg(Span),
    Not(Span),
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add(Span),
    Sub(Span),
    Mul(Span),
    Div(Span),
    Rem(Span),
    Eq(Span),
    Ne(Span),
    Lt(Span),
    Le(Span),
    Gt(Span),
    Ge(Span),
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Wildcard,
    Ident(Ident),
    Destructure { ty: Path, fields: Vec<Pattern> },
}

#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Literal),
    Ident(Ident),
    Block {
        exprs: Vec<Expr>,
        span: Span,
    },
    Tuple {
        exprs: Vec<Expr>,
        span: Span,
    },
    NamedConstructor {
        path: Path,
        fields: Vec<(Ident, Expr)>,
        brace_span: Span,
    },
    Array {
        exprs: Vec<Expr>,
        span: Span,
    },

    Get {
        object: Box<Expr>,
        field: Ident,
    },
    Set {
        object: Box<Expr>,
        field: Ident,
        value: Box<Expr>,
    },

    Call {
        callee: Box<Expr>,
        arguments: Vec<Expr>,
        paren_span: Span,
    },
    ContApplication {
        callee: Box<Expr>,
        arguments: HashMap<Ident, Expr>,
        bracket_span: Span,
    },

    Unary {
        operator: UnaryOp,
        operand: Box<Expr>,
    },
    Binary {
        left: Box<Expr>,
    },

    Declare {
        name: Ident,
        ty: Path,
        value: Box<Expr>,
        span: Span,
    },
    Assign {
        name: Ident,
        value: Box<Expr>,
    },

    Match {
        scrutinee: Box<Expr>,
        arms: Vec<(Pattern, Expr)>,
    },
}
