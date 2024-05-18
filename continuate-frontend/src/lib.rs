pub mod lexer;
pub mod parser;

use continuate_error::Span;

#[derive(Debug, Clone)]
pub enum Literal<'src> {
    Int(i64, Span),
    Float(f64, Span),
    String(&'src str, Span),
}

#[derive(Debug, Clone)]
pub struct Ident<'src> {
    pub string: &'src str,
    pub span: Span,
}

impl<'src> Ident<'src> {
    pub const fn new(string: &'src str, span: Span) -> Ident {
        Ident { string, span }
    }
}

#[derive(Debug, Clone)]
pub enum PathIdentSegment<'src> {
    Ident(Ident<'src>),
    Package(Span),
    Super(Span),
}

#[derive(Debug, Clone)]
pub struct PathSegment<'src> {
    pub ident: PathIdentSegment<'src>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Path<'src> {
    pub segments: Vec<PathSegment<'src>>,
    pub span: Span,
}

impl<'src> From<Ident<'src>> for Path<'src> {
    fn from(value: Ident<'src>) -> Self {
        let span = value.span;
        let segment = PathSegment {
            ident: PathIdentSegment::Ident(value),
            span,
        };
        Path {
            segments: vec![segment],
            span,
        }
    }
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
pub enum Pattern<'src> {
    Wildcard(Span),
    Ident(Ident<'src>),
    NamedDestructure {
        ty: Path<'src>,
        fields: Vec<(Ident<'src>, Option<Pattern<'src>>)>,
        brace_span: Span,
    },
    AnonymousDestructure {
        ty: Option<Path<'src>>,
        fields: Vec<Pattern<'src>>,
        paren_span: Span,
    },
}

#[derive(Debug, Clone)]
pub enum Expr<'src> {
    Literal(Literal<'src>),
    Path(Path<'src>),
    Block {
        exprs: Vec<Expr<'src>>,
        span: Span,
    },
    Tuple {
        exprs: Vec<Expr<'src>>,
        span: Span,
    },
    NamedConstructor {
        path: Path<'src>,
        fields: Vec<(Ident<'src>, Option<Expr<'src>>)>,
        brace_span: Span,
    },
    Array {
        exprs: Vec<Expr<'src>>,
        span: Span,
    },
    Match {
        scrutinee: Box<Expr<'src>>,
        arms: Vec<(Pattern<'src>, Expr<'src>)>,
        brace_span: Span,
    },

    Get {
        object: Box<Expr<'src>>,
        field: Ident<'src>,
    },
    Set {
        object: Box<Expr<'src>>,
        field: Ident<'src>,
        value: Box<Expr<'src>>,
    },

    Call {
        callee: Box<Expr<'src>>,
        arguments: Vec<Expr<'src>>,
        paren_span: Span,
    },
    ContApplication {
        callee: Box<Expr<'src>>,
        arguments: Vec<(Ident<'src>, Option<Expr<'src>>)>,
        bracket_span: Span,
    },

    Unary {
        operator: UnaryOp,
        operand: Box<Expr<'src>>,
    },

    Binary {
        left: Box<Expr<'src>>,
        operator: BinaryOp,
        right: Box<Expr<'src>>,
    },

    Declare {
        name: Ident<'src>,
        ty: Path<'src>,
        value: Box<Expr<'src>>,
        span: Span,
    },
    Assign {
        name: Ident<'src>,
        value: Box<Expr<'src>>,
    },
}
