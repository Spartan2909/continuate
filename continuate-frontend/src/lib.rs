mod lexer;
pub use lexer::lex;
pub use lexer::Spacing;
pub use lexer::Token;

mod name_resolution;
pub use name_resolution::resolve_names;

mod parser;
pub use parser::parse;

use std::hash::Hash;
use std::hash::Hasher;
use std::mem;

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
    pub const fn new(string: &'src str, span: Span) -> Ident<'src> {
        Ident { string, span }
    }
}

impl PartialEq for Ident<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.string == other.string
    }
}

impl Eq for Ident<'_> {}

impl Hash for Ident<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.string.hash(state);
    }
}

#[derive(Debug, Clone)]
pub enum PathIdentSegment<'src> {
    Ident(Ident<'src>),
    Package(Span),
    Super(Span),
}

impl PartialEq for PathIdentSegment<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (PathIdentSegment::Ident(this), PathIdentSegment::Ident(other)) => this == other,
            (PathIdentSegment::Package(_), PathIdentSegment::Package(_))
            | (PathIdentSegment::Super(_), PathIdentSegment::Super(_)) => true,
            _ => false,
        }
    }
}

impl Eq for PathIdentSegment<'_> {}

impl Hash for PathIdentSegment<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        mem::discriminant(self).hash(state);
        if let PathIdentSegment::Ident(ident) = self {
            ident.hash(state);
        }
    }
}

#[derive(Debug, Clone)]
pub struct PathSegment<'src> {
    pub ident: PathIdentSegment<'src>,
    pub span: Span,
}

impl PartialEq for PathSegment<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.ident == other.ident
    }
}

impl Eq for PathSegment<'_> {}

impl Hash for PathSegment<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ident.hash(state);
    }
}

#[derive(Debug, Clone)]
pub struct Path<'src> {
    pub segments: Vec<PathSegment<'src>>,
    pub span: Span,
}

impl PartialEq for Path<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.segments == other.segments
    }
}

impl Eq for Path<'_> {}

impl Hash for Path<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.segments.hash(state);
    }
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

#[derive(Debug, Clone)]
pub enum Type<'src> {
    Path(Path<'src>),
    Tuple {
        items: Vec<Type<'src>>,
        span: Span,
    },
    Function {
        params: Vec<Type<'src>>,
        continuations: Vec<(Ident<'src>, Type<'src>)>,
        span: Span,
    },
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
        tail: Option<Box<Expr<'src>>>,
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
        ty: Option<Type<'src>>,
        value: Box<Expr<'src>>,
        span: Span,
    },
    Assign {
        name: Ident<'src>,
        value: Box<Expr<'src>>,
    },
}

#[derive(Debug, Clone)]
pub struct Function<'src> {
    pub name: Ident<'src>,
    pub params: Vec<(Ident<'src>, Type<'src>)>,
    pub continuations: Vec<(Ident<'src>, Type<'src>)>,
    pub body: Vec<Expr<'src>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum UserDefinedTyFields<'src> {
    Named(Vec<(Ident<'src>, Type<'src>)>),
    Anonymous(Vec<Type<'src>>),
    Unit,
}

#[derive(Debug, Clone)]
pub enum UserDefinedTy<'src> {
    Product {
        name: Ident<'src>,
        fields: UserDefinedTyFields<'src>,
        span: Span,
    },
    Sum {
        name: Ident<'src>,
        variants: Vec<(Ident<'src>, UserDefinedTyFields<'src>)>,
        span: Span,
    },
}

impl<'src> UserDefinedTy<'src> {
    const fn name(&self) -> &Ident<'src> {
        match self {
            UserDefinedTy::Product {
                name,
                fields: _,
                span: _,
            }
            | UserDefinedTy::Sum {
                name,
                variants: _,
                span: _,
            } => name,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Item<'src> {
    Function(Function<'src>),
    UserDefinedTy(UserDefinedTy<'src>),
}

impl<'src> Item<'src> {
    pub const fn as_function(&self) -> Option<&Function<'src>> {
        if let Item::Function(function) = self {
            Some(function)
        } else {
            None
        }
    }

    pub const fn as_user_defined_ty(&self) -> Option<&UserDefinedTy<'src>> {
        if let Item::UserDefinedTy(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub const fn name(&self) -> &Ident<'src> {
        match self {
            Item::Function(function) => &function.name,
            Item::UserDefinedTy(ty) => ty.name(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Program<'src> {
    pub items: Vec<Item<'src>>,
}
