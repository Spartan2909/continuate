use std::cmp;
use std::fmt;
use std::hash;

use continuate_error::Span;

#[derive(Clone, Copy)]
pub struct Ident(pub(crate) u32, Span);

impl Ident {
    pub(crate) const fn new(value: u32) -> Ident {
        Ident(value, Span::dummy())
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Ident {}

impl PartialOrd for Ident {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ident {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl hash::Hash for Ident {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl From<Ident> for u32 {
    fn from(value: Ident) -> Self {
        value.0
    }
}

impl fmt::Debug for Ident {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ident({})", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncRef(pub(crate) u32);

impl From<FuncRef> for u32 {
    fn from(value: FuncRef) -> Self {
        value.0
    }
}

impl fmt::Debug for FuncRef {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FuncRef({})", self.0)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl BinaryOp {
    pub const fn is_arithmetic(self) -> bool {
        use BinaryOp as Op;
        matches!(self, Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Rem)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
    Discriminant,
    Terminate,
}
