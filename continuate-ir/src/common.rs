use std::fmt;

use continuate_arena::ArenaSafeCopy;
use continuate_arena::ArenaSafeStatic;

#[derive(Clone, Copy, PartialEq, Eq, Hash, ArenaSafeCopy)]
pub struct Ident(pub(crate) u64);

impl fmt::Debug for Ident {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ident({})", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, ArenaSafeCopy)]
pub struct FuncRef(pub(crate) u64);

impl fmt::Debug for FuncRef {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FuncRef({})", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, ArenaSafeCopy)]
pub struct TypeRef(pub(crate) u64);

impl fmt::Debug for TypeRef {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeRef({})", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, ArenaSafeStatic)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ArenaSafeCopy)]
pub enum UnaryOp {
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ArenaSafeCopy)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, ArenaSafeCopy)]
pub(crate) enum Intrinsic {
    Discriminant,
    Terminate,
}
