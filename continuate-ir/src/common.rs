use std::cmp;
use std::fmt;
use std::hash;
use std::num::NonZero;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

use continuate_error::SourceCache;
use continuate_error::Span;

#[derive(Clone, Copy)]
pub struct Ident(NonZero<u64>, Span);

impl Ident {
    /// ## Panics
    ///
    /// Panics if the total number of identifiers exceeds [`u64::MAX`].
    #[allow(clippy::new_without_default)]
    pub fn new(span: Span) -> Ident {
        static NEXT: AtomicU64 = AtomicU64::new(1);

        let value = NEXT.fetch_add(1, Ordering::Relaxed);
        Ident(NonZero::new(value).expect("ident overflow"), span)
    }

    /// ## Panics
    ///
    /// Panics if `self` does not originate from a source in `cache`.
    #[track_caller]
    pub fn name<'a>(&self, cache: &'a SourceCache) -> &'a str {
        cache.str(self.1).expect("invalid `SourceCache` for ident")
    }

    #[must_use]
    pub const fn with_span(self, span: Span) -> Ident {
        Ident(self.0, span)
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

impl fmt::Debug for Ident {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ident({})", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncRef(NonZero<u32>);

impl FuncRef {
    pub const ENTRY_POINT: FuncRef = match NonZero::new(1) {
        Some(one) => FuncRef(one),
        None => unreachable!(),
    };

    /// Get a new unique `FuncRef`.
    ///
    /// ## Panics
    ///
    /// Panics if the total number of `FuncRef`s (including [`ENTRY_POINT`]) exceeds [`u32::MAX`].
    ///
    /// [`ENTRY_POINT`]: FuncRef::ENTRY_POINT
    #[allow(clippy::new_without_default)]
    pub fn new() -> FuncRef {
        static NEXT: AtomicU32 = AtomicU32::new(2);

        let next = NEXT.fetch_add(1, Ordering::Relaxed);
        FuncRef(NonZero::new(next).expect("funcref overflow"))
    }
}

impl From<FuncRef> for u32 {
    fn from(value: FuncRef) -> Self {
        value.0.get()
    }
}

impl fmt::Debug for FuncRef {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FuncRef({})", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UserDefinedTyRef(NonZero<u64>);

impl UserDefinedTyRef {
    /// ## Panics
    ///
    /// Panics if the total number of identifiers exceeds [`u64::MAX`].
    #[allow(clippy::new_without_default)]
    pub fn new() -> UserDefinedTyRef {
        static NEXT: AtomicU64 = AtomicU64::new(1);

        let value = NEXT.fetch_add(1, Ordering::Relaxed);
        UserDefinedTyRef(NonZero::new(value).expect("userdefinedtyref overflow"))
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

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::Div => "/",
            BinaryOp::Rem => "%",
            BinaryOp::Eq => "==",
            BinaryOp::Ne => "!=",
            BinaryOp::Lt => "<",
            BinaryOp::Le => "<=",
            BinaryOp::Gt => ">",
            BinaryOp::Ge => ">=",
        };
        f.write_str(s)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
    Discriminant,
    Terminate,
    Unreachable,
}
