use std::cmp;
use std::fmt;
use std::hash;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

use continuate_error::SourceCache;
use continuate_error::Span;

#[derive(Clone, Copy)]
pub struct Ident(u64, Span);

impl Ident {
    /// ## Panics
    ///
    /// Panics if the total number of identifiers exceeds `u64::MAX - 1`.
    #[allow(clippy::new_without_default)]
    pub fn new(span: Span) -> Ident {
        static NEXT: AtomicU64 = AtomicU64::new(0);

        let value = NEXT.fetch_add(1, Ordering::Relaxed);
        assert_ne!(value, u64::MAX, "ident overflow");
        Ident(value, span)
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
pub struct FuncRef(u32);

impl FuncRef {
    pub const ENTRY_POINT: FuncRef = FuncRef(0);

    /// Get a new unique `FuncRef`.
    ///
    /// ## Panics
    ///
    /// Panics if the total number of `FuncRef`s exceeds `u32::MAX - 2`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> FuncRef {
        static NEXT: AtomicU32 = AtomicU32::new(1);

        let next = NEXT.fetch_add(1, Ordering::Relaxed);
        assert_ne!(next, u32::MAX, "function overflow");
        FuncRef(next)
    }
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UserDefinedTyRef(u64);

impl UserDefinedTyRef {
    /// ## Panics
    ///
    /// Panics if the total number of identifiers exceeds `u64::MAX - 1`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> UserDefinedTyRef {
        static NEXT: AtomicU64 = AtomicU64::new(0);

        let value = NEXT.fetch_add(1, Ordering::Relaxed);
        assert_ne!(value, u64::MAX, "ty ref overflow");
        UserDefinedTyRef(value)
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
