use std::collections::HashMap;
use std::fmt;

use continuate_arena::Arena;

use crate::lib_std::{self, StdLib};

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ident(pub(crate) u64);

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Ident({})", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
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

#[derive(Debug)]
pub enum Pattern<'arena> {
    Ident(Ident),
    Wildcard,
    Destructure {
        ty: &'arena Type<'arena>,
        variant: Option<usize>,
        fields: Vec<(Pattern<'arena>, Option<Ident>)>,
    },
}

#[derive(Debug)]
#[non_exhaustive]
pub enum Expr<'arena> {
    Literal(Literal),
    Ident(Ident),
    Function(FuncRef),
    Block(Vec<&'arena Expr<'arena>>),
    Tuple(Vec<&'arena Expr<'arena>>),
    Constructor {
        ty: &'arena Type<'arena>,
        index: Option<usize>,
        fields: Vec<&'arena Expr<'arena>>,
    },
    Array(Vec<&'arena Expr<'arena>>),

    ExprContinuation,

    Get {
        object: &'arena Expr<'arena>,
        object_variant: Option<usize>,
        field: usize,
    },
    Set {
        object: &'arena Expr<'arena>,
        object_variant: Option<usize>,
        field: usize,
        value: &'arena Expr<'arena>,
    },

    Call(&'arena Expr<'arena>, Vec<&'arena Expr<'arena>>),
    ContApplication(&'arena Expr<'arena>, HashMap<Ident, &'arena Expr<'arena>>),

    Unary(UnaryOp, &'arena Expr<'arena>),

    Binary(&'arena Expr<'arena>, BinaryOp, &'arena Expr<'arena>),

    Declare {
        ident: Ident,
        ty: &'arena Type<'arena>,
        expr: &'arena Expr<'arena>,
    },
    Assign {
        ident: Ident,
        expr: &'arena Expr<'arena>,
    },

    Match {
        scrutinee: &'arena Expr<'arena>,
        arms: HashMap<Pattern<'arena>, BlockId>,
    },
    Goto(BlockId),

    Closure {
        func: &'arena Expr<'arena>,
    },

    Unreachable,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncRef(u64);

impl fmt::Debug for FuncRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FuncRef({})", self.0)
    }
}

#[derive(Debug)]
pub enum Type<'arena> {
    Int,
    Float,
    String,
    Array(&'arena Type<'arena>, u32),
    Tuple(Vec<&'arena Type<'arena>>),
    Function {
        params: Vec<&'arena Type<'arena>>,
        continuations: Vec<&'arena Type<'arena>>,
    },
    UserDefined(&'arena UserDefinedType<'arena>),
}

#[derive(Debug)]
pub struct UserDefinedType<'arena> {
    pub constructor: TypeConstructor<'arena>,
}

#[derive(Debug)]
pub enum TypeConstructor<'arena> {
    Product(Vec<&'arena Type<'arena>>),
    Sum(Vec<Vec<&'arena Type<'arena>>>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(u64);

impl fmt::Debug for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BlockId({})", self.0)
    }
}

#[derive(Debug)]
pub struct Block<'arena> {
    pub expr: &'arena Expr<'arena>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Intrinsic {
    Discriminant,
    Terminate,
}

#[derive(Debug)]
pub struct Function<'arena> {
    pub params: HashMap<Ident, &'arena Type<'arena>>,
    pub continuations: HashMap<Ident, &'arena Type<'arena>>,
    pub blocks: HashMap<BlockId, Block<'arena>>,
    pub(crate) intrinsic: Option<Intrinsic>,
    next_ident: u64,
    next_block: u64,
}

impl<'arena> Function<'arena> {
    pub fn new() -> Function<'arena> {
        Function {
            params: HashMap::new(),
            continuations: HashMap::new(),
            blocks: HashMap::new(),
            intrinsic: None,
            next_ident: 0,
            next_block: 1,
        }
    }

    pub fn ident(&mut self) -> Ident {
        let ident = Ident(self.next_ident);
        self.next_ident += 1;
        ident
    }

    #[allow(clippy::unused_self)]
    pub const fn entry_point(&self) -> BlockId {
        BlockId(0)
    }

    pub fn new_block(&mut self) -> BlockId {
        let block = BlockId(self.next_ident);
        self.next_block += 1;
        block
    }
}

impl<'arena> Default for Function<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct Program<'arena> {
    pub functions: HashMap<FuncRef, &'arena Function<'arena>>,
    next_function: u64,
    lib_std: StdLib<'arena>,
}

impl<'arena> Program<'arena> {
    pub fn new(arena: &'arena Arena<'arena>) -> Program<'arena> {
        Program {
            functions: HashMap::new(),
            next_function: 1,
            lib_std: lib_std::standard_library(arena),
        }
    }

    pub const fn lib_std(&self) -> StdLib<'arena> {
        self.lib_std.clone()
    }

    #[allow(clippy::unused_self)]
    pub const fn entry_point(&self) -> FuncRef {
        FuncRef(0)
    }

    pub fn function(&mut self) -> FuncRef {
        let func_ref = FuncRef(self.next_function);
        self.next_function += 1;
        func_ref
    }
}
