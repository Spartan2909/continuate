mod interpreter;
pub use interpreter::run as interpret;

mod lowering;
pub use lowering::lower;

mod visit;
pub use visit::run_passes;

use crate::{
    common::{BinaryOp, FuncRef, Ident, Intrinsic, Literal, UnaryOp},
    high_level_ir as hir,
    lib_std::StdLib,
};

use std::{
    collections::{HashMap, HashSet},
    fmt, hash,
    sync::Arc,
};

use itertools::Itertools as _;

#[derive(Debug, Clone)]
pub enum Expr {
    Literal(ExprLiteral),
    Ident(ExprIdent),
    Function(ExprFunction),
    Tuple(ExprTuple),
    Constructor(ExprConstructor),
    Array(ExprArray),
    Get(ExprGet),
    Set(ExprSet),
    Call(ExprCall),
    Application(ExprApplication),
    Unary(ExprUnary),
    Binary(ExprBinary),
    Assign(ExprAssign),
    Switch(ExprSwitch),
    Goto(ExprGoto),
    Closure(ExprClosure),
    Intrinsic(ExprIntrinsic),
}

#[derive(Debug, Clone)]
pub struct ExprLiteral {
    pub literal: Literal,
}

#[derive(Debug, Clone)]
pub struct ExprIdent {
    pub ident: Ident,
}

#[derive(Debug, Clone)]
pub struct ExprFunction {
    pub function: FuncRef,
}

#[derive(Debug, Clone)]
pub struct ExprTuple {
    pub ty: Arc<Type>,
    pub values: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprConstructor {
    pub ty: Arc<Type>,
    pub index: Option<usize>,
    pub fields: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprArray {
    pub ty: Arc<Type>,
    pub values: Vec<Expr>,
    pub value_ty: Arc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprGet {
    pub object: Box<Expr>,
    pub object_ty: Arc<Type>,
    pub object_variant: Option<usize>,
    pub field: usize,
}

#[derive(Debug, Clone)]
pub struct ExprSet {
    pub object: Box<Expr>,
    pub object_ty: Arc<Type>,
    pub object_variant: Option<usize>,
    pub field: usize,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprCall {
    pub callee: Box<Expr>,
    pub callee_ty: Arc<Type>,
    pub positional: Vec<Expr>,
    pub named: Vec<(Ident, Expr)>,
}

#[derive(Debug, Clone)]
pub struct ExprApplication {
    pub callee: Box<Expr>,
    pub callee_ty: Arc<Type>,
    pub positional: Vec<Expr>,
    pub named: Vec<(Ident, Expr)>,
    pub result_ty: Arc<Type>,
    pub storage_ty: Arc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprUnary {
    pub operator: UnaryOp,
    pub operand: Box<Expr>,
    pub operand_ty: Arc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprBinary {
    pub left: Box<Expr>,
    pub left_ty: Arc<Type>,
    pub operator: BinaryOp,
    pub right: Box<Expr>,
    pub right_ty: Arc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprAssign {
    pub ident: Ident,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprSwitch {
    pub scrutinee: Box<Expr>,
    pub arms: HashMap<i64, BlockId>,
    pub otherwise: BlockId,
}

#[derive(Debug, Clone)]
pub struct ExprGoto {
    pub block: BlockId,
}

#[derive(Debug, Clone)]
pub struct ExprClosure {
    pub func_ref: FuncRef,
    pub captures: Vec<Ident>,
    pub storage_ty: Arc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprIntrinsic {
    pub intrinsic: Intrinsic,
    pub values: Vec<(Expr, Arc<Type>)>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionTy {
    pub positional_params: Vec<Arc<Type>>,
    pub named_params: HashMap<Ident, Arc<Type>>,
}

impl hash::Hash for FunctionTy {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.positional_params.hash(state);
        for (&name, ty) in self
            .named_params
            .iter()
            .sorted_unstable_by_key(|&(&ident, _)| ident)
        {
            (name, ty).hash(state);
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Bool,
    Int,
    Float,
    String,
    Array(Arc<Type>, u64),
    Tuple(Vec<Arc<Type>>),
    Function(FunctionTy),
    UserDefined(UserDefinedType),
    Unknown,
    None,
}

impl Type {
    #[inline]
    pub const fn function(
        positional_params: Vec<Arc<Type>>,
        named_params: HashMap<Ident, Arc<Type>>,
    ) -> Type {
        Type::Function(FunctionTy {
            positional_params,
            named_params,
        })
    }

    #[inline]
    pub const fn as_function(&self) -> Option<&FunctionTy> {
        if let Type::Function(func) = self {
            Some(func)
        } else {
            None
        }
    }

    #[inline]
    pub const fn as_user_defined(&self) -> Option<&UserDefinedType> {
        if let Type::UserDefined(user_defined) = self {
            Some(user_defined)
        } else {
            None
        }
    }

    pub(crate) fn field(&self, variant: Option<usize>, field: usize) -> Option<Arc<Type>> {
        let user_defined = self.as_user_defined()?;
        match (variant, &user_defined) {
            (None, UserDefinedType::Product(fields)) => fields.get(field).cloned(),
            (Some(variant), UserDefinedType::Sum(variants)) => {
                variants.get(variant)?.get(field).cloned()
            }
            _ => None,
        }
    }

    #[inline]
    pub const fn is_primitive(&self) -> bool {
        matches!(
            self,
            Type::Bool | Type::Int | Type::Float | Type::String | Type::Function(_)
        )
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum UserDefinedType {
    Product(Vec<Arc<Type>>),
    Sum(Vec<Vec<Arc<Type>>>),
}

impl UserDefinedType {
    #[inline]
    pub const fn as_sum(&self) -> Option<&Vec<Vec<Arc<Type>>>> {
        if let UserDefinedType::Sum(variants) = self {
            Some(variants)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub(crate) u64);

impl fmt::Debug for BlockId {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BlockId({})", self.0)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub exprs: Vec<Expr>,
}

impl Block {
    #[inline]
    pub const fn new() -> Block {
        Block { exprs: Vec::new() }
    }
}

#[derive(Debug)]
pub struct ClosureCaptures {
    pub captures: Vec<Ident>,
    pub storage_ty: Arc<Type>,
}

#[derive(Debug)]
pub struct Function {
    pub positional_params: Vec<(Ident, Arc<Type>)>,
    pub named_params: HashMap<Ident, Arc<Type>>,
    pub declarations: HashMap<Ident, (Arc<Type>, Option<Literal>)>,
    pub blocks: HashMap<BlockId, Block>,
    pub captures: Option<ClosureCaptures>,
    next_block: u64,
    pub name: String,
}

impl Function {
    #[inline]
    pub fn new(name: String) -> Function {
        Function {
            positional_params: Vec::new(),
            named_params: HashMap::new(),
            declarations: HashMap::new(),
            blocks: HashMap::new(),
            captures: None,
            next_block: 1,
            name,
        }
    }

    #[inline]
    pub fn type_of_var(&self, var: Ident) -> Option<&Arc<Type>> {
        self.named_params
            .get(&var)
            .or_else(|| self.declarations.get(&var).map(|(ty, _)| ty))
            .or_else(|| {
                self.positional_params
                    .iter()
                    .find(|&&(ident, _)| ident == var)
                    .map(|(_, var)| var)
            })
    }

    #[inline]
    pub fn ty(&self) -> FunctionTy {
        FunctionTy {
            positional_params: self
                .positional_params
                .iter()
                .map(|(_, ty)| Arc::clone(ty))
                .collect(),
            named_params: self.named_params.clone(),
        }
    }

    #[inline]
    pub const fn entry_point() -> BlockId {
        BlockId(0)
    }

    #[inline]
    pub const fn block(&mut self) -> BlockId {
        let block = BlockId(self.next_block);
        self.next_block += 1;
        block
    }
}

#[derive(Debug)]
pub struct Program {
    pub functions: HashMap<FuncRef, Function>,
    pub signatures: HashMap<FuncRef, Arc<Type>>,
    pub types: HashSet<Arc<Type>>,
    pub lib_std: StdLib,
    pub name: String,
}

impl Program {
    #[inline]
    pub fn new(program: &hir::Program<Arc<hir::Type>>) -> Program {
        Program {
            functions: HashMap::new(),
            signatures: HashMap::new(),
            types: HashSet::new(),
            lib_std: *program.lib_std(),
            name: program.name.clone(),
        }
    }

    #[inline]
    pub fn insert_type(&mut self, ty: Type) -> Arc<Type> {
        if let Some(ty) = self.types.get(&ty) {
            Arc::clone(ty)
        } else {
            let ty = Arc::new(ty);
            self.types.insert(Arc::clone(&ty));
            ty
        }
    }
}
