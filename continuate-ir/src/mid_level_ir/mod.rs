mod lowering;
pub use lowering::lower;

mod visit;
pub use visit::run_passes;

use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::UnaryOp;
use crate::high_level_ir::Program as HirProgram;
use crate::lib_std::StdLib;

use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::hash;
use std::rc::Rc;

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
    ContApplication(ExprContApplication),
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
    pub ty: Rc<Type>,
    pub values: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprConstructor {
    pub ty: Rc<Type>,
    pub index: Option<usize>,
    pub fields: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprArray {
    pub ty: Rc<Type>,
    pub values: Vec<Expr>,
    pub value_ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprGet {
    pub object: Box<Expr>,
    pub object_ty: Rc<Type>,
    pub object_variant: Option<usize>,
    pub field: usize,
}

#[derive(Debug, Clone)]
pub struct ExprSet {
    pub object: Box<Expr>,
    pub object_ty: Rc<Type>,
    pub object_variant: Option<usize>,
    pub field: usize,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprCall {
    pub callee: Box<Expr>,
    pub callee_ty: Rc<Type>,
    pub args: Vec<(Option<Ident>, Expr)>,
}

#[derive(Debug, Clone)]
pub struct ExprContApplication {
    pub callee: Box<Expr>,
    pub callee_ty: Rc<Type>,
    pub continuations: Vec<(Ident, Expr)>,
    pub result_ty: Rc<Type>,
    pub storage_ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprUnary {
    pub operator: UnaryOp,
    pub operand: Box<Expr>,
    pub operand_ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprBinary {
    pub left: Box<Expr>,
    pub left_ty: Rc<Type>,
    pub operator: BinaryOp,
    pub right: Box<Expr>,
    pub right_ty: Rc<Type>,
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
    pub storage_ty: Rc<Type>,
}

#[derive(Debug, Clone)]
pub struct ExprIntrinsic {
    pub intrinsic: Intrinsic,
    pub values: Vec<(Expr, Rc<Type>)>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionTy {
    pub params: Vec<Rc<Type>>,
    pub continuations: HashMap<Ident, Rc<Type>>,
}

impl hash::Hash for FunctionTy {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.params.hash(state);
        for (&name, ty) in self
            .continuations
            .iter()
            .sorted_unstable_by_key(|(&ident, _)| ident)
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
    Array(Rc<Type>, u64),
    Tuple(Vec<Rc<Type>>),
    Function(FunctionTy),
    UserDefined(UserDefinedType),
    Unknown,
    None,
}

impl Type {
    pub const fn function(params: Vec<Rc<Type>>, continuations: HashMap<Ident, Rc<Type>>) -> Type {
        Type::Function(FunctionTy {
            params,
            continuations,
        })
    }

    pub const fn as_function(&self) -> Option<&FunctionTy> {
        if let Type::Function(func) = self {
            Some(func)
        } else {
            None
        }
    }

    pub const fn as_user_defined(&self) -> Option<&UserDefinedType> {
        if let Type::UserDefined(user_defined) = self {
            Some(user_defined)
        } else {
            None
        }
    }

    pub(crate) fn field(&self, variant: Option<usize>, field: usize) -> Option<Rc<Type>> {
        let user_defined = self.as_user_defined()?;
        match (variant, &user_defined) {
            (None, UserDefinedType::Product(fields)) => fields.get(field).cloned(),
            (Some(variant), UserDefinedType::Sum(variants)) => {
                variants.get(variant)?.get(field).cloned()
            }
            _ => None,
        }
    }

    pub const fn is_primitive(&self) -> bool {
        matches!(
            self,
            Type::Bool | Type::Int | Type::Float | Type::String | Type::Function(_)
        )
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum UserDefinedType {
    Product(Vec<Rc<Type>>),
    Sum(Vec<Vec<Rc<Type>>>),
}

impl UserDefinedType {
    pub const fn as_sum(&self) -> Option<&Vec<Vec<Rc<Type>>>> {
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BlockId({})", self.0)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Block {
    pub exprs: Vec<Expr>,
}

impl Block {
    pub const fn new() -> Block {
        Block { exprs: Vec::new() }
    }
}

#[derive(Debug)]
pub struct ClosureCaptures {
    pub captures: Vec<Ident>,
    pub storage_ty: Rc<Type>,
}

#[derive(Debug)]
pub struct Function {
    pub params: Vec<(Ident, Rc<Type>)>,
    pub continuations: HashMap<Ident, Rc<Type>>,
    pub declarations: HashMap<Ident, (Rc<Type>, Option<Literal>)>,
    pub blocks: HashMap<BlockId, Block>,
    pub captures: Option<ClosureCaptures>,
    next_block: u64,
    pub name: String,
}

impl Function {
    pub fn new(name: String) -> Function {
        Function {
            params: Vec::new(),
            continuations: HashMap::new(),
            declarations: HashMap::new(),
            blocks: HashMap::new(),
            captures: None,
            next_block: 1,
            name,
        }
    }

    pub fn type_of_var(&self, var: Ident) -> Option<&Rc<Type>> {
        self.continuations
            .get(&var)
            .or_else(|| self.declarations.get(&var).map(|(ty, _)| ty))
            .or_else(|| {
                self.params
                    .iter()
                    .find(|&&(ident, _)| ident == var)
                    .map(|(_, var)| var)
            })
    }

    pub fn ty(&self) -> FunctionTy {
        FunctionTy {
            params: self.params.iter().map(|(_, ty)| Rc::clone(ty)).collect(),
            continuations: self.continuations.clone(),
        }
    }

    pub const fn entry_point() -> BlockId {
        BlockId(0)
    }

    pub const fn block(&mut self) -> BlockId {
        let block = BlockId(self.next_block);
        self.next_block += 1;
        block
    }
}

#[derive(Debug)]
pub struct Program {
    pub functions: HashMap<FuncRef, Function>,
    pub signatures: HashMap<FuncRef, Rc<Type>>,
    pub types: HashSet<Rc<Type>>,
    pub lib_std: StdLib,
    pub name: String,
}

impl Program {
    pub fn new(program: &HirProgram) -> Program {
        Program {
            functions: HashMap::new(),
            signatures: HashMap::new(),
            types: HashSet::new(),
            lib_std: *program.lib_std(),
            name: program.name.clone(),
        }
    }

    pub fn insert_type(&mut self, ty: Type) -> Rc<Type> {
        if let Some(ty) = self.types.get(&ty) {
            Rc::clone(ty)
        } else {
            let ty = Rc::new(ty);
            self.types.insert(Rc::clone(&ty));
            ty
        }
    }
}
