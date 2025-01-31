mod lowering;
pub use lowering::lower;

use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::common::UnaryOp;
use crate::high_level_ir::Program as HirProgram;
use crate::lib_std::StdLib;

use std::fmt;
use std::hash;

use bumpalo::Bump;

use continuate_utils::bimap::BiMap;
use continuate_utils::collect_into;
use continuate_utils::HashMap;
use continuate_utils::Vec;

use itertools::Itertools as _;

#[derive(Debug)]
pub enum Expr<'arena> {
    Literal(Literal),
    Ident(Ident),
    Function(FuncRef),
    Tuple {
        ty: TypeRef,
        values: Vec<'arena, Expr<'arena>>,
    },
    Constructor {
        ty: TypeRef,
        index: Option<usize>,
        fields: Vec<'arena, Expr<'arena>>,
    },
    Array {
        ty: TypeRef,
        values: Vec<'arena, Expr<'arena>>,
        value_ty: TypeRef,
    },

    Get {
        object: &'arena Expr<'arena>,
        object_ty: TypeRef,
        object_variant: Option<usize>,
        field: usize,
    },
    Set {
        object: &'arena Expr<'arena>,
        object_ty: TypeRef,
        object_variant: Option<usize>,
        field: usize,
        value: &'arena Expr<'arena>,
    },

    Call {
        callee: &'arena Expr<'arena>,
        callee_ty: &'arena FunctionTy<'arena>,
        args: Vec<'arena, Expr<'arena>>,
    },
    ContApplication(&'arena Expr<'arena>, HashMap<'arena, Ident, Expr<'arena>>),

    Unary {
        operator: UnaryOp,
        operand: &'arena Expr<'arena>,
        operand_ty: TypeRef,
    },

    Binary {
        left: &'arena Expr<'arena>,
        left_ty: TypeRef,
        operator: BinaryOp,
        right: &'arena Expr<'arena>,
        right_ty: TypeRef,
    },

    Assign {
        ident: Ident,
        expr: &'arena Expr<'arena>,
    },

    Switch {
        scrutinee: &'arena Expr<'arena>,
        arms: HashMap<'arena, i64, BlockId>,
        otherwise: BlockId,
    },
    Goto(BlockId),

    Closure {
        func_ref: FuncRef,
        captures: HashMap<'arena, Ident, TypeRef>,
    },

    Intrinsic {
        intrinsic: Intrinsic,
        value: &'arena Expr<'arena>,
        value_ty: TypeRef,
    },

    Unreachable,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionTy<'arena> {
    pub params: Vec<'arena, TypeRef>,
    pub continuations: HashMap<'arena, Ident, TypeRef>,
}

impl hash::Hash for FunctionTy<'_> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.params.hash(state);
        for (&name, &ty) in self
            .continuations
            .iter()
            .sorted_unstable_by_key(|(&ident, _)| ident.0)
        {
            (name, ty).hash(state);
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Type<'arena> {
    Int,
    Float,
    String,
    Array(TypeRef, u64),
    Tuple(Vec<'arena, TypeRef>),
    Function(FunctionTy<'arena>),
    UserDefined(UserDefinedType<'arena>),
    Unknown,
    None,
}

impl<'arena> Type<'arena> {
    pub const fn function(
        params: Vec<'arena, TypeRef>,
        continuations: HashMap<'arena, Ident, TypeRef>,
    ) -> Type<'arena> {
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

    pub(crate) fn field(&self, variant: Option<usize>, field: usize) -> Option<TypeRef> {
        let user_defined = self.as_user_defined()?;
        match (variant, &user_defined.constructor) {
            (None, TypeConstructor::Product(fields)) => fields.get(field).copied(),
            (Some(variant), TypeConstructor::Sum(variants)) => {
                variants.get(variant)?.get(field).copied()
            }
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct UserDefinedType<'arena> {
    pub constructor: TypeConstructor<'arena>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TypeConstructor<'arena> {
    Product(Vec<'arena, TypeRef>),
    Sum(Vec<'arena, Vec<'arena, TypeRef>>),
}

impl<'arena> TypeConstructor<'arena> {
    pub const fn as_sum(&self) -> Option<&Vec<'arena, Vec<'arena, TypeRef>>> {
        if let TypeConstructor::Sum(variants) = self {
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

#[derive(Debug)]
pub struct Block<'arena> {
    pub exprs: Vec<'arena, Expr<'arena>>,
}

impl<'arena> Block<'arena> {
    pub const fn new(arena: &'arena Bump) -> Block<'arena> {
        Block {
            exprs: Vec::new_in(arena),
        }
    }
}

#[derive(Debug)]
pub struct Function<'arena> {
    pub params: Vec<'arena, (Ident, TypeRef)>,
    pub continuations: HashMap<'arena, Ident, TypeRef>,
    pub declarations: HashMap<'arena, Ident, (TypeRef, Option<Literal>)>,
    pub blocks: HashMap<'arena, BlockId, Block<'arena>>,
    pub captures: HashMap<'arena, Ident, TypeRef>,
    next_ident: u32,
    next_block: u64,
    pub name: String,
}

impl<'arena> Function<'arena> {
    pub fn new(name: String, arena: &'arena Bump) -> Function<'arena> {
        Function {
            params: Vec::new_in(arena),
            continuations: HashMap::new_in(arena),
            declarations: HashMap::new_in(arena),
            blocks: HashMap::new_in(arena),
            captures: HashMap::new_in(arena),
            next_ident: 0,
            next_block: 1,
            name,
        }
    }

    pub fn ident(&mut self) -> Ident {
        let ident = Ident::new(self.next_ident);
        self.next_ident += 1;
        ident
    }

    pub fn type_of_var(&self, var: Ident) -> Option<TypeRef> {
        self.continuations
            .get(&var)
            .or_else(|| self.declarations.get(&var).map(|(ty, _)| ty))
            .or_else(|| {
                self.params
                    .iter()
                    .find(|&&(ident, _)| ident == var)
                    .map(|(_, var)| var)
            })
            .copied()
    }

    pub fn ty(&self, arena: &'arena Bump) -> FunctionTy {
        FunctionTy {
            params: collect_into(self.params.iter().map(|&(_, ty)| ty), Vec::new_in(arena)),
            continuations: self.continuations.clone(),
        }
    }

    pub const fn entry_point() -> BlockId {
        BlockId(0)
    }

    pub fn block(&mut self) -> BlockId {
        let block = BlockId(self.next_block);
        self.next_block += 1;
        block
    }
}

#[derive(Debug)]
pub struct Program<'arena> {
    pub functions: HashMap<'arena, FuncRef, &'arena Function<'arena>>,
    pub signatures: HashMap<'arena, FuncRef, TypeRef>,
    pub types: BiMap<'arena, TypeRef, &'arena Type<'arena>>,
    pub lib_std: StdLib,
    next_function: u32,
    next_ty: u64,
    pub name: String,
}

impl<'arena> Program<'arena> {
    pub fn new(program: &HirProgram, arena: &'arena Bump) -> Program<'arena> {
        Program {
            functions: HashMap::new_in(arena),
            signatures: HashMap::new_in(arena),
            types: BiMap::new(arena),
            lib_std: *program.lib_std(),
            next_function: program.next_function,
            next_ty: program.next_ty,
            name: program.name.clone(),
        }
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

    pub fn ty(&mut self) -> TypeRef {
        let ty_ref = TypeRef(self.next_ty);
        self.next_ty += 1;
        ty_ref
    }

    #[allow(clippy::missing_panics_doc)] // Cannot panic
    pub fn insert_type(
        &mut self,
        ty: Type<'arena>,
        arena: &'arena Bump,
    ) -> (TypeRef, &'arena Type<'arena>) {
        if let Some(type_ref) = self.types.get_by_right(&ty) {
            let ty = *self.types.get_by_left(type_ref).unwrap();
            (*type_ref, ty)
        } else {
            let type_ref = self.ty();
            let ty = arena.alloc(ty);
            self.types.insert(type_ref, ty);
            (type_ref, ty)
        }
    }

    #[allow(clippy::missing_panics_doc)]
    pub fn is_primitive(&self, ty: TypeRef) -> bool {
        [
            self.lib_std.ty_bool,
            self.lib_std.ty_int,
            self.lib_std.ty_float,
            self.lib_std.ty_string,
        ]
        .contains(&ty)
            || self.types.get_by_left(&ty).unwrap().as_function().is_some()
    }
}
