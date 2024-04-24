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

use std::collections::HashMap;
use std::fmt;
use std::hash;

use bimap::BiHashMap;

use continuate_arena::Arena;
use continuate_arena::ArenaSafe;
use continuate_arena::ArenaSafeCopy;

use continuate_error::Error;

use itertools::Itertools as _;

#[derive(Debug, ArenaSafe)]
pub enum Expr<'arena> {
    Literal(Literal),
    Ident(Ident),
    Function(FuncRef),
    Tuple {
        ty: TypeRef,
        values: Vec<&'arena Expr<'arena>>,
    },
    Constructor {
        ty: TypeRef,
        index: Option<usize>,
        fields: Vec<&'arena Expr<'arena>>,
    },
    Array {
        ty: TypeRef,
        values: Vec<&'arena Expr<'arena>>,
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

    Call(&'arena Expr<'arena>, Vec<&'arena Expr<'arena>>),
    ContApplication(&'arena Expr<'arena>, HashMap<Ident, &'arena Expr<'arena>>),

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
        arms: HashMap<i64, BlockId>,
        otherwise: BlockId,
    },
    Goto(BlockId),

    Closure {
        func_ref: FuncRef,
        captures: HashMap<Ident, TypeRef>,
    },

    Intrinsic {
        intrinsic: Intrinsic,
        value: &'arena Expr<'arena>,
        value_ty: TypeRef,
    },

    Unreachable,
}

#[derive(Debug, PartialEq, Eq, ArenaSafe)]
pub struct FunctionTy {
    pub params: Vec<TypeRef>,
    pub continuations: HashMap<Ident, TypeRef>,
}

impl hash::Hash for FunctionTy {
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

#[derive(Debug, PartialEq, Eq, Hash, ArenaSafe)]
pub enum Type {
    Int,
    Float,
    String,
    Array(TypeRef, u64),
    Tuple(Vec<TypeRef>),
    Function(FunctionTy),
    UserDefined(UserDefinedType),
    Unknown,
    None,
}

impl Type {
    pub const fn function(params: Vec<TypeRef>, continuations: HashMap<Ident, TypeRef>) -> Type {
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

    /// Ensure that `self` fits in `other`.
    pub(crate) fn unify<'arena>(
        &'arena self,
        other: &'arena Type,
        program: &mut Program<'arena>,
        arena: &'arena Arena<'arena>,
    ) -> Result<&'arena Type, Error> {
        if self == other {
            return Ok(self);
        }

        match (self, other) {
            (Type::Array(ty_1, len_1), Type::Array(ty_2, len_2)) if len_1 == len_2 => {
                let ty_1 = *program.types.get_by_left(ty_1).unwrap();
                let ty_2 = *program.types.get_by_left(ty_2).unwrap();
                let ty = ty_1.unify(ty_2, program, arena)?;
                Ok(program
                    .insert_type(
                        Type::Array(*program.types.get_by_right(ty).unwrap(), *len_1),
                        arena,
                    )
                    .1)
            }
            (Type::Tuple(t1), Type::Tuple(t2)) if t1.len() == t2.len() => {
                let types: Result<_, _> = t1
                    .iter()
                    .zip(t2.iter())
                    .map(|(ty_1, ty_2)| -> Result<TypeRef, Error> {
                        let ty_1 = *program.types.get_by_left(ty_1).unwrap();
                        let ty_2 = *program.types.get_by_left(ty_2).unwrap();
                        let ty = ty_1.unify(ty_2, program, arena)?;
                        Ok(*program.types.get_by_right(ty).unwrap())
                    })
                    .collect();
                Ok(program.insert_type(Type::Tuple(types?), arena).1)
            }
            (
                Type::Function(FunctionTy {
                    params: params_1,
                    continuations: continuations_1,
                }),
                Type::Function(FunctionTy {
                    params: params_2,
                    continuations: continuations_2,
                }),
            ) if params_1.len() == params_2.len() => {
                let params: Result<_, _> = params_1
                    .iter()
                    .zip(params_2.iter())
                    .map(|(ty_1, ty_2)| -> Result<TypeRef, Error> {
                        let ty_1 = *program.types.get_by_left(ty_1).unwrap();
                        let ty_2 = *program.types.get_by_left(ty_2).unwrap();
                        let ty = ty_1.unify(ty_2, program, arena)?;
                        Ok(*program.types.get_by_right(ty).unwrap())
                    })
                    .collect();

                let continuations: Result<_, Error> = continuations_1
                    .iter()
                    .sorted_unstable_by_key(|(ident, _)| ident.0)
                    .zip(
                        continuations_2
                            .iter()
                            .sorted_unstable_by_key(|(ident, _)| ident.0),
                    )
                    .map(|((&ident_1, ty_1), (&ident_2, ty_2))| {
                        if ident_1 != ident_2 {
                            Err("mismatched continuation")?;
                        }

                        let ty_1 = *program.types.get_by_left(ty_1).unwrap();
                        let ty_2 = *program.types.get_by_left(ty_2).unwrap();
                        let ty = ty_1.unify(ty_2, program, arena)?;
                        Ok((ident_1, *program.types.get_by_right(ty).unwrap()))
                    })
                    .collect();

                let ty = Type::function(params?, continuations?);
                Ok(program.insert_type(ty, arena).1)
            }
            (Type::UserDefined(u1), Type::UserDefined(u2)) if u1 == u2 => Ok(self),
            (Type::Unknown | Type::None, _) => Ok(other),
            (_, Type::Unknown) => Ok(self),
            _ => Err(format!("expected {other:?}, found {self:?}").into()),
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

    pub(crate) fn variants(&self) -> Option<usize> {
        Some(self.as_user_defined()?.constructor.as_sum()?.len())
    }
}

#[derive(Debug, PartialEq, Eq, Hash, ArenaSafe)]
pub struct UserDefinedType {
    pub constructor: TypeConstructor,
}

#[derive(Debug, PartialEq, Eq, Hash, ArenaSafe)]
pub enum TypeConstructor {
    Product(Vec<TypeRef>),
    Sum(Vec<Vec<TypeRef>>),
}

impl TypeConstructor {
    pub const fn as_sum(&self) -> Option<&Vec<Vec<TypeRef>>> {
        if let TypeConstructor::Sum(variants) = self {
            Some(variants)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, ArenaSafeCopy)]
pub struct BlockId(pub(crate) u64);

impl fmt::Debug for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BlockId({})", self.0)
    }
}

#[derive(Debug, Default, ArenaSafe)]
pub struct Block<'arena> {
    pub exprs: Vec<&'arena Expr<'arena>>,
}

impl<'arena> Block<'arena> {
    pub const fn new() -> Block<'arena> {
        Block { exprs: vec![] }
    }
}

#[derive(Debug, ArenaSafe)]
pub struct Function<'arena> {
    pub params: Vec<(Ident, TypeRef)>,
    pub continuations: HashMap<Ident, TypeRef>,
    pub declarations: HashMap<Ident, (TypeRef, Option<Literal>)>,
    pub blocks: HashMap<BlockId, Block<'arena>>,
    pub captures: HashMap<Ident, TypeRef>,
    next_ident: u32,
    next_block: u64,
    pub name: String,
}

impl<'arena> Function<'arena> {
    pub fn new(name: String) -> Function<'arena> {
        Function {
            params: Vec::new(),
            continuations: HashMap::new(),
            declarations: HashMap::new(),
            blocks: HashMap::new(),
            captures: HashMap::new(),
            next_ident: 0,
            next_block: 1,
            name,
        }
    }

    pub fn ident(&mut self) -> Ident {
        let ident = Ident(self.next_ident);
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

    pub fn ty(&self) -> FunctionTy {
        FunctionTy {
            params: self.params.iter().map(|&(_, ty)| ty).collect(),
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
    pub functions: HashMap<FuncRef, &'arena Function<'arena>>,
    pub signatures: HashMap<FuncRef, TypeRef>,
    pub types: BiHashMap<TypeRef, &'arena Type>,
    pub lib_std: StdLib,
    next_function: u64,
    next_ty: u64,
    pub name: String,
}

impl<'arena> Program<'arena> {
    pub fn new(program: &HirProgram) -> Program<'arena> {
        Program {
            functions: HashMap::new(),
            signatures: HashMap::new(),
            types: BiHashMap::new(),
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
        ty: Type,
        arena: &'arena Arena<'arena>,
    ) -> (TypeRef, &'arena Type) {
        if let Some(type_ref) = self.types.get_by_right(&ty) {
            let ty = *self.types.get_by_left(type_ref).unwrap();
            (*type_ref, ty)
        } else {
            let type_ref = self.ty();
            let ty = arena.allocate(ty);
            self.types.insert(type_ref, ty);
            (type_ref, ty)
        }
    }
}
