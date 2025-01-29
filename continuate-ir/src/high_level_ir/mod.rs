mod typeck;
pub use typeck::typeck;

use crate::bimap::BiMap;
use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::common::UnaryOp;
use crate::lib_std;
use crate::lib_std::StdLib;
use crate::try_collect_into;
use crate::HashMap;
use crate::Vec;

use std::hash;

use bumpalo::Bump;

use continuate_error::Result;

use continuate_utils::Box;

use itertools::Itertools as _;

#[derive(Debug, PartialEq)]
pub enum Pattern<'arena> {
    Wildcard,
    Ident(Ident),
    Destructure {
        ty: TypeRef,
        variant: Option<usize>,
        fields: Vec<'arena, Pattern<'arena>>,
    },
}

impl Pattern<'_> {
    pub const fn as_ident(&self) -> Option<Ident> {
        if let Pattern::Ident(ident) = self {
            Some(*ident)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub enum Expr<'arena> {
    Literal(Literal),
    Ident(Ident),
    Function(FuncRef),
    Block(Vec<'arena, Expr<'arena>>, TypeRef),
    Tuple(Vec<'arena, Expr<'arena>>, TypeRef),
    Constructor {
        ty: TypeRef,
        index: Option<usize>,
        fields: Vec<'arena, Expr<'arena>>,
    },
    Array {
        exprs: Vec<'arena, Expr<'arena>>,
        ty: TypeRef,
    },

    Get {
        object: Box<'arena, Expr<'arena>>,
        object_ty: TypeRef,
        field: usize,
    },
    Set {
        object: Box<'arena, Expr<'arena>>,
        object_ty: TypeRef,
        field: usize,
        value: Box<'arena, Expr<'arena>>,
        value_ty: TypeRef,
    },

    Call {
        callee: Box<'arena, Expr<'arena>>,
        callee_ty: TypeRef,
        args: Vec<'arena, Expr<'arena>>,
    },
    ContApplication {
        callee: Box<'arena, Expr<'arena>>,
        callee_ty: TypeRef,
        continuations: HashMap<'arena, Ident, Expr<'arena>>,
    },

    Unary {
        op: UnaryOp,
        right: Box<'arena, Expr<'arena>>,
        right_ty: TypeRef,
    },

    Binary {
        left: Box<'arena, Expr<'arena>>,
        left_ty: TypeRef,
        op: BinaryOp,
        right: Box<'arena, Expr<'arena>>,
        right_ty: TypeRef,
    },

    Declare {
        ident: Ident,
        ty: TypeRef,
        expr: Box<'arena, Expr<'arena>>,
    },
    Assign {
        ident: Ident,
        expr: Box<'arena, Expr<'arena>>,
    },

    Match {
        scrutinee: Box<'arena, Expr<'arena>>,
        arms: Vec<'arena, (Pattern<'arena>, Expr<'arena>)>,
    },

    Closure {
        func: FuncRef,
        captures: Option<HashMap<'arena, Ident, TypeRef>>,
    },

    Intrinsic {
        intrinsic: Intrinsic,
        value: Box<'arena, Expr<'arena>>,
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

    pub const fn as_user_defined(&self) -> Option<&UserDefinedType<'arena>> {
        if let Type::UserDefined(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    /// Ensure that `self` fits in `other`.
    pub(crate) fn unify(
        &'arena self,
        other: &'arena Type,
        program: &mut Program<'arena>,
        arena: &'arena Bump,
    ) -> Result<&'arena Type<'arena>> {
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
                let types: Result<_> = try_collect_into(
                    t1.iter()
                        .zip(t2.iter())
                        .map(|(ty_1, ty_2)| -> Result<TypeRef> {
                            let ty_1 = *program.types.get_by_left(ty_1).unwrap();
                            let ty_2 = *program.types.get_by_left(ty_2).unwrap();
                            let ty = ty_1.unify(ty_2, program, arena)?;
                            Ok(*program.types.get_by_right(ty).unwrap())
                        }),
                    Vec::new_in(arena),
                );
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
                let params: Result<_> = try_collect_into(
                    params_1
                        .iter()
                        .zip(params_2.iter())
                        .map(|(ty_1, ty_2)| -> Result<TypeRef> {
                            let ty_1 = *program.types.get_by_left(ty_1).unwrap();
                            let ty_2 = *program.types.get_by_left(ty_2).unwrap();
                            let ty = ty_1.unify(ty_2, program, arena)?;
                            Ok(*program.types.get_by_right(ty).unwrap())
                        }),
                    Vec::new_in(arena),
                );

                let continuations: Result<_> = try_collect_into(
                    continuations_1
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
                        }),
                    HashMap::new_in(arena),
                );

                let ty = Type::function(params?, continuations?);
                Ok(program.insert_type(ty, arena).1)
            }
            (Type::UserDefined(u1), Type::UserDefined(u2)) if u1 == u2 => Ok(self),
            (Type::Unknown | Type::None, _) => Ok(other),
            (_, Type::Unknown) => Ok(self),
            _ => Err(format!("expected {other:?}, found {self:?}").into()),
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

#[derive(Debug)]
pub struct Function<'arena> {
    pub params: Vec<'arena, (Ident, TypeRef)>,
    pub continuations: HashMap<'arena, Ident, TypeRef>,
    pub body: Vec<'arena, Expr<'arena>>,
    pub captures: Vec<'arena, Ident>,
    next_ident: u32,
    pub name: String,
}

impl<'arena> Function<'arena> {
    pub fn new(name: String, arena: &'arena Bump) -> Function<'arena> {
        Function {
            params: Vec::new_in(arena),
            continuations: HashMap::new_in(arena),
            body: Vec::new_in(arena),
            captures: Vec::new_in(arena),
            next_ident: 0,
            name,
        }
    }

    pub fn ident(&mut self) -> Ident {
        let ident = Ident::new(self.next_ident);
        self.next_ident += 1;
        ident
    }
}

#[derive(Debug)]
pub struct Program<'arena> {
    pub functions: HashMap<'arena, FuncRef, Function<'arena>>,
    pub signatures: HashMap<'arena, FuncRef, TypeRef>,
    pub types: BiMap<'arena, TypeRef, &'arena Type<'arena>>,
    pub(crate) next_function: u32,
    pub(crate) next_ty: u64,
    lib_std: Option<StdLib>,
    pub name: String,
}

impl<'arena> Program<'arena> {
    pub fn new(name: String, arena: &'arena Bump) -> Program<'arena> {
        let mut program = Program {
            functions: HashMap::new_in(arena),
            signatures: HashMap::new_in(arena),
            types: BiMap::new(arena),
            next_function: 1,
            next_ty: 0,
            lib_std: None,
            name,
        };
        program.lib_std = Some(lib_std::standard_library(&mut program, arena));
        program
    }

    #[allow(clippy::missing_panics_doc)] // Will not panic.
    pub const fn lib_std(&self) -> &StdLib {
        self.lib_std.as_ref().unwrap()
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
}
