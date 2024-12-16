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
use crate::HashMap;
use crate::Vec;

use std::hash;

use bumpalo::Bump;

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
    Block(Vec<'arena, Expr<'arena>>),
    Tuple(Vec<'arena, Expr<'arena>>),
    Constructor {
        ty: TypeRef,
        index: Option<usize>,
        fields: Vec<'arena, Expr<'arena>>,
    },
    Array(Vec<'arena, Expr<'arena>>),

    Get {
        object: &'arena Expr<'arena>,
        field: usize,
    },
    Set {
        object: &'arena Expr<'arena>,
        field: usize,
        value: &'arena Expr<'arena>,
    },

    Call(&'arena Expr<'arena>, Vec<'arena, Expr<'arena>>),
    ContApplication(&'arena Expr<'arena>, HashMap<'arena, Ident, Expr<'arena>>),

    Unary(UnaryOp, &'arena Expr<'arena>),

    Binary(&'arena Expr<'arena>, BinaryOp, &'arena Expr<'arena>),

    Declare {
        ident: Ident,
        ty: TypeRef,
        expr: &'arena Expr<'arena>,
    },
    Assign {
        ident: Ident,
        expr: &'arena Expr<'arena>,
    },

    Match {
        scrutinee: &'arena Expr<'arena>,
        arms: Vec<'arena, (Pattern<'arena>, Expr<'arena>)>,
    },

    Closure {
        func: FuncRef,
    },

    Intrinsic {
        intrinsic: Intrinsic,
        value: &'arena Expr<'arena>,
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

    pub fn insert_type(&mut self, ty: Type<'arena>, arena: &'arena Bump) -> TypeRef {
        if let Some(type_ref) = self.types.get_by_right(&ty) {
            *type_ref
        } else {
            let type_ref = self.ty();
            self.types.insert(type_ref, arena.alloc(ty));
            type_ref
        }
    }
}
