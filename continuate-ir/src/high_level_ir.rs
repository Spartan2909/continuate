use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::common::UnaryOp;
use crate::lib_std;
use crate::lib_std::StdLib;

use std::collections::HashMap;
use std::hash;

use bimap::BiHashMap;

use continuate_arena::Arena;
use continuate_arena::ArenaSafe;

use itertools::Itertools as _;

#[derive(Debug, PartialEq, ArenaSafe)]
pub enum Pattern {
    Wildcard,
    Ident(Ident),
    Destructure {
        ty: TypeRef,
        variant: Option<usize>,
        fields: Vec<Pattern>,
    },
}

impl Pattern {
    pub const fn as_ident(&self) -> Option<Ident> {
        if let Pattern::Ident(ident) = self {
            Some(*ident)
        } else {
            None
        }
    }
}

#[derive(Debug, ArenaSafe)]
#[non_exhaustive]
pub enum Expr<'arena> {
    Literal(Literal),
    Ident(Ident),
    Function(FuncRef),
    Block(Vec<&'arena Expr<'arena>>),
    Tuple(Vec<&'arena Expr<'arena>>),
    Constructor {
        ty: TypeRef,
        index: Option<usize>,
        fields: Vec<&'arena Expr<'arena>>,
    },
    Array(Vec<&'arena Expr<'arena>>),

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
        ty: TypeRef,
        expr: &'arena Expr<'arena>,
    },
    Assign {
        ident: Ident,
        expr: &'arena Expr<'arena>,
    },

    Match {
        scrutinee: &'arena Expr<'arena>,
        arms: Vec<(Pattern, &'arena Expr<'arena>)>,
    },

    Closure {
        func: FuncRef,
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
    Array(TypeRef, u32),
    Tuple(Vec<TypeRef>),
    Function(FunctionTy),
    UserDefined(UserDefinedType),
}

impl Type {
    pub const fn function(params: Vec<TypeRef>, continuations: HashMap<Ident, TypeRef>) -> Type {
        Type::Function(FunctionTy {
            params,
            continuations,
        })
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

#[derive(Debug, ArenaSafe)]
pub struct Function<'arena> {
    pub params: Vec<(Ident, TypeRef)>,
    pub continuations: HashMap<Ident, TypeRef>,
    pub body: Vec<&'arena Expr<'arena>>,
    pub captures: Vec<Ident>,
    pub(crate) intrinsic: Option<Intrinsic>,
    next_ident: u64,
    pub(crate) next_block: u64,
}

impl<'arena> Function<'arena> {
    pub fn new() -> Function<'arena> {
        Function {
            params: Vec::new(),
            continuations: HashMap::new(),
            body: Vec::new(),
            captures: Vec::new(),
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
}

impl<'arena> Default for Function<'arena> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct Program<'arena> {
    pub functions: HashMap<FuncRef, &'arena Function<'arena>>,
    pub signatures: HashMap<FuncRef, TypeRef>,
    pub types: BiHashMap<TypeRef, &'arena Type>,
    pub(crate) next_function: u64,
    pub(crate) next_ty: u64,
    lib_std: Option<StdLib<'arena>>,
}

impl<'arena> Program<'arena> {
    pub fn new(arena: &'arena Arena<'arena>) -> Program<'arena> {
        let mut program = Program {
            functions: HashMap::new(),
            signatures: HashMap::new(),
            types: BiHashMap::new(),
            next_function: 1,
            next_ty: 0,
            lib_std: None,
        };
        program.lib_std = Some(lib_std::standard_library(&mut program, arena));
        program
    }

    #[allow(clippy::missing_panics_doc)] // Will not panic.
    pub fn lib_std(&self) -> &StdLib<'arena> {
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

    pub fn insert_type(&mut self, ty: Type, arena: &'arena Arena<'arena>) -> TypeRef {
        if let Some(type_ref) = self.types.get_by_right(&ty) {
            *type_ref
        } else {
            let type_ref = self.ty();
            self.types.insert(type_ref, arena.allocate(ty));
            type_ref
        }
    }
}
