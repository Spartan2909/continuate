mod lowering;
pub use lowering::lower;

mod typeck;
pub use typeck::typeck;

use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::UnaryOp;
use crate::common::UserDefinedTyRef;
use crate::lib_std;
use crate::lib_std::StdLib;

use std::hash;
use std::ops::Range;
use std::slice;

use bumpalo::Bump;

use continuate_error::Result;
use continuate_error::Span;

use continuate_utils::try_collect_into;
use continuate_utils::Box;
use continuate_utils::HashMap;
use continuate_utils::HashSet;
use continuate_utils::Vec;

use itertools::Itertools as _;

#[derive(Debug, PartialEq)]
pub enum DestructureFields<'arena> {
    Named(Vec<'arena, (String, Pattern<'arena>)>),
    Anonymous(Vec<'arena, Pattern<'arena>>),
    Unit,
}

#[derive(Debug, PartialEq)]
pub enum Pattern<'arena> {
    Wildcard,
    Ident(Ident),
    Destructure {
        ty: &'arena Type<'arena>,
        variant: Option<String>,
        fields: DestructureFields<'arena>,
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
    Block(ExprBlock<'arena>),
    Tuple(ExprTuple<'arena>),
    Constructor(ExprConstructor<'arena>),
    Array(ExprArray<'arena>),
    Get(ExprGet<'arena>),
    Set(ExprSet<'arena>),
    Call(ExprCall<'arena>),
    ContApplication(ExprContApplication<'arena>),
    Unary(ExprUnary<'arena>),
    Binary(ExprBinary<'arena>),
    Declare(ExprDeclare<'arena>),
    Assign(ExprAssign<'arena>),
    Match(ExprMatch<'arena>),
    Closure(ExprClosure<'arena>),
    Intrinsic(ExprIntrinsic<'arena>),
}

#[derive(Debug)]
pub struct ExprBlock<'arena> {
    pub exprs: Vec<'arena, Expr<'arena>>,
    pub ty: &'arena Type<'arena>,
}

#[derive(Debug)]
pub struct ExprTuple<'arena> {
    pub exprs: Vec<'arena, Expr<'arena>>,
    pub ty: &'arena Type<'arena>,
}

#[derive(Debug)]
pub enum ExprConstructorFields<'arena> {
    Named(Vec<'arena, (String, Expr<'arena>)>),
    Anonymous(Vec<'arena, Expr<'arena>>),
    Unit,
}

#[derive(Debug)]
pub struct ExprConstructor<'arena> {
    pub ty: &'arena Type<'arena>,
    pub variant: Option<String>,
    pub fields: ExprConstructorFields<'arena>,
}

#[derive(Debug)]
pub struct ExprArray<'arena> {
    pub exprs: Vec<'arena, Expr<'arena>>,
    pub ty: &'arena Type<'arena>,
    pub element_ty: &'arena Type<'arena>,
}

#[derive(Debug)]
pub struct ExprGet<'arena> {
    pub object: Box<'arena, Expr<'arena>>,
    pub object_ty: &'arena Type<'arena>,
    pub field: String,
}

#[derive(Debug)]
pub struct ExprSet<'arena> {
    pub object: Box<'arena, Expr<'arena>>,
    pub object_ty: &'arena Type<'arena>,
    pub field: String,
    pub value: Box<'arena, Expr<'arena>>,
    pub value_ty: &'arena Type<'arena>,
}

#[derive(Debug)]
pub struct ExprCall<'arena> {
    pub callee: Box<'arena, Expr<'arena>>,
    pub callee_ty: &'arena Type<'arena>,
    pub args: Vec<'arena, Expr<'arena>>,
}

#[derive(Debug)]
pub struct ExprContApplication<'arena> {
    pub callee: Box<'arena, Expr<'arena>>,
    pub callee_ty: &'arena Type<'arena>,
    pub continuations: Vec<'arena, (Ident, Expr<'arena>)>,
    pub result_ty: &'arena Type<'arena>,
}

#[derive(Debug)]
pub struct ExprUnary<'arena> {
    pub op: UnaryOp,
    pub right: Box<'arena, Expr<'arena>>,
    pub right_ty: &'arena Type<'arena>,
}

#[derive(Debug)]
pub struct ExprBinary<'arena> {
    pub left: Box<'arena, Expr<'arena>>,
    pub left_ty: &'arena Type<'arena>,
    pub op: BinaryOp,
    pub right: Box<'arena, Expr<'arena>>,
    pub right_ty: &'arena Type<'arena>,
}

#[derive(Debug)]
pub struct ExprDeclare<'arena> {
    pub ident: Ident,
    pub ty: &'arena Type<'arena>,
    pub expr: Box<'arena, Expr<'arena>>,
}

#[derive(Debug)]
pub struct ExprAssign<'arena> {
    pub ident: Ident,
    pub expr: Box<'arena, Expr<'arena>>,
}

#[derive(Debug)]
pub struct ExprMatch<'arena> {
    pub scrutinee: Box<'arena, Expr<'arena>>,
    pub scrutinee_ty: &'arena Type<'arena>,
    pub ty: &'arena Type<'arena>,
    pub arms: Vec<'arena, (Pattern<'arena>, Expr<'arena>)>,
}

#[derive(Debug)]
pub struct ExprClosure<'arena> {
    pub func: FuncRef,
    pub captures: Option<HashMap<'arena, Ident, &'arena Type<'arena>>>,
}

#[derive(Debug)]
pub struct ExprIntrinsic<'arena> {
    pub intrinsic: Intrinsic,
    pub value: Box<'arena, Expr<'arena>>,
    pub value_ty: &'arena Type<'arena>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct FunctionTy<'arena> {
    pub params: Vec<'arena, &'arena Type<'arena>>,
    pub continuations: HashMap<'arena, Ident, &'arena Type<'arena>>,
}

impl hash::Hash for FunctionTy<'_> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.params.hash(state);
        for (&name, &ty) in self
            .continuations
            .iter()
            .sorted_unstable_by_key(|(&ident, _)| ident)
        {
            (name, ty).hash(state);
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Type<'arena> {
    Bool,
    Int,
    Float,
    String,
    Array(&'arena Type<'arena>, u64),
    Tuple(Vec<'arena, &'arena Type<'arena>>),
    Function(FunctionTy<'arena>),
    UserDefined(UserDefinedTyRef),
    Unknown,
    None,
}

impl<'arena> Type<'arena> {
    pub const fn function(
        params: Vec<'arena, &'arena Type<'arena>>,
        continuations: HashMap<'arena, Ident, &'arena Type<'arena>>,
    ) -> Type<'arena> {
        Type::Function(FunctionTy {
            params,
            continuations,
        })
    }

    pub const fn as_user_defined(&self) -> Option<UserDefinedTyRef> {
        if let Type::UserDefined(ty) = self {
            Some(*ty)
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
                let ty = ty_1.unify(ty_2, program, arena)?;
                Ok(program.insert_type(Type::Array(ty, *len_1), arena))
            }
            (Type::Tuple(t1), Type::Tuple(t2)) if t1.len() == t2.len() => {
                let types: Result<_> = try_collect_into(
                    Vec::new_in(arena),
                    t1.iter()
                        .zip(t2.iter())
                        .map(|(ty_1, ty_2)| ty_1.unify(ty_2, program, arena)),
                );
                Ok(program.insert_type(Type::Tuple(types?), arena))
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
                    Vec::new_in(arena),
                    params_1
                        .iter()
                        .zip(params_2.iter())
                        .map(|(ty_1, ty_2)| ty_1.unify(ty_2, program, arena)),
                );

                let continuations: Result<_> = try_collect_into(
                    HashMap::new_in(arena),
                    continuations_1
                        .iter()
                        .sorted_unstable_by_key(|(ident, _)| **ident)
                        .zip(
                            continuations_2
                                .iter()
                                .sorted_unstable_by_key(|(ident, _)| **ident),
                        )
                        .map(|((&ident_1, ty_1), (&ident_2, ty_2))| {
                            if ident_1 != ident_2 {
                                Err("mismatched continuation")?;
                            }

                            let ty = ty_1.unify(ty_2, program, arena)?;
                            Ok((ident_1, ty))
                        }),
                );

                let ty = Type::function(params?, continuations?);
                Ok(program.insert_type(ty, arena))
            }
            (Type::UserDefined(u1), Type::UserDefined(u2)) if u1 == u2 => Ok(self),
            (Type::Unknown | Type::None, _) => Ok(other),
            (_, Type::Unknown) => Ok(self),
            _ => Err(format!("expected {other:?}, found {self:?}").into()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum UserDefinedType<'arena> {
    Product(UserDefinedTypeFields<'arena>),
    Sum(Vec<'arena, (String, UserDefinedTypeFields<'arena>)>),
}

impl<'arena> UserDefinedType<'arena> {
    pub const fn as_product(&self) -> Option<&UserDefinedTypeFields<'arena>> {
        if let UserDefinedType::Product(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub const fn as_sum(&self) -> Option<&Vec<'arena, (String, UserDefinedTypeFields<'arena>)>> {
        if let UserDefinedType::Sum(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub fn fields(&self, variant: Option<&str>) -> Option<&UserDefinedTypeFields<'arena>> {
        match (self, variant) {
            (UserDefinedType::Product(fields), None) => Some(fields),
            (UserDefinedType::Sum(variants), Some(variant)) => variants
                .iter()
                .find(|(name, _)| name == variant)
                .map(|(_, fields)| fields),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum UserDefinedTypeFields<'arena> {
    Named(Vec<'arena, (String, &'arena Type<'arena>)>),
    Anonymous(Vec<'arena, &'arena Type<'arena>>),
    Unit,
}

impl<'arena> UserDefinedTypeFields<'arena> {
    pub fn as_named(&self) -> Option<&[(String, &'arena Type<'arena>)]> {
        if let UserDefinedTypeFields::Named(fields) = self {
            Some(fields)
        } else {
            None
        }
    }

    pub fn get(&self, field: &str) -> Option<&'arena Type<'arena>> {
        match self {
            UserDefinedTypeFields::Named(fields) => fields
                .iter()
                .find(|(name, _)| name == field)
                .map(|&(_, ty)| ty),
            UserDefinedTypeFields::Anonymous(fields) => {
                fields.get(field.parse::<usize>().ok()?).copied()
            }
            UserDefinedTypeFields::Unit => None,
        }
    }

    pub fn index_of(&self, field: &str) -> Option<usize> {
        match self {
            UserDefinedTypeFields::Named(fields) => {
                fields.iter().position(|(name, _)| name == field)
            }
            UserDefinedTypeFields::Anonymous(_) => field.parse().ok(),
            UserDefinedTypeFields::Unit => None,
        }
    }

    #[expect(
        clippy::iter_on_empty_collections,
        reason = "must be an empty slice to typecheck"
    )]
    pub fn iter(&self) -> impl Iterator<Item = &'arena Type<'arena>> + use<'_, 'arena> {
        enum Iter<'a, 'arena> {
            Named(slice::Iter<'a, (String, &'arena Type<'arena>)>),
            Anonymous(slice::Iter<'a, &'arena Type<'arena>>),
        }

        impl<'arena> Iterator for Iter<'_, 'arena> {
            type Item = &'arena Type<'arena>;

            fn next(&mut self) -> Option<Self::Item> {
                match self {
                    Iter::Named(iter) => iter.next().map(|&(_, ty)| ty),
                    Iter::Anonymous(iter) => iter.next().copied(),
                }
            }
        }

        match self {
            UserDefinedTypeFields::Named(fields) => Iter::Named(fields.iter()),
            UserDefinedTypeFields::Anonymous(fields) => Iter::Anonymous(fields.iter()),
            UserDefinedTypeFields::Unit => Iter::Anonymous([].iter()),
        }
    }

    pub fn names(&self) -> impl Iterator<Item = String> + use<'_> {
        enum Iter<'a> {
            Named(slice::Iter<'a, (String, &'a Type<'a>)>),
            Anonymous(Range<usize>),
        }

        impl Iterator for Iter<'_> {
            type Item = String;

            fn next(&mut self) -> Option<Self::Item> {
                match self {
                    Iter::Named(iter) => iter.next().map(|(name, _)| name.clone()),
                    Iter::Anonymous(iter) => iter.next().as_ref().map(ToString::to_string),
                }
            }
        }

        match self {
            UserDefinedTypeFields::Named(fields) => Iter::Named(fields.iter()),
            UserDefinedTypeFields::Anonymous(fields) => Iter::Anonymous(0..fields.len()),
            UserDefinedTypeFields::Unit => Iter::Anonymous(0..0),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            UserDefinedTypeFields::Named(fields) => fields.len(),
            UserDefinedTypeFields::Anonymous(fields) => fields.len(),
            UserDefinedTypeFields::Unit => 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug)]
pub struct Function<'arena> {
    pub params: Vec<'arena, (Ident, &'arena Type<'arena>)>,
    pub continuations: HashMap<'arena, Ident, &'arena Type<'arena>>,
    pub body: Vec<'arena, Expr<'arena>>,
    pub captures: Vec<'arena, Ident>,
    pub name: String,
}

impl<'arena> Function<'arena> {
    pub fn new(name: String, arena: &'arena Bump) -> Function<'arena> {
        Function {
            params: Vec::new_in(arena),
            continuations: HashMap::new_in(arena),
            body: Vec::new_in(arena),
            captures: Vec::new_in(arena),
            name,
        }
    }
}

#[derive(Debug)]
pub struct Program<'arena> {
    pub functions: HashMap<'arena, FuncRef, Function<'arena>>,
    pub signatures: HashMap<'arena, FuncRef, &'arena Type<'arena>>,
    pub types: HashSet<'arena, &'arena Type<'arena>>,
    lib_std: Option<StdLib>,
    pub name: String,
    pub continuation_idents: HashMap<'arena, String, Ident>,
    pub user_defined_types: HashMap<'arena, UserDefinedTyRef, &'arena UserDefinedType<'arena>>,
}

impl<'arena> Program<'arena> {
    pub fn new(name: String, arena: &'arena Bump) -> Program<'arena> {
        let mut program = Program {
            functions: HashMap::new_in(arena),
            signatures: HashMap::new_in(arena),
            types: HashSet::new_in(arena),
            lib_std: None,
            name,
            continuation_idents: HashMap::new_in(arena),
            user_defined_types: HashMap::new_in(arena),
        };
        program.lib_std = Some(lib_std::standard_library(&mut program, arena));
        program
    }

    #[allow(clippy::missing_panics_doc)] // Will not panic.
    pub const fn lib_std(&self) -> &StdLib {
        self.lib_std.as_ref().unwrap()
    }

    pub fn insert_type(&mut self, ty: Type<'arena>, arena: &'arena Bump) -> &'arena Type<'arena> {
        if let Some(ty) = self.types.get(&ty) {
            ty
        } else {
            let ty = arena.alloc(ty);
            self.types.insert(ty);
            ty
        }
    }

    pub fn continuation_ident(&mut self, continuation: &str, span: Span) -> Ident {
        if let Some(ident) = self.continuation_idents.get(continuation) {
            ident.with_span(span)
        } else {
            let ident = Ident::new(span);
            self.continuation_idents
                .insert(continuation.to_string(), ident);
            ident
        }
    }
}
