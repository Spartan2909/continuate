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

use std::collections::HashMap;
use std::collections::HashSet;
use std::hash;
use std::ops::Range;
use std::rc::Rc;
use std::slice;

use continuate_error::Result;
use continuate_error::Span;

use itertools::Itertools as _;

#[derive(Debug, Clone, PartialEq)]
pub enum DestructureFields {
    Named(Vec<(String, Pattern)>),
    Anonymous(Vec<Pattern>),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard,
    Ident(Ident),
    Destructure {
        ty: Rc<Type>,
        variant: Option<String>,
        fields: DestructureFields,
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

#[derive(Debug)]
pub enum Expr {
    Literal(Literal),
    Ident(Ident),
    Function(FuncRef),
    Block(ExprBlock),
    Tuple(ExprTuple),
    Constructor(ExprConstructor),
    Array(ExprArray),
    Get(ExprGet),
    Set(ExprSet),
    Call(ExprCall),
    ContApplication(ExprContApplication),
    Unary(ExprUnary),
    Binary(ExprBinary),
    Declare(ExprDeclare),
    Assign(ExprAssign),
    Match(ExprMatch),
    Closure(ExprClosure),
    Intrinsic(ExprIntrinsic),
}

#[derive(Debug)]
pub struct ExprBlock {
    pub exprs: Vec<Expr>,
}

#[derive(Debug)]
pub struct ExprTuple {
    pub exprs: Vec<Expr>,
}

#[derive(Debug)]
pub enum ExprConstructorFields {
    Named(Vec<(String, Expr)>),
    Anonymous(Vec<Expr>),
    Unit,
}

#[derive(Debug)]
pub struct ExprConstructor {
    pub ty: Rc<Type>,
    pub variant: Option<String>,
    pub fields: ExprConstructorFields,
}

#[derive(Debug)]
pub struct ExprArray {
    pub exprs: Vec<Expr>,
}

#[derive(Debug)]
pub struct ExprGet {
    pub object: Box<Expr>,
    pub field: String,
}

#[derive(Debug)]
pub struct ExprSet {
    pub object: Box<Expr>,
    pub field: String,
    pub value: Box<Expr>,
}

#[derive(Debug)]
pub struct ExprCall {
    pub callee: Box<Expr>,
    pub args: Vec<Expr>,
}

#[derive(Debug)]
pub struct ExprContApplication {
    pub callee: Box<Expr>,
    pub continuations: Vec<(Ident, Expr)>,
}

#[derive(Debug)]
pub struct ExprUnary {
    pub op: UnaryOp,
    pub right: Box<Expr>,
}

#[derive(Debug)]
pub struct ExprBinary {
    pub left: Box<Expr>,
    pub op: BinaryOp,
    pub right: Box<Expr>,
}

#[derive(Debug)]
pub struct ExprDeclare {
    pub ident: Ident,
    pub ty: Option<Rc<Type>>,
    pub expr: Box<Expr>,
}

#[derive(Debug)]
pub struct ExprAssign {
    pub ident: Ident,
    pub expr: Box<Expr>,
}

#[derive(Debug)]
pub struct ExprMatch {
    pub scrutinee: Box<Expr>,
    pub arms: Vec<(Pattern, Expr)>,
}

#[derive(Debug)]
pub struct ExprClosure {
    pub func: FuncRef,
    pub captures: Option<HashMap<Ident, Rc<Type>>>,
}

#[derive(Debug)]
pub struct ExprIntrinsic {
    pub intrinsic: Intrinsic,
    pub values: Vec<Expr>,
}

#[derive(Debug)]
pub enum TypedExpr {
    Literal(Literal),
    Ident(Ident),
    Function(FuncRef),
    Block(Typed<TypedExprBlock>),
    Tuple(Typed<TypedExprTuple>),
    Constructor(TypedExprConstructor),
    Array(TypedExprArray),
    Get(TypedExprGet),
    Set(TypedExprSet),
    Call(TypedExprCall),
    ContApplication(Typed<TypedExprContApplication>),
    Unary(TypedExprUnary),
    Binary(TypedExprBinary),
    Declare(TypedExprDeclare),
    Assign(TypedExprAssign),
    Match(Typed<TypedExprMatch>),
    Closure(TypedExprClosure),
    Intrinsic(TypedExprIntrinsic),
}

#[derive(Debug)]
pub struct Typed<T> {
    pub value: T,
    pub ty: Rc<Type>,
}

impl<T> Typed<T> {
    pub const fn new(value: T, ty: Rc<Type>) -> Typed<T> {
        Typed { value, ty }
    }

    pub fn boxed(self) -> Typed<Box<T>> {
        Typed {
            value: Box::new(self.value),
            ty: self.ty,
        }
    }

    pub fn into_value_ty(self) -> (T, Rc<Type>) {
        let Typed { value, ty } = self;
        (value, ty)
    }
}

#[derive(Debug)]
pub struct TypedExprBlock {
    pub exprs: Vec<TypedExpr>,
}

#[derive(Debug)]
pub struct TypedExprTuple {
    pub exprs: Vec<TypedExpr>,
}

#[derive(Debug)]
pub enum TypedExprConstructorFields {
    Named(Vec<(String, TypedExpr)>),
    Anonymous(Vec<TypedExpr>),
    Unit,
}

#[derive(Debug)]
pub struct TypedExprConstructor {
    pub ty: Rc<Type>,
    pub variant: Option<String>,
    pub fields: TypedExprConstructorFields,
}

#[derive(Debug)]
pub struct TypedExprArray {
    pub exprs: Vec<TypedExpr>,
    pub element_ty: Rc<Type>,
}

#[derive(Debug)]
pub struct TypedExprGet {
    pub object: Typed<Box<TypedExpr>>,
    pub field: String,
}

#[derive(Debug)]
pub struct TypedExprSet {
    pub object: Typed<Box<TypedExpr>>,
    pub field: String,
    pub value: Typed<Box<TypedExpr>>,
}

#[derive(Debug)]
pub struct TypedExprCall {
    pub callee: Typed<Box<TypedExpr>>,
    pub args: Vec<TypedExpr>,
}

#[derive(Debug)]
pub struct TypedExprContApplication {
    pub callee: Typed<Box<TypedExpr>>,
    pub continuations: Vec<(Ident, TypedExpr)>,
}

#[derive(Debug)]
pub struct TypedExprUnary {
    pub op: UnaryOp,
    pub right: Typed<Box<TypedExpr>>,
}

#[derive(Debug)]
pub struct TypedExprBinary {
    pub left: Typed<Box<TypedExpr>>,
    pub op: BinaryOp,
    pub right: Typed<Box<TypedExpr>>,
}

#[derive(Debug)]
pub struct TypedExprDeclare {
    pub ident: Ident,
    pub ty: Rc<Type>,
    pub expr: Box<TypedExpr>,
}

#[derive(Debug)]
pub struct TypedExprAssign {
    pub ident: Ident,
    pub expr: Box<TypedExpr>,
}

#[derive(Debug)]
pub struct TypedExprMatch {
    pub scrutinee: Typed<Box<TypedExpr>>,
    pub arms: Vec<(Pattern, TypedExpr)>,
}

#[derive(Debug)]
pub struct TypedExprClosure {
    pub func: FuncRef,
    pub captures: HashMap<Ident, Rc<Type>>,
}

#[derive(Debug)]
pub struct TypedExprIntrinsic {
    pub intrinsic: Intrinsic,
    pub values: Vec<Typed<TypedExpr>>,
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
    UserDefined(UserDefinedTyRef),
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

    pub const fn as_user_defined(&self) -> Option<UserDefinedTyRef> {
        if let Type::UserDefined(ty) = self {
            Some(*ty)
        } else {
            None
        }
    }

    /// Ensure that `self` fits in `other`.
    pub(crate) fn unify(
        self: &Rc<Type>,
        other: &Rc<Type>,
        program: &mut Program<TypedExpr>,
    ) -> Result<Rc<Type>> {
        if self == other {
            return Ok(Rc::clone(self));
        }

        match (&**self, &**other) {
            (Type::Array(ty_1, len_1), Type::Array(ty_2, len_2)) if len_1 == len_2 => {
                let ty = ty_1.unify(ty_2, program)?;
                Ok(program.insert_type(Type::Array(ty, *len_1)))
            }
            (Type::Tuple(t1), Type::Tuple(t2)) if t1.len() == t2.len() => {
                let types: Result<_> = t1
                    .iter()
                    .zip(t2.iter())
                    .map(|(ty_1, ty_2)| ty_1.unify(ty_2, program))
                    .collect();
                Ok(program.insert_type(Type::Tuple(types?)))
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
                let params: Result<_> = params_1
                    .iter()
                    .zip(params_2.iter())
                    .map(|(ty_1, ty_2)| ty_1.unify(ty_2, program))
                    .collect();

                let continuations: Result<_> = continuations_1
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

                        let ty = ty_1.unify(ty_2, program)?;
                        Ok((ident_1, ty))
                    })
                    .collect();

                let ty = Type::function(params?, continuations?);
                Ok(program.insert_type(ty))
            }
            (Type::Unknown | Type::None, _) => Ok(Rc::clone(other)),
            (_, Type::Unknown) => Ok(Rc::clone(self)),
            _ => Err(format!("expected {other:?}, found {self:?}").into()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UserDefinedType {
    Product(UserDefinedTypeFields),
    Sum(Vec<(String, UserDefinedTypeFields)>),
}

impl UserDefinedType {
    pub const fn as_product(&self) -> Option<&UserDefinedTypeFields> {
        if let UserDefinedType::Product(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub const fn as_sum(&self) -> Option<&Vec<(String, UserDefinedTypeFields)>> {
        if let UserDefinedType::Sum(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    pub fn fields(&self, variant: Option<&str>) -> Option<&UserDefinedTypeFields> {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UserDefinedTypeFields {
    Named(Vec<(String, Rc<Type>)>),
    Anonymous(Vec<Rc<Type>>),
    Unit,
}

impl UserDefinedTypeFields {
    pub fn as_named(&self) -> Option<&[(String, Rc<Type>)]> {
        if let UserDefinedTypeFields::Named(fields) = self {
            Some(fields)
        } else {
            None
        }
    }

    pub fn get(&self, field: &str) -> Option<&Rc<Type>> {
        match self {
            UserDefinedTypeFields::Named(fields) => fields
                .iter()
                .find(|(name, _)| name == field)
                .map(|(_, ty)| ty),
            UserDefinedTypeFields::Anonymous(fields) => fields.get(field.parse::<usize>().ok()?),
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
    pub fn iter(&self) -> impl Iterator<Item = &Rc<Type>> + use<'_> {
        enum Iter<'a> {
            Named(slice::Iter<'a, (String, Rc<Type>)>),
            Anonymous(slice::Iter<'a, Rc<Type>>),
        }

        impl<'a> Iterator for Iter<'a> {
            type Item = &'a Rc<Type>;

            fn next(&mut self) -> Option<Self::Item> {
                match self {
                    Iter::Named(iter) => iter.next().map(|(_, ty)| ty),
                    Iter::Anonymous(iter) => iter.next(),
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
            Named(slice::Iter<'a, (String, Rc<Type>)>),
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
pub struct Function<E> {
    pub params: Vec<(Ident, Rc<Type>)>,
    pub continuations: HashMap<Ident, Rc<Type>>,
    pub body: Vec<E>,
    pub captures: Vec<Ident>,
    pub name: String,
}

impl<E> Function<E> {
    pub fn new(name: String) -> Function<E> {
        Function {
            params: Vec::new(),
            continuations: HashMap::new(),
            body: Vec::new(),
            captures: Vec::new(),
            name,
        }
    }

    pub fn clone_metadata<E2>(function: &Function<E2>, body: Vec<E>) -> Function<E> {
        Function {
            params: function.params.clone(),
            continuations: function.continuations.clone(),
            body,
            captures: function.captures.clone(),
            name: function.name.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Program<E> {
    pub functions: HashMap<FuncRef, Function<E>>,
    pub signatures: HashMap<FuncRef, Rc<Type>>,
    pub types: HashSet<Rc<Type>>,
    lib_std: Option<StdLib>,
    pub name: String,
    pub continuation_idents: HashMap<String, Ident>,
    pub user_defined_types: HashMap<UserDefinedTyRef, Rc<UserDefinedType>>,
}

impl Program<Expr> {
    pub fn new(name: String) -> Program<Expr> {
        let mut program = Program {
            functions: HashMap::new(),
            signatures: HashMap::new(),
            types: HashSet::new(),
            lib_std: None,
            name,
            continuation_idents: HashMap::new(),
            user_defined_types: HashMap::new(),
        };
        program.lib_std = Some(lib_std::standard_library(&mut program));
        program
    }
}

impl<E> Program<E> {
    pub fn clone_metadata<E2>(program: &Program<E2>) -> Program<E> {
        Program {
            functions: HashMap::new(),
            signatures: program.signatures.clone(),
            types: program.types.clone(),
            lib_std: program.lib_std,
            name: program.name.clone(),
            continuation_idents: program.continuation_idents.clone(),
            user_defined_types: program.user_defined_types.clone(),
        }
    }

    #[allow(clippy::missing_panics_doc)] // Will not panic.
    pub const fn lib_std(&self) -> &StdLib {
        self.lib_std.as_ref().unwrap()
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
