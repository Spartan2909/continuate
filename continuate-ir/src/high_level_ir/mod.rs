mod lowering;
pub use lowering::lower;

mod typeck;
pub use typeck::typeck;

use crate::{
    common::{BinaryOp, FuncRef, Ident, Intrinsic, Literal, UnaryOp, UserDefinedTyRef},
    lib_std::{self, StdLib},
};

use std::{
    collections::{HashMap, HashSet},
    fmt, hash,
    ops::{self, Range},
    slice,
    sync::Arc,
};

use continuate_error::{Result, Span};

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
        ty: Arc<Type>,
        variant: Option<String>,
        fields: DestructureFields,
    },
}

impl Pattern {
    #[inline]
    pub const fn as_ident(&self) -> Option<Ident> {
        if let Pattern::Ident(ident) = self {
            Some(*ident)
        } else {
            None
        }
    }
}

pub trait Tag: fmt::Debug {
    type Tagged<T: fmt::Debug>: fmt::Debug;
}

impl Tag for () {
    type Tagged<T: fmt::Debug> = T;
}

#[derive(Debug)]
pub struct Typed<T> {
    pub value: T,
    pub ty: Arc<Type>,
}

impl<T> Typed<T> {
    #[inline]
    pub const fn new(value: T, ty: Arc<Type>) -> Typed<T> {
        Typed { value, ty }
    }

    #[inline]
    pub fn into_pair(self) -> (T, Arc<Type>) {
        let Typed { value, ty } = self;
        (value, ty)
    }

    #[inline]
    pub fn boxed(self) -> Typed<Box<T>> {
        let Typed { value, ty } = self;
        Typed {
            value: Box::new(value),
            ty,
        }
    }
}

impl<T> ops::Deref for Typed<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> ops::DerefMut for Typed<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl Tag for Arc<Type> {
    type Tagged<T: fmt::Debug> = Typed<T>;
}

pub enum Expr<T: Tag> {
    Literal(Literal),
    Ident(ExprIdent<T>),
    Function(FuncRef),
    Block(T::Tagged<ExprBlock<T>>),
    Tuple(T::Tagged<ExprTuple<T>>),
    Constructor(ExprConstructor<T>),
    Array(T::Tagged<ExprArray<T>>),
    Get(ExprGet<T>),
    Set(ExprSet<T>),
    Call(ExprCall<T>),
    Application(T::Tagged<ExprApplication<T>>),
    Unary(ExprUnary<T>),
    Binary(ExprBinary<T>),
    Declare(ExprDeclare<T>),
    Assign(ExprAssign<T>),
    Match(ExprMatch<T>),
    Closure(ExprClosure),
    Intrinsic(ExprIntrinsic<T>),
}

impl<T: Tag> fmt::Debug for Expr<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Literal(l) => f.debug_tuple("Literal").field(l).finish(),
            Expr::Ident(i) => f.debug_tuple("Ident").field(i).finish(),
            Expr::Function(fun) => f.debug_tuple("Function").field(fun).finish(),
            Expr::Block(x) => f.debug_tuple("Block").field(x).finish(),
            Expr::Tuple(x) => f.debug_tuple("Tuple").field(x).finish(),
            Expr::Constructor(x) => f.debug_tuple("Constructor").field(x).finish(),
            Expr::Array(x) => f.debug_tuple("Array").field(x).finish(),
            Expr::Get(x) => f.debug_tuple("Get").field(x).finish(),
            Expr::Set(x) => f.debug_tuple("Set").field(x).finish(),
            Expr::Call(x) => f.debug_tuple("Call").field(x).finish(),
            Expr::Application(x) => f.debug_tuple("Application").field(x).finish(),
            Expr::Unary(x) => f.debug_tuple("Unary").field(x).finish(),
            Expr::Binary(x) => f.debug_tuple("Binary").field(x).finish(),
            Expr::Declare(x) => f.debug_tuple("Declare").field(x).finish(),
            Expr::Assign(x) => f.debug_tuple("Assign").field(x).finish(),
            Expr::Match(x) => f.debug_tuple("Match").field(x).finish(),
            Expr::Closure(x) => f.debug_tuple("Closure").field(x).finish(),
            Expr::Intrinsic(x) => f.debug_tuple("Intrinsic").field(x).finish(),
        }
    }
}

#[derive(Debug)]
pub struct ExprIdent<T: Tag> {
    pub ident: T::Tagged<Ident>,
}

#[derive(Debug)]
pub struct ExprBlock<T: Tag> {
    pub exprs: Vec<Expr<T>>,
}

#[derive(Debug)]
pub struct ExprTuple<T: Tag> {
    pub exprs: Vec<Expr<T>>,
}

#[derive(Debug)]
pub enum ExprConstructorFields<T: Tag> {
    Named(Vec<(String, Expr<T>)>),
    Anonymous(Vec<Expr<T>>),
    Unit,
}

#[derive(Debug)]
pub struct ExprConstructor<T: Tag> {
    pub ty: Arc<Type>,
    pub variant: Option<String>,
    pub fields: ExprConstructorFields<T>,
}

#[derive(Debug)]
pub struct ExprArray<T: Tag> {
    pub exprs: Vec<Expr<T>>,
}

#[derive(Debug)]
pub struct ExprGet<T: Tag> {
    pub object: T::Tagged<Box<Expr<T>>>,
    pub field: String,
}

#[derive(Debug)]
pub struct ExprSet<T: Tag> {
    pub object: T::Tagged<Box<Expr<T>>>,
    pub field: String,
    pub value: Box<Expr<T>>,
}

#[derive(Debug)]
pub struct ExprCall<T: Tag> {
    pub callee: T::Tagged<Box<Expr<T>>>,
    pub positional: Vec<Expr<T>>,
    pub named: Vec<(Ident, Expr<T>)>,
}

#[derive(Debug)]
pub struct ExprApplication<T: Tag> {
    pub callee: T::Tagged<Box<Expr<T>>>,
    pub positional: Vec<Expr<T>>,
    pub named: Vec<(Ident, Expr<T>)>,
}

#[derive(Debug)]
pub struct ExprUnary<T: Tag> {
    pub op: UnaryOp,
    pub right: T::Tagged<Box<Expr<T>>>,
}

#[derive(Debug)]
pub struct ExprBinary<T: Tag> {
    pub left: T::Tagged<Box<Expr<T>>>,
    pub op: BinaryOp,
    pub right: T::Tagged<Box<Expr<T>>>,
}

#[derive(Debug)]
pub struct ExprDeclare<T: Tag> {
    pub ident: Ident,
    pub ty: Arc<Type>,
    pub expr: Box<Expr<T>>,
}

#[derive(Debug)]
pub struct ExprAssign<T: Tag> {
    pub ident: Ident,
    pub expr: Box<Expr<T>>,
}

#[derive(Debug)]
pub struct ExprMatch<T: Tag> {
    pub scrutinee: T::Tagged<Box<Expr<T>>>,
    pub arms: Vec<(Pattern, Expr<T>)>,
}

#[derive(Debug)]
pub struct ExprClosure {
    pub func: FuncRef,
    pub captures: HashMap<Ident, Arc<Type>>,
}

#[derive(Debug)]
pub struct ExprIntrinsic<T: Tag> {
    pub intrinsic: Intrinsic,
    pub values: Vec<T::Tagged<Expr<T>>>,
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
    UserDefined(UserDefinedTyRef),
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
    pub const fn as_array(&self) -> Option<(&Arc<Type>, u64)> {
        if let Type::Array(ty, n) = self {
            Some((ty, *n))
        } else {
            None
        }
    }

    #[inline]
    pub const fn as_user_defined(&self) -> Option<UserDefinedTyRef> {
        if let Type::UserDefined(ty) = self {
            Some(*ty)
        } else {
            None
        }
    }

    /// Ensure that `self` fits in `other`.
    pub(crate) fn unify(
        self: &Arc<Type>,
        other: &Arc<Type>,
        program: &mut Program<Arc<Type>>,
    ) -> Result<Arc<Type>> {
        if self == other {
            return Ok(Arc::clone(self));
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
                    positional_params: positional_params_1,
                    named_params: named_params_1,
                }),
                Type::Function(FunctionTy {
                    positional_params: positional_params_2,
                    named_params: named_params_2,
                }),
            ) if positional_params_1.len() == positional_params_2.len() => {
                let params: Result<_> = positional_params_1
                    .iter()
                    .zip(positional_params_2.iter())
                    .map(|(ty_1, ty_2)| ty_1.unify(ty_2, program))
                    .collect();

                let named_params: Result<_> = named_params_1
                    .iter()
                    .sorted_unstable_by_key(|(ident, _)| **ident)
                    .zip(
                        named_params_2
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

                let ty = Type::function(params?, named_params?);
                Ok(program.insert_type(ty))
            }
            (Type::Unknown | Type::None, _) => Ok(Arc::clone(other)),
            (_, Type::Unknown) => Ok(Arc::clone(self)),
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
    #[inline]
    pub const fn as_product(&self) -> Option<&UserDefinedTypeFields> {
        if let UserDefinedType::Product(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    #[inline]
    pub const fn as_sum(&self) -> Option<&Vec<(String, UserDefinedTypeFields)>> {
        if let UserDefinedType::Sum(ty) = self {
            Some(ty)
        } else {
            None
        }
    }

    #[inline]
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
    Named(Vec<(String, Arc<Type>)>),
    Anonymous(Vec<Arc<Type>>),
    Unit,
}

impl UserDefinedTypeFields {
    #[inline]
    pub fn as_named(&self) -> Option<&[(String, Arc<Type>)]> {
        if let UserDefinedTypeFields::Named(fields) = self {
            Some(fields)
        } else {
            None
        }
    }

    #[inline]
    pub fn get(&self, field: &str) -> Option<&Arc<Type>> {
        match self {
            UserDefinedTypeFields::Named(fields) => fields
                .iter()
                .find(|(name, _)| name == field)
                .map(|(_, ty)| ty),
            UserDefinedTypeFields::Anonymous(fields) => fields.get(field.parse::<usize>().ok()?),
            UserDefinedTypeFields::Unit => None,
        }
    }

    #[inline]
    pub fn index_of(&self, field: &str) -> Option<usize> {
        match self {
            UserDefinedTypeFields::Named(fields) => {
                fields.iter().position(|(name, _)| name == field)
            }
            UserDefinedTypeFields::Anonymous(_) => field.parse().ok(),
            UserDefinedTypeFields::Unit => None,
        }
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &Arc<Type>> + use<'_> {
        enum Iter<'a> {
            Named(slice::Iter<'a, (String, Arc<Type>)>),
            Anonymous(slice::Iter<'a, Arc<Type>>),
        }

        impl<'a> Iterator for Iter<'a> {
            type Item = &'a Arc<Type>;

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

    #[inline]
    pub fn names(&self) -> impl Iterator<Item = String> + use<'_> {
        enum Iter<'a> {
            Named(slice::Iter<'a, (String, Arc<Type>)>),
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

    #[inline]
    pub const fn len(&self) -> usize {
        match self {
            UserDefinedTypeFields::Named(fields) => fields.len(),
            UserDefinedTypeFields::Anonymous(fields) => fields.len(),
            UserDefinedTypeFields::Unit => 0,
        }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug)]
pub struct Function<T: Tag> {
    pub positional: Vec<(Ident, Arc<Type>)>,
    pub named: HashMap<Ident, Arc<Type>>,
    pub body: Vec<Expr<T>>,
    pub captures: Vec<Ident>,
    pub name: String,
}

impl<T: Tag> Function<T> {
    #[inline]
    pub fn new(name: String) -> Function<T> {
        Function {
            positional: Vec::new(),
            named: HashMap::new(),
            body: Vec::new(),
            captures: Vec::new(),
            name,
        }
    }

    #[inline]
    pub fn clone_metadata<U: Tag>(function: &Function<U>, body: Vec<Expr<T>>) -> Function<T> {
        Function {
            positional: function.positional.clone(),
            named: function.named.clone(),
            body,
            captures: function.captures.clone(),
            name: function.name.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Program<T: Tag> {
    pub functions: HashMap<FuncRef, Function<T>>,
    pub signatures: HashMap<FuncRef, Arc<Type>>,
    pub types: HashSet<Arc<Type>>,
    lib_std: Option<StdLib>,
    pub name: String,
    pub continuation_idents: HashMap<String, Ident>,
    pub user_defined_types: HashMap<UserDefinedTyRef, Arc<UserDefinedType>>,
}

impl Program<()> {
    #[inline]
    pub fn new(name: String) -> Program<()> {
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

impl<T: Tag> Program<T> {
    #[inline]
    pub fn clone_metadata<U: Tag>(program: &Program<U>) -> Program<T> {
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

    #[expect(clippy::missing_panics_doc, reason = "will not panic")]
    #[inline]
    pub const fn lib_std(&self) -> &StdLib {
        self.lib_std.as_ref().unwrap()
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

    #[inline]
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
