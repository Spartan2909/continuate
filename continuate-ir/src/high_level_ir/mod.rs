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

#[derive(Debug, PartialEq)]
pub enum DestructureFields {
    Named(Vec<(String, Pattern)>),
    Anonymous(Vec<Pattern>),
    Unit,
}

#[derive(Debug, PartialEq)]
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
    pub ty: Rc<Type>,
}

#[derive(Debug)]
pub struct ExprTuple {
    pub exprs: Vec<Expr>,
    pub ty: Rc<Type>,
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
    pub ty: Rc<Type>,
    pub element_ty: Rc<Type>,
}

#[derive(Debug)]
pub struct ExprGet {
    pub object: Box<Expr>,
    pub object_ty: Rc<Type>,
    pub field: String,
}

#[derive(Debug)]
pub struct ExprSet {
    pub object: Box<Expr>,
    pub object_ty: Rc<Type>,
    pub field: String,
    pub value: Box<Expr>,
    pub value_ty: Rc<Type>,
}

#[derive(Debug)]
pub struct ExprCall {
    pub callee: Box<Expr>,
    pub callee_ty: Rc<Type>,
    pub args: Vec<Expr>,
}

#[derive(Debug)]
pub struct ExprContApplication {
    pub callee: Box<Expr>,
    pub callee_ty: Rc<Type>,
    pub continuations: Vec<(Ident, Expr)>,
    pub result_ty: Rc<Type>,
}

#[derive(Debug)]
pub struct ExprUnary {
    pub op: UnaryOp,
    pub right: Box<Expr>,
    pub right_ty: Rc<Type>,
}

#[derive(Debug)]
pub struct ExprBinary {
    pub left: Box<Expr>,
    pub left_ty: Rc<Type>,
    pub op: BinaryOp,
    pub right: Box<Expr>,
    pub right_ty: Rc<Type>,
}

#[derive(Debug)]
pub struct ExprDeclare {
    pub ident: Ident,
    pub ty: Rc<Type>,
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
    pub scrutinee_ty: Rc<Type>,
    pub ty: Rc<Type>,
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
    pub value: Box<Expr>,
    pub value_ty: Rc<Type>,
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
        program: &mut Program,
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
pub struct Function {
    pub params: Vec<(Ident, Rc<Type>)>,
    pub continuations: HashMap<Ident, Rc<Type>>,
    pub body: Vec<Expr>,
    pub captures: Vec<Ident>,
    pub name: String,
}

impl Function {
    pub fn new(name: String) -> Function {
        Function {
            params: Vec::new(),
            continuations: HashMap::new(),
            body: Vec::new(),
            captures: Vec::new(),
            name,
        }
    }
}

#[derive(Debug)]
pub struct Program {
    pub functions: HashMap<FuncRef, Function>,
    pub signatures: HashMap<FuncRef, Rc<Type>>,
    pub types: HashSet<Rc<Type>>,
    lib_std: Option<StdLib>,
    pub name: String,
    pub continuation_idents: HashMap<String, Ident>,
    pub user_defined_types: HashMap<UserDefinedTyRef, Rc<UserDefinedType>>,
}

impl Program {
    pub fn new(name: String) -> Program {
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
