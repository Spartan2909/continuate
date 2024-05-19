use std::collections::HashMap;

use crate::common::FuncRef;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::high_level_ir::Expr;
use crate::high_level_ir::Function;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;
use crate::high_level_ir::TypeConstructor;
use crate::high_level_ir::UserDefinedType;

use continuate_arena::Arena;

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct StdLib {
    pub ty_bool: TypeRef,
    pub ty_int: TypeRef,
    pub ty_float: TypeRef,
    pub ty_string: TypeRef,

    pub fn_termination: FuncRef,
    pub fn_discriminant: FuncRef,
}

impl StdLib {
    pub const fn ty_for(&self, literal: &Literal) -> TypeRef {
        match literal {
            Literal::Int(_) => self.ty_int,
            Literal::Float(_) => self.ty_float,
            Literal::String(_) => self.ty_string,
        }
    }
}

pub(crate) fn standard_library<'arena>(
    program: &mut Program<'arena>,
    arena: &'arena Arena<'arena>,
) -> StdLib {
    let ty_bool = UserDefinedType {
        constructor: TypeConstructor::Sum(vec![vec![], vec![]]),
    };
    let ty_bool = arena.allocate(Type::UserDefined(ty_bool));
    let ty_bool_ref = program.ty();
    program.types.insert(ty_bool_ref, ty_bool);

    let ty_int = arena.allocate(Type::Int);
    let ty_int_ref = program.ty();
    program.types.insert(ty_int_ref, ty_int);

    let ty_float = arena.allocate(Type::Float);
    let ty_float_ref = program.ty();
    program.types.insert(ty_float_ref, ty_float);

    let ty_string = arena.allocate(Type::String);
    let ty_string_ref = program.ty();
    program.types.insert(ty_string_ref, ty_string);

    let mut fn_termination = Function::new("termination".to_string(), arena);
    let param = fn_termination.ident();
    fn_termination.params.push((param, ty_int_ref));
    fn_termination.body.push(Expr::Intrinsic {
        intrinsic: Intrinsic::Terminate,
        value: arena.allocate(Expr::Ident(param)),
    });

    let fn_termination_ref = program.function();
    program.functions.insert(fn_termination_ref, fn_termination);

    let int_fn = Type::function(vec![ty_int_ref], HashMap::new());
    let int_fn_ref = program.insert_type(int_fn, arena);

    let mut fn_discriminant = Function::new("discriminant".to_string(), arena);
    let param = fn_discriminant.ident();
    fn_discriminant.params.push((param, ty_bool_ref)); // TODO: Should be generic.
    let cont = fn_discriminant.ident();
    fn_discriminant.continuations.insert(cont, int_fn_ref);
    let intrinsic = Expr::Intrinsic {
        intrinsic: Intrinsic::Discriminant,
        value: arena.allocate(Expr::Ident(param)),
    };
    let discriminant = fn_discriminant.ident();
    let declare = Expr::Declare {
        ident: discriminant,
        ty: ty_int_ref,
        expr: arena.allocate(intrinsic),
    };
    fn_discriminant.body.push(declare);
    let mut args = Vec::with_capacity_in(1, arena);
    args.push(Expr::Ident(discriminant));
    let cont_call = Expr::Call(arena.allocate(Expr::Ident(cont)), args);
    fn_discriminant.body.push(cont_call);

    let fn_discriminant_ref = program.function();
    program
        .functions
        .insert(fn_discriminant_ref, fn_discriminant);

    StdLib {
        ty_bool: ty_bool_ref,
        ty_int: ty_int_ref,
        ty_float: ty_float_ref,
        ty_string: ty_string_ref,
        fn_termination: fn_termination_ref,
        fn_discriminant: fn_discriminant_ref,
    }
}
