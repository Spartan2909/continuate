use crate::common::FuncRef;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::high_level_ir::Expr;
use crate::high_level_ir::ExprCall;
use crate::high_level_ir::ExprDeclare;
use crate::high_level_ir::ExprIntrinsic;
use crate::high_level_ir::Function;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;
use crate::high_level_ir::TypeConstructor;
use crate::high_level_ir::UserDefinedType;
use crate::HashMap;
use crate::Vec;

use bumpalo::Bump;

use continuate_utils::Box;

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct StdLib {
    pub ty_bool: TypeRef,
    pub ty_int: TypeRef,
    pub ty_float: TypeRef,
    pub ty_string: TypeRef,
    pub ty_unknown: TypeRef,

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
    arena: &'arena Bump,
) -> StdLib {
    let empty_vec = Vec::new_in(arena);
    let mut variants = Vec::with_capacity_in(2, arena);
    variants.extend([empty_vec.clone(), empty_vec]);
    let ty_bool = UserDefinedType {
        constructor: TypeConstructor::Sum(variants),
    };
    let ty_bool = arena.alloc(Type::UserDefined(ty_bool));
    let ty_bool_ref = program.ty();
    program.types.insert(ty_bool_ref, ty_bool);

    let ty_int = arena.alloc(Type::Int);
    let ty_int_ref = program.ty();
    program.types.insert(ty_int_ref, ty_int);

    let ty_float = arena.alloc(Type::Float);
    let ty_float_ref = program.ty();
    program.types.insert(ty_float_ref, ty_float);

    let ty_string = arena.alloc(Type::String);
    let ty_string_ref = program.ty();
    program.types.insert(ty_string_ref, ty_string);

    let ty_unknown_ref = program.insert_type(Type::Unknown, arena).0;

    let mut fn_termination = Function::new("termination".to_string(), arena);
    let param = fn_termination.ident();
    fn_termination.params.push((param, ty_int_ref));
    fn_termination.body.push(Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Terminate,
        value: Box::new_in(Expr::Ident(param), arena),
        value_ty: ty_unknown_ref,
    }));

    let fn_termination_ref = program.function();
    program.functions.insert(fn_termination_ref, fn_termination);

    let mut fn_termination_params = Vec::with_capacity_in(1, arena);
    fn_termination_params.push(ty_int_ref);
    let fn_termination_ty = Type::function(fn_termination_params, HashMap::new_in(arena));
    let fn_termination_ty = program.insert_type(fn_termination_ty, arena).0;
    program
        .signatures
        .insert(fn_termination_ref, fn_termination_ty);

    let mut params = Vec::with_capacity_in(1, arena);
    params.push(ty_int_ref);
    let int_fn = Type::function(params, HashMap::new_in(arena));
    let int_fn_ref = program.insert_type(int_fn, arena).0;

    let mut fn_discriminant = Function::new("discriminant".to_string(), arena);
    let param = fn_discriminant.ident();
    fn_discriminant.params.push((param, ty_bool_ref)); // TODO: Should be generic.
    let cont = fn_discriminant.ident();
    fn_discriminant.continuations.insert(cont, int_fn_ref);
    let intrinsic = Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Discriminant,
        value: Box::new_in(Expr::Ident(param), arena),
        value_ty: ty_unknown_ref,
    });
    let discriminant = fn_discriminant.ident();
    let declare = Expr::Declare(ExprDeclare {
        ident: discriminant,
        ty: ty_int_ref,
        expr: Box::new_in(intrinsic, arena),
    });
    fn_discriminant.body.push(declare);
    let mut args = Vec::with_capacity_in(1, arena);
    args.push(Expr::Ident(discriminant));
    let cont_call = Expr::Call(ExprCall {
        callee: Box::new_in(Expr::Ident(cont), arena),
        callee_ty: ty_unknown_ref,
        args,
    });
    fn_discriminant.body.push(cont_call);

    let fn_discriminant_ref = program.function();
    program
        .functions
        .insert(fn_discriminant_ref, fn_discriminant);

    let mut fn_discriminant_params = Vec::with_capacity_in(1, arena);
    fn_discriminant_params.push(ty_bool_ref);
    let mut fn_discriminant_conts = HashMap::with_capacity_in(1, arena);
    fn_discriminant_conts.insert(cont, int_fn_ref);
    let fn_discriminant_ty = Type::function(fn_discriminant_params, fn_discriminant_conts);
    let fn_discriminant_ty = program.insert_type(fn_discriminant_ty, arena).0;
    program
        .signatures
        .insert(fn_discriminant_ref, fn_discriminant_ty);

    StdLib {
        ty_bool: ty_bool_ref,
        ty_int: ty_int_ref,
        ty_float: ty_float_ref,
        ty_string: ty_string_ref,
        ty_unknown: ty_unknown_ref,
        fn_termination: fn_termination_ref,
        fn_discriminant: fn_discriminant_ref,
    }
}
