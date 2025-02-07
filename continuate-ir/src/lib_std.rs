use crate::common::FuncRef;
use crate::common::Intrinsic;
use crate::high_level_ir::Expr;
use crate::high_level_ir::ExprCall;
use crate::high_level_ir::ExprDeclare;
use crate::high_level_ir::ExprIntrinsic;
use crate::high_level_ir::Function;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;

use bumpalo::Bump;

use continuate_utils::Box;
use continuate_utils::HashMap;
use continuate_utils::Vec;

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct StdLib {
    pub fn_termination: FuncRef,
}

pub(crate) fn standard_library<'arena>(
    program: &mut Program<'arena>,
    arena: &'arena Bump,
) -> StdLib {
    let ty_bool = arena.alloc(Type::Bool);

    let ty_int = arena.alloc(Type::Int);

    let ty_unknown = program.insert_type(Type::Unknown, arena);

    let mut fn_termination = Function::new("termination".to_string(), arena);
    let param = fn_termination.ident();
    fn_termination.params.push((param, ty_int));
    fn_termination.body.push(Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Terminate,
        value: Box::new_in(Expr::Ident(param), arena),
        value_ty: ty_unknown,
    }));

    let fn_termination_ref = program.function();
    program.functions.insert(fn_termination_ref, fn_termination);

    let mut fn_termination_params = Vec::with_capacity_in(1, arena);
    fn_termination_params.push(&*ty_int);
    let fn_termination_ty = Type::function(fn_termination_params, HashMap::new_in(arena));
    let fn_termination_ty = program.insert_type(fn_termination_ty, arena);
    program
        .signatures
        .insert(fn_termination_ref, fn_termination_ty);

    let mut params = Vec::with_capacity_in(1, arena);
    params.push(&*ty_int);
    let int_fn = Type::function(params, HashMap::new_in(arena));
    let int_fn = program.insert_type(int_fn, arena);

    let mut fn_discriminant = Function::new("discriminant".to_string(), arena);
    let param = fn_discriminant.ident();
    fn_discriminant.params.push((param, ty_bool)); // TODO: Should be generic.
    let cont = fn_discriminant.ident();
    fn_discriminant.continuations.insert(cont, int_fn);
    let intrinsic = Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Discriminant,
        value: Box::new_in(Expr::Ident(param), arena),
        value_ty: ty_unknown,
    });
    let discriminant = fn_discriminant.ident();
    let declare = Expr::Declare(ExprDeclare {
        ident: discriminant,
        ty: ty_int,
        expr: Box::new_in(intrinsic, arena),
    });
    fn_discriminant.body.push(declare);
    let mut args = Vec::with_capacity_in(1, arena);
    args.push(Expr::Ident(discriminant));
    let cont_call = Expr::Call(ExprCall {
        callee: Box::new_in(Expr::Ident(cont), arena),
        callee_ty: ty_unknown,
        args,
    });
    fn_discriminant.body.push(cont_call);

    let fn_discriminant_ref = program.function();
    program
        .functions
        .insert(fn_discriminant_ref, fn_discriminant);

    let mut fn_discriminant_params = Vec::with_capacity_in(1, arena);
    fn_discriminant_params.push(&*ty_bool);
    let mut fn_discriminant_conts = HashMap::with_capacity_in(1, arena);
    fn_discriminant_conts.insert(cont, int_fn);
    let fn_discriminant_ty = Type::function(fn_discriminant_params, fn_discriminant_conts);
    let fn_discriminant_ty = program.insert_type(fn_discriminant_ty, arena);
    program
        .signatures
        .insert(fn_discriminant_ref, fn_discriminant_ty);

    StdLib {
        fn_termination: fn_termination_ref,
    }
}
