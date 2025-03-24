use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::high_level_ir::Expr;
use crate::high_level_ir::ExprCall;
use crate::high_level_ir::ExprDeclare;
use crate::high_level_ir::ExprIntrinsic;
use crate::high_level_ir::Function;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;

use std::collections::HashMap;
use std::rc::Rc;

use continuate_error::Span;

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct StdLib {
    pub fn_termination: FuncRef,
}

pub(crate) fn standard_library(program: &mut Program) -> StdLib {
    let ty_bool = program.insert_type(Type::Bool);

    let ty_int = program.insert_type(Type::Int);

    let ty_unknown = program.insert_type(Type::Unknown);

    let mut fn_termination = Function::new("termination".to_string());
    let param = Ident::new(Span::dummy());
    fn_termination.params.push((param, Rc::clone(&ty_int)));
    fn_termination.body.push(Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Terminate,
        value: Box::new(Expr::Ident(param)),
        value_ty: Rc::clone(&ty_unknown),
    }));

    let fn_termination_ref = FuncRef::new();
    program.functions.insert(fn_termination_ref, fn_termination);

    let fn_termination_ty = Type::function(vec![Rc::clone(&ty_int)], HashMap::new());
    let fn_termination_ty = program.insert_type(fn_termination_ty);
    program
        .signatures
        .insert(fn_termination_ref, fn_termination_ty);

    let int_fn = Type::function(vec![Rc::clone(&ty_int)], HashMap::new());
    let int_fn = program.insert_type(int_fn);

    let mut fn_discriminant = Function::new("discriminant".to_string());
    let param = Ident::new(Span::dummy());
    fn_discriminant.params.push((param, Rc::clone(&ty_bool))); // TODO: Should be generic.
    let cont = Ident::new(Span::dummy());
    fn_discriminant
        .continuations
        .insert(cont, Rc::clone(&int_fn));
    let intrinsic = Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Discriminant,
        value: Box::new(Expr::Ident(param)),
        value_ty: Rc::clone(&ty_unknown),
    });
    let discriminant = Ident::new(Span::dummy());
    let declare = Expr::Declare(ExprDeclare {
        ident: discriminant,
        ty: ty_int,
        expr: Box::new(intrinsic),
    });
    fn_discriminant.body.push(declare);
    let cont_call = Expr::Call(ExprCall {
        callee: Box::new(Expr::Ident(cont)),
        callee_ty: ty_unknown,
        args: vec![Expr::Ident(discriminant)],
    });
    fn_discriminant.body.push(cont_call);

    let fn_discriminant_ref = FuncRef::new();
    program
        .functions
        .insert(fn_discriminant_ref, fn_discriminant);

    let mut fn_discriminant_conts = HashMap::with_capacity(1);
    fn_discriminant_conts.insert(cont, int_fn);
    let fn_discriminant_ty = Type::function(vec![Rc::clone(&ty_bool)], fn_discriminant_conts);
    let fn_discriminant_ty = program.insert_type(fn_discriminant_ty);
    program
        .signatures
        .insert(fn_discriminant_ref, fn_discriminant_ty);

    StdLib {
        fn_termination: fn_termination_ref,
    }
}
