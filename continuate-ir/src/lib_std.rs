use crate::{
    common::{FuncRef, Ident, Intrinsic},
    high_level_ir::{
        Expr, ExprCall, ExprDeclare, ExprIdent, ExprIntrinsic, Function, Program, Type,
    },
};

use std::{collections::HashMap, sync::Arc};

use continuate_error::Span;

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct StdLib {
    pub fn_termination: FuncRef,
}

pub(crate) fn standard_library(program: &mut Program<()>) -> StdLib {
    let ty_bool = program.insert_type(Type::Bool);

    let ty_int = program.insert_type(Type::Int);

    let mut fn_termination = Function::new("termination".to_string());
    let param = Ident::new(Span::dummy());
    fn_termination.positional.push((param, Arc::clone(&ty_int)));
    let param = ExprIdent { ident: param };
    fn_termination.body.push(Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Terminate,
        values: vec![Expr::Ident(param)],
    }));

    let fn_termination_ref = FuncRef::new();
    program.functions.insert(fn_termination_ref, fn_termination);

    let fn_termination_ty = Type::function(vec![Arc::clone(&ty_int)], HashMap::new());
    let fn_termination_ty = program.insert_type(fn_termination_ty);
    program
        .signatures
        .insert(fn_termination_ref, fn_termination_ty);

    let int_fn = Type::function(vec![Arc::clone(&ty_int)], HashMap::new());
    let int_fn = program.insert_type(int_fn);

    let mut fn_discriminant = Function::new("discriminant".to_string());
    let param = Ident::new(Span::dummy());
    fn_discriminant
        .positional
        .push((param, Arc::clone(&ty_bool))); // TODO: Should be generic.
    let param = ExprIdent { ident: param };
    let cont = Ident::new(Span::dummy());
    fn_discriminant.named.insert(cont, Arc::clone(&int_fn));
    let cont_expr = ExprIdent { ident: cont };
    let intrinsic = Expr::Intrinsic(ExprIntrinsic {
        intrinsic: Intrinsic::Discriminant,
        values: vec![Expr::Ident(param)],
    });
    let discriminant = Ident::new(Span::dummy());
    let declare = Expr::Declare(ExprDeclare {
        ident: discriminant,
        ty: ty_int,
        expr: Box::new(intrinsic),
    });
    let discriminant = ExprIdent {
        ident: discriminant,
    };
    fn_discriminant.body.push(declare);
    let cont_call = Expr::Call(ExprCall {
        callee: Box::new(Expr::Ident(cont_expr)),
        positional: vec![Expr::Ident(discriminant)],
        named: vec![],
    });
    fn_discriminant.body.push(cont_call);

    let fn_discriminant_ref = FuncRef::new();
    program
        .functions
        .insert(fn_discriminant_ref, fn_discriminant);

    let mut fn_discriminant_conts = HashMap::with_capacity(1);
    fn_discriminant_conts.insert(cont, int_fn);
    let fn_discriminant_ty = Type::function(vec![Arc::clone(&ty_bool)], fn_discriminant_conts);
    let fn_discriminant_ty = program.insert_type(fn_discriminant_ty);
    program
        .signatures
        .insert(fn_discriminant_ref, fn_discriminant_ty);

    StdLib {
        fn_termination: fn_termination_ref,
    }
}
