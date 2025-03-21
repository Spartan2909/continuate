use super::default_expr_call;
use super::default_expr_cont_application;
use super::Visit;

use crate::common::Literal;
use crate::mid_level_ir::Expr;
use crate::mid_level_ir::ExprCall;
use crate::mid_level_ir::ExprContApplication;

use std::mem;

use continuate_utils::collect_into;

pub(super) struct CombineCallApplication;

impl<'arena> Visit<'arena> for CombineCallApplication {
    fn always_enabled(&self) -> bool {
        true
    }

    fn expr_call(&self, expr: &mut ExprCall<'arena>) {
        default_expr_call(self, expr);

        if let Expr::ContApplication(callee) = &mut *expr.callee {
            let arena = *callee.continuations.allocator();
            let continuations = mem::replace(&mut callee.continuations, Vec::new_in(arena));
            let mut args = collect_into(
                Vec::new_in(arena),
                continuations
                    .into_iter()
                    .map(|(ident, expr)| (Some(ident), expr)),
            );
            args.extend(mem::replace(&mut expr.args, Vec::new_in(arena)));
            expr.args = args;
            let callee = mem::replace(&mut *callee.callee, Expr::Literal(Literal::Int(0)));
            expr.callee = Box::new_in(callee, arena);
        }
    }

    fn expr_cont_application(&self, expr: &mut ExprContApplication<'arena>) {
        default_expr_cont_application(self, expr);

        if let Expr::ContApplication(callee) = &mut *expr.callee {
            let arena = *callee.continuations.allocator();
            let mut continuations = mem::replace(&mut callee.continuations, Vec::new_in(arena));
            continuations.extend(mem::replace(&mut expr.continuations, Vec::new_in(arena)));
            expr.continuations = continuations;
            let callee = mem::replace(&mut *callee.callee, Expr::Literal(Literal::Int(0)));
            expr.callee = Box::new_in(callee, arena);
        }
    }
}
