use super::default_expr_call;
use super::default_expr_cont_application;
use super::Visit;

use crate::common::Literal;
use crate::mid_level_ir::Expr;
use crate::mid_level_ir::ExprCall;
use crate::mid_level_ir::ExprContApplication;

use std::mem;

pub(super) struct CombineCallApplication;

impl Visit for CombineCallApplication {
    fn always_enabled(&self) -> bool {
        true
    }

    fn expr_call(&self, expr: &mut ExprCall) {
        default_expr_call(self, expr);

        if let Expr::ContApplication(callee) = &mut *expr.callee {
            let continuations = mem::take(&mut callee.continuations);
            let mut args: Vec<_> = continuations
                .into_iter()
                .map(|(ident, expr)| (Some(ident), expr))
                .collect();
            args.extend(mem::take(&mut expr.args));
            expr.args = args;
            let callee = mem::replace(&mut *callee.callee, Expr::Literal(Literal::Int(0)));
            expr.callee = Box::new(callee);
        }
    }

    fn expr_cont_application(&self, expr: &mut ExprContApplication) {
        default_expr_cont_application(self, expr);

        if let Expr::ContApplication(callee) = &mut *expr.callee {
            let mut continuations = mem::take(&mut callee.continuations);
            continuations.extend(mem::take(&mut expr.continuations));
            expr.continuations = continuations;
            let callee = mem::replace(&mut *callee.callee, Expr::Literal(Literal::Int(0)));
            expr.callee = Box::new(callee);
        }
    }
}
