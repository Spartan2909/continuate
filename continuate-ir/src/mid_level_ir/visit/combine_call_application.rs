use crate::{
    common::Literal,
    mid_level_ir::{
        Expr, ExprApplication, ExprCall, ExprLiteral,
        visit::{Visit, default_expr_application, default_expr_call},
    },
};

use std::mem;

const fn empty_expr() -> Expr {
    Expr::Literal(ExprLiteral {
        literal: Literal::Int(0),
    })
}

pub(super) struct CombineCallApplication;

impl Visit for CombineCallApplication {
    fn always_enabled(&self) -> bool {
        true
    }

    fn expr_call(&self, expr: &mut ExprCall) {
        default_expr_call(self, expr);

        if let Expr::Application(callee) = &mut *expr.callee {
            let mut positional = mem::take(&mut callee.positional);
            positional.extend(mem::take(&mut expr.positional));
            expr.positional = positional;
            let named = mem::take(&mut callee.named);
            expr.named.extend(named);
            let callee = mem::replace(&mut *callee.callee, empty_expr());
            *expr.callee = callee;
        }
    }

    fn expr_application(&self, expr: &mut ExprApplication) {
        default_expr_application(self, expr);

        if let Expr::Application(callee) = &mut *expr.callee {
            let mut positional = mem::take(&mut callee.positional);
            positional.extend(mem::take(&mut expr.positional));
            expr.positional = positional;
            let named = mem::take(&mut callee.named);
            expr.named.extend(named);
            let callee = mem::replace(&mut *callee.callee, empty_expr());
            *expr.callee = callee;
        }
    }
}
