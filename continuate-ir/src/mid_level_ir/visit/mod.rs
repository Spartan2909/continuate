#![allow(clippy::needless_pass_by_ref_mut, reason = "forwards compatibility")]

mod combine_call_application;

use super::Block;
use super::Expr;
use super::ExprArray;
use super::ExprAssign;
use super::ExprBinary;
use super::ExprCall;
use super::ExprClosure;
use super::ExprConstructor;
use super::ExprContApplication;
use super::ExprFunction;
use super::ExprGet;
use super::ExprGoto;
use super::ExprIdent;
use super::ExprIntrinsic;
use super::ExprLiteral;
use super::ExprSet;
use super::ExprSwitch;
use super::ExprTuple;
use super::ExprUnary;
use super::Function;
use super::Program;

trait Visit {
    fn always_enabled(&self) -> bool {
        false
    }

    fn expr_literal(&self, expr: &mut ExprLiteral) {
        default_expr_literal(self, expr);
    }

    fn expr_ident(&self, expr: &mut ExprIdent) {
        default_expr_ident(self, expr);
    }

    fn expr_function(&self, expr: &mut ExprFunction) {
        default_expr_function(self, expr);
    }

    fn expr_tuple(&self, expr: &mut ExprTuple) {
        default_expr_tuple(self, expr);
    }

    fn expr_constructor(&self, expr: &mut ExprConstructor) {
        default_expr_constructor(self, expr);
    }

    fn expr_array(&self, expr: &mut ExprArray) {
        default_expr_array(self, expr);
    }

    fn expr_get(&self, expr: &mut ExprGet) {
        default_expr_get(self, expr);
    }

    fn expr_set(&self, expr: &mut ExprSet) {
        default_expr_set(self, expr);
    }

    fn expr_call(&self, expr: &mut ExprCall) {
        default_expr_call(self, expr);
    }

    fn expr_cont_application(&self, expr: &mut ExprContApplication) {
        default_expr_cont_application(self, expr);
    }

    fn expr_unary(&self, expr: &mut ExprUnary) {
        default_expr_unary(self, expr);
    }

    fn expr_binary(&self, expr: &mut ExprBinary) {
        default_expr_binary(self, expr);
    }

    fn expr_assign(&self, expr: &mut ExprAssign) {
        default_expr_assign(self, expr);
    }

    fn expr_switch(&self, expr: &mut ExprSwitch) {
        default_expr_switch(self, expr);
    }

    fn expr_goto(&self, expr: &mut ExprGoto) {
        default_expr_goto(self, expr);
    }

    fn expr_closure(&self, expr: &mut ExprClosure) {
        default_expr_closure(self, expr);
    }

    fn expr_intrinsic(&self, expr: &mut ExprIntrinsic) {
        default_expr_intrinsic(self, expr);
    }

    fn expr(&self, expr: &mut Expr) {
        default_expr(self, expr);
    }

    fn block(&self, block: &mut Block) {
        default_block(self, block);
    }

    fn function(&self, function: &mut Function) {
        default_function(self, function);
    }

    fn visit(&self, program: &mut Program) {
        default_visit(self, program);
    }
}

fn default_expr_literal<V: Visit + ?Sized>(_: &V, expr: &mut ExprLiteral) {
    let ExprLiteral { literal: _ } = expr;
}

fn default_expr_ident<V: Visit + ?Sized>(_: &V, expr: &mut ExprIdent) {
    let ExprIdent { ident: _ } = expr;
}

fn default_expr_function<V: Visit + ?Sized>(_: &V, expr: &mut ExprFunction) {
    let ExprFunction { function: _ } = expr;
}

fn default_expr_tuple<V: Visit + ?Sized>(v: &V, expr: &mut ExprTuple) {
    let ExprTuple { ty: _, values } = expr;
    for expr in values {
        v.expr(expr);
    }
}

fn default_expr_constructor<V: Visit + ?Sized>(v: &V, expr: &mut ExprConstructor) {
    let ExprConstructor {
        ty: _,
        index: _,
        fields,
    } = expr;
    for expr in fields {
        v.expr(expr);
    }
}

fn default_expr_array<V: Visit + ?Sized>(v: &V, expr: &mut ExprArray) {
    let ExprArray {
        ty: _,
        values,
        value_ty: _,
    } = expr;
    for expr in values {
        v.expr(expr);
    }
}

fn default_expr_get<V: Visit + ?Sized>(v: &V, expr: &mut ExprGet) {
    let ExprGet {
        object,
        object_ty: _,
        object_variant: _,
        field: _,
    } = expr;
    v.expr(object);
}

fn default_expr_set<V: Visit + ?Sized>(v: &V, expr: &mut ExprSet) {
    let ExprSet {
        object,
        object_ty: _,
        object_variant: _,
        field: _,
        value,
    } = expr;
    v.expr(object);
    v.expr(value);
}

fn default_expr_call<V: Visit + ?Sized>(v: &V, expr: &mut ExprCall) {
    let ExprCall {
        callee,
        callee_ty: _,
        args,
    } = expr;
    v.expr(callee);
    for (_, expr) in args {
        v.expr(expr);
    }
}

fn default_expr_cont_application<V: Visit + ?Sized>(v: &V, expr: &mut ExprContApplication) {
    let ExprContApplication {
        callee,
        callee_ty: _,
        continuations,
        result_ty: _,
        storage_ty: _,
    } = expr;
    v.expr(callee);
    for (_, expr) in continuations {
        v.expr(expr);
    }
}

fn default_expr_unary<V: Visit + ?Sized>(v: &V, expr: &mut ExprUnary) {
    let ExprUnary {
        operator: _,
        operand,
        operand_ty: _,
    } = expr;
    v.expr(operand);
}

fn default_expr_binary<V: Visit + ?Sized>(v: &V, expr: &mut ExprBinary) {
    let ExprBinary {
        left,
        left_ty: _,
        operator: _,
        right,
        right_ty: _,
    } = expr;
    v.expr(left);
    v.expr(right);
}

fn default_expr_assign<V: Visit + ?Sized>(v: &V, expr: &mut ExprAssign) {
    let ExprAssign { ident: _, expr } = expr;
    v.expr(expr);
}

fn default_expr_switch<V: Visit + ?Sized>(v: &V, expr: &mut ExprSwitch) {
    let ExprSwitch {
        scrutinee,
        arms: _,
        otherwise: _,
    } = expr;
    v.expr(scrutinee);
}

fn default_expr_goto<V: Visit + ?Sized>(_: &V, expr: &mut ExprGoto) {
    let ExprGoto { block: _ } = expr;
}

const fn default_expr_closure<V: Visit + ?Sized>(_v: &V, expr: &mut ExprClosure) {
    let ExprClosure {
        func_ref: _,
        captures: _,
        storage_ty: _,
    } = expr;
}

fn default_expr_intrinsic<V: Visit + ?Sized>(v: &V, expr: &mut ExprIntrinsic) {
    let ExprIntrinsic {
        intrinsic: _,
        values,
    } = expr;
    for (expr, _) in values {
        v.expr(expr);
    }
}

fn default_expr<V: Visit + ?Sized>(v: &V, expr: &mut Expr) {
    match expr {
        Expr::Literal(expr) => v.expr_literal(expr),
        Expr::Ident(expr) => v.expr_ident(expr),
        Expr::Function(expr) => v.expr_function(expr),
        Expr::Tuple(expr) => v.expr_tuple(expr),
        Expr::Constructor(expr) => v.expr_constructor(expr),
        Expr::Array(expr) => v.expr_array(expr),
        Expr::Get(expr) => v.expr_get(expr),
        Expr::Set(expr) => v.expr_set(expr),
        Expr::Call(expr) => v.expr_call(expr),
        Expr::ContApplication(expr) => v.expr_cont_application(expr),
        Expr::Unary(expr) => v.expr_unary(expr),
        Expr::Binary(expr) => v.expr_binary(expr),
        Expr::Assign(expr) => v.expr_assign(expr),
        Expr::Switch(expr) => v.expr_switch(expr),
        Expr::Goto(expr) => v.expr_goto(expr),
        Expr::Closure(expr) => v.expr_closure(expr),
        Expr::Intrinsic(expr) => v.expr_intrinsic(expr),
    }
}

fn default_block<V: Visit + ?Sized>(v: &V, block: &mut Block) {
    for expr in &mut block.exprs {
        v.expr(expr);
    }
}

fn default_function<V: Visit + ?Sized>(v: &V, function: &mut Function) {
    for block in function.blocks.values_mut() {
        v.block(block);
    }
}

fn default_visit<V: Visit + ?Sized>(v: &V, program: &mut Program) {
    for function in &mut program.functions.values_mut() {
        v.function(function);
    }
}

const PASSES: &[&dyn Visit] = &[&combine_call_application::CombineCallApplication];

pub fn run_passes(program: &mut Program, optimisations: bool) {
    for pass in PASSES {
        if optimisations || pass.always_enabled() {
            pass.visit(program);
        }
    }
}
