use std::collections::HashMap;
use std::iter;

use continuate_ir::common::BinaryOp;
use continuate_ir::common::Literal;
use continuate_ir::high_level_ir::Expr;
use continuate_ir::high_level_ir::Function;
use continuate_ir::high_level_ir::Program;
use continuate_ir::high_level_ir::Type;
use continuate_ir::ir_interpreter;
use continuate_ir::low_level_ir;

use continuate_arena::Arena;

fn main() {
    let lir_arena = Arena::new();

    let program = {
        let hir_arena = Arena::new();
        let mut program = Program::new(&hir_arena);

        let std_lib = program.lib_std();

        let int_fn = Type::function(vec![std_lib.ty_int], HashMap::new());
        let int_fn_ref = program.insert_type(int_fn, &hir_arena);

        let sum_fn = hir_arena.allocate(Function::new("sum".to_string()));
        let cont = sum_fn.ident();
        sum_fn.continuations.insert(cont, int_fn_ref);

        let l = hir_arena.allocate(Expr::Literal(Literal::Int(3)));
        let r = hir_arena.allocate(Expr::Literal(Literal::Int(7)));
        let sum = hir_arena.allocate(Expr::Binary(l, BinaryOp::Add, r));

        let cont_ref = hir_arena.allocate(Expr::Ident(cont));
        let cont_call = hir_arena.allocate(Expr::Call(cont_ref, vec![sum]));

        sum_fn.body.push(cont_call);

        let sum_fn_ref = program.function();
        program.functions.insert(sum_fn_ref, sum_fn);

        let sum_fn_ty = Type::function(vec![], iter::once((cont, int_fn_ref)).collect());
        let sum_fn_ty = program.insert_type(sum_fn_ty, &hir_arena);

        program.signatures.insert(sum_fn_ref, sum_fn_ty);

        let main_fn = hir_arena.allocate(Function::new("main".to_string()));
        let termination_cont = main_fn.ident();
        main_fn.continuations.insert(termination_cont, int_fn_ref);

        let callee = hir_arena.allocate(Expr::Function(sum_fn_ref));
        let cont_ref = hir_arena.allocate(Expr::Ident(termination_cont));
        let application = hir_arena.allocate(Expr::ContApplication(
            callee,
            iter::once((cont, &*cont_ref)).collect(),
        ));
        let call = hir_arena.allocate(Expr::Call(application, vec![]));

        main_fn.body.push(call);

        let main_fn_ref = program.entry_point();
        program.functions.insert(main_fn_ref, main_fn);

        low_level_ir::lower(&program, &lir_arena)
    };

    dbg!(ir_interpreter::run(program.unwrap(), &lir_arena));
}
