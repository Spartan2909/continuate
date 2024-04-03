use std::iter;

use continuate::high_level_ir::BinaryOp;
use continuate::high_level_ir::Block;
use continuate::high_level_ir::Expr;
use continuate::high_level_ir::Function;
use continuate::high_level_ir::Literal;
use continuate::high_level_ir::Program;
use continuate::high_level_ir::Type;
use continuate::ir_interpreter;
use continuate::low_level_ir;

use continuate_arena::with_arena;

fn main() {
    with_arena(|lir_arena| {
        let program = with_arena(|hir_arena| {
            let mut program = Program::new(hir_arena);

            let std_lib = program.lib_std();

            let int_fn = hir_arena.allocate(Type::Function {
                params: vec![std_lib.ty_int],
                continuations: vec![],
            });

            let sum_fn = hir_arena.allocate(Function::new());
            let cont = sum_fn.ident();
            sum_fn.continuations.insert(cont, int_fn);

            let l = hir_arena.allocate(Expr::Literal(Literal::Int(3)));
            let r = hir_arena.allocate(Expr::Literal(Literal::Int(7)));
            let sum = hir_arena.allocate(Expr::Binary(l, BinaryOp::Add, r));

            let cont_ref = hir_arena.allocate(Expr::Ident(cont));
            let cont_call = hir_arena.allocate(Expr::Call(cont_ref, vec![sum]));

            let block = Block { expr: cont_call };
            let block_id = sum_fn.entry_point();
            sum_fn.blocks.insert(block_id, block);

            let sum_fn_ref = program.function();
            program.functions.insert(sum_fn_ref, sum_fn);

            let main_fn = hir_arena.allocate(Function::new());
            let termination_cont = main_fn.ident();
            main_fn.continuations.insert(termination_cont, int_fn);

            let callee = hir_arena.allocate(Expr::Function(sum_fn_ref));
            let cont_ref = hir_arena.allocate(Expr::Ident(cont));
            let application = hir_arena.allocate(Expr::ContApplication(
                callee,
                iter::once((cont, &*cont_ref)).collect(),
            ));
            let call = hir_arena.allocate(Expr::Call(application, vec![]));

            let block = Block { expr: call };
            let block_id = main_fn.entry_point();
            main_fn.blocks.insert(block_id, block);

            let main_fn_ref = program.entry_point();
            program.functions.insert(main_fn_ref, main_fn);

            low_level_ir::lower(program, lir_arena)
        });

        dbg!(ir_interpreter::run(program, lir_arena));
    });
}
