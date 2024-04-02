use std::iter;

use continuate::ir_interpreter;
use continuate::low_level_ir::BinaryOp;
use continuate::low_level_ir::Block;
use continuate::low_level_ir::Expr;
use continuate::low_level_ir::Function;
use continuate::low_level_ir::Literal;
use continuate::low_level_ir::Program;
use continuate::low_level_ir::Type;

use continuate_arena::Arena;

fn main() {
    let arena = Arena::new();
    let mut program = Program::new();

    let std_lib = ir_interpreter::standard_library(&arena, &mut program);

    let int_fn = arena.allocate(Type::Function {
        params: vec![std_lib.ty_int],
        continuations: vec![],
    });

    let sum_fn = arena.allocate(Function::new());
    let cont = sum_fn.ident();
    sum_fn.continuations.insert(cont, int_fn);

    let l = arena.allocate(Expr::Literal(Literal::Int(3)));
    let r = arena.allocate(Expr::Literal(Literal::Int(7)));
    let sum = arena.allocate(Expr::Binary(l, BinaryOp::Add, r));

    let cont_ref = arena.allocate(Expr::Ident(cont));
    let cont_call = arena.allocate(Expr::Call(cont_ref, vec![sum]));

    let block = Block { expr: cont_call };
    let block_id = sum_fn.entry_point();
    sum_fn.blocks.insert(block_id, block);

    let sum_fn_ref = program.function();
    program.functions.insert(sum_fn_ref, sum_fn);

    let main_fn = arena.allocate(Function::new());
    let termination_cont = main_fn.ident();
    main_fn.continuations.insert(termination_cont, int_fn);

    let callee = arena.allocate(Expr::Function(sum_fn_ref));
    let cont_ref = arena.allocate(Expr::Ident(cont));
    let application = arena.allocate(Expr::ContApplication(
        callee,
        iter::once((cont, &*cont_ref)).collect(),
    ));
    let call = arena.allocate(Expr::Call(application, vec![]));

    let block = Block { expr: call };
    let block_id = main_fn.entry_point();
    main_fn.blocks.insert(block_id, block);

    let main_fn_ref = program.entry_point();
    program.functions.insert(main_fn_ref, main_fn);

    dbg!(ir_interpreter::run(
        program,
        termination_cont,
        std_lib.fn_termination,
        &arena
    ));
}
