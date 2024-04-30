use std::collections::HashMap;
use std::fs;
use std::iter;
use std::process;
use std::process::Stdio;

use continuate_ir::common::BinaryOp;
use continuate_ir::common::Literal;
use continuate_ir::high_level_ir::Expr;
use continuate_ir::high_level_ir::Function;
use continuate_ir::high_level_ir::Program;
use continuate_ir::high_level_ir::Type;
use continuate_ir::mid_level_ir;

use continuate_arena::Arena;

use log::LevelFilter;

use simple_logger::SimpleLogger;

#[cfg(target_family = "unix")]
fn link_command() -> process::Command {
    let mut command = process::Command::new("cc");
    command.args([
        "./out/object.o",
        "./target/debug/libcontinuate_rt.a",
        "-o",
        "./out/result",
    ]);
    command
}

#[cfg(target_family = "windows")]
fn link_command() -> process::Command {
    let mut command = process::Command::new("lld-link");
    command.args([
        "./target/debug/continuate_rt.lib",
        "./out/object.o",
        "libcmt.lib",
        "Ws2_32.lib",
        "Synchronization.lib",
        "Userenv.lib",
        "ntdll.lib",
        "/out:./out/result.exe",
    ]);
    command
}

fn main() {
    SimpleLogger::new()
        .with_level(LevelFilter::Info)
        .with_colors(true)
        .without_timestamps()
        .init()
        .unwrap();

    let lir_arena = Arena::new();

    let program = {
        let hir_arena = Arena::new();
        let mut program = Program::new("test".to_string(), &hir_arena);

        let std_lib = program.lib_std();
        let ty_int = std_lib.ty_int;

        let int_fn = Type::function(vec![ty_int], HashMap::new());
        let int_fn_ref = program.insert_type(int_fn, &hir_arena);

        let sum_fn = hir_arena.allocate(Function::new("test::sum".to_string()));
        let cont = sum_fn.ident();
        let param_1 = sum_fn.ident();
        let param_2 = sum_fn.ident();
        sum_fn.params.extend([(param_1, ty_int), (param_2, ty_int)]);
        sum_fn.continuations.insert(cont, int_fn_ref);

        let l = hir_arena.allocate(Expr::Ident(param_1));
        let r = hir_arena.allocate(Expr::Ident(param_2));
        let sum = hir_arena.allocate(Expr::Binary(l, BinaryOp::Add, r));

        let cont_ref = hir_arena.allocate(Expr::Ident(cont));
        let cont_call = hir_arena.allocate(Expr::Call(cont_ref, vec![sum]));

        sum_fn.body.push(cont_call);

        let sum_fn_ref = program.function();
        program.functions.insert(sum_fn_ref, sum_fn);

        let sum_fn_ty = Type::function(
            vec![ty_int, ty_int],
            iter::once((cont, int_fn_ref)).collect(),
        );
        let sum_fn_ty = program.insert_type(sum_fn_ty, &hir_arena);

        program.signatures.insert(sum_fn_ref, sum_fn_ty);

        let main_fn = hir_arena.allocate(Function::new("test::main".to_string()));
        let termination_cont = main_fn.ident();
        main_fn.continuations.insert(termination_cont, int_fn_ref);

        let three = hir_arena.allocate(Expr::Literal(Literal::Int(3)));
        let seven = hir_arena.allocate(Expr::Literal(Literal::Int(7)));

        let callee = hir_arena.allocate(Expr::Function(sum_fn_ref));
        let cont_ref = hir_arena.allocate(Expr::Ident(termination_cont));
        let application = hir_arena.allocate(Expr::ContApplication(
            callee,
            iter::once((cont, &*cont_ref)).collect(),
        ));
        let call = hir_arena.allocate(Expr::Call(application, vec![three, seven]));

        main_fn.body.push(call);

        let main_fn_ref = program.entry_point();
        program.functions.insert(main_fn_ref, main_fn);

        mid_level_ir::lower(&program, &lir_arena)
    };

    let object = continuate_backend::compile(program.unwrap(), true);
    let object = object.emit().unwrap();
    fs::create_dir_all("./out").unwrap();
    fs::write("./out/object.o", object).unwrap();

    link_command()
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .output()
        .unwrap();
}
