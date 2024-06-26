#![feature(allocator_api)]

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

use tracing_subscriber::filter::LevelFilter;

#[cfg(target_family = "unix")]
fn link_command() -> process::Command {
    let mut command = process::Command::new("cc");
    command.args([
        "./out/object.o",
        option_env!("CONTINUATE_RT_PATH").unwrap_or("./target/debug/libcontinuate_rt.a"),
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
        "ucrt.lib",
        "Ws2_32.lib",
        "Synchronization.lib",
        "Userenv.lib",
        "ntdll.lib",
        "Advapi32.lib",
        "/out:./out/result.exe",
    ]);
    command
}

fn main() {
    continuate_common::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

    let hir_arena = Arena::new();
    let mut program = Program::new("test".to_string(), &hir_arena);

    let std_lib = program.lib_std();
    let ty_int = std_lib.ty_int;

    let int_fn = Type::function(vec![ty_int], HashMap::new());
    let int_fn_ref = program.insert_type(int_fn, &hir_arena);

    let mut sum_fn = Function::new("test::sum".to_string(), &hir_arena);
    let cont = sum_fn.ident();
    let param_1 = sum_fn.ident();
    let param_2 = sum_fn.ident();
    sum_fn.params.extend([(param_1, ty_int), (param_2, ty_int)]);
    sum_fn.continuations.insert(cont, int_fn_ref);

    let l = hir_arena.allocate(Expr::Ident(param_1));
    let r = hir_arena.allocate(Expr::Ident(param_2));
    let sum = Expr::Binary(l, BinaryOp::Add, r);

    let cont_ref = hir_arena.allocate(Expr::Ident(cont));
    let mut args = Vec::with_capacity_in(1, &hir_arena);
    args.push(sum);
    sum_fn.body.push(Expr::Call(cont_ref, args));

    let sum_fn_ref = program.function();
    program.functions.insert(sum_fn_ref, sum_fn);

    let sum_fn_ty = Type::function(
        vec![ty_int, ty_int],
        iter::once((cont, int_fn_ref)).collect(),
    );
    let sum_fn_ty = program.insert_type(sum_fn_ty, &hir_arena);

    program.signatures.insert(sum_fn_ref, sum_fn_ty);

    let mut main_fn = Function::new("test::main".to_string(), &hir_arena);
    let termination_cont = main_fn.ident();
    main_fn.continuations.insert(termination_cont, int_fn_ref);

    let string = Expr::Literal(Literal::String("hello".to_string()));
    let assign_string = Expr::Declare {
        ident: main_fn.ident(),
        ty: program.lib_std().ty_string,
        expr: hir_arena.allocate(string),
    };
    main_fn.body.push(assign_string);

    let three = Expr::Literal(Literal::Int(3));
    let seven = Expr::Literal(Literal::Int(7));

    let callee = hir_arena.allocate(Expr::Function(sum_fn_ref));
    let cont_ref = Expr::Ident(termination_cont);
    let application = hir_arena.allocate(Expr::ContApplication(
        callee,
        iter::once((cont, cont_ref)).collect(),
    ));
    let mut args = Vec::with_capacity_in(2, &hir_arena);
    args.extend([three, seven]);
    main_fn.body.push(Expr::Call(application, args));

    let main_fn_ref = program.entry_point();
    program.functions.insert(main_fn_ref, main_fn);

    let mir_arena = Arena::new();

    let mir_program = mid_level_ir::lower(&program, &mir_arena).unwrap();

    drop(program);
    drop(hir_arena);

    let object = continuate_backend::compile(mir_program, true);

    drop(mir_arena);

    let object = object.emit().unwrap();
    fs::create_dir_all("./out").unwrap();
    fs::write("./out/object.o", object).unwrap();

    link_command()
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .output()
        .unwrap();

    process::Command::new("./out/result")
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .output()
        .unwrap();
}
