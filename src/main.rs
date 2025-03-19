#![feature(allocator_api)]

use std::fs;
use std::path::PathBuf;
use std::process;
use std::process::Stdio;

use bumpalo::Bump;

use clap::Parser;

use continuate_error::Error;
use continuate_ir::high_level_ir::typeck;
use continuate_ir::mid_level_ir;

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
        "libcmt.lib",
        "Ws2_32.lib",
        "Synchronization.lib",
        "Userenv.lib",
        "ntdll.lib",
        "Advapi32.lib",
        "/out:./out/result.exe",
    ]);
    command
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    source: PathBuf,
}

fn fold_errors(errors: impl IntoIterator<Item = Error>) -> Option<Error> {
    errors.into_iter().fold(None, |acc, err| {
        if let Some(acc) = acc {
            Some(acc.combine(err))
        } else {
            Some(err)
        }
    })
}

fn main() {
    continuate_common::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

    let args = Args::parse();

    let input = std::fs::read_to_string(&args.source).unwrap();

    let program_name = args
        .source
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .into_owned();

    let mut source_cache = continuate_error::SourceCache::new();
    let source_id = source_cache.insert_source(&*input, args.source);

    let (tokens, lex_errors) = continuate_frontend::lex(&input, source_id);

    let (ast, parse_errors) =
        continuate_frontend::parse(&tokens, source_cache.eof(source_id).unwrap(), &program_name)
            .into_output_errors();

    let error = fold_errors(lex_errors.into_iter().chain(parse_errors));
    if let Some(error) = error {
        error.eprint(&source_cache).unwrap();
        panic!("failed due to above error");
    }

    let ast = ast.unwrap();

    let name_map = continuate_frontend::resolve_names(&ast);

    let hir_arena = Bump::new();
    let mut program = continuate_ir::high_level_ir::lower(&ast, name_map, program_name, &hir_arena);

    typeck(&hir_arena, &mut program).unwrap();

    let mir_arena = Bump::new();

    let mut mir_program = mid_level_ir::lower(&program, &mir_arena);

    drop(program);
    drop(hir_arena);

    continuate_ir::mid_level_ir::run_passes(&mut mir_program, true);

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
