use std::path::PathBuf;

use clap::Parser;

use continuate_error::Error;
use continuate_ir::high_level_ir::typeck;
use continuate_ir::mid_level_ir;

use tracing_subscriber::filter::LevelFilter;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    source: PathBuf,
}

fn fold_errors(errors: impl IntoIterator<Item = Error>) -> Option<Error> {
    errors.into_iter().reduce(|acc, err| acc.combine(err))
}

fn main() {
    continuate_rt::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

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

    let program = continuate_ir::high_level_ir::lower(&ast, name_map, program_name);

    let program = typeck(&program).unwrap();

    let mut mir_program = mid_level_ir::lower(&program);

    drop(program);

    continuate_ir::mid_level_ir::run_passes(&mut mir_program, true);

    continuate_backend::jit_compile(mir_program).run();
}
