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

fn main() -> anyhow::Result<()> {
    continuate_rt::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

    let args = Args::parse();

    let input = std::fs::read_to_string(&args.source)?;

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

    let error = lex_errors
        .into_iter()
        .chain(parse_errors)
        .reduce(Error::combine);
    if let Some(error) = error {
        error.eprint(&source_cache)?;
        return Err(anyhow::anyhow!("failed due to above error"));
    }

    let ast = ast.unwrap();

    let name_map = continuate_frontend::resolve_names(&ast);

    let program = continuate_ir::high_level_ir::lower(&ast, name_map, program_name);

    let program = match typeck(&program) {
        Ok(x) => x,
        Err(e) => {
            e.eprint(&source_cache)?;
            return Err(anyhow::anyhow!("failed due to above error"));
        }
    };

    let mut mir_program = mid_level_ir::lower(&program);

    drop(program);

    continuate_ir::mid_level_ir::run_passes(&mut mir_program, true);

    let res = continuate_backend::jit::compile(mir_program).run();
    println!("out: {res}");

    Ok(())
}
