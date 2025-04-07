pub(crate) mod check_sat;
pub(crate) mod commands;
pub(crate) mod context;
pub(crate) mod log;
pub(crate) mod prelude;
pub(crate) mod smt2lib;
pub(crate) mod statistics;

use anyhow::bail;
use clap::Parser;
use context::Context;
use egglog::SerializeConfig;

#[derive(Parser)]
struct Args {
    input: std::path::PathBuf,
    #[arg(short, long)]
    egglog_output: Vec<std::path::PathBuf>,
    #[arg(short, long)]
    markdown_output: Vec<std::path::PathBuf>,
    #[arg(short, long)]
    json_egraph_path: Option<std::path::PathBuf>,
    #[arg(short, long)]
    dot_egraph_path: Option<std::path::PathBuf>,
    #[arg(short, long)]
    svg_egraph_path: Option<std::path::PathBuf>,
    #[arg(long)]
    keep_functions: bool,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let mut ctx: Context = context::Context::new();

    if args.keep_functions {
        ctx.keep_functions();
    }

    // Add egglog and markdown sinks
    for out in args.egglog_output.iter() {
        ctx.add_egglog_sink(out)?;
    }
    for out in args.markdown_output.iter() {
        ctx.add_markdown_sink(out)?;
    }

    ctx.run_prelude()?;

    // Read SMT2 problem description and generate matching egglog definitions
    let file = std::fs::File::open(&args.input)?;
    let reader = std::io::BufReader::new(file);
    let stream = smt2parser::CommandStream::new(
        reader,
        smt2parser::concrete::SyntaxBuilder,
        Some(format!("{}", args.input.display())),
    );

    for command in stream {
        match command {
            Ok(cmd) => ctx.handle_smt2lib_command(&cmd)?,
            Err(
                smt2parser::Error::SyntaxError(pos, msg)
                | smt2parser::Error::ParsingError(pos, msg),
            ) => {
                bail!(
                    "(error \"parse error at {}:{}:{} - {msg}\")",
                    pos.path.unwrap(),
                    pos.line,
                    pos.column
                );
            }
        }
    }

    let serialized = ctx.egraph.serialize(SerializeConfig::default());

    if let Some(json_egraph_path) = args.json_egraph_path {
        serialized.to_json_file(json_egraph_path)?;
    }

    if let Some(dot_egraph_path) = args.dot_egraph_path {
        serialized.to_dot_file(dot_egraph_path)?;
    }

    if let Some(svg_egraph_path) = args.svg_egraph_path {
        serialized.to_svg_file(svg_egraph_path)?;
    }

    Ok(())
}
