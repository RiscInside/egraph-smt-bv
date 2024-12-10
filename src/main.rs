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

#[derive(Parser)]
struct Args {
    input: std::path::PathBuf,
    #[arg(short, long)]
    egglog_output: Vec<std::path::PathBuf>,
    #[arg(short, long)]
    markdown_output: Vec<std::path::PathBuf>,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let mut ctx: Context = context::Context::new();

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

    Ok(())
}
