use anyhow::bail;
use clap::Parser;
use egraph_smt_bv::Context;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser)]
struct Args {
    input: std::path::PathBuf,
    #[arg(short, long)]
    egglog_output: Vec<std::path::PathBuf>,
    #[arg(short, long)]
    markdown_output: Vec<std::path::PathBuf>,
    #[arg(long)]
    json: Option<std::path::PathBuf>,
    #[arg(long)]
    html: Option<std::path::PathBuf>,
    #[arg(long)]
    history: Option<std::path::PathBuf>,
    #[arg(long, short)]
    timeout: Option<u64>,
    #[arg(long)]
    keep_functions: bool,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let mut ctx: Context = Context::new();

    ctx.print_results_to_stdout();

    if args.keep_functions {
        ctx.keep_functions();
    }

    if args.history.is_some() {
        ctx.enable_history_collection();
    }

    if let Some(ms) = args.timeout {
        ctx.add_timeout(std::time::Duration::from_millis(ms));
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
            Ok(cmd) => ctx.run_smt2lib_command(&cmd)?,
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

    if let Some(json_egraph_path) = args.json {
        ctx.dump_json(&json_egraph_path)?;
    }

    if let Some(html_egraph_path) = args.html {
        ctx.dump_html(&html_egraph_path)?;
    }

    if let Some(history) = args.history {
        ctx.dump_html_history(&history)?;
    }

    Ok(())
}
