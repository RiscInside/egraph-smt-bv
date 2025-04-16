/// Context keeps track of all the solver's state. Namely, this includes
///
/// - EGraph with all the terms
/// - Sinks to send all the steps to (markdown, egglog, etc)
/// - All SMT2LIB functions that are in scope, along with their types
use crate::{
    log::{
        eggloglog, markdown,
        output::{LogSink, LogStream},
        Log, LogItem,
    },
    smt2lib,
    status::SATStatus,
};
use anyhow::{bail, Context as _};
use egglog::EGraph;
use itertools::Itertools;

/// Context representing the problem we are trying to solve
pub struct Context {
    /// EGraph with the problem description
    pub(crate) egraph: EGraph,
    /// Log sink with all the outputs
    pub(crate) sinks: LogSink,
    /// SMT2 sort/function contexts
    pub(crate) smt2contexts: Vec<smt2lib::Context>,
    /// Assertions count
    pub(crate) asserts_so_far: usize,
    /// True if functions should be kept in the e-graph
    pub(crate) keep_functions: bool,
}

impl Context {
    pub(crate) fn text(&mut self, text: &str) -> anyhow::Result<()> {
        self.sinks.add_text(text)
    }

    pub(crate) fn newline(&mut self) -> anyhow::Result<()> {
        self.sinks.newline()
    }

    pub(crate) fn run_code(
        &mut self,
        source: &str,
        commands: Vec<egglog::ast::Command>,
    ) -> anyhow::Result<()> {
        self.sinks.egglog_code_pre_exec(source)?;
        match self.egraph.run_program(commands) {
            Ok(_) => {}
            Err(error) => bail!("Failed to run egglog code: {error:?}"),
        }
        self.sinks.egglog_code_post_exec()
    }

    pub(crate) fn run_log(&mut self, log: &Log) -> anyhow::Result<()> {
        for (item, newline) in log.items.iter() {
            match item {
                LogItem::Egglog { code, commands } => self
                    .run_code(code, commands.clone())
                    .context("Failed to execute log")?,
                LogItem::RawText { text } => self.text(text)?,
            }
            if *newline {
                self.sinks.newline()?;
            }
        }
        Ok(())
    }
}

impl Context {
    pub fn new() -> Context {
        let egraph = EGraph::default();
        Context {
            egraph,
            sinks: LogSink::new(),
            smt2contexts: vec![smt2lib::Context::new()],
            asserts_so_far: 0,
            keep_functions: false,
        }
    }

    pub fn keep_functions(&mut self) {
        self.keep_functions = true;
    }

    pub fn add_egglog_sink(&mut self, path: &std::path::Path) -> anyhow::Result<()> {
        self.add_output(eggloglog::EgglogLogStream::new(std::fs::File::create(
            path,
        )?));
        Ok(())
    }

    pub fn add_markdown_sink(&mut self, path: &std::path::Path) -> anyhow::Result<()> {
        self.add_output(markdown::MarkdownLogStream::new(std::fs::File::create(
            path,
        )?));
        Ok(())
    }

    pub fn print_results_to_stdout(&mut self) {
        struct StdoutCmdResultsStream;

        impl LogStream for StdoutCmdResultsStream {
            fn check_sat_status(&mut self, status: SATStatus) -> anyhow::Result<()> {
                match status {
                    SATStatus::UnSat => println!("unsat"),
                    SATStatus::Sat => println!("sat"),
                    SATStatus::Unknown => println!("unknown"),
                }
                Ok(())
            }
        }

        self.add_output(StdoutCmdResultsStream);
    }

    pub fn add_output(&mut self, out: impl LogStream + 'static) {
        self.sinks.add_output(out);
    }

    pub fn run_cmds(&mut self, commands: Vec<egglog::ast::Command>) -> anyhow::Result<()> {
        let rendered = commands.iter().join("\n");
        self.run_code(&rendered, commands)
    }

    pub fn serialize(&self, config: egglog::SerializeConfig) -> egraph_serialize::EGraph {
        self.egraph.serialize(config)
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}
