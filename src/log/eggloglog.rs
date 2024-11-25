//// Egglog logger stashes all inferences in the egglog file. This is usually
//// quite easy to do as all inference actions are mostly done within egglog
//// anyway. Solver can also recover from egglog log by rerunnning all commands
//// in the file. This potentially allows user to make tweaks to unblock
//// inferences.

use super::output::LogStream;
use itertools::Itertools;
use std::io::Write;

pub(crate) struct EgglogLogStream {
    writer: std::io::BufWriter<std::fs::File>,
    trailing_newline: bool,
}

impl EgglogLogStream {
    pub(crate) fn new(file: std::fs::File) -> EgglogLogStream {
        EgglogLogStream {
            writer: std::io::BufWriter::new(file),
            trailing_newline: true,
        }
    }
}

impl LogStream for EgglogLogStream {
    fn egglog_code_pre_exec(&mut self, source: &str) -> anyhow::Result<()> {
        self.trailing_newline = false;
        write!(self.writer, "{source}\n")?;
        Ok(())
    }

    fn egglog_code_post_exec(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn add_text(&mut self, text: &str) -> anyhow::Result<()> {
        self.trailing_newline = false;
        write!(
            self.writer,
            "{}\n",
            text.split('\n')
                .map(|x| if x.trim().is_empty() {
                    ";".to_owned()
                } else {
                    format!("; {x}")
                })
                .join("\n"),
        )?;
        Ok(())
    }

    fn newline(&mut self) -> anyhow::Result<()> {
        if !self.trailing_newline {
            write!(self.writer, "\n")?;
            self.trailing_newline = true;
        }
        Ok(())
    }
}
