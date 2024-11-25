//// Markdown log stream implementation. While we can't recover changes from
//// markdown files, they provide an alternative way to display solver's
//// inference history in a human-readable manner. They can also be used to
//// watch solver's progress live in editors like VSCode - markdown log stream
//// will flush output before executing any egglog code.

use super::output::LogStream;
use std::io::{Seek, Write};

pub(crate) struct MarkdownLogStream {
    file: std::io::BufWriter<std::fs::File>,
    backticks_pos: Option<u64>,
    trailing_newline: bool,
}

impl MarkdownLogStream {
    pub(crate) fn new(file: std::fs::File) -> MarkdownLogStream {
        MarkdownLogStream {
            file: std::io::BufWriter::new(file),
            backticks_pos: None,
            trailing_newline: true,
        }
    }

    pub(crate) fn open_code_block(&mut self) -> anyhow::Result<()> {
        if let Some(backticks_pos) = self.backticks_pos {
            self.file
                .seek(std::io::SeekFrom::Start(self.backticks_pos.unwrap()))?;
            self.file.get_mut().set_len(backticks_pos)?;
            write!(self.file, "\n")?;
        } else {
            write!(self.file, "```egg\n")?;
        }
        Ok(())
    }
}

impl LogStream for MarkdownLogStream {
    fn egglog_code_pre_exec(&mut self, source: &str) -> anyhow::Result<()> {
        self.trailing_newline = false;
        self.open_code_block()?;
        write!(self.file, "{source}\n")?;
        self.backticks_pos = Some(self.file.stream_position()?);
        write!(self.file, "```\nExecution in progress ↺\n")?;
        self.file.flush()?;
        Ok(())
    }

    fn egglog_code_post_exec(&mut self) -> anyhow::Result<()> {
        self.file
            .seek(std::io::SeekFrom::Start(self.backticks_pos.unwrap()))?;
        self.file.get_mut().set_len(self.backticks_pos.unwrap())?;
        write!(self.file, "```\n")?;
        Ok(())
    }

    fn add_text(&mut self, text: &str) -> anyhow::Result<()> {
        self.backticks_pos = None;
        self.trailing_newline = false;
        write!(self.file, "{text}\n")?;
        Ok(())
    }

    fn newline(&mut self) -> anyhow::Result<()> {
        if !self.trailing_newline {
            write!(self.file, "\n")?;
            self.trailing_newline = true;
        }
        Ok(())
    }
}
