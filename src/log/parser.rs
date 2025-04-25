use crate::log::{macros, Log, LogItem};
use itertools::repeat_n;

fn logbook_egglog_parser() -> egglog::ast::Parser {
    // Any macro definitions would go in here
    let mut parser = egglog::ast::Parser::default();
    macros::register_macros(&mut parser);
    parser
}

impl Log {
    fn add_text_line(&mut self, new_text: &str) {
        match self.items.last_mut() {
            Some((_, true) | (LogItem::Egglog { .. }, false)) | None => {
                self.items.push((
                    LogItem::RawText {
                        text: new_text.trim_end().to_owned(),
                    },
                    false,
                ));
            }
            Some((LogItem::RawText { text }, false)) => {
                text.push('\n');
                text.push_str(new_text.trim_end());
            }
        }
    }

    fn add_egglog_line(&mut self, new_code: &str, line_number: usize) {
        match self.items.last_mut() {
            Some((LogItem::RawText { .. }, _)) | None => {
                self.items.push((
                    LogItem::Egglog {
                        code: new_code.to_owned(),
                        commands: vec![],
                        line_number,
                    },
                    false,
                ));
            }
            Some((LogItem::Egglog { code, .. }, b @ true)) => {
                code.push_str("\n\n");
                code.push_str(new_code);
                *b = false;
            }
            Some((LogItem::Egglog { code, .. }, false)) => {
                code.push('\n');
                code.push_str(new_code);
            }
        }
    }

    fn parse_egglog(
        &mut self,
        filename: Option<&str>,
        parser: &mut egglog::ast::Parser,
    ) -> anyhow::Result<()> {
        for item in self.items.iter_mut() {
            if let LogItem::Egglog {
                code,
                commands,
                line_number,
            } = &mut item.0
            {
                // Probably the worst possible way to make spans correct. Not sure what's the better
                // aproach is
                let mut code_with_newlines: String = repeat_n('\n', *line_number).collect();
                code_with_newlines.push_str(code);

                *commands = parser.get_program_from_string(
                    filename.map(|filename| filename.to_owned()),
                    &code_with_newlines,
                )?;
            }
        }
        Ok(())
    }

    pub(crate) fn from_egglog_source(source: &str, filename: Option<&str>) -> anyhow::Result<Log> {
        let mut log = Log::new();

        for (line_number, line) in source.split('\n').enumerate() {
            if line.trim().is_empty() {
                log.newline();
            } else if let Some(stripped) = line.strip_prefix(";") {
                log.add_text_line(stripped.strip_prefix(" ").unwrap_or(stripped));
            } else {
                log.add_egglog_line(line, line_number);
            }
        }

        // Remove final newline
        if let Some((_, final_newline)) = log.items.last_mut() {
            *final_newline = false;
        }

        let mut parser = logbook_egglog_parser();
        log.parse_egglog(filename, &mut parser)?;
        Ok(log)
    }
}
