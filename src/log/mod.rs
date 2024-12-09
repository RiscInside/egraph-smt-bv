//// Logging infrastructure. Logger produces runnable egglog code that user can
//// modify in any way they wish

pub(crate) mod eggloglog;
pub(crate) mod markdown;
pub(crate) mod output;
pub(crate) mod parser;
pub(crate) mod preprocess;

/// One log item.
#[derive(Clone, Debug)]
pub(crate) enum LogItem {
    /// Egglog code that has been ran/is to be ran
    Egglog {
        code: String,
        commands: Vec<egglog::ast::Command>,
    },
    /// Text embedded into egglog file. Markdown renderer assumes this text is
    /// in Markdown and includes it as is. Leading and trailing whitespace is
    /// stripped.
    RawText { text: String },
}

#[derive(Debug)]
pub(crate) struct Log {
    pub(crate) items: Vec<(LogItem, bool)>,
}

impl Log {
    pub(crate) fn new() -> Log {
        Log { items: vec![] }
    }

    pub(crate) fn add_text_line(&mut self, new_text: &str) {
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

    pub(crate) fn add_egglog_line(&mut self, new_code: &str) {
        match self.items.last_mut() {
            Some((LogItem::RawText { .. }, _)) | None => {
                self.items.push((
                    LogItem::Egglog {
                        code: new_code.to_owned(),
                        commands: vec![],
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

    pub(crate) fn newline(&mut self) {
        match self.items.last_mut() {
            Some((_, b)) => {
                *b = true;
            }
            None => {}
        }
    }

    pub(crate) fn parse_egglog(&mut self, filename: Option<&str>) -> anyhow::Result<()> {
        for item in self.items.iter_mut() {
            if let LogItem::Egglog { code, commands } = &mut item.0 {
                *commands =
                    egglog::ast::parse_program(filename.map(|filename| filename.to_owned()), code)?;
            }
        }
        Ok(())
    }
}
