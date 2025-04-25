//! Logging infrastructure. Logger produces runnable egglog code that user can
//! modify in any way they wish

pub(crate) mod eggloglog;
pub(crate) mod macros;
pub(crate) mod markdown;
pub(crate) mod output;
pub(crate) mod parser;
pub(crate) mod transforms;

/// One log item.
#[derive(Clone, Debug)]
pub(crate) enum LogItem {
    /// Egglog code that has been ran/is to be ran
    Egglog {
        code: String,
        commands: Vec<egglog::ast::Command>,
        /// Line number in the log file if present. We only remember this for parsing egglog
        /// in the file, might be a good idea to remove in the future.
        line_number: usize,
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

    pub(crate) fn newline(&mut self) {
        if let Some((_, b)) = self.items.last_mut() {
            *b = true;
        }
    }
}
