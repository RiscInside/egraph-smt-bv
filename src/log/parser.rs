use crate::log::{macros, Log};

fn logbook_egglog_parser() -> egglog::ast::Parser {
    // Any macro definitions would go in here
    let mut parser = egglog::ast::Parser::default();
    macros::register_macros(&mut parser);
    parser
}

impl Log {
    pub(crate) fn from_egglog_source(source: &str, filename: Option<&str>) -> anyhow::Result<Log> {
        let mut log = Log::new();

        for line in source.split('\n') {
            if line.trim().is_empty() {
                log.newline();
            } else if let Some(stripped) = line.strip_prefix(";") {
                log.add_text_line(stripped.strip_prefix(" ").unwrap_or(stripped));
            } else {
                log.add_egglog_line(line);
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
