use crate::log::Log;

impl Log {
    pub(crate) fn from_egglog_source(source: &str, filename: Option<&str>) -> anyhow::Result<Log> {
        let mut log = Log::new();

        for line in source.split('\n') {
            if line.trim().is_empty() {
                log.newline();
            } else if line.starts_with(";") {
                let mut line = &line[1..];
                // Peel off the space
                if line.starts_with(" ") {
                    line = &line[1..];
                }
                log.add_text_line(line);
            } else {
                log.add_egglog_line(line);
            }
        }

        // Remove final newline
        if let Some((_, final_newline)) = log.items.last_mut() {
            *final_newline = false;
        }

        log.parse_egglog(filename)?;
        Ok(log)
    }
}