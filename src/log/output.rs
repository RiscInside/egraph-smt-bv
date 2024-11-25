pub(crate) trait LogStream {
    fn egglog_code_pre_exec(&mut self, source: &str) -> anyhow::Result<()>;
    fn egglog_code_post_exec(&mut self) -> anyhow::Result<()>;
    fn add_text(&mut self, text: &str) -> anyhow::Result<()>;
    fn newline(&mut self) -> anyhow::Result<()>;
}

pub(crate) struct LogSink {
    outputs: Vec<Box<dyn LogStream>>,
}

impl LogSink {
    pub(crate) fn new() -> LogSink {
        LogSink { outputs: vec![] }
    }

    pub(crate) fn add_output(&mut self, out: impl LogStream + 'static) {
        self.outputs.push(Box::new(out));
    }
}

impl LogStream for LogSink {
    fn egglog_code_pre_exec(&mut self, source: &str) -> anyhow::Result<()> {
        for output in self.outputs.iter_mut() {
            output.egglog_code_pre_exec(source)?;
        }
        Ok(())
    }

    fn egglog_code_post_exec(&mut self) -> anyhow::Result<()> {
        for output in self.outputs.iter_mut() {
            output.egglog_code_post_exec()?;
        }
        Ok(())
    }

    fn add_text(&mut self, text: &str) -> anyhow::Result<()> {
        for output in self.outputs.iter_mut() {
            output.add_text(text)?;
        }
        Ok(())
    }

    fn newline(&mut self) -> anyhow::Result<()> {
        for output in self.outputs.iter_mut() {
            output.newline()?;
        }
        Ok(())
    }
}
