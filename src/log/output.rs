use crate::status::SATStatus;

pub trait LogStream {
    fn egglog_code_pre_exec(&mut self, _source: &str) -> anyhow::Result<()> {
        Ok(())
    }

    fn egglog_code_post_exec(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn add_text(&mut self, _text: &str) -> anyhow::Result<()> {
        Ok(())
    }

    fn newline(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn check_sat_status(&mut self, status: SATStatus) -> anyhow::Result<()> {
        match status {
            SATStatus::UnSat => self.add_text("Result: **UNSAT**"),
            SATStatus::Sat => self.add_text("Result: **SAT**"),
            SATStatus::Unknown => self.add_text("Result: **Unknown**"),
        }
    }
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

    fn check_sat_status(&mut self, status: SATStatus) -> anyhow::Result<()> {
        for output in self.outputs.iter_mut() {
            output.check_sat_status(status)?;
        }
        Ok(())
    }
}
