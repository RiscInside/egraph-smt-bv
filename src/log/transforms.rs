//// Various log book preprocessing passes/analysis
use super::Log;

impl Log {
    pub(crate) fn wrap_in_details(mut self) -> Log {
        let mut res = Log { items: vec![] };
        res.add_text_line("<details>");
        res.items.append(&mut self.items);
        res.add_text_line("</details>");
        res
    }

    pub(crate) fn followed_by(mut self, mut other: Log) -> Log {
        self.items.append(&mut other.items);
        Log { items: self.items }
    }
}
