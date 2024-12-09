//// Various log book preprocessing passes/analysis

use itertools::Itertools;

use super::{Log, LogItem};

/// Preprocessing pass for AIG logbook that converts boolean rules to those
/// on bitvectors
pub(crate) mod aig;

impl Log {
    pub(crate) fn add_generated_code(&mut self, commands: Vec<egglog::ast::Command>) {
        self.items.push((
            LogItem::Egglog {
                code: commands.iter().join("\n"),
                commands,
            },
            false,
        ));
    }

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
