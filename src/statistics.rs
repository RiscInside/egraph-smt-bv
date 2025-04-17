use crate::context::Context;
use egglog::{ast::Symbol, util::IndexMap, RunReport};
use itertools::Itertools;
use std::time::Duration;

fn format_rule_name(given: &str) -> String {
    given
        .split_ascii_whitespace()
        .filter(|s| !s.is_empty())
        .join(" ")
        .replace("rewrite_var__", "|rv|")
}

const DISPLAYED_RULES_DEFAULT: usize = 5;

fn top_entries<T: std::cmp::Ord + Copy>(
    map: &IndexMap<Symbol, T>,
    threshold: T,
) -> Vec<(String, T)> {
    let mut output_size: usize = 0;

    // Rules that are explicitly named something ending in question mark are
    // always incldued in output. This is quite useful if we want to check
    // whether some particular rule has been applied (even once), as chances
    // are this rule would not be in top 5
    map.iter()
        .map(|(name, value)| (*name, *value))
        .sorted_by_key(|(_, value)| std::cmp::Reverse(*value))
        .filter(|(name, value)| {
            (name.as_str().ends_with('?'))
                || (*value > threshold) && {
                    if output_size >= DISPLAYED_RULES_DEFAULT {
                        false
                    } else {
                        output_size += 1;
                        true
                    }
                }
        })
        .map(|(name, value)| (format_rule_name(name.as_str()), value))
        .collect::<Vec<_>>()
}

fn get_ruleset_times(report: &RunReport, name: &str) -> (Duration, Duration, Duration) {
    let symbol = Symbol::from(name);
    (
        report
            .search_time_per_ruleset
            .get(&symbol)
            .cloned()
            .unwrap_or(Duration::ZERO),
        report
            .apply_time_per_ruleset
            .get(&symbol)
            .cloned()
            .unwrap_or(Duration::ZERO),
        report
            .rebuild_time_per_ruleset
            .get(&symbol)
            .cloned()
            .unwrap_or(Duration::ZERO),
    )
}

impl Context {
    pub(crate) fn print_all_applied_rules(&mut self, report: &RunReport) -> anyhow::Result<()> {
        for (name, matches) in report
            .num_matches_per_rule
            .iter()
            .sorted_by_key(|(_, matches)| std::cmp::Reverse(**matches))
            .filter(|(_, matches)| **matches > 0)
        {
            self.text(&format!(
                "- `{}` ({matches} matches)",
                format_rule_name(name.as_str())
            ))?;
        }
        Ok(())
    }

    pub(crate) fn print_stats(&mut self, report: &RunReport) -> anyhow::Result<()> {
        let top_apps = top_entries(&report.num_matches_per_rule, 0);
        let top_search_time = top_entries(&report.search_time_per_rule, Duration::new(0, 0));
        let top_apply_time = top_entries(&report.apply_time_per_rule, Duration::new(0, 0));

        let (fold_search, fold_apply, fold_rebuild) = get_ruleset_times(report, "fold");
        let (safe_search, safe_apply, safe_rebuild) = get_ruleset_times(report, "safe");
        let (unsafe_search, unsafe_apply, unsafe_rebuild) = get_ruleset_times(report, "unsafe");

        self.text("<details>\n<summary>Rewrite rule application statistics</summary>")?;
        self.newline()?;

        self.text("#### Overall ruleset statistics")?;
        self.newline()?;
        self.text("| Ruleset | Search time | Apply time | Rebuild time |")?;
        self.text("|---------|-------------|------------|--------------|")?;
        self.text(&format!(
            "| `fold` | {fold_search:?} | {fold_apply:?} | {fold_rebuild:?}"
        ))?;
        self.text(&format!(
            "| `safe` | {safe_search:?} | {safe_apply:?} | {safe_rebuild:?}"
        ))?;
        self.text(&format!(
            "| `unsafe` | {unsafe_search:?} | {unsafe_apply:?} | {unsafe_rebuild:?}"
        ))?;
        self.newline()?;

        self.text("#### Rewrite rules by number of applications")?;

        for (i, (name, applications)) in top_apps.iter().enumerate() {
            self.text(&format!(
                "{}) Rule `{name}` ({applications} {})",
                i + 1,
                if *applications == 1 {
                    "application"
                } else {
                    "applications"
                }
            ))?;
        }
        self.newline()?;

        self.text("#### Top {} rules by search time")?;
        for (i, (name, time)) in top_search_time.iter().enumerate() {
            self.text(&format!("{}) Rule `{name}` ({time:?})", i + 1))?;
        }
        self.newline()?;

        self.text("#### Top rules by application time")?;
        for (i, (name, time)) in top_apply_time.iter().enumerate() {
            self.text(&format!("{}) Rule `{name}` ({time:?})", i + 1))?;
        }
        self.newline()?;

        self.text("</details>")
    }
}
