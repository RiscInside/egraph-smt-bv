//! Plans for the `egraph-smt-bv` solver.
//! This currently mostly mimics egglog schedules, but more elaborate tactics can be added in the future.

use std::path::PathBuf;

use crate::{Context, LogStream, SATStatus};
use anyhow::{bail, Context as _};
use egglog::{
    ast::{Command, Expr, GenericSchedule, RunConfig, Symbol},
    call, span, RunReport,
};
use itertools::Itertools;
use lazy_static::lazy_static;
use smt2parser::concrete::{Constant, SExpr};

lazy_static! {
    static ref PROVEN_UNSAT: Expr = call!("ProvenUnsat", []);
}

/// Tactics are small atomic operations that solver can perform to simplify the problem or check
/// for satisfiability. They are used in the `Plan` struct to build more complex plans.
#[derive(Clone, Debug)]
pub(crate) enum Tactic {
    /// Run egglog ruleset
    RunRuleset(Symbol),
    /// Dump the current e-graph to a json file
    DumpJson(PathBuf),
    /// Dump the current e-graph html to a file
    DumpHtml(PathBuf),
    /// Dump the current e-graph history to a file
    DumpHtmlHistory(PathBuf),
    /// Print a message to the log
    Log(String),
}

/// Plans are sequences of tactics that the solver can use to check for satisfiability. They can be
/// composed of other plans, allowing for complex strategies to be built. The `Plan` struct is used
/// to represent a plan, which can be a sequence of tactics, a timeout, a saturation strategy,
/// or a repeated plan.
#[derive(Clone, Debug)]
pub(crate) enum Plan {
    /// Run plan until no progress is made
    Saturate(Vec<Plan>),
    /// Run a sequenced plan
    Seq(Vec<Plan>),
    /// Run until timeout is reached
    Timeout(Vec<Plan>, std::time::Duration),
    /// Repeat the given plan a specified number of times.
    Repeat(Vec<Plan>, usize),
    /// Run subplan and print all rules that have been applied
    Delta(Vec<Plan>),
    /// Leaf tactic
    Leaf(Tactic),
}

impl Plan {
    /// Default plan for checking satisfiability.
    pub(crate) fn check_sat_default(timeout: Option<std::time::Duration>) -> Plan {
        // Initial preprocessing pass
        let saturate_first = Plan::Saturate(vec![
            Plan::Leaf(Tactic::RunRuleset(Symbol::from("width"))),
            Plan::Leaf(Tactic::RunRuleset(Symbol::from("fold"))),
            Plan::Leaf(Tactic::RunRuleset(Symbol::from("eq"))),
        ]);
        // Run the `once` ruleset with very explosive rules
        let run_once = Plan::Leaf(Tactic::RunRuleset(Symbol::from("once")));
        // Build the main reasoning block based on repetition
        let repeat_block = Plan::Seq(vec![
            Plan::Saturate(vec![
                Plan::Saturate(vec![
                    Plan::Leaf(Tactic::RunRuleset(Symbol::from("width"))),
                    Plan::Leaf(Tactic::RunRuleset(Symbol::from("eq"))),
                    Plan::Leaf(Tactic::RunRuleset(Symbol::from("fold"))),
                ]),
                Plan::Leaf(Tactic::RunRuleset(Symbol::from("safe"))),
            ]),
            Plan::Leaf(Tactic::RunRuleset(Symbol::from("unsafe"))),
        ]);
        // Repeat it 5 times
        let repeat_block = Plan::Repeat(vec![repeat_block], 5);
        // Optionally wrap the repeat block in a timeout
        let repeat_block = if let Some(timeout) = timeout {
            Plan::Timeout(vec![repeat_block], timeout)
        } else {
            repeat_block
        };

        Plan::Seq(vec![saturate_first, run_once, repeat_block])
    }

    /// Parse the plan from concrete SExpr
    pub(crate) fn parse(sexpr: &SExpr) -> anyhow::Result<Plan> {
        let sexprs = match sexpr {
            SExpr::Application(sexprs) => sexprs,
            SExpr::Symbol(symbol) => match symbol.0.as_str() {
                ruleset @ ("safe" | "unsafe" | "fold" | "width" | "eq" | "once") => {
                    return Ok(Plan::Leaf(Tactic::RunRuleset(ruleset.into())));
                }
                _ => bail!("Unknown tactic: `{}`", symbol.0),
            },
            SExpr::Constant(Constant::String(name)) => {
                return Ok(Plan::Leaf(Tactic::RunRuleset(name.into())));
            }
            _ => {
                bail!("Expected a plan, got: {sexpr:?}");
            }
        };
        match sexprs.as_slice() {
            [SExpr::Symbol(name), SExpr::Constant(Constant::Numeral(num)), plans @ ..]
                if name.0 == "timeout" =>
            {
                let plans = plans
                    .iter()
                    .map(Plan::parse)
                    .collect::<anyhow::Result<Vec<_>>>()?;

                let duration = std::time::Duration::from_millis(
                    u64::try_from(num).context("Parsing timeout")?,
                );
                Ok(Plan::Timeout(plans, duration))
            }
            [SExpr::Symbol(name), SExpr::Constant(Constant::Numeral(num)), plans @ ..]
                if name.0 == "repeat" =>
            {
                let plans = plans
                    .iter()
                    .map(Plan::parse)
                    .collect::<anyhow::Result<Vec<_>>>()?;

                Ok(Plan::Repeat(
                    plans,
                    usize::try_from(num).context("Repetition count")?,
                ))
            }
            [SExpr::Symbol(name), SExpr::Constant(Constant::String(path))]
                if name.0 == "dump-json" =>
            {
                let path = PathBuf::from(path);
                Ok(Plan::Leaf(Tactic::DumpJson(path)))
            }
            [SExpr::Symbol(name), SExpr::Constant(Constant::String(path))]
                if name.0 == "dump-html" =>
            {
                let path = PathBuf::from(path);
                Ok(Plan::Leaf(Tactic::DumpHtml(path)))
            }
            [SExpr::Symbol(name), SExpr::Constant(Constant::String(path))]
                if name.0 == "dump-html-history" =>
            {
                let path = PathBuf::from(path);
                Ok(Plan::Leaf(Tactic::DumpHtmlHistory(path)))
            }
            [SExpr::Symbol(name), SExpr::Constant(Constant::String(msg))] if name.0 == "log" => {
                Ok(Plan::Leaf(Tactic::Log(msg.clone())))
            }
            [SExpr::Symbol(name), plans @ ..] => {
                let plans = plans
                    .iter()
                    .map(Plan::parse)
                    .collect::<anyhow::Result<Vec<_>>>()?;
                Ok(match name.0.as_str() {
                    "saturate" => Plan::Saturate(plans),
                    "seq" => Plan::Seq(plans),
                    "delta?" => Plan::Delta(plans),
                    _ => {
                        bail!("Unknown plan combinator name: {}", name.0);
                    }
                })
            }
            _ => bail!("Expected a plan, got: {sexpr:?}"),
        }
    }
}

pub enum PlanError {
    /// anyhow::Error
    Anyhow(anyhow::Error),
    /// Timeout elapsing
    Timeout,
    /// SAT status can be provided
    SATStatusReady(SATStatus),
}

impl From<anyhow::Error> for PlanError {
    fn from(err: anyhow::Error) -> Self {
        PlanError::Anyhow(err)
    }
}

type PlanResult<T> = Result<T, PlanError>;

impl Context {
    pub(crate) fn check_for_unsat(&mut self) -> PlanResult<()> {
        let (_, value) = self.egraph.eval_expr(&PROVEN_UNSAT).unwrap();
        assert!(
            value.bits < 2,
            "bool sort only allows for true and false values"
        );
        if value.bits == 1 {
            Err(PlanError::SATStatusReady(SATStatus::UnSat))
        } else {
            Ok(())
        }
    }

    fn check_sat_using_tactic(
        &mut self,
        tactic: &Tactic,
        timeout: Option<std::time::Instant>,
        report: &mut RunReport,
    ) -> PlanResult<bool> {
        // Check for timeout elapsing here
        if let Some(timeout) = timeout {
            if timeout < std::time::Instant::now() {
                return Err(PlanError::Timeout);
            }
        }

        match tactic {
            Tactic::RunRuleset(ruleset) => {
                self.run_cmds(vec![Command::RunSchedule(GenericSchedule::Run(
                    span!(),
                    RunConfig {
                        ruleset: *ruleset,
                        until: None,
                    },
                ))])?;
                let delta = self.egraph.get_run_report().as_ref().unwrap().clone();
                let updated = delta.updated;
                *report = report.union(&delta);

                // Try to rebuild
                if self.egraph.rebuild().is_err() {
                    self.text("**UNSOUNDNESS DETECTED during rebuild**")?;
                    self.newline()?;
                    self.text(&format!("Offending ruleset: {ruleset}\n"))?;
                    self.newline()?;
                    self.text("Matched rules:")?;
                    self.print_all_applied_rules(report)?;
                    panic!("Unsoundness detected during rebuilding");
                }

                if updated && self.rewriting_history.is_some() {
                    let serialized = self.serialize()?;
                    if let Some(history) = &mut self.rewriting_history {
                        history.push(serialized);
                    }
                }

                self.check_for_unsat()?;

                Ok(updated)
            }
            Tactic::DumpJson(path) => {
                self.dump_json(path)?;
                Ok(false)
            }
            Tactic::DumpHtml(path) => {
                self.dump_html(path)?;
                Ok(false)
            }
            Tactic::DumpHtmlHistory(path) => {
                self.dump_html_history(path)?;
                Ok(false)
            }
            Tactic::Log(msg) => {
                self.text(msg)?;
                Ok(false)
            }
        }
    }

    fn check_sat_using_seq_plan(
        &mut self,
        plans: &[Plan],
        timeout: Option<std::time::Instant>,
        report: &mut RunReport,
    ) -> PlanResult<bool> {
        plans
            .iter()
            .map(|plan| self.check_sat_using_plan(plan, timeout, report))
            .fold_ok(false, std::ops::BitOr::bitor)
    }

    fn check_sat_using_plan(
        &mut self,
        plan: &Plan,
        timeout: Option<std::time::Instant>,
        report: &mut RunReport,
    ) -> PlanResult<bool> {
        match plan {
            Plan::Saturate(plans) => {
                let mut updated = false;
                while self.check_sat_using_seq_plan(plans, timeout, report)? {
                    updated = true;
                }
                Ok(updated)
            }
            Plan::Seq(plans) => self.check_sat_using_seq_plan(plans, timeout, report),
            Plan::Timeout(plans, duration) => {
                let new_timeout = std::time::Instant::now() + *duration;
                let new_timeout = timeout
                    .map(|timeout| std::cmp::min(timeout, new_timeout))
                    .or(Some(new_timeout));
                self.check_sat_using_seq_plan(plans, new_timeout, report)
            }
            Plan::Repeat(plans, times) => {
                let mut updated = false;
                for _ in 0..*times {
                    let new_updates = self.check_sat_using_seq_plan(plans, timeout, report)?;
                    updated |= new_updates;
                    if !new_updates {
                        break;
                    }
                }
                Ok(updated)
            }
            Plan::Leaf(tactic) => self.check_sat_using_tactic(tactic, timeout, report),
            Plan::Delta(plans) => {
                let mut delta = RunReport::default();
                let res = self.check_sat_using_seq_plan(plans, timeout, &mut delta);

                self.print_all_applied_rules(&delta)?;
                self.newline()?;
                *report = report.union(&delta);
                res
            }
        }
    }

    pub(crate) fn check_sat(&mut self) -> anyhow::Result<()> {
        self.text("### Running `(check-sat)`")?;
        self.newline()?;

        let plan = self.check_sat_plan.clone();
        let mut report = RunReport::default();
        let status = match self.check_sat_using_plan(&plan, None, &mut report) {
            Ok(_) | Err(PlanError::Timeout) => SATStatus::Unknown,
            Err(PlanError::Anyhow(err)) => return Err(err),
            Err(PlanError::SATStatusReady(status)) => status,
        };

        self.sinks.check_sat_status(status)?;
        self.newline()?;
        self.print_stats(&report)?;
        self.newline()?;

        Ok(())
    }
}
