use anyhow::{bail, Result};
use egraph_smt_bv::{Context, LogStream, SATStatus};
use glob::glob;
use libtest_mimic::{run, Arguments, Trial};
use std::path::Path;

struct AssertExactStatus(SATStatus);

impl LogStream for AssertExactStatus {
    fn check_sat_status(&mut self, status: SATStatus) -> anyhow::Result<()> {
        if self.0 != status {
            bail!("Expected {} result, got {status} instead", self.0);
        }
        Ok(())
    }
}

fn run_unsat_test(path: &Path) {
    let mut ctx: Context = Context::new();
    ctx.add_output(AssertExactStatus(SATStatus::UnSat));
    ctx.run_prelude().unwrap();

    let file = std::fs::File::open(path).unwrap();
    let reader = std::io::BufReader::new(file);
    let stream = smt2parser::CommandStream::new(
        reader,
        smt2parser::concrete::SyntaxBuilder,
        Some(format!("{}", path.display())),
    );

    for command in stream {
        match command {
            Ok(cmd) => ctx.run_smt2lib_command(&cmd).unwrap(),
            Err(_) => panic!("failed to parse"),
        }
    }
}

fn unsat_tests_from_smt2_files(pattern: &'static str, trials: &mut Vec<Trial>) {
    for path in glob(pattern).unwrap().map(Result::unwrap) {
        trials.push(Trial::test(
            path.file_stem().unwrap().display().to_string(),
            move || {
                run_unsat_test(&path);
                Ok(())
            },
        ));
    }
}

pub fn main() {
    let mut tests = vec![];
    unsat_tests_from_smt2_files("../**/*.unsat*.smt2", &mut tests);
    run(&Arguments::from_args(), tests).exit_if_failed();
}
