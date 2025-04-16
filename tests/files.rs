use anyhow::{bail, Result};
use egraph_smt_bv::{Context, LogStream, SATStatus};
use glob::glob;
use libtest_mimic::{run, Arguments, Trial};
use std::path::{Path, PathBuf};
use subprocess::Exec;

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
            path.file_stem().unwrap().to_str().unwrap().to_owned(),
            move || {
                run_unsat_test(&path);
                Ok(())
            },
        ));
    }
}

fn run_yosys_scripts(pattern: &'static str) {
    fn expected_smt2_filename(path: &Path) -> PathBuf {
        let mut result = path.to_path_buf();
        result.set_extension("generated.unsat.smt2");
        result
    }

    let Ok(yosys) = which::which("yosys") else {
        eprintln!("`yosys` not foud - no hardware tests will be generated");
        return;
    };

    for yosys_script_path in glob(pattern).unwrap().map(Result::unwrap) {
        let expected_output = expected_smt2_filename(&yosys_script_path);
        if expected_output.exists() {
            continue;
        }

        eprintln!(
            "generating SMT2LIB file `{}` from yosys script `{}`",
            expected_output.display(),
            yosys_script_path.display()
        );

        let result = Exec::cmd(&yosys)
            .arg(yosys_script_path.to_string_lossy().as_ref())
            .args(&["-f", "script"])
            .capture()
            .unwrap();

        if !result.success() {
            eprintln!("failed to run yosys on `{}`", yosys_script_path.display());
            std::process::exit(1);
        }

        if !expected_output.exists() {
            eprintln!(
                "yosys script `{}` did not produce required file `{}`",
                yosys_script_path.display(),
                expected_output.display()
            );
            std::process::exit(1);
        }
    }
}

pub fn main() {
    // Generate all smt2lib problems we can from yosys scripts
    run_yosys_scripts("../**/*.ys-test");
    // Create trials from smt2lib files
    let mut tests = vec![];
    unsat_tests_from_smt2_files("../**/*.unsat*.smt2", &mut tests);
    run(&Arguments::from_args(), tests).exit_if_failed();
}
