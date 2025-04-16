use anyhow::{bail, Result};
use cap::Cap;
use egraph_smt_bv::{Context, LogStream, SATStatus};
use glob::glob;
use libtest_mimic::{run, Arguments, Trial};
use std::{
    alloc,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};
struct AssertExactStatus(SATStatus);

#[global_allocator]
static ALLOCATOR: Cap<alloc::System> = Cap::new(alloc::System, 1024 * 1024 * 1024);

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
        eprintln!("Yosys binary not found - no hardware tests will be generated");
        return;
    };

    let yosys = yosys.canonicalize().unwrap();
    eprintln!("Using yosys at `{}`", yosys.display());

    let mut launched_yosys_processes = vec![];
    for yosys_script_path in glob(pattern).unwrap().map(Result::unwrap) {
        let expected_output = expected_smt2_filename(&yosys_script_path);
        if expected_output.exists() {
            continue;
        }

        eprintln!(
            "Generating SMT2LIB file `{}` from yosys script `{}`",
            expected_output.display(),
            yosys_script_path.display()
        );

        launched_yosys_processes.push((
            Command::new(&yosys)
                .current_dir(yosys_script_path.canonicalize().unwrap().parent().unwrap())
                .arg(yosys_script_path.file_name().unwrap().to_str().unwrap())
                .args(["-f", "script"])
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap(),
            yosys_script_path,
            expected_output,
        ));
    }

    for (yosys_process, yosys_script_path, expected_output) in launched_yosys_processes {
        let result = yosys_process.wait_with_output().unwrap();
        if !result.status.success() {
            eprintln!(
                "Failed to run yosys on `{}`. Yosys stderr:\n{}",
                yosys_script_path.display(),
                String::from_utf8_lossy(&result.stderr)
            );
            std::process::exit(1);
        }

        if !expected_output.exists() {
            eprintln!(
                "Yosys script `{}` did not produce required file `{}`",
                yosys_script_path.display(),
                expected_output.display()
            );
            std::process::exit(1);
        }
    }
}

pub fn main() {
    // Generate all smt2lib problems we can from yosys scripts
    run_yosys_scripts("**/*.ys-test");
    // Create trials from smt2lib files
    let mut tests = vec![];
    unsat_tests_from_smt2_files("**/*.unsat*.smt2", &mut tests);
    run(&Arguments::from_args(), tests).exit_if_failed();
}
