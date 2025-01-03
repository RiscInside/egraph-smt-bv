use crate::{log::Log, Context};
use egglog::{ast::Expr, call};
use lazy_static::lazy_static;

lazy_static! {
    static ref CHECK_SAT: Log =
        Log::from_egglog_source(include_str!("check_sat.egg"), Some("check_sat.egg")).unwrap();
    static ref PROVEN_UNSAT: Expr = call!("ProvenUnsat", []);
}

impl Context {
    pub(crate) fn check_sat(&mut self) -> anyhow::Result<()> {
        self.run_log(&*CHECK_SAT)?;
        let (_, value) = self.egraph.eval_expr(&*&PROVEN_UNSAT).unwrap();
        assert!(
            value.bits < 2,
            "bool sort only allows for true and false values"
        );

        if value.bits == 1 {
            self.text("Result: **UNSAT**")?;
            println!("unsat");
        } else {
            self.text("Result: **Unknown**")?;
            println!("unknown");
        }

        self.newline()?;
        self.print_stats()?;
        self.newline()?;

        Ok(())
    }
}
