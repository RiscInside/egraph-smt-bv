use crate::context::Context;
use crate::log::Log;
use lazy_static::lazy_static;

lazy_static! {
    static ref PRELUDE_EGG: Log = Log::from_egglog_source(
        include_str!("prelude/prelude.egg"),
        Some("src/prelude/prelude.egg")
    )
    .unwrap();
    static ref CORE_THEORY_EGG: Log = Log::from_egglog_source(
        include_str!("prelude/core_theory.egg"),
        Some("src/prelude/core_theory.egg")
    )
    .unwrap();
    static ref BV_THEORY_EGG: Log = Log::from_egglog_source(
        include_str!("prelude/bv_theory.egg"),
        Some("src/prelude/bv_theory.egg")
    )
    .unwrap();
    static ref FOLD_EGG: Log = Log::from_egglog_source(
        include_str!("prelude/fold.egg"),
        Some("src/prelude/fold.egg")
    )
    .unwrap();
    static ref ALGEBRAIC_EGG: Log = Log::from_egglog_source(
        include_str!("prelude/algebraic.egg"),
        Some("src/prelude/algebraic.egg")
    )
    .unwrap();
}

impl Context {
    pub(crate) fn run_prelude(&mut self) -> anyhow::Result<()> {
        self.run_log(&*PRELUDE_EGG)?;
        self.run_log(&*CORE_THEORY_EGG)?;
        self.run_log(&*&BV_THEORY_EGG)?;
        self.run_log(&*&FOLD_EGG)?;
        self.run_log(&*&ALGEBRAIC_EGG)?;

        self.newline()?;
        self.text("## Solving log")?;

        self.newline()
    }
}
