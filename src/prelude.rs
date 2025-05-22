use crate::context::Context;
use crate::log::Log;
use lazy_static::lazy_static;

#[macro_export]
macro_rules! embed {
    ($path:literal) => {
        (Log::from_egglog_source(include_str!($path), Some(concat!("src/", $path))).unwrap())
    };
}

fn prelude_logbook() -> Log {
    embed!("prelude/prelude.egg")
        .wrap_in_details()
        .followed_by(embed!("prelude/operators.egg").wrap_in_details())
        .followed_by(embed!("prelude/eq.egg").wrap_in_details())
        .followed_by(embed!("prelude/propositional.egg").wrap_in_details())
        .followed_by(embed!("prelude/bitwise.egg").wrap_in_details())
        .followed_by(embed!("prelude/implications.egg").wrap_in_details())
        .followed_by(embed!("prelude/add.egg").wrap_in_details())
        .followed_by(embed!("prelude/comparisons.egg").wrap_in_details())
        .followed_by(embed!("prelude/mul.egg").wrap_in_details())
        .followed_by(embed!("prelude/div.egg").wrap_in_details())
        .followed_by(embed!("prelude/ite.egg").wrap_in_details())
        .followed_by(embed!("prelude/bpnf.egg").wrap_in_details())
        .followed_by(embed!("prelude/solvers.egg").wrap_in_details())
}

lazy_static! {
    static ref PRELUDE: Log = prelude_logbook();
}

impl Context {
    pub fn run_prelude(&mut self) -> anyhow::Result<()> {
        self.text("## Prelude definitions")?;
        self.run_log(&PRELUDE).unwrap();

        self.newline()?;
        self.text("## Solving log")?;

        self.newline()
    }
}
