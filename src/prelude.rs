use crate::context::Context;
use crate::log::Log;
use lazy_static::lazy_static;

macro_rules! embed {
    ($path:literal) => {
        (Log::from_egglog_source(include_str!($path), Some(concat!("src/", $path))).unwrap())
    };
}

fn prelude_logbook() -> Log {
    embed!("prelude/prelude.egg")
        .wrap_in_details()
        .followed_by(embed!("prelude/core_theory.egg").wrap_in_details())
        .followed_by(embed!("prelude/bv_theory.egg").wrap_in_details())
        .followed_by(embed!("prelude/propositional.egg").wrap_in_details())
        .followed_by(embed!("prelude/ac.egg").wrap_in_details())
        .followed_by(
            embed!("prelude/bitwise.egg")
                .generate_bv_rules()
                .wrap_in_details(),
        )
        .followed_by(embed!("prelude/add.egg").wrap_in_details())
}

lazy_static! {
    static ref PRELUDE: Log = prelude_logbook();
}

impl Context {
    pub(crate) fn run_prelude(&mut self) -> anyhow::Result<()> {
        self.text("## Prelude definitions")?;
        self.run_log(&*&PRELUDE).unwrap();

        self.newline()?;
        self.text("## Solving log")?;

        self.newline()
    }
}
