//// Various macros used in prelude logbooks

pub(crate) mod aig;
pub(crate) mod destructive_rw;

use std::sync::Arc;

pub(crate) fn register_macros(parser: &mut egglog::ast::Parser) {
    parser.add_command_macro(Arc::new(aig::AIGMacro));
}
