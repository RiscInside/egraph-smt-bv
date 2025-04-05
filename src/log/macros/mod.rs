//// Various macros used in prelude logbooks

pub(crate) mod bitwise;

use std::sync::Arc;

pub(crate) fn register_macros(parser: &mut egglog::ast::Parser) {
    parser.add_command_macro(Arc::new(bitwise::BitwiseMacro::Plain));
    parser.add_command_macro(Arc::new(bitwise::BitwiseMacro::Replacing));
    parser.add_command_macro(Arc::new(bitwise::BitwiseMacro::Bi));
    parser.add_command_macro(Arc::new(bitwise::BitwiseMacro::Unsafe));
    parser.add_command_macro(Arc::new(bitwise::BitwiseMacro::BiUnsafe));
}
