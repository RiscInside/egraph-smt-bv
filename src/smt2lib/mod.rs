//! `smt2lib` - SMT2LIB to egglog lowering code

use egglog::ast::Symbol;
use im_rc::HashMap;

pub(crate) mod constants;
pub(crate) mod fun;
pub(crate) mod prelude;
pub(crate) mod sort;
pub(crate) mod term;

pub(crate) fn to_egglog_name(name: &str) -> Symbol {
    // Desugar names to be valid egglog names
    let mut result = String::new();
    for char in name.chars() {
        match char {
            '%' => result.push_str("%%"),
            ' ' => result.push_str("%_"),
            '|' => result.push_str("%|"),
            _ => result.push(char),
        }
    }
    result.into()
}

#[derive(Clone)]
pub(crate) struct Context {
    /// Sorts available in scope
    pub(crate) sorts: HashMap<String, sort::Sort>,
    /// Functions available in-scope
    pub(crate) functions: HashMap<String, fun::FunctionDef>,
    /// How many fresh variables we generated in global context
    pub(crate) fresh_vars_count: usize,
}
