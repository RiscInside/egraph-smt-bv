//// SMT2 - smt2 -> egraph lowering code

use im_rc::HashMap;

pub(crate) mod constants;
pub(crate) mod fun;
pub(crate) mod prelude;
pub(crate) mod sort;
pub(crate) mod term;

#[derive(Clone)]
pub(crate) struct Context {
    /// Sorts available in scope
    pub(crate) sorts: HashMap<String, sort::Sort>,
    /// Functions available in-scope
    pub(crate) functions: HashMap<String, fun::FunctionDef>,
    /// How many fresh variables we generated in global context
    pub(crate) fresh_vars_count: usize,
}
