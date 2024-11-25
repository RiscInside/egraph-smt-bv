use self::fun::egglog_for_application;
use crate::smt2lib::{fun, sort::Sort, Context};
use anyhow::{bail, Ok};
use im_rc::HashMap;
use smt2parser::{concrete, visitors::Index};

/// A term lowered into egglog
#[derive(Clone)]
pub(crate) struct Lowered {
    pub(crate) expr: egglog::ast::Expr,
    pub(crate) sort: Sort,
}

pub(crate) struct LocalContext<'ctx> {
    /// Pointer to the smt2 context
    pub(crate) global: &'ctx mut Context,
    /// Symbol table stores both the type and the egglog expression used to
    /// refer to the variable (typically a symbol)
    pub(crate) bindings: HashMap<String, Lowered>,
    /// All let statements are flattened into a single list of let actions
    pub(crate) generated_lets: Vec<(egglog::ast::Symbol, egglog::ast::Expr)>,
    /// Local fresh variables count (for fresh variable generation)
    pub(crate) fresh_vars_count: usize,
    /// Boolean indicating if lowering happens in global context
    pub(crate) global_lowering: bool,
}

impl<'ctx> LocalContext<'ctx> {
    /// Create local context for lowering a global term. This can be used for
    /// asseritons.
    pub(crate) fn new_global(global: &'ctx mut Context) -> LocalContext<'ctx> {
        let fresh_vars_count = global.fresh_vars_count;
        LocalContext {
            global,
            bindings: HashMap::new(),
            generated_lets: vec![],
            fresh_vars_count,
            global_lowering: true,
        }
    }

    /// Create a local context for lowering a local term (with local let defs)
    pub(crate) fn new_local(global: &'ctx mut Context) -> LocalContext<'ctx> {
        LocalContext {
            global,
            bindings: HashMap::new(),
            generated_lets: vec![],
            fresh_vars_count: 0,
            global_lowering: false,
        }
    }
}

impl Drop for LocalContext<'_> {
    fn drop(&mut self) {
        if self.global_lowering {
            // Make sure other instances of local lowering won't reuse variable
            // identifiers
            self.global.fresh_vars_count = self.fresh_vars_count;
        }
    }
}

fn parse_qual_id<'a>(
    identifier: &'a concrete::QualIdentifier,
) -> anyhow::Result<(&'a str, &'a [Index], Option<Sort>)> {
    let (name, indices): (_, &[Index]) = match identifier {
        concrete::QualIdentifier::Simple { identifier }
        | concrete::QualIdentifier::Sorted { identifier, .. } => match identifier {
            concrete::Identifier::Simple { symbol } => (&symbol.0, &[]),
            concrete::Identifier::Indexed { symbol, indices } => (&symbol.0, indices),
        },
    };
    let expected_sort = match identifier {
        concrete::QualIdentifier::Simple { .. } => None,
        concrete::QualIdentifier::Sorted { sort, .. } => Some(Sort::from_concrete(sort)?),
    };

    Ok((name, indices, expected_sort))
}

impl LocalContext<'_> {
    pub(crate) fn lower_app(
        &mut self,
        name: &str,
        indices: &[Index],
        arguments: &[concrete::Term],
    ) -> anyhow::Result<Lowered> {
        let arguments = arguments
            .iter()
            .map(|arg| self.lower_term(arg))
            .collect::<Result<Vec<_>, _>>()?;

        let Some(function_def) = self.global.functions.get(name) else {
            bail!("No function with the name {name} in the current context");
        };

        if function_def.expected_indices != indices.len() {
            bail!(
                "Expected {} indices for {name} (got {})",
                function_def.expected_indices,
                indices.len()
            );
        }

        let sort = fun::check_application(name, &function_def.sort_check, &arguments, indices)?;

        Ok(Lowered {
            expr: egglog_for_application(&function_def.lowering, arguments, indices),
            sort,
        })
    }

    pub(crate) fn lower_id_or_app(
        &mut self,
        identifier: &concrete::QualIdentifier,
        arguments: &[concrete::Term],
    ) -> anyhow::Result<Lowered> {
        let (name, indices, expected_sort) = parse_qual_id(identifier)?;

        let lowered = match self.bindings.get(name) {
            Some(result) => {
                if !arguments.is_empty() {
                    bail!("No arguments expected for variable {name}");
                }
                result.clone()
            }
            None => match self.maybe_bv_identifier_constant(name, indices)? {
                Some(val) => val,
                None => self.lower_app(name, indices, arguments)?,
            },
        };

        if let Some(expected_sort) = expected_sort {
            if lowered.sort != expected_sort {
                bail!("Sort mismatch for the sorted identifier `(as {name} {expected_sort})` (got {})", lowered.sort);
            }
        }

        Ok(lowered)
    }

    pub(crate) fn new_fresh(&mut self) -> (egglog::ast::Symbol, egglog::ast::Expr) {
        let fresh_var_index = self.fresh_vars_count;
        self.fresh_vars_count += 1;
        let egglog_name = egglog::ast::Symbol::new(format!("|{fresh_var_index}|"));
        (egglog_name, egglog::ast::Expr::var_no_span(egglog_name))
    }

    pub(crate) fn lower_let(
        &mut self,
        var_bindings: &[(concrete::Symbol, concrete::Term)],
        term: &concrete::Term,
    ) -> anyhow::Result<Lowered> {
        let mut new_env = self.bindings.clone();
        for (concrete::Symbol(name, ..), term) in var_bindings {
            let lowered = self.lower_term(term)?;
            let lowered_sort = lowered.sort;

            let (egglog_name, var_expr) = self.new_fresh();
            self.generated_lets.push((egglog_name, lowered.expr));
            new_env.insert(
                name.clone(),
                Lowered {
                    expr: var_expr,
                    sort: lowered_sort,
                },
            );
        }

        std::mem::swap(&mut new_env, &mut self.bindings);
        let lowered = self.lower_term(term)?;
        std::mem::swap(&mut new_env, &mut self.bindings);
        Ok(lowered)
    }

    pub(crate) fn lower_term(&mut self, term: &concrete::Term) -> anyhow::Result<Lowered> {
        match term {
            concrete::Term::Constant(constant) => self.lower_constant(constant),
            concrete::Term::QualIdentifier(identifier) => self.lower_id_or_app(identifier, &[]),
            concrete::Term::Application {
                qual_identifier,
                arguments,
            } => self.lower_id_or_app(qual_identifier, &arguments),
            concrete::Term::Let { var_bindings, term } => self.lower_let(var_bindings, term),
            concrete::Term::Forall { .. } | concrete::Term::Exists { .. } => {
                bail!("Quantifiers aren't supported by the solver")
            }
            concrete::Term::Match { .. } => {
                bail!("Inductive types aren't supported by the solver")
            }
            concrete::Term::Attributes { .. } => {
                bail!("Attributes aren't supported by the solver")
            }
        }
    }
}
