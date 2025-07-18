use std::{num::NonZero, time::Duration};

use anyhow::bail;
use egglog::{
    ast::{
        call, lit, var, Action, Change, Command, Expr, GenericActions, GenericFact, Rule,
        RunConfig, Schedule, Schema, Symbol,
    },
    span,
};
use smt2parser::{
    concrete::{self, Constant, SExpr},
    visitors::AttributeValue,
};

use crate::{
    plan::Plan,
    smt2lib::{
        fun::{FunctionDef, FunctionLoweringSpec, FunctionSortCheckSpec},
        sort::Sort,
        term::{LocalContext, Lowered},
        to_egglog_name,
    },
    Context,
};

const MAX_TERM_STR_LEN: usize = 60;

fn fun_decl_egglog_command(name: Symbol, params_len: usize) -> Command {
    Command::Constructor {
        name,
        schema: Schema {
            input: std::iter::repeat_n("V".into(), params_len).collect(),
            output: "V".into(),
        },
        cost: None,
        unextractable: true,
        span: span!(),
    }
}

mod schedule {
    use super::*;
    pub(crate) fn run(ruleset: &'static str) -> Schedule {
        Schedule::Run(
            span!(),
            RunConfig {
                ruleset: ruleset.into(),
                until: None,
            },
        )
    }

    pub(crate) fn saturate(schedule: Schedule) -> Schedule {
        Schedule::Saturate(span!(), Box::new(schedule))
    }

    pub(crate) fn seq2(schedule1: Schedule, schedule2: Schedule) -> Schedule {
        Schedule::Sequence(span!(), vec![schedule1, schedule2])
    }
}

impl Context {
    pub(crate) fn run_desugar(&mut self) -> anyhow::Result<()> {
        use schedule::*;
        self.run_cmds(vec![Command::RunSchedule(seq2(
            saturate(seq2(run("width"), run("desugar"))),
            run("post-desugar"),
        ))])
    }

    pub(crate) fn smt2lib_context_mut(&mut self) -> &mut crate::smt2lib::Context {
        self.smt2contexts.last_mut().unwrap()
    }

    pub(crate) fn assert_term(&mut self, term: &concrete::Term) -> anyhow::Result<()> {
        self.asserts_so_far += 1;

        let smt2context = self.smt2contexts.last_mut().unwrap();

        let commands = {
            let mut local_ctx = LocalContext::new_global(smt2context);
            let lowered = local_ctx.lower_term(term)?;

            if lowered.sort != Sort::Bool {
                bail!("Boolean sorted value expected for assert");
            }

            let mut egglog_commands = vec![];

            for (let_var, let_def) in std::mem::take(&mut local_ctx.generated_lets) {
                egglog_commands.push(Command::Action(Action::Let(span!(), let_var, let_def)));
            }

            egglog_commands.push(Command::Action(Action::Union(
                span!(),
                lowered.expr,
                var!("tt"),
            )));

            egglog_commands
        };

        // TODO(iurii): there is probably a better way to do this
        let term_str = format!("{}", term);
        let heading = if term_str.len() <= MAX_TERM_STR_LEN {
            format!("### Assertion #{} (`{term_str}`)", self.asserts_so_far)
        } else {
            format!("### Assertion #{}", self.asserts_so_far)
        };

        self.text(&heading)?;
        self.newline()?;
        self.run_cmds(commands)?;
        self.run_desugar()?;
        self.newline()?;

        Ok(())
    }

    pub(crate) fn declare_const(
        &mut self,
        name: &str,
        sort: &concrete::Sort,
    ) -> anyhow::Result<()> {
        self.declare_fun(name, &[], sort)
    }

    pub(crate) fn add_fun_mapping(
        &mut self,
        name: &str,
        egglog_name: Symbol,
        params: Vec<Sort>,
        result: Sort,
    ) -> anyhow::Result<()> {
        let smt2context = self.smt2contexts.last_mut().unwrap();

        let im_rc::hashmap::Entry::Vacant(vacant_entry) =
            smt2context.functions.entry(name.to_owned())
        else {
            bail!("Redefinition of function {name} (overloading is currently unsupported)")
        };

        vacant_entry.insert(FunctionDef::simple(
            FunctionSortCheckSpec::Fixed { params, result },
            FunctionLoweringSpec::direct(egglog_name),
        ));

        Ok(())
    }

    pub(crate) fn declare_fun(
        &mut self,
        name: &str,
        params: &[concrete::Sort],
        sort: &concrete::Sort,
    ) -> anyhow::Result<()> {
        let egglog_name = to_egglog_name(name);
        let params = params
            .iter()
            .map(|concrete| self.smt2lib_context_mut().parse_sort(concrete))
            .collect::<Result<Vec<_>, _>>()?;
        let sort = self.smt2lib_context_mut().parse_sort(sort)?;

        let mut commands = vec![fun_decl_egglog_command(egglog_name, params.len())];

        let width = match sort {
            Sort::Bool => NonZero::<u32>::new(1).unwrap(),
            Sort::BitVec(width) => width,
        };

        // Add a rule for computing width of the expression
        let res = var!("|res|");
        let args: Vec<Expr> = (0..params.len())
            .map(|i| var!(&format!("|arg{i}|")))
            .collect();

        commands.push(Command::Rule {
            name: format!("{name}-width").into(),
            ruleset: "width".into(),
            rule: Rule {
                span: span!(),
                head: GenericActions(vec![Action::Set(
                    span!(),
                    "Width".into(),
                    vec![res.clone()],
                    lit!(width.get() as i64),
                )]),
                body: vec![GenericFact::Eq(
                    span!(),
                    res.clone(),
                    call!(egglog_name, args),
                )],
            },
        });

        // TODO: we should also support uninterpreted functions here, but for now that's not a huge concern
        if params.is_empty() {
            // Add simulation input rule
            commands.push(Command::Rule {
                name: format!("{name}-add-input").into(),
                ruleset: "snitch".into(),
                rule: Rule {
                    span: span!(),
                    head: GenericActions(vec![
                        Action::Set(
                            span!(),
                            "VProxy".into(),
                            vec![res.clone()],
                            call!("proxy", [res.clone(), lit!(width.get() as i64)]),
                        ),
                        Action::Expr(
                            span!(),
                            call!(
                                "solvers-input",
                                [
                                    res.clone(),
                                    lit!(Symbol::from(name)),
                                    lit!(width.get() as i64)
                                ]
                            ),
                        ),
                    ]),
                    body: vec![GenericFact::Eq(
                        span!(),
                        res.clone(),
                        call!(egglog_name, []),
                    )],
                },
            });
        }

        self.text(&format!("### Declaration of `{name}` (`{egglog_name}`"))?;
        self.newline()?;
        self.run_cmds(commands)?;
        self.newline()?;

        self.add_fun_mapping(name, egglog_name, params, sort)
    }

    pub(crate) fn define_fun(
        &mut self,
        sig: &concrete::FunctionDec,
        term: &concrete::Term,
    ) -> anyhow::Result<()> {
        let egglog_name = to_egglog_name(&sig.name.0);
        let keep_functions = self.keep_functions;
        let mut param_sorts = vec![];
        let smt2context = self.smt2lib_context_mut();
        let result_sort = smt2context.parse_sort(&sig.result)?;

        let commands = {
            let mut local_ctx = LocalContext::new_local(smt2context);
            let mut params_exprs = vec![];

            for (param_name, param_sort) in &sig.parameters {
                let param_sort = local_ctx.global.parse_sort(param_sort)?;
                param_sorts.push(param_sort);

                let im_rc::hashmap::Entry::Vacant(vacant_entry) =
                    local_ctx.bindings.entry(param_name.0.clone())
                else {
                    bail!(
                        "Parameter with name {} has been previously declared",
                        param_name.0
                    );
                };

                let param_expr = var!(param_name.0.clone());
                params_exprs.push(param_expr.clone());

                vacant_entry.insert(Lowered {
                    expr: param_expr,
                    sort: param_sort,
                });
            }

            let (_, eclass_expr) = local_ctx.new_fresh();

            let term = local_ctx.lower_term(term)?;
            if term.sort != result_sort {
                bail!(
                    "Unexpected returned sort in {} (expected {}, got {})",
                    &sig.name.0,
                    result_sort,
                    term.sort
                );
            }

            let mut actions = vec![];
            for (let_var, let_def) in std::mem::take(&mut local_ctx.generated_lets) {
                actions.push(Action::Let(span!(), let_var, let_def));
            }
            actions.push(Action::Union(span!(), eclass_expr.clone(), term.expr));
            actions.push(Action::Change(
                span!(),
                if keep_functions {
                    Change::Subsume
                } else {
                    Change::Delete
                },
                egglog_name,
                params_exprs.clone(),
            ));
            let enode_expr = egglog::ast::call!(egglog_name, params_exprs);

            vec![
                fun_decl_egglog_command(egglog_name, sig.parameters.len()),
                egglog::ast::Command::Rule {
                    name: egglog_name,
                    ruleset: "desugar".into(),
                    rule: Rule {
                        span: span!(),
                        head: GenericActions(actions),
                        body: vec![GenericFact::Eq(span!(), eclass_expr, enode_expr)],
                    },
                },
            ]
        };

        self.text(&format!("### Definition of function `{}`", &sig.name.0))?;
        self.newline()?;
        self.run_cmds(commands)?;
        self.newline()?;
        self.add_fun_mapping(&sig.name.0, egglog_name, param_sorts, result_sort)?;
        Ok(())
    }

    pub(crate) fn get_value(&mut self, _: &[concrete::Term]) -> anyhow::Result<()> {
        todo!()
    }

    pub(crate) fn define_sort(
        &mut self,
        symbol: &concrete::Symbol,
        parameters: &[concrete::Symbol],
        sort: &concrete::Sort,
    ) -> anyhow::Result<()> {
        let context = self.smt2lib_context_mut();
        if !parameters.is_empty() {
            bail!("Parametric type synonyms aren't supported")
        }
        let rhs_sort = context.parse_sort(sort)?;
        match context.sorts.entry(symbol.0.clone()) {
            im_rc::hashmap::Entry::Occupied(..) => bail!("Sort {} already defined", symbol.0),
            im_rc::hashmap::Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(rhs_sort);
                Ok(())
            }
        }
    }

    pub(crate) fn set_option(
        &mut self,
        keyword: &str,
        value: &AttributeValue,
    ) -> anyhow::Result<()> {
        match (keyword, value) {
            ("plan", AttributeValue::SExpr(sexprs)) => {
                self.custom_check_sat_plan =
                    Some(Plan::parse(&SExpr::Application(sexprs.clone()))?);
                Ok(())
            }
            ("plan", _) => bail!("Expected plan to be an S-expression"),

            ("blast-solver", AttributeValue::Symbol(symbol)) if symbol.0.as_str() == "true" => {
                self.use_bitblasting_solver = true;
                Ok(())
            }
            ("blast-solver", AttributeValue::Symbol(symbol)) if symbol.0.as_str() == "false" => {
                self.use_bitblasting_solver = false;
                Ok(())
            }
            ("blast-solver", _) => bail!("Expected a boolean argument to `blast-solver`"),

            ("linear-solver", AttributeValue::Symbol(symbol)) if symbol.0.as_str() == "true" => {
                self.use_linear_solver = true;
                Ok(())
            }
            ("linear-solver", AttributeValue::Symbol(symbol)) if symbol.0.as_str() == "false" => {
                self.use_linear_solver = false;
                Ok(())
            }
            ("linear-solver", _) => bail!("Expected a boolean argument to `linear-solver`"),

            ("keep-functions", AttributeValue::Symbol(symbol)) if symbol.0.as_str() == "true" => {
                self.keep_functions = true;
                Ok(())
            }
            ("keep-functions", AttributeValue::Symbol(symbol)) if symbol.0.as_str() == "false" => {
                self.keep_functions = false;
                Ok(())
            }
            ("keep-functions", _) => bail!("Expected a boolean argument to `keep-functions`"),

            ("timeout", AttributeValue::Constant(Constant::Numeral(val))) => {
                self.check_sat_timeout = Some(Duration::from_millis(val.try_into()?));
                Ok(())
            }
            ("timeout", _) => bail!("Expected an integer argument to `timeout`"),

            ("outer-iters", AttributeValue::Constant(Constant::Numeral(val))) => {
                self.outer_iterations = val.try_into()?;
                Ok(())
            }
            ("outer-iters", _) => bail!("Expected an integer argument to `outer-iters`"),

            ("inner-iters", AttributeValue::Constant(Constant::Numeral(val))) => {
                self.inner_iterations = val.try_into()?;
                Ok(())
            }
            ("inner-iters", _) => bail!("Expected an integer argument to `inner-iters`"),

            _ => bail!("Unsupported option {keyword}"),
        }
    }

    pub fn run_smt2lib_command(&mut self, command: &concrete::Command) -> anyhow::Result<()> {
        use concrete::Command::*;
        match command {
            Assert { term } => self.assert_term(term),
            CheckSat => self.check_sat(),
            CheckSatAssuming { .. } => bail!("check-sat-assuming isn't supported"),
            DeclareConst { symbol, sort } => self.declare_const(&symbol.0, sort),
            DeclareDatatype { .. } | DeclareDatatypes { .. } => {
                bail!("Inductive types aren't supported")
            }
            DeclareFun {
                symbol,
                parameters,
                sort,
            } => self.declare_fun(&symbol.0, parameters, sort),
            DeclareSort { .. } => bail!("User-declared sorts aren't supported"),
            DefineFun { sig, term } => self.define_fun(sig, term),
            DefineFunRec { .. } | DefineFunsRec { .. } => {
                bail!("Recursive functions aren't supported")
            }
            DefineSort {
                symbol,
                parameters,
                sort,
            } => self.define_sort(symbol, parameters, sort),
            Echo { message } => {
                println!("\"{message}\"");
                Ok(())
            }
            Exit => std::process::exit(0),
            GetAssertions => bail!("get-assertions isn't supported"),
            GetAssignment => bail!("get-assignment isn't supported"),
            GetInfo { .. } => bail!("get-info isn't supported"),
            GetModel => bail!("get-model isn't supported"),
            GetOption { .. } => bail!("get-option isn't supported"),
            GetProof => bail!("get-proof isn't supported"),
            GetUnsatAssumptions => bail!("get-unsat-assumptions isn't supported"),
            GetUnsatCore => bail!("get-unsat-core isn't supported"),
            GetValue { terms } => self.get_value(terms),
            Pop { .. } | Push { .. } => bail!("push/pop aren't supported"),
            Reset => bail!("reset isn't supported"),
            ResetAssertions => bail!("reset-assertions isn't supported"),
            SetInfo { .. } => Ok(()),
            SetLogic { symbol } => {
                if symbol.0 != "QF_BV" && symbol.0 != "QF_UFBV" {
                    bail!("Unsupported logic {}", symbol.0);
                }
                Ok(())
            }
            SetOption { keyword, value } => self.set_option(&keyword.0, value),
        }
    }
}
