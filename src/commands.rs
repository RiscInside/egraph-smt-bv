use anyhow::bail;
use egglog::{
    ast::{
        call, lit, var, Action, Change, Command, Expr, GenericActions, GenericFact, Rule,
        RunConfig, Schedule, Schema, Symbol,
    },
    span,
};
use smt2parser::concrete;

use crate::{
    smt2lib::{
        fun::{FunctionDef, FunctionLoweringSpec, FunctionSortCheckSpec},
        sort::Sort,
        term::{LocalContext, Lowered},
    },
    Context,
};

const MAX_TERM_STR_LEN: usize = 60;

fn fun_decl_egglog_command(name: &str, params_len: usize) -> Command {
    Command::Constructor {
        name: name.into(),
        schema: Schema {
            input: std::iter::repeat_n("V".into(), params_len).collect(),
            output: "V".into(),
        },
        cost: None,
        unextractable: true,
        span: span!(),
    }
}

fn saturate_schedule(ruleset: &'static str) -> Schedule {
    Schedule::Saturate(
        span!(),
        Box::new(egglog::ast::GenericSchedule::Run(
            span!(),
            RunConfig {
                ruleset: ruleset.into(),
                until: None,
            },
        )),
    )
}

impl Context {
    pub(crate) fn run_desugar(&mut self) -> anyhow::Result<()> {
        self.run_cmds(vec![Command::RunSchedule(Schedule::Sequence(
            span!(),
            vec![
                saturate_schedule("desugar"),
                saturate_schedule("post-desugar"),
            ],
        ))])
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
            FunctionLoweringSpec::direct(name),
        ));

        Ok(())
    }

    pub(crate) fn declare_fun(
        &mut self,
        name: &str,
        params: &[concrete::Sort],
        sort: &concrete::Sort,
    ) -> anyhow::Result<()> {
        let params = params
            .iter()
            .map(Sort::from_concrete)
            .collect::<Result<Vec<_>, _>>()?;
        let sort = Sort::from_concrete(sort)?;

        let mut commands = vec![fun_decl_egglog_command(name, params.len())];

        if let Sort::BitVec(width) = sort {
            // Add a rule for computing bitvector width
            let res = var!("|res|");
            let args: Vec<Expr> = (0..params.len())
                .map(|i| var!(&format!("|arg{i}|")))
                .collect();

            commands.push(Command::Rule {
                name: format!("{name}-width").into(),
                ruleset: "safe".into(),
                rule: Rule {
                    span: span!(),
                    head: GenericActions(vec![Action::Set(
                        span!(),
                        "Width".into(),
                        vec![res.clone()],
                        lit!(width.get() as i64),
                    )]),
                    body: vec![GenericFact::Eq(span!(), res, call!(name, args))],
                },
            })
        }

        self.text(&format!("### Declaration of `{name}`"))?;
        self.newline()?;
        self.run_cmds(commands)?;
        self.newline()?;

        self.add_fun_mapping(name, params, sort)
    }

    pub(crate) fn define_fun(
        &mut self,
        sig: &concrete::FunctionDec,
        term: &concrete::Term,
    ) -> anyhow::Result<()> {
        let mut param_sorts = vec![];
        let result_sort = Sort::from_concrete(&sig.result)?;

        let smt2context = self.smt2contexts.last_mut().unwrap();
        let commands = {
            let mut local_ctx = LocalContext::new_local(smt2context);
            let mut params_exprs = vec![];

            for (param_name, param_sort) in &sig.parameters {
                let param_sort = Sort::from_concrete(&param_sort)?;
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
                Change::Delete,
                Symbol::new(sig.name.0.to_owned()),
                params_exprs.clone(),
            ));
            let enode_expr = egglog::ast::call!(&sig.name.0, params_exprs);

            vec![
                fun_decl_egglog_command(&sig.name.0, sig.parameters.len()),
                egglog::ast::Command::Rule {
                    name: sig.name.0.to_owned().into(),
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
        self.add_fun_mapping(&sig.name.0, param_sorts, result_sort)?;
        Ok(())
    }

    pub(crate) fn get_value(&mut self, _: &[concrete::Term]) -> anyhow::Result<()> {
        todo!()
    }

    pub(crate) fn handle_smt2lib_command(
        &mut self,
        command: &concrete::Command,
    ) -> anyhow::Result<()> {
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
            } => self.declare_fun(&symbol.0, &parameters, sort),
            DeclareSort { .. } => bail!("User-declared sorts aren't supported"),
            DefineFun { sig, term } => self.define_fun(sig, term),
            DefineFunRec { .. } | DefineFunsRec { .. } => {
                bail!("Recursive functions aren't supported")
            }
            DefineSort { .. } => bail!("Sort synonyms aren't supported"),
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
            GetValue { terms } => self.get_value(&terms),
            Pop { .. } | Push { .. } => bail!("push/pop aren't supported"),
            Reset => bail!("reset isn't supported"),
            ResetAssertions => bail!("reset-assertions isn't supported"),
            SetInfo { .. } => bail!("set-info isn't supported"),
            SetLogic { symbol } => {
                if symbol.0 != "QF_BV" {
                    bail!("Unsupported logic {}", symbol.0);
                }
                Ok(())
            }
            SetOption { .. } => bail!("set-option isn't supported"),
        }
    }
}
