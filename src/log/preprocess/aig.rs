//// Preprocessing pass for AIG log book. This code pattern matches against
//// rewrite rules on boolean values and derives value equivalents.

use egglog::ast::{
    Action, Change, Command, Expr, GenericActions, GenericFact, Literal, Rewrite, Rule, Symbol,
    DUMMY_SPAN,
};

use crate::log::{Log, LogItem};

fn bool_const_to_bv(w_used: &mut bool, val: bool) -> Expr {
    *w_used = true;
    Expr::call_no_span(
        "BvAll",
        vec![
            Expr::lit_no_span(Literal::Bool(val)),
            Expr::var_no_span("|w|"),
        ],
    )
}

fn bool_fcall_to_bv(w_used: &mut bool, sym: Symbol, args: &[egglog::ast::Expr]) -> Option<Expr> {
    Some(Expr::call_no_span(
        sym,
        args.iter()
            .map(|expr| bool_expr_to_bv(w_used, expr))
            .collect::<Option<Vec<_>>>()?,
    ))
}

fn bool_expr_to_bv(w_used: &mut bool, expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::Lit(..) => None,
        Expr::Var(_, head) => match head.as_str() {
            "w" => None,
            "tt" => Some(bool_const_to_bv(w_used, true)),
            "ff" => Some(bool_const_to_bv(w_used, false)),
            _ => Some(Expr::var_no_span(*head)),
        },
        Expr::Call(_, head, args) => match head.as_str() {
            "B" => {
                *w_used = true;
                assert_eq!(args.len(), 1, "expected at most one argument for B");
                let arg = args[0].clone();
                Some(Expr::call_no_span(
                    "BvAll",
                    vec![arg, Expr::var_no_span("|w|")],
                ))
            }
            "And" => bool_fcall_to_bv(w_used, "BvAnd".into(), &args),
            "Or" => bool_fcall_to_bv(w_used, "BvOr".into(), &args),
            "Not" => bool_fcall_to_bv(w_used, "BvNot".into(), &args),
            "Xor" => bool_fcall_to_bv(w_used, "BvXor".into(), &args),
            _ => None,
        },
    }
}

fn process_command(command: &Command) -> Option<Command> {
    let Command::Rewrite(
        ruleset,
        Rewrite {
            lhs,
            rhs,
            conditions,
            ..
        },
        subsume,
    ) = command
    else {
        return None;
    };

    // No support for condition at the moment
    if conditions.len() > 0 {
        return None;
    }

    let mut width_required = false;
    let lhs = bool_expr_to_bv(&mut width_required, lhs)?;
    let rhs = bool_expr_to_bv(&mut width_required, rhs)?;

    if !width_required {
        return Some(Command::Rewrite(
            *ruleset,
            Rewrite {
                span: DUMMY_SPAN.clone(),
                lhs,
                rhs,
                conditions: vec![],
            },
            *subsume,
        ));
    }

    let mut actions = vec![Action::Union(
        DUMMY_SPAN.clone(),
        Expr::var_no_span("|self|"),
        rhs,
    )];

    if *subsume {
        let Expr::Call(_, lhs_name, lhs_args) = lhs.clone() else {
            return None;
        };
        actions.push(Action::Change(
            DUMMY_SPAN.clone(),
            Change::Subsume,
            lhs_name,
            lhs_args,
        ));
    }

    Some(Command::Rule {
        name: "".into(),
        ruleset: *ruleset,
        rule: Rule {
            span: DUMMY_SPAN.clone(),
            head: GenericActions(actions),
            body: vec![
                GenericFact::Eq(DUMMY_SPAN.clone(), vec![Expr::var_no_span("|self|"), lhs]),
                GenericFact::Eq(
                    DUMMY_SPAN.clone(),
                    vec![
                        Expr::var_no_span("|w|"),
                        Expr::call_no_span("Width", vec![Expr::var_no_span("|self|")]),
                    ],
                ),
            ],
        },
    })
}

impl Log {
    pub(crate) fn generate_aig_rules(mut self) -> Log {
        let mut new_commands = vec![];
        for (item, _) in self.items.iter() {
            match item {
                LogItem::Egglog { commands, .. } => {
                    for command in commands {
                        if let Some(generated_bv_rewrite) = process_command(command) {
                            new_commands.push(generated_bv_rewrite);
                        }
                    }
                }
                _ => {}
            }
        }

        self.newline();
        self.add_text_line("### Lifting boolean AIG rules to bitwise bitvector operations");
        self.add_text_line(
            &format!("The rules after this point are generated automatically from boolean rules. See code for the generator in `{}`.", file!())
        );
        self.newline();
        self.add_generated_code(new_commands);
        self.newline();

        self
    }
}
