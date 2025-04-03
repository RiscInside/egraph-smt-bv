//// Preprocessing pass for bitwise log book. This code pattern matches against
//// rewrite rules on boolean values and derives bitvector equivalents.

use egglog::{
    ast::{
        call, lit, var, Action, Change, Command, Expr, GenericActions, GenericFact, Literal,
        Rewrite, RewriteKind, Rule, Symbol,
    },
    span,
};

use crate::log::{Log, LogItem};

fn bool_const_to_bv(w_used: &mut bool, val: bool) -> Expr {
    *w_used = true;
    call!("BvAll", [lit!(Literal::Bool(val)), var!("|w|")])
}

fn bool_fcall_to_bv(w_used: &mut bool, sym: Symbol, args: &[egglog::ast::Expr]) -> Option<Expr> {
    Some(call!(
        sym,
        args.iter()
            .map(|expr| bool_expr_to_bv(w_used, expr))
            .collect::<Option<Vec<_>>>()?
    ))
}

fn bool_expr_to_bv(w_used: &mut bool, expr: &Expr) -> Option<Expr> {
    match expr {
        Expr::Lit(..) => None,
        Expr::Var(_, head) => match head.as_str() {
            "w" => None,
            "tt" => Some(bool_const_to_bv(w_used, true)),
            "ff" => Some(bool_const_to_bv(w_used, false)),
            _ => Some(var!(*head)),
        },
        Expr::Call(_, head, args) => match head.as_str() {
            "B" => {
                *w_used = true;
                assert_eq!(args.len(), 1, "expected at most one argument for B");
                let arg = args[0].clone();
                Some(call!("BvAll", [arg, var!("|w|")]))
            }
            "And" => bool_fcall_to_bv(w_used, "BvAnd".into(), &args),
            "Or" => bool_fcall_to_bv(w_used, "BvOr".into(), &args),
            "Not" => bool_fcall_to_bv(w_used, "BvNot".into(), &args),
            "Xor" => bool_fcall_to_bv(w_used, "BvXor".into(), &args),
            _ => None,
        },
    }
}

fn process_rewrite(
    ruleset: Symbol,
    lhs: &Expr,
    rhs: &Expr,
    rewrite_kind: RewriteKind,
) -> Option<Command> {
    let mut width_required = false;
    let lhs = bool_expr_to_bv(&mut width_required, lhs)?;
    let rhs = bool_expr_to_bv(&mut width_required, rhs)?;

    if !width_required {
        return Some(Command::Rewrite(
            ruleset,
            Rewrite {
                span: span!(),
                lhs,
                rhs,
                conditions: vec![],
            },
            rewrite_kind,
        ));
    }

    let mut actions = vec![Action::Union(span!(), var!("|self|"), rhs)];

    match rewrite_kind {
        RewriteKind::Plain => {}
        RewriteKind::Subsuming => {
            let Expr::Call(_, lhs_name, lhs_args) = lhs.clone() else {
                return None;
            };
            actions.push(Action::Change(span!(), Change::Subsume, lhs_name, lhs_args));
        }
        RewriteKind::Replacing => {
            let Expr::Call(_, lhs_name, lhs_args) = lhs.clone() else {
                return None;
            };
            let Expr::Call(_, rhs_name, rhs_args) = lhs.clone() else {
                return None;
            };
            if lhs_name == rhs_name {
                actions.push(Action::Replace(span!(), lhs_name, lhs_args, vec![rhs_args]));
            } else {
                actions.push(Action::Change(span!(), Change::Subsume, lhs_name, lhs_args));
            }
        }
    }

    Some(Command::Rule {
        name: "".into(),
        ruleset: ruleset,
        rule: Rule {
            span: span!(),
            head: GenericActions(actions),
            body: vec![
                GenericFact::Eq(span!(), var!("|self|"), lhs),
                GenericFact::Eq(span!(), var!("|w|"), call!("Width", [var!("|self|")])),
            ],
        },
    })
}

fn process_command(source_command: &Command, generated: &mut Vec<Command>) {
    match source_command {
        Command::Rewrite(
            ruleset,
            Rewrite {
                lhs,
                rhs,
                conditions,
                ..
            },
            subsume,
        ) if conditions.is_empty() => {
            if let Some(cmd) = process_rewrite(*ruleset, lhs, rhs, *subsume) {
                generated.push(cmd);
            }
        }
        Command::BiRewrite(
            ruleset,
            Rewrite {
                lhs,
                rhs,
                conditions,
                ..
            },
        ) if conditions.is_empty() => {
            if let Some(cmd) = process_rewrite(*ruleset, lhs, rhs, RewriteKind::Plain) {
                generated.push(cmd);
            }
            if let Some(cmd) = process_rewrite(*ruleset, rhs, lhs, RewriteKind::Plain) {
                generated.push(cmd);
            }
        }
        _ => {}
    }
}

impl Log {
    pub(crate) fn generate_bv_rules(mut self) -> Log {
        let mut new_commands = vec![];
        for (item, _) in self.items.iter() {
            match item {
                LogItem::Egglog { commands, .. } => {
                    for command in commands {
                        process_command(command, &mut new_commands);
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
