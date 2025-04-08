//// Log macro handler for bitwise rules. Bitwise rules work with plain booleans and
//// bitvectors and it's potentially error-prone to write same rule twice.

use egglog::{
    ast::{
        Command, Expr, GenericAction, GenericActions, GenericFact, Literal, Macro, ParseError,
        Rule, Sexp, Span, Symbol,
    },
    util::FreshGen,
};
use std::collections::HashSet;

#[derive(Clone, Copy, PartialEq, Eq)]
enum BitwiseBinOp {
    And,
    Or,
    Xor,
}

enum BitwiseExpr {
    Lift(Span, BoxedBitwiseExpr),
    Const(Span, bool),
    Var(Span, Symbol),
    BinOp(Span, BitwiseBinOp, BoxedBitwiseExpr, BoxedBitwiseExpr),
    Not(Span, BoxedBitwiseExpr),
}

type BoxedBitwiseExpr = Box<BitwiseExpr>;

impl BitwiseExpr {
    fn from_sexp<'exp, 'vars>(
        sexp: &'exp Sexp,
        on_var: &mut impl FnMut(Symbol, &'exp Span) -> Result<(), egglog::ast::ParseError>,
    ) -> Result<BoxedBitwiseExpr, egglog::ast::ParseError> {
        Ok(Box::new(match sexp {
            Sexp::List(sexps, span) => match sexps.as_slice() {
                [Sexp::Atom(f, _), x] if f.as_str() == "not" => {
                    BitwiseExpr::Not(span.clone(), Self::from_sexp(&x, on_var)?)
                }
                [Sexp::Atom(f, _), x] if f.as_str() == "lift" => {
                    BitwiseExpr::Lift(span.clone(), Self::from_sexp(&x, on_var)?)
                }
                [Sexp::Atom(f, span), x, y] => BitwiseExpr::BinOp(
                    span.clone(),
                    match f.as_str() {
                        "and" => BitwiseBinOp::And,
                        "or" => BitwiseBinOp::Or,
                        "xor" => BitwiseBinOp::Xor,
                        _ => {
                            return Err(ParseError(
                                span.clone(),
                                "unknown boolean/bitvector function".to_owned(),
                            ))
                        }
                    },
                    Self::from_sexp(&x, on_var)?,
                    Self::from_sexp(&y, on_var)?,
                ),
                _ => {
                    return Err(ParseError(
                        span.clone(),
                        "expected one operand not or two operand and".to_owned(),
                    ))
                }
            },
            Sexp::Atom(var, span) => {
                on_var(*var, span)?;
                BitwiseExpr::Var(span.clone(), *var)
            }
            Sexp::Literal(Literal::Bool(b), span) => BitwiseExpr::Const(span.clone(), *b),
            Sexp::Literal(_, span) => {
                return Err(ParseError(
                    span.clone(),
                    "expected boolean expression".to_owned(),
                ))
            }
        }))
    }

    fn lhs_from_sexp<'exp, 'vars>(
        sexp: &'exp Sexp,
    ) -> Result<(BoxedBitwiseExpr, HashSet<Symbol>), egglog::ast::ParseError> {
        let mut vars = HashSet::new();
        Ok((
            Self::from_sexp(sexp, &mut |v, _| {
                vars.insert(v);
                Ok(())
            })?,
            vars,
        ))
    }

    fn rhs_from_sexp<'exp, 'vars>(
        sexp: &'exp Sexp,
        defined: &HashSet<Symbol>,
    ) -> Result<BoxedBitwiseExpr, egglog::ast::ParseError> {
        Self::from_sexp(sexp, &mut |v, span| {
            if defined.contains(&v) {
                Ok(())
            } else {
                Err(ParseError(
                    span.clone(),
                    format!("Bitwise variable {v} not present in LHS"),
                ))
            }
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BitwiseLoweringMode {
    Bool,
    BV,
    Literal,
}

impl BitwiseLoweringMode {
    /// Promoting expression from one computing egglog boolean to one computing same
    /// boolean within the embedding
    fn literal_embedding(&self, span: &Span, bv_width_var: Symbol, expression: Expr) -> Expr {
        match self {
            BitwiseLoweringMode::Bool => Expr::Call(span.clone(), "B".into(), vec![expression]),
            BitwiseLoweringMode::BV => Expr::Call(
                span.clone(),
                "BvAll".into(),
                vec![expression, Expr::Var(span.clone(), bv_width_var)],
            ),
            BitwiseLoweringMode::Literal => expression,
        }
    }
}

impl BitwiseExpr {
    fn lower_to_egglog(
        &self,
        parser: &mut egglog::ast::Parser,
        bv_width_var: Symbol,
        lowering_mode: BitwiseLoweringMode,
    ) -> Expr {
        match self {
            BitwiseExpr::Lift(span, op) => lowering_mode.literal_embedding(
                span,
                bv_width_var,
                op.lower_to_egglog(parser, bv_width_var, BitwiseLoweringMode::Literal),
            ),
            BitwiseExpr::Const(span, lit) => lowering_mode.literal_embedding(
                span,
                bv_width_var,
                Expr::Lit(span.clone(), Literal::Bool(*lit)),
            ),
            BitwiseExpr::Var(span, name) => Expr::Var(span.clone(), *name),
            BitwiseExpr::BinOp(span, op, lhs, rhs) => {
                let lhs = lhs.lower_to_egglog(parser, bv_width_var, lowering_mode);
                let rhs = rhs.lower_to_egglog(parser, bv_width_var, lowering_mode);
                let name = match (op, lowering_mode) {
                    (BitwiseBinOp::And, BitwiseLoweringMode::Bool) => "And",
                    (BitwiseBinOp::Or, BitwiseLoweringMode::Bool) => "Or",
                    (BitwiseBinOp::Xor, BitwiseLoweringMode::Bool) => "Xor",
                    (BitwiseBinOp::And, BitwiseLoweringMode::BV) => "BvAnd",
                    (BitwiseBinOp::Or, BitwiseLoweringMode::BV) => "BvOr",
                    (BitwiseBinOp::Xor, BitwiseLoweringMode::BV) => "BvXor",
                    (BitwiseBinOp::And, BitwiseLoweringMode::Literal) => "and",
                    (BitwiseBinOp::Or, BitwiseLoweringMode::Literal) => "or",
                    (BitwiseBinOp::Xor, BitwiseLoweringMode::Literal) => "xor",
                };
                Expr::Call(span.clone(), name.into(), vec![lhs, rhs])
            }
            BitwiseExpr::Not(span, op) => {
                let op = op.lower_to_egglog(parser, bv_width_var, lowering_mode);
                let name = match lowering_mode {
                    BitwiseLoweringMode::Bool => "Not",
                    BitwiseLoweringMode::BV => "BvNot",
                    BitwiseLoweringMode::Literal => "not",
                };
                Expr::Call(span.clone(), name.into(), vec![op])
            }
        }
    }
}

fn generate_rule(
    parser: &mut egglog::ast::Parser,
    span: Span,
    lhs: &BitwiseExpr,
    rhses: &[Box<BitwiseExpr>],
    lowering_mode: BitwiseLoweringMode,
    replace: bool,
    ruleset: &'static str,
) -> egglog::ast::Command {
    let target_var = parser.symbol_gen.fresh(&"__rewrite_var".into());
    let bv_width_var = parser.symbol_gen.fresh(&"__bv_width_var".into());
    let target_var_expr = Expr::Var(span.clone(), target_var);

    let lhs = lhs.lower_to_egglog(parser, bv_width_var, lowering_mode);
    let rhses = rhses
        .iter()
        .map(|e| e.lower_to_egglog(parser, bv_width_var, lowering_mode))
        .collect::<Vec<_>>();

    let mut actions: Vec<_> = rhses
        .iter()
        .map(|rhs| GenericAction::Union(span.clone(), target_var_expr.clone(), rhs.clone()))
        .collect();

    // Compute all potentially overlapping expressions for the replace operation
    if replace {
        if let Expr::Call(_, name, args) = &lhs {
            let overlapping: Vec<_> = rhses
                .iter()
                .filter_map(|rhs| match &rhs {
                    Expr::Call(_, rhs_name, rhs_args) if rhs_name == name => Some(rhs_args.clone()),
                    _ => None,
                })
                .collect();

            actions.push(GenericAction::Replace(
                span.clone(),
                *name,
                args.clone(),
                overlapping,
            ));
        }
    }

    let mut facts = vec![GenericFact::Eq(span.clone(), target_var_expr, lhs)];
    if lowering_mode == BitwiseLoweringMode::BV {
        // Add bitwidth condition
        facts.push(GenericFact::Eq(
            span.clone(),
            Expr::Var(span.clone(), bv_width_var),
            Expr::Call(
                span.clone(),
                "Width".into(),
                vec![Expr::Var(span.clone(), target_var)],
            ),
        ));
    }

    Command::Rule {
        name: "".into(),
        ruleset: ruleset.into(),
        rule: Rule {
            span: span.clone(),
            head: GenericActions(actions),
            body: facts,
        },
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum BitwiseMacro {
    Plain,
    Replacing,
    Bi,
    Unsafe,
    BiUnsafe,
}

impl Macro<Vec<Command>> for BitwiseMacro {
    fn name(&self) -> egglog::ast::Symbol {
        match self {
            BitwiseMacro::Plain => "bw-rewrite",
            BitwiseMacro::Replacing => "bw-replace",
            BitwiseMacro::Bi => "bw-birewrite",
            BitwiseMacro::Unsafe => "bw-rewrite-unsafe",
            BitwiseMacro::BiUnsafe => "bw-birewrite-unsafe",
        }
        .into()
    }

    fn parse(
        &self,
        args: &[Sexp],
        span: egglog::ast::Span,
        parser: &mut egglog::ast::Parser,
    ) -> Result<Vec<Command>, egglog::ast::ParseError> {
        // Allow optionally specifiying rule name
        let [lhs, alternative_forms @ ..] = args else {
            return Err(ParseError(
                span,
                format!("usage: ({} \"name\"? <lhs> <rhs>*)", self.name()),
            ));
        };

        let (lhs, vars) = BitwiseExpr::lhs_from_sexp(lhs)?;

        if let BitwiseExpr::Lift(..) | BitwiseExpr::Const(..) | BitwiseExpr::Var(..) = *lhs {
            return Err(ParseError(
                span,
                "expected call on LHS of bitwise rule".to_owned(),
            ));
        }

        let rhses = alternative_forms
            .iter()
            .map(|e| BitwiseExpr::rhs_from_sexp(e, &vars))
            .collect::<Result<Vec<_>, _>>()?;

        let ruleset = match *self {
            BitwiseMacro::BiUnsafe | BitwiseMacro::Unsafe => "unsafe",
            BitwiseMacro::Replacing => "fold",
            BitwiseMacro::Plain | BitwiseMacro::Bi => "safe",
        };

        let replace = *self == BitwiseMacro::Replacing;
        macro_rules! gen_rule {
            ($lhs:expr => $rhses:expr; $mode:ident) => {
                generate_rule(
                    parser,
                    span.clone(),
                    $lhs,
                    $rhses,
                    BitwiseLoweringMode::$mode,
                    replace,
                    ruleset,
                )
            };
        }

        let commands = match self {
            BitwiseMacro::Plain | BitwiseMacro::Replacing | BitwiseMacro::Unsafe => vec![
                gen_rule!(&lhs => &rhses; Bool),
                gen_rule!(&lhs => &rhses; BV),
            ],
            BitwiseMacro::Bi | BitwiseMacro::BiUnsafe => {
                if rhses.len() != 1 {
                    return Err(ParseError(
                        span,
                        "expected one (and only) RHS for bw-birewrite".to_owned(),
                    ));
                }

                let lhses = [lhs];
                vec![
                    gen_rule!(&lhses[0] => &rhses; Bool),
                    gen_rule!(&lhses[0] => &rhses; BV),
                    gen_rule!(&rhses[0] => &lhses; Bool),
                    gen_rule!(&rhses[0] => &lhses; BV),
                ]
            }
        };

        Ok(commands)
    }
}
