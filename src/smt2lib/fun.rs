use crate::smt2lib::sort::Sort;
use anyhow::{bail, Context as _};
use egglog::{
    ast::{Expr, Symbol},
    call, lit, var,
};
use std::{fmt::Display, num::NonZeroU32};

use super::term::Lowered;

/// Description how function application should be typechecked
#[derive(Clone)]
pub(crate) enum FunctionSortCheckSpec {
    /// Most straightforward type of declaration - give me a list of arguments
    /// with [`FunctionDecl::Fixed::args`] sorts and I will return the result of
    /// [`FunctionDecl::Fixed::result`] sort. This is used for user-defined
    /// functions.
    Fixed { params: Vec<Sort>, result: Sort },
    /// Boolean fold - combine a bunch of boolean arguments together and return
    /// a boolean. Require at least one operand
    BooleanFold,
    /// Unary operation on bitvectors
    BVUnary,
    /// Binary operator on identical length bitvectors
    BVBinary,
    /// Identical bitvector fold - combine a bunch of bitvectors together and
    /// return a boolean. Require at least one operand
    IdenticalBVFold,
    /// Comparison operation on two bitvectors
    BVCompare,
    /// Concatenation - add lengths of bitvectors up
    Concat,
    /// Bitvector extraction/slicing with two indices
    Extract,
    /// Bitvector rotation
    Rotate,
    /// Repetition - multiply bitvector length by an index
    Repeat,
    /// Extension - adding first index to the length of the bitvector argument
    Extension,
    /// If-then-else. First parameter is a boolean, next two parameters are
    /// values of the same sort, resulting sort is the same as both arguments
    Ite,
    /// Comparison of n values, all of the same/different sorts
    EqualOrDistinct,
}

impl FunctionSortCheckSpec {
    pub(crate) fn fixed(
        params: impl IntoIterator<Item = Sort>,
        result: Sort,
    ) -> FunctionSortCheckSpec {
        FunctionSortCheckSpec::Fixed {
            params: params.into_iter().collect(),
            result,
        }
    }
}

/// Description of how function application should be lowered into egglog.
/// Complex functions that require and chaining/pairwise should be lowered
/// as unary functions on variadic lists and converted into desugared forms
/// within egglog - this allows us to not duplicate user-provided terms.
#[derive(Clone)]
pub(crate) enum FunctionLoweringSpec {
    /// Lower directly as n-ary function application. This should be used
    /// for most operations where arity is fixed.
    Direct { symbol: Symbol },
    /// Lower as a left-associative fold.
    LeftAssociative { symbol: Symbol },
    /// Lower as a right-associative fold.
    RightAssociative { symbol: Symbol },
    /// Lower as unary function application with a variadic argument list
    Variadic { symbol: Symbol },
    /// Lower as a variable
    Variable { symbol: Symbol },
}

impl FunctionLoweringSpec {
    pub(crate) fn direct(name: impl Into<Symbol>) -> FunctionLoweringSpec {
        FunctionLoweringSpec::Direct {
            symbol: name.into(),
        }
    }

    pub(crate) fn left_associative(name: &str) -> FunctionLoweringSpec {
        FunctionLoweringSpec::LeftAssociative {
            symbol: name.into(),
        }
    }

    pub(crate) fn right_associative(name: &str) -> FunctionLoweringSpec {
        FunctionLoweringSpec::RightAssociative {
            symbol: name.into(),
        }
    }

    pub(crate) fn variadic(name: &str) -> FunctionLoweringSpec {
        FunctionLoweringSpec::Variadic {
            symbol: name.into(),
        }
    }

    pub(crate) fn variable(name: &str) -> FunctionLoweringSpec {
        FunctionLoweringSpec::Variable {
            symbol: name.into(),
        }
    }
}

#[derive(Clone)]
pub(crate) struct FunctionDef {
    /// Number of indices expected. This should be 0 for normal functions
    pub(crate) expected_indices: usize,
    /// Function typechecking spec
    pub(crate) sort_check: FunctionSortCheckSpec,
    /// Function lowering spec
    pub(crate) lowering: FunctionLoweringSpec,
}

impl FunctionDef {
    pub(crate) fn simple(
        sort_check: FunctionSortCheckSpec,
        lowering: FunctionLoweringSpec,
    ) -> FunctionDef {
        FunctionDef {
            expected_indices: 0,
            sort_check,
            lowering,
        }
    }
}

fn expect_one_arg<'a>(name: &str, args: &'a [Lowered]) -> anyhow::Result<&'a Lowered> {
    if args.len() != 1 {
        bail!(
            "Expected one argument for {name} (got {} arguments instead)",
            args.len()
        );
    }
    Ok(&args[0])
}

fn expect_two_args<'a>(
    name: &str,
    args: &'a [Lowered],
) -> anyhow::Result<(&'a Lowered, &'a Lowered)> {
    if args.len() != 2 {
        bail!(
            "Expected two arguments for {name} (got {} arguments instead)",
            args.len()
        );
    }
    Ok((&args[0], &args[1]))
}

fn expect_three_args<'a>(
    name: &str,
    args: &'a [Lowered],
) -> anyhow::Result<(&'a Lowered, &'a Lowered, &'a Lowered)> {
    if args.len() != 3 {
        bail!(
            "Expected three arguments for {name} (got {} arguments instead)",
            args.len()
        );
    }
    Ok((&args[0], &args[1], &args[2]))
}

fn expect_some_args(name: &str, args: &[Lowered]) -> anyhow::Result<()> {
    if args.is_empty() {
        bail!("Expected at least one argument for {name}");
    }
    Ok(())
}

fn expect_n_args(name: &str, args: &[Lowered], count: usize) -> anyhow::Result<()> {
    if args.len() != count {
        if count == 1 {
            bail!(
                "Expected 1 argument for {name} (got {} instead)",
                args.len()
            );
        } else {
            bail!(
                "Expected {} arguments for {name} (got {} instead)",
                count,
                args.len()
            );
        }
    }
    Ok(())
}

struct ArgNo(usize);

impl Display for ArgNo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 % 10 {
            0 => write!(f, "{}st", self.0 + 1),
            1 => write!(f, "{}nd", self.0 + 1),
            2 => write!(f, "{}rd", self.0 + 1),
            _ => write!(f, "{}th", self.0 + 1),
        }
    }
}

fn expect_bitvector(name: &str, argno: usize, arg: &Lowered) -> anyhow::Result<NonZeroU32> {
    match arg.sort {
        Sort::BitVec(width) => Ok(width),
        _ => bail!(
            "Expected a term of sort (_ BitVec ?) for {} argument of {name} (got {} instead)",
            ArgNo(argno),
            arg.sort
        ),
    }
}

fn expect_sort(name: &str, argno: usize, arg: &Lowered, sort: Sort) -> anyhow::Result<()> {
    if arg.sort != sort {
        bail!(
            "Expected a term of sort {sort} for {} argument of {name} (got {} instead)",
            ArgNo(argno),
            arg.sort
        );
    }
    Ok(())
}

fn get_u32_index(
    name: &str,
    idx: usize,
    indices: &[smt2parser::visitors::Index],
) -> anyhow::Result<u32> {
    let smt2parser::visitors::Index::Numeral(val) = &indices[idx] else {
        bail!("Indices to {name} must be integers");
    };
    val.try_into().context("Index out of 32 bit range")
}

fn get_non_zero_u32_index(
    name: &str,
    idx: usize,
    indices: &[smt2parser::visitors::Index],
) -> anyhow::Result<NonZeroU32> {
    get_u32_index(name, idx, indices)?
        .try_into()
        .context("Non-zero index value expected")
}

pub(crate) fn check_application(
    name: &str,
    spec: &FunctionSortCheckSpec,
    args: &[Lowered],
    indices: &[smt2parser::visitors::Index],
) -> anyhow::Result<Sort> {
    match spec {
        FunctionSortCheckSpec::Fixed { params, result } => {
            expect_n_args(name, args, params.len())?;
            for (i, (expected, actual)) in params.iter().zip(args.iter()).enumerate() {
                expect_sort(name, i, actual, *expected)?;
            }
            Ok(*result)
        }
        FunctionSortCheckSpec::BooleanFold => {
            expect_some_args(name, args)?;
            for (i, arg) in args.iter().enumerate() {
                expect_sort(name, i, arg, Sort::Bool)?;
            }
            Ok(Sort::Bool)
        }
        FunctionSortCheckSpec::BVUnary => {
            let arg = expect_one_arg(name, args)?;
            let _ = expect_bitvector(name, 0, arg)?;
            Ok(arg.sort)
        }
        FunctionSortCheckSpec::BVBinary => {
            let (lhs, rhs) = expect_two_args(name, args)?;
            expect_bitvector(name, 0, lhs)?;
            expect_sort(name, 1, rhs, lhs.sort)?;
            Ok(lhs.sort)
        }
        FunctionSortCheckSpec::IdenticalBVFold => {
            expect_some_args(name, args)?;
            let width = expect_bitvector(name, 0, &args[0])?;
            for (i, arg) in args.iter().enumerate() {
                expect_sort(name, i, arg, Sort::BitVec(width))?;
            }
            Ok(Sort::BitVec(width))
        }
        FunctionSortCheckSpec::BVCompare => {
            let (lhs, rhs) = expect_two_args(name, args)?;
            expect_bitvector(name, 0, lhs)?;
            expect_sort(name, 1, rhs, lhs.sort)?;
            Ok(Sort::Bool)
        }
        FunctionSortCheckSpec::Concat => {
            expect_some_args(name, args)?;
            let mut width = expect_bitvector(name, 0, &args[0])?;
            for (i, arg) in args.iter().enumerate().skip(1) {
                let extra_width = expect_bitvector(name, i, arg)?;
                width = width
                    .checked_add(extra_width.get())
                    .context("Concatenated bitvector is too big (length >= 2^32)")?;
            }
            Ok(Sort::BitVec(width))
        }
        FunctionSortCheckSpec::Extract => {
            let arg = expect_one_arg(name, args)?;
            let width = expect_bitvector(name, 0, arg)?;
            let i = get_u32_index(name, 0, indices)?;
            let j = get_u32_index(name, 1, indices)?;
            if i >= width.get() || j > i {
                bail!("Indices {i} {j} are out of range for {name} on {width} bit bitvecteor");
            }

            Ok(Sort::BitVec(NonZeroU32::new(i - j + 1).unwrap()))
        }
        FunctionSortCheckSpec::Repeat => {
            let arg = expect_one_arg(name, args)?;
            let width = expect_bitvector(name, 0, arg)?;
            let n: NonZeroU32 = get_non_zero_u32_index(name, 0, indices)?;

            Ok(Sort::BitVec(n.checked_mul(width).context(
                "Repated bitvector is too big for the 2^32 range",
            )?))
        }
        FunctionSortCheckSpec::Rotate => {
            let arg = expect_one_arg(name, args)?;
            let width = expect_bitvector(name, 0, arg)?;
            get_u32_index(name, 0, indices)?;
            Ok(Sort::BitVec(width))
        }
        FunctionSortCheckSpec::Extension => {
            let arg = expect_one_arg(name, args)?;
            let width = expect_bitvector(name, 0, arg)?;
            let extra_bits = get_u32_index(name, 0, indices)?;
            Ok(Sort::BitVec(
                width
                    .checked_add(extra_bits)
                    .context("Extended bitvector is too big")?,
            ))
        }
        FunctionSortCheckSpec::Ite => {
            let (cond, e1, e2) = expect_three_args(name, args)?;
            expect_sort(name, 0, cond, Sort::Bool)?;
            expect_sort(name, 2, e2, e1.sort)?;
            Ok(e1.sort)
        }
        FunctionSortCheckSpec::EqualOrDistinct => {
            expect_some_args(name, args)?;
            let sort = args[0].sort;
            for (i, arg) in args.iter().enumerate() {
                expect_sort(name, i, arg, sort)?;
            }
            Ok(Sort::Bool)
        }
    }
}

fn left_associative_fold(args: Vec<Lowered>, sym: Symbol) -> Expr {
    args.into_iter()
        .map(|arg| arg.expr)
        .reduce(|lhs, rhs| call!(sym, [lhs, rhs]))
        .unwrap()
}

fn right_associative_fold(args: Vec<Lowered>, sym: Symbol) -> Expr {
    args.into_iter()
        .rev()
        .map(|arg| arg.expr)
        .reduce(|rhs, lhs| call!(sym, [lhs, rhs]))
        .unwrap()
}

fn vararg_list(args: Vec<Lowered>) -> Expr {
    args.into_iter().rev().fold(call!("VSNil", []), |acc, arg| {
        call!("VSCons", [arg.expr, acc])
    })
}

fn egglog_for_indices(indices: &[smt2parser::visitors::Index]) -> impl Iterator<Item = Expr> + '_ {
    indices.iter().map(|index| match index {
        smt2parser::visitors::Index::Numeral(big_uint) => {
            let smol_int: u32 = big_uint.try_into().unwrap();
            lit!(smol_int as i64)
        }
        smt2parser::visitors::Index::Symbol(sym) => {
            lit!(egglog::ast::Symbol::new(&sym.0))
        }
    })
}

pub(crate) fn egglog_for_application(
    spec: &FunctionLoweringSpec,
    args: Vec<Lowered>,
    indices: &[smt2parser::visitors::Index],
) -> Expr {
    match spec {
        FunctionLoweringSpec::Direct { symbol } => call!(
            *symbol,
            egglog_for_indices(indices).chain(args.into_iter().map(|arg| arg.expr))
        ),
        FunctionLoweringSpec::LeftAssociative { symbol } => left_associative_fold(args, *symbol),
        FunctionLoweringSpec::RightAssociative { symbol } => right_associative_fold(args, *symbol),
        FunctionLoweringSpec::Variadic { symbol } => call!(
            *symbol,
            egglog_for_indices(indices).chain(std::iter::once(vararg_list(args)))
        ),
        FunctionLoweringSpec::Variable { symbol } => var!(*symbol),
    }
}
