use std::num::NonZeroU32;

use crate::smt2lib::{
    sort::Sort,
    term::{LocalContext, Lowered},
};
use anyhow::{anyhow, bail, Context as _};
use egglog::ast::Expr;
use lazy_static::lazy_static;
use regex::Regex;
use smt2parser::{concrete, visitors::Index, Numeral};

lazy_static! {
    pub(crate) static ref bv_literal_regex: Regex = Regex::new("^bv([0-9]*)$").unwrap();
}

fn digits_to_biguint(digits: impl Iterator<Item = u8>, radix: u8) -> Numeral {
    let mut res = Numeral::from(0 as u32);
    for digit in digits {
        res *= radix;
        res += digit;
    }
    res
}

impl LocalContext<'_> {
    pub(crate) fn lower_constant(
        &mut self,
        constant: &concrete::Constant,
    ) -> anyhow::Result<Lowered> {
        let (value, digits, bits_per_digit) = match constant {
            concrete::Constant::Hexadecimal(vec) => (
                digits_to_biguint(vec.iter().cloned(), 16),
                vec.len(),
                NonZeroU32::new(4).unwrap(),
            ),
            concrete::Constant::Binary(vec) => (
                digits_to_biguint(vec.iter().map(|x| *x as u8), 16),
                vec.len(),
                NonZeroU32::new(1).unwrap(),
            ),
            _ => bail!("Only bitvector constants are supported"),
        };
        let value = Expr::call_no_span(
            "from-string",
            [Expr::lit_no_span(egglog::ast::Symbol::new(format!(
                "{value}"
            )))],
        );

        let digits = NonZeroU32::try_from(u32::try_from(digits).context("Too many digits")?)
            .context("At least one digit expected")?;

        let bits: NonZeroU32 = digits
            .checked_mul(bits_per_digit)
            .ok_or_else(|| anyhow!("Too many digits"))?;

        let expr = Expr::call_no_span("BvConst", [Expr::lit_no_span(bits.get() as i64), value]);

        Ok(Lowered {
            expr,
            sort: Sort::BitVec(bits),
        })
    }

    pub(crate) fn maybe_bv_identifier_constant(
        &mut self,
        value: &str,
        indices: &[Index],
    ) -> anyhow::Result<Option<Lowered>> {
        let [Index::Numeral(val)] = indices else {
            return Ok(None);
        };

        let Some(captures) = (*bv_literal_regex).captures(value) else {
            return Ok(None);
        };

        let (_, [value_as_string]) = captures.extract();
        let value = Expr::call_no_span(
            "from-string",
            [Expr::lit_no_span(egglog::ast::Symbol::new(format!(
                "{value_as_string}"
            )))],
        );

        let width = NonZeroU32::try_from(
            u32::try_from(val).context("Bitvector literal width is too large")?,
        )
        .context("Bit-vector literals can't be empty")?;

        Ok(Some(Lowered {
            expr: Expr::call_no_span("BvConst", [Expr::lit_no_span(width.get() as i64), value]),
            sort: Sort::BitVec(width),
        }))
    }
}
