use std::num::NonZeroU32;

use anyhow::{bail, Context as _};
use smt2parser::concrete;
use std::fmt::Display;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Sort {
    Bool,
    BitVec(NonZeroU32),
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::BitVec(non_zero) => write!(f, "(_ BitVec {})", non_zero),
        }
    }
}

impl Sort {
    /// Parses sort from a concrete syntax tree
    pub(crate) fn from_concrete(concrete: &concrete::Sort) -> anyhow::Result<Sort> {
        match concrete {
            concrete::Sort::Simple {
                identifier: concrete::Identifier::Simple { symbol },
            } if symbol.0 == "Bool" => Ok(Sort::Bool),
            concrete::Sort::Simple {
                identifier: concrete::Identifier::Indexed { symbol, indices },
            } if symbol.0 == "BitVec" => {
                if indices.len() != 1 {
                    bail!("BitVec sort only has one index");
                }
                let smt2parser::visitors::Index::Numeral(width) = &indices[0] else {
                    bail!("BitVec's only index should be integer width of the bitvector - variable-length bitvectors aren't yet supported");
                };
                let width: u32 = width.try_into().context("Bitvectors over 2^32 in length aren't supported (what kind of hw design do you have there?)")?;
                let width: NonZeroU32 = width
                    .try_into()
                    .context("Zero-length bitvectors aren't allowed")?;
                Ok(Sort::BitVec(width))
            }
            _ => {
                bail!("Only Bool and BitVec sorts are supported")
            }
        }
    }
}