use std::sync::Arc;

use egglog::{
    add_primitives,
    ast::Symbol,
    sort::{FromSort, IntoSort, Sort},
    span, EGraph, Value,
};
use lazy_static::lazy_static;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct SmallBitVec(u64);

#[derive(Debug)]
struct SmallBitVecSort;

macro_rules! lift_u64_unary {
    ($info:expr, $name:literal = |$var:ident| $computation:expr) => {
        add_primitives!(
            $info,
            $name = |v: SmallBitVec, n: i64| -> SmallBitVec {
                {
                    let $var = v.0;
                    SmallBitVec($computation % (1 << n))
                }
            }
        );
    };
}

macro_rules! lift_u64_binary {
    ($info:expr, $name:literal = |$var1:ident, $var2:ident| $computation:expr) => {
        add_primitives!(
            $info,
            $name = |a: SmallBitVec, b: SmallBitVec, n: i64| -> SmallBitVec {
                {
                    let $var1 = a.0;
                    let $var2 = b.0;
                    SmallBitVec($computation % (1u64 << n))
                }
            }
        );
    };
}

lazy_static! {
    static ref SMALL_BV_SORT_NAME: Symbol = "SmallBitVec".into();
}

impl Sort for SmallBitVecSort {
    fn name(&self) -> Symbol {
        *SMALL_BV_SORT_NAME
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn register_primitives(self: std::sync::Arc<Self>, info: &mut egglog::TypeInfo) {
        type T = SmallBitVec;
        lift_u64_unary!(info, "neg" = |a| a.wrapping_neg());
        lift_u64_unary!(info, "not-sbv" = |a| !a);

        lift_u64_binary!(info, "+" = |a, b| a.wrapping_add(b));
        lift_u64_binary!(info, "-" = |a, b| a.wrapping_sub(b));
        lift_u64_binary!(info, "*" = |a, b| a.wrapping_mul(b));
        add_primitives!(
            info,
            "/u" = |a: T, b: T, n: i64| -> T {
                if b.0 == 0 {
                    SmallBitVec(1u64.wrapping_shl(n as u32).wrapping_sub(1))
                } else {
                    SmallBitVec(a.0 / b.0)
                }
            }
        );

        lift_u64_binary!(info, "&" = |a, b| a & b);
        lift_u64_binary!(info, "|" = |a, b| a | b);
        lift_u64_binary!(info, "^" = |a, b| a ^ b);
        lift_u64_binary!(info, "<<" = |a, b| a.wrapping_shl(b as u32));
        // Logical right shift (fills space with zeroes)
        lift_u64_binary!(info, ">>" = |a, b| a.wrapping_shr(b as u32));

        add_primitives!(
            info,
            "<<-int" = |a: T, b: i64| -> T { SmallBitVec(a.0.wrapping_shl(b as u32)) }
        );

        add_primitives!(
            info,
            ">>-int" = |a: T, b: i64| -> T { SmallBitVec(a.0.wrapping_shr(b as u32)) }
        );

        add_primitives!(info, "u<" = |a: T, b: T| -> bool { a < b });
        add_primitives!(info, "u>" = |a: T, b: T| -> bool { a > b });
        add_primitives!(info, "u<=" = |a: T, b: T| -> bool { a <= b });
        add_primitives!(info, "u>=" = |a: T, b: T| -> bool { a >= b });
        add_primitives!(
            info,
            "s<" = |a: T, b: T| -> bool { (a.0 as i64) < (b.0 as i64) }
        );
        add_primitives!(
            info,
            "s>" = |a: T, b: T| -> bool { (a.0 as i64) > (b.0 as i64) }
        );
        add_primitives!(
            info,
            "s<=" = |a: T, b: T| -> bool { (a.0 as i64) <= (b.0 as i64) }
        );
        add_primitives!(
            info,
            "s>=" = |a: T, b: T| -> bool { (a.0 as i64) >= (b.0 as i64) }
        );
        add_primitives!(
            info,
            "from-string" = |a: Symbol| -> Option<SmallBitVec> {
                a.as_str().parse::<u64>().map(SmallBitVec).ok()
            }
        );
        // here `n` is size of bitvector `b` that `a` is prepended to
        add_primitives!(
            info,
            "concat" =
                |a: T, b: T, n: i64| -> T { SmallBitVec(a.0.checked_shl(n as u32).unwrap() | b.0) }
        );
        // same extraction semantics as
        add_primitives!(
            info,
            "extract" = |a: T, n: i64, m: i64| -> T {
                SmallBitVec((a.0 >> m) & (1u64.wrapping_shl(n as u32 - m as u32 + 1) - 1))
            }
        );
    }

    fn extract_term(
        &self,
        _egraph: &EGraph,
        value: Value,
        _extractor: &egglog::extract::Extractor,
        termdag: &mut egglog::TermDag,
    ) -> Option<(egglog::extract::Cost, egglog::Term)> {
        #[cfg(debug_assertions)]
        debug_assert_eq!(value.tag, self.name());

        let SmallBitVec(value) = SmallBitVec::load(self, &value);

        let as_string = termdag.lit(egglog::ast::Literal::String(value.to_string().into()));
        Some((1, termdag.app("from-string".into(), vec![as_string])))
    }
}

impl FromSort for SmallBitVec {
    type Sort = SmallBitVecSort;

    fn load(_sort: &Self::Sort, value: &Value) -> Self {
        SmallBitVec(value.bits)
    }
}

impl IntoSort for SmallBitVec {
    type Sort = SmallBitVecSort;

    fn store(self, sort: &Self::Sort) -> Option<Value> {
        Some(Value {
            #[cfg(debug_assertions)]
            tag: sort.name(),
            bits: self.0,
        })
    }
}

pub(crate) fn register_small_bitvec_sort(egraph: &mut EGraph) {
    egraph
        .add_arcsort(Arc::new(SmallBitVecSort), span!())
        .unwrap();
}
