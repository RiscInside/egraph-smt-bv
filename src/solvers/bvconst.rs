use egglog::{
    add_primitives,
    ast::Literal,
    sort::{FromSort, IntoSort, Sort},
    util::IndexSet,
    Value,
};
use num_bigint::BigUint;

use crate::solvers::SolversRef;

pub(crate) struct BvConstSort {
    solvers: SolversRef,
}

impl BvConstSort {
    pub(crate) fn new(solvers: SolversRef) -> Self {
        Self { solvers }
    }
}

impl std::fmt::Debug for BvConstSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BvConstSort").finish()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) struct BvConst(pub(crate) BigUint);

impl BvConst {
    fn wrap(value: BigUint, width: i64) -> Self {
        BvConst(value & ((BigUint::from(1u32) << width) - BigUint::from(1u32)))
    }
}

type C = BvConst;

pub(crate) type BvConstTable = IndexSet<BvConst>;

impl Sort for BvConstSort {
    fn name(&self) -> egglog::ast::Symbol {
        "BvConstSort".into()
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn register_primitives(self: std::sync::Arc<Self>, info: &mut egglog::TypeInfo) {
        type Opt<T = ()> = Option<T>;

        add_primitives!(
            info,
            "bvconst-from-string" = |a: Symbol| -> Opt<C> { a.as_str().parse().map(BvConst).ok() }
        );
        add_primitives!(
            info,
            "negate" = |a: C, w: i64| -> C {
                if a.0.bits() == 0 {
                    a
                } else {
                    BvConst((BigUint::from(1u32) << w) - a.0)
                }
            }
        );
        add_primitives!(
            info,
            "not-bv" = |a: C, w: i64| -> C {
                BvConst(((BigUint::from(1u32) << w) - BigUint::from(1u32)) - a.0)
            }
        );
        add_primitives!(
            info,
            "+" = |a: C, b: C, w: i64| -> C { BvConst::wrap(a.0 + b.0, w) }
        );
        add_primitives!(
            info,
            "*" = |a: C, b: C, w: i64| -> C { BvConst::wrap(a.0 * b.0, w) }
        );
        add_primitives!(info, "&" = |a: C, b: C| -> C { BvConst(a.0 & b.0) });
        add_primitives!(
            info,
            "i64-shl" = |a: C, rhs: i64, w: i64| -> C { BvConst::wrap(a.0 << rhs, w) }
        );
        add_primitives!(
            info,
            "concat" = |a: C, b: C, bwidth: i64| -> C { BvConst(a.0 << bwidth | b.0) }
        );
        add_primitives!(
            info,
            "extract" = |i: i64, j: i64, a: C| -> C { BvConst::wrap(a.0 >> j, i + 1 - j) }
        );
        add_primitives!(
            info,
            "exceeds-bitwidth" =
                |a: C, w: i64| -> Opt { Some(()).filter(|_| a.0.bits() > (w as u64)) }
        );
    }

    fn extract_term(
        &self,
        _egraph: &egglog::EGraph,
        value: egglog::Value,
        _extractor: &egglog::extract::Extractor,
        termdag: &mut egglog::TermDag,
    ) -> Option<(egglog::extract::Cost, egglog::Term)> {
        #[cfg(debug_assertions)]
        debug_assert_eq!(value.tag, self.name());
        let value = BvConst::load(self, &value);
        let as_string = termdag.lit(Literal::String(value.0.to_string().into()));
        Some((
            1,
            termdag.app("bvconst-from-string".into(), vec![as_string]),
        ))
    }
}

impl FromSort for BvConst {
    type Sort = BvConstSort;

    fn load(sort: &Self::Sort, value: &Value) -> Self {
        let i = value.bits as usize;
        sort.solvers
            .lock()
            .unwrap()
            .bv_constants_index
            .get_index(i)
            .unwrap()
            .clone()
    }
}

impl IntoSort for BvConst {
    type Sort = BvConstSort;

    fn store(self, sort: &Self::Sort) -> Option<Value> {
        let (i, _) = sort
            .solvers
            .lock()
            .unwrap()
            .bv_constants_index
            .insert_full(self);
        Some(Value {
            #[cfg(debug_assertions)]
            tag: sort.name(),
            bits: i as u64,
        })
    }
}
