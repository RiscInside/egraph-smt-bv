use crate::solvers::{bvconst::BvConst, SolversRef, Width};
use egglog::{
    add_primitives,
    ast::Literal,
    sort::{FromSort, IntoSort, Sort},
    util::IndexSet,
    Value,
};
use num_bigint::BigUint;

pub(crate) struct BvRangeSort {
    solvers: SolversRef,
}

impl BvRangeSort {
    pub(crate) fn new(solvers: SolversRef) -> Self {
        Self { solvers }
    }
}

impl std::fmt::Debug for BvRangeSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BvRangeSort").finish()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) struct BvRange {
    pub(crate) min: BigUint,
    pub(crate) max: BigUint,
    pub(crate) width: Width,
}

impl BvRange {
    fn valid(&self) -> bool {
        self.min <= self.max
    }

    #[track_caller]
    fn assert_valid(self) -> Self {
        assert!(self.valid());
        self
    }

    fn compute_for_monotonic_binop(
        &self,
        other: &BvRange,
        op: impl Fn(&BigUint, &BigUint) -> BigUint,
    ) -> Option<BvRange> {
        if self.width != other.width || !self.valid() || !other.valid() {
            return None;
        }

        let limit = (BigUint::from(1u32) << self.width) - BigUint::from(1u32);
        let result_for_max = op(&self.max, &other.max);

        (result_for_max <= limit).then(|| BvRange {
            min: std::cmp::min(op(&self.min, &other.min), limit),
            max: result_for_max,
            width: self.width,
        })
    }

    fn compute_from_bit_sizes(
        &self,
        other: &BvRange,
        op_width: impl Fn(Width, Width) -> Width,
    ) -> Option<BvRange> {
        if self.width != other.width || !self.valid() || !other.valid() {
            return None;
        }

        let max_bits = op_width(self.max.bits() as Width, other.max.bits() as Width);

        Some(
            BvRange {
                min: BigUint::from(0u32),
                max: (BigUint::from(1u32) << max_bits) - BigUint::from(1u32),
                width: self.width,
            }
            .assert_valid(),
        )
    }

    fn neg(&self) -> Option<BvRange> {
        if !self.valid() {
            return None;
        }
        let exclusive_limit = BigUint::from(1u32) << self.width;

        Some(
            if self.min.bits() != 0 {
                BvRange {
                    min: &exclusive_limit - &self.max,
                    max: &exclusive_limit - &self.min,
                    width: self.width,
                }
            } else {
                BvRange {
                    min: BigUint::from(0u32),
                    max: if self.max.bits() == 0 {
                        BigUint::from(0u32)
                    } else {
                        exclusive_limit - BigUint::from(1u32)
                    },
                    width: self.width,
                }
            }
            .assert_valid(),
        )
    }

    fn add(&self, other: &BvRange) -> Option<BvRange> {
        self.compute_for_monotonic_binop(other, |lhs, rhs| lhs + rhs)
    }

    fn mul(&self, other: &BvRange) -> Option<BvRange> {
        self.compute_for_monotonic_binop(other, |lhs, rhs| lhs * rhs)
    }

    fn and(&self, other: &BvRange) -> Option<BvRange> {
        self.compute_from_bit_sizes(other, std::cmp::min)
    }

    fn or(&self, other: &BvRange) -> Option<BvRange> {
        self.compute_from_bit_sizes(other, std::cmp::max)
    }

    fn refine_ule(&self, other: &BvRange) -> Option<BvRange> {
        if self.width != other.width {
            return None;
        }

        Some(BvRange {
            min: self.min.clone(),
            max: std::cmp::min(&self.max, &other.max).clone(),
            width: self.width,
        })
    }

    fn refine_ult(&self, other: &BvRange) -> Option<BvRange> {
        if self.width != other.width {
            return None;
        }

        Some(BvRange {
            min: self.min.clone(),
            max: std::cmp::min(self.max.clone(), &other.max - BigUint::from(1u32)),
            width: self.width,
        })
    }

    fn refine_uge(&self, other: &BvRange) -> Option<BvRange> {
        if self.width != other.width {
            return None;
        }

        Some(BvRange {
            min: std::cmp::max(&self.min, &other.min).clone(),
            max: self.max.clone(),
            width: self.width,
        })
    }

    fn refine_ugt(&self, other: &BvRange) -> Option<BvRange> {
        if self.width != other.width {
            return None;
        }

        Some(BvRange {
            min: std::cmp::max(self.min.clone(), &other.min + BigUint::from(1u32)).clone(),
            max: self.max.clone(),
            width: self.width,
        })
    }

    fn zero_extend(&self, bits: Width) -> Option<BvRange> {
        if !self.valid() {
            return None;
        }

        Some(
            BvRange {
                min: self.min.clone(),
                max: self.max.clone(),
                width: self.width + bits,
            }
            .assert_valid(),
        )
    }

    fn merge(&self, other: &BvRange) -> Option<BvRange> {
        if self.width != other.width {
            return None;
        }

        let res = BvRange {
            min: std::cmp::max(&self.min, &other.min).clone(),
            max: std::cmp::min(&self.max, &other.max).clone(),
            width: self.width,
        };

        Some(res)
    }

    fn no_add_overflow(&self, other: &BvRange) -> Option<()> {
        if self.width != other.width {
            return None;
        }

        ((&self.max + &other.max).bits() <= self.width).then_some(())
    }

    fn no_mul_overflow(&self, other: &BvRange) -> Option<()> {
        if self.width != other.width {
            return None;
        }

        ((&self.max * &other.max).bits() <= self.width).then_some(())
    }
}

type C = BvConst;
type R = BvRange;

pub(crate) type BvRangeTable = IndexSet<BvRange>;

impl Sort for BvRangeSort {
    fn name(&self) -> egglog::ast::Symbol {
        "BvRangeSort".into()
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
            "bvrange" = |min: C, max: C, width: i64| -> Option<R> {
                Some(BvRange {
                    min: min.0,
                    max: max.0,
                    width: width.try_into().ok()?,
                })
            }
        );

        add_primitives!(
            info,
            "bvrange-full" = |width: i64| -> Option<R> {
                Some(BvRange {
                    width: width.try_into().ok()?,
                    min: BigUint::from(0u32),
                    max: (BigUint::from(1u32) << width) - BigUint::from(1u32),
                })
            }
        );

        add_primitives!(
            info,
            "bvrange-const" = |width: i64, constant: C| -> Option<R> {
                Some(BvRange {
                    width: width.try_into().ok()?,
                    min: constant.0.clone(),
                    max: constant.0,
                })
            }
        );

        add_primitives!(
            info,
            "bvrange-add" = |lhs: R, rhs: R| -> Opt<R> { lhs.add(&rhs) }
        );
        add_primitives!(info, "bvrange-neg" = |op: R| -> Opt<R> { op.neg() });
        add_primitives!(
            info,
            "bvrange-mul" = |lhs: R, rhs: R| -> Opt<R> { lhs.mul(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-and" = |lhs: R, rhs: R| -> Opt<R> { lhs.and(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-or" = |lhs: R, rhs: R| -> Opt<R> { lhs.or(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-merge" = |lhs: R, rhs: R| -> Opt<R> { lhs.merge(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-zero-ext" = |op: R, extra_width: i64| -> Option<R> {
                op.zero_extend(extra_width.try_into().ok()?)
            }
        );
        add_primitives!(
            info,
            "bvrange-fits-in" = |op: R, width: i64| -> Option<()> {
                (op.valid() && op.max.bits() <= width.try_into().ok()?).then_some(())
            }
        );
        add_primitives!(
            info,
            "bvrange-try-get-constant" =
                |op: R| -> Option<C> { (op.max == op.min).then_some(BvConst(op.max)) }
        );
        add_primitives!(
            info,
            "bvrange-refine-uge" = |lhs: R, rhs: R| -> Opt<R> { lhs.refine_uge(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-refine-ugt" = |lhs: R, rhs: R| -> Opt<R> { lhs.refine_ugt(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-refine-ule" = |lhs: R, rhs: R| -> Opt<R> { lhs.refine_ule(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-refine-ult" = |lhs: R, rhs: R| -> Opt<R> { lhs.refine_ult(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-empty" = |range: R| -> Opt<()> { (range.min > range.max).then_some(()) }
        );
        add_primitives!(
            info,
            "bvrange-no-add-ovf" = |lhs: R, rhs: R| -> Opt<()> { lhs.no_add_overflow(&rhs) }
        );
        add_primitives!(
            info,
            "bvrange-no-mul-ovf" = |lhs: R, rhs: R| -> Opt<()> { lhs.no_mul_overflow(&rhs) }
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
        let value = BvRange::load(self, &value);

        let min_as_string = termdag.lit(Literal::String(value.min.to_string().into()));
        let max_as_string = termdag.lit(Literal::String(value.max.to_string().into()));

        let min_as_bvconst = termdag.app("bvconst-from-string".into(), vec![min_as_string]);
        let max_as_bvconst = termdag.app("bvconst-from-string".into(), vec![max_as_string]);

        let width = termdag.lit(Literal::Int(value.width as i64));

        Some((
            3,
            termdag.app(
                "bvrange".into(),
                vec![min_as_bvconst, max_as_bvconst, width],
            ),
        ))
    }
}

impl FromSort for BvRange {
    type Sort = BvRangeSort;

    fn load(sort: &Self::Sort, value: &Value) -> Self {
        let i = value.bits as usize;
        sort.solvers
            .lock()
            .unwrap()
            .bv_ranges_index
            .get_index(i)
            .unwrap()
            .clone()
    }
}

impl IntoSort for BvRange {
    type Sort = BvRangeSort;

    fn store(self, sort: &Self::Sort) -> Option<Value> {
        let (i, _) = sort
            .solvers
            .lock()
            .unwrap()
            .bv_ranges_index
            .insert_full(self);
        Some(Value {
            #[cfg(debug_assertions)]
            tag: sort.name(),
            bits: i as u64,
        })
    }
}
