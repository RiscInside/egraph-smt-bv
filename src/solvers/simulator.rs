//! Simulator is a component responsible for running many simulations on the e-graph
//! and keeping track of e-nodes that are potentially equal.
//!
//! The main data structure maintained by the simulator is the directed acyclic
//! graph of e-classes. While we do not keep track of the topological order of
//! e-classes (i.e. ordering in which e-classes are evaluated), we do make sure
//! that such topological ordering can always be constructed - i.e. there are no
//! cyclical dependencies in evaluation. The way we enforce this invariant is simple
//! and perhaps even a bit crude - every time e-graph core communicated to us a new
//! v = op(v1, v2, .. vn) equation, we only accept it if
//!
//! - v has not been seen by the simulator before
//! - v1, v2, .. vn have been seen before and have lowerings.
//!
//! Note that second point here implies that initial lowerings for e-classes have to be
//! communicated to the simulator in bottom-up fashion - if they are communicated out of order,
//! solver core will reject them. This is taken care of in the core.
//!
//! Another source of complexity is functional dependencies between input slices. Consider the
//! following:
//! ```smt2
//! (declare-const a (_ BitVec 256))
//! (declare-const b (_ BitVec 256))
//!
//! (assert (= a (not b)))
//! ```
//!
//! It would be unwise for us to think that both `a` and `b` are inputs to the problem here. As
//! such, simulator core should be able to deduce that only `b` should be assigned a value.
//! However, we still need to ensure that evaluation graph is still acyclic. Additionally, there
//! could be functional dependencies between different slices of the input (as in yosys generated
//! outputs):
//!
//! ```smt2
//! (declare-const a (_ BitVec 256))
//! (assert (= ((_ extract 31 0) a) ((_ extract 131 100) a)))
//! ```
//!
//! We need to be able to support these cases, while rejecting e.g.
//!
//! ```smt2
//! (assert (= a (bvand a b)))
//! ```
//!
//! as a functional dependency (this would lead to a cycle).
//!
//! We support this safety check via an input set analysis. For each node, we compute what
//! inputs it depends on (specifically, we track, for each e-class corresponding to an input
//! variable, what input slices are used). This set is first computed when we add an equation
//! for computing value of the e-class. Later, this can be canonicalized in UF-like fashion:
//! we go through each "input" e-class, see if now it's actually computed, and, if so,
//! add it's dependencies (recursively canonicalizing input set for that old input like we do
//! UF path compression). Once we get a canonical input set, a simple aliasing check is sufficient
//! to see if cycle has been introduced.
//!
//! Overall, we have the following set of data-structured being maintained live:
//!
//! 1) Mapping from e-class to equation computing this e-class. There are two cases
//!
//!    - Input slice. The input doesn't have to be live (i.e. it's okay if we have an equation for this
//!      slice).
//!    - Computed expression (identified by operation and a list of inputs)
//!     
//!    Equation also stores (potentially uncanonical) input set used for computing this expression.
//!
//! 2) Input slice mapping. For each input e-class, we keep an interval tree with e-classes computing
//!    each interval. This map is used during input set canonicalization to see if parts of the input
//!    set can now be computed from other input slices.

#![allow(dead_code)]

use crate::solvers::{Variable, Width};
use hashbrown::HashMap;
use iset::IntervalMap;
use std::{cell::Cell, collections::BinaryHeap, ops::RangeBounds};

/// Bit-range, i.e. slice of the bitvector. Not using Range here, as it doesn't implement Copy.
/// Guaranteed to be non-empty, i.e. hi > lo
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct BitRange {
    lo: Width,
    hi: Width,
}

impl RangeBounds<Width> for BitRange {
    fn start_bound(&self) -> std::ops::Bound<&Width> {
        std::ops::Bound::Included(&self.lo)
    }

    fn end_bound(&self) -> std::ops::Bound<&Width> {
        std::ops::Bound::Excluded(&self.hi)
    }
}

impl std::fmt::Debug for BitRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.lo..self.hi)
    }
}

impl std::fmt::Display for BitRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Set of bit-ranges of one input e-class.
#[derive(Debug, PartialEq, Eq)]
struct BitRangeSet {
    /// Different bit-ranges of input, sorted, non-overlapping, and non-touching
    ranges: Vec<BitRange>,
}

/// Builder of bit-range sets. Allows for efficient addition of new intervals and can be converted
/// into BitRangeSet in the end.
struct BitRangeSetBuilder {
    // Binary heap of open/close events. Open events
    range_events: BinaryHeap<(bool, Width)>,
}

/// Set of bit ranges of each value
struct UsedBitRanges<V: Variable> {
    bit_range_sets: HashMap<V, BitRangeSet>,
    canonicalization_ts: u64,
}

impl<V: Variable> UsedBitRanges<V> {
    fn check_subsumption(other: &UsedBitRanges<V>) {}
}

/// Operation for computing values
enum Op {
    Add,
    Neg,
    Not,
    Const,
    Mul,
}

/// Operation used to compute value of the DAG node during simulation.
enum DAGNodeKind<V: Variable> {
    /// Value is derived from values for some inputs.
    Computed { inputs: Vec<V> },
    /// This e-class has been unioned with some other one and the other one won.
    Redirect(Cell<V>),
    /// Value can be obtained by slicing the input.
    InputSlice { node: V, range: BitRange },
}

/// Node in the simulation DAG, explaining how to compute value for the e-class.
struct DAGNode<V: Variable> {
    /// Operation computing value of the node.
    operation: DAGNodeKind<V>,
    /// Set of inputs used in node computation.
    used_bit_ranges: UsedBitRanges<V>,
    /// All input portions this node computes (there could well be multiple)
    input_portions: Vec<(V, BitRange)>,
    /// Height of the node. For inputs, this is 0, but for everything else this could be higher.
    /// For computed nodes, height of children must be smaller than height of the parent.
    height: usize,
}

/// Intervals of the input that can be computed.
type ComputedBitRanges<V> = IntervalMap<Width, V>;

struct SimulationCore<V: Variable> {
    mappings: HashMap<V, DAGNode<V>>,
    /// For each input, keeps track of what parts of it can be computed, and how.
    computed_input_intervals: HashMap<V, ComputedBitRanges<V>>,
    /// Last input set update timestamp
    canonicalization_ts: u64,
}

mod input_set_canon {
    use std::{cmp::Reverse, collections::binary_heap::BinaryHeap};

    use hashbrown::HashSet;

    use super::*;

    trait SplitByComputability<V> {
        /// Given a bit-range of a value, split it into smaller bit-ranges, some of which
        /// are derivable (from other inputs), and some aren't. Call the first function
        /// for non-derivable bit-ranges and the second for derivable/computable ones.
        fn split_by_computability(
            &self,
            bitrange: BitRange,
            non_computable: impl FnMut(BitRange),
            computable: impl FnMut(V),
        );
    }

    impl<V: Variable> SplitByComputability<V> for ComputedBitRanges<V> {
        fn split_by_computability(
            &self,
            bitrange: BitRange,
            mut on_non_computable: impl FnMut(BitRange),
            mut on_computable: impl FnMut(V),
        ) {
            let mut non_computable_range_start = bitrange.lo;

            for (computable_interval, value) in self.iter(bitrange) {
                if computable_interval.start > non_computable_range_start {
                    on_non_computable(BitRange {
                        lo: non_computable_range_start,
                        hi: computable_interval.start,
                    })
                }
                non_computable_range_start = computable_interval.end;
                on_computable(*value);
            }

            if non_computable_range_start < bitrange.hi {
                on_non_computable(BitRange {
                    lo: non_computable_range_start,
                    hi: bitrange.hi,
                })
            }
        }
    }

    #[derive(PartialEq, Eq, PartialOrd, Ord)]
    struct OpenCloseEvent(Width, bool);

    impl OpenCloseEvent {
        fn open(start: Width) -> Self {
            OpenCloseEvent(start, false)
        }

        fn close(end: Width) -> Self {
            OpenCloseEvent(end, true)
        }
    }

    /// Helper used to construct new bit range sets.
    #[derive(Default)]
    struct BitRangeSetBuilder {
        /// Interval open and close events, in-order. We use `Reverse` here as
        /// BinaryHeap is a max heap and we want low to high iteration.
        open_close_events: BinaryHeap<Reverse<OpenCloseEvent>>,
    }

    impl BitRangeSetBuilder {
        fn add_range(&mut self, BitRange { lo, hi }: BitRange) {
            self.open_close_events
                .push(Reverse(OpenCloseEvent::open(lo)));
            self.open_close_events
                .push(Reverse(OpenCloseEvent::close(hi)));
        }

        fn build(mut self) -> BitRangeSet {
            let mut counter: usize = 0;
            let mut start: Width = 0;
            let mut ranges = vec![];

            while let Some(Reverse(OpenCloseEvent(elem, close))) = self.open_close_events.pop() {
                if close {
                    counter -= 1;
                    if counter == 0 {
                        ranges.push(BitRange {
                            lo: start,
                            hi: elem,
                        });
                    }
                } else {
                    if counter == 0 {
                        start = elem;
                    }
                    counter += 1;
                }
            }

            BitRangeSet { ranges }
        }
    }

    impl<V: Variable> SimulationCore<V> {
        /// Ensures that input set for `v` is canonical. Canonical input sets can be compared
        /// against each other for subsumption and aliasing.
        ///
        /// In the process, this can recursively canonicalize input sets for other e-classes.
        pub(super) fn canonicalize_input_set_for(&mut self, v: V) {
            if self.mappings[&v].used_bit_ranges.canonicalization_ts == self.canonicalization_ts {
                return;
            }

            let mut worklist_pre = vec![v];
            let mut worklist_post: Vec<(HashMap<V, BitRangeSetBuilder>, HashSet<V>, V)> = vec![];

            while let Some(v) = worklist_pre.pop() {
                let mut bit_range_set_builders: HashMap<V, BitRangeSetBuilder> = HashMap::new();
                let mut computable_deps: HashSet<V> = HashSet::new();

                let entry = &self.mappings[&v];
                if entry.used_bit_ranges.canonicalization_ts == self.canonicalization_ts {
                    continue;
                }

                for (&input_eclass, bit_range_set) in entry.used_bit_ranges.bit_range_sets.iter() {
                    for &range in &bit_range_set.ranges {
                        self.computed_input_intervals[&input_eclass].split_by_computability(
                            range,
                            |non_computable_range| {
                                bit_range_set_builders
                                    .entry(input_eclass)
                                    .or_default()
                                    .add_range(non_computable_range)
                            },
                            |computable_dep| {
                                worklist_pre.push(computable_dep);
                                computable_deps.insert(computable_dep);
                            },
                        );
                    }
                }

                worklist_post.push((bit_range_set_builders, computable_deps, v));
            }

            while let Some((mut builders, deps, v)) = worklist_post.pop() {
                for dep in deps.iter() {
                    let dep_deps = &self.mappings[dep].used_bit_ranges;

                    for (dep_dep, dep_bitranges) in dep_deps.bit_range_sets.iter() {
                        let bitranges = builders.entry(*dep_dep).or_default();
                        for range in dep_bitranges.ranges.iter() {
                            bitranges.add_range(*range);
                        }
                    }
                }

                let new_used_bit_ranges = UsedBitRanges {
                    bit_range_sets: builders
                        .into_iter()
                        .map(|(value, bit_range_set)| (value, bit_range_set.build()))
                        .collect(),
                    canonicalization_ts: self.canonicalization_ts,
                };

                self.mappings.get_mut(&v).unwrap().used_bit_ranges = new_used_bit_ranges;
            }
        }
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn test_bit_range_set_builder() {
            let mut builder = BitRangeSetBuilder::default();

            builder.add_range(BitRange { lo: 13, hi: 15 });
            builder.add_range(BitRange { lo: 3, hi: 10 });
            builder.add_range(BitRange { lo: 0, hi: 1 });
            builder.add_range(BitRange { lo: 20, hi: 24 });
            builder.add_range(BitRange { lo: 2, hi: 7 });
            builder.add_range(BitRange { lo: 11, hi: 13 });

            let actual = builder.build();
            let expected = BitRangeSet {
                ranges: vec![
                    BitRange { lo: 0, hi: 1 },
                    BitRange { lo: 2, hi: 10 },
                    BitRange { lo: 11, hi: 15 },
                    BitRange { lo: 20, hi: 24 },
                ],
            };

            assert_eq!(actual, expected);
        }
    }
}

impl<V: Variable> SimulationCore<V> {
    // Simple find on DAG nodes with path-compression
    fn find(&self, mut variable: V) -> V {
        let mut result = variable;
        while let Some(DAGNode {
            operation: DAGNodeKind::Redirect(cell),
            ..
        }) = self.mappings.get(&result)
        {
            result = cell.get();
        }

        while let Some(DAGNode {
            operation: DAGNodeKind::Redirect(cell),
            ..
        }) = self.mappings.get(&variable)
        {
            variable = cell.get();
            cell.set(result);
        }

        result
    }

    fn assert_canonical(&self, variable: V) {
        assert!(!matches!(
            self.mappings.get(&variable),
            Some(DAGNode {
                operation: DAGNodeKind::Redirect(_),
                ..
            })
        ));
    }

    fn union(&mut self, old: V, new: V) {
        // Unions we recieve from e-graph core are for canonical values only
        self.assert_canonical(old);
        self.assert_canonical(new);
    }
}

impl<V: Variable> Default for SimulationCore<V> {
    fn default() -> Self {
        Self {
            mappings: Default::default(),
            computed_input_intervals: Default::default(),
            canonicalization_ts: Default::default(),
        }
    }
}
