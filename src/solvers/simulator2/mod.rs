use crate::solvers::{Variable, Width};
use dag::Dag;

mod dag;
mod lazy_heap;
mod skyline;

pub(in crate::solvers) use dag::Operation;

/// Bitvector slice
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(in crate::solvers) struct Slice {
    pub(in crate::solvers) start: Width,
    pub(in crate::solvers) end: Width,
}

impl From<std::ops::Range<Width>> for Slice {
    fn from(value: std::ops::Range<Width>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl Slice {
    fn subslice(self, subslice: Slice) -> Self {
        Self {
            start: self.start + subslice.start,
            end: self.start + subslice.end,
        }
    }
}

pub(in crate::solvers) struct SimulationCore<V: Variable> {
    /// Spanning DAG of the e-graph
    dag: Dag<V>,
}

impl<V: Variable> Default for SimulationCore<V> {
    fn default() -> Self {
        Self {
            dag: Default::default(),
        }
    }
}

impl<V: Variable> SimulationCore<V> {
    pub(in crate::solvers) fn add_input(&mut self, input: V, name: String, width: Width) {
        self.dag.declare_input(input, width, name);
    }

    pub(in crate::solvers) fn add_operation(&mut self, op: Operation, inputs: Vec<V>, out: V) {
        self.dag.add_equation(op, inputs, out);
    }

    pub(in crate::solvers) fn add_extract(&mut self, input: V, slice: Slice, out: V) {
        self.dag.add_extract(input, slice, out);
    }

    pub(in crate::solvers) fn union(&mut self, old: V, new: V) {
        self.dag.union(old, new);
    }

    pub(in crate::solvers) fn summary(&mut self) -> String {
        self.dag.summary()
    }
}
