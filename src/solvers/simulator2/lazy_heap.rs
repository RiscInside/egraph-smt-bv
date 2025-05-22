use hashbrown::HashMap;
use std::collections::BinaryHeap;

/// Simple wrapper around binary heap that supports amortized O(1) removals by tracking
/// elements to be removed in a hash multiset.
pub(in crate::solvers::simulator2) struct LazyRemovalHeap<T> {
    actual_heap: BinaryHeap<T>,
    to_remove_set: HashMap<T, usize>,
}

impl<T: Ord> Default for LazyRemovalHeap<T> {
    fn default() -> Self {
        Self {
            actual_heap: Default::default(),
            to_remove_set: Default::default(),
        }
    }
}

impl<T: Ord + std::hash::Hash> LazyRemovalHeap<T> {
    pub(in crate::solvers::simulator2) fn insert(&mut self, elem: T) {
        self.actual_heap.push(elem);
    }

    pub(in crate::solvers::simulator2) fn remove(&mut self, elem: T) {
        *self.to_remove_set.entry(elem).or_default() += 1
    }

    pub(in crate::solvers::simulator2) fn peek_max(&mut self) -> Option<&T> {
        while let Some(actual_heap_min) = self.actual_heap.iter().next() {
            if let Some(delete_count) = self.to_remove_set.get_mut(actual_heap_min) {
                *delete_count -= 1;
                if *delete_count == 0 {
                    self.to_remove_set.remove(actual_heap_min);
                }
                self.actual_heap.pop();
            } else {
                return self.actual_heap.peek();
            }
        }
        None
    }
}
