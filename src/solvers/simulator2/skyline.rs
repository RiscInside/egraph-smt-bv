use itertools::{EitherOrBoth, Itertools};

use crate::solvers::{
    simulator2::{lazy_heap::LazyRemovalHeap, Slice},
    Width,
};

/// Skyline tracks, for each input slice, the "height" of it in computation of the value.
/// Height is a minimum number of dependenant intermediate computations required dependant
/// on that slice before evaluation of this value can begin. We use height sets to check if
/// value is potentially used in computation of the other value.
///
/// The height set is stored as a vector of height updates. Each update is represented as
/// an offset and height tuple, translating into "from this offset, we have this height until
/// the next update". Updates are sorted by the offset, which is represented with the Width
/// type.
#[derive(Default, Debug)]
pub(in crate::solvers::simulator2) struct Skyline {
    pub(in crate::solvers::simulator2) updates: Vec<(Width, usize)>,
}

impl Skyline {
    /// Iterate over all slices of non-zero height
    pub(in crate::solvers::simulator2) fn non_zero_height_slices_iter(
        &self,
    ) -> impl Iterator<Item = (Slice, usize)> + use<'_> {
        self.updates
            .iter()
            .tuple_windows()
            .map(|(&(start, height), &(end, _))| (Slice { start, end }, height))
            .filter(|(_, height)| *height != 0)
    }

    /// Compare this skyline with the other one. First boolean is true when there is a point
    /// at which self is higher than other. Second boolean is true when there is a point
    /// at which other is higher than self.
    pub(in crate::solvers::simulator2) fn compare(&self, other: &Skyline) -> (bool, bool) {
        let (mut self_higher_than_other, mut other_higher_than_self) = (false, false);

        let mut self_height = 0;
        let mut other_height = 0;

        for update in self
            .updates
            .iter()
            .merge_join_by(other.updates.iter(), |(off1, ..), (off2, ..)| {
                off1.cmp(off2)
            })
        {
            match update {
                EitherOrBoth::Both((_, new_self_height), (_, new_other_height)) => {
                    // Very important that we perform simultaneous update here
                    self_height = *new_self_height;
                    other_height = *new_other_height;
                }
                EitherOrBoth::Left((_, new_self_height)) => self_height = *new_self_height,
                EitherOrBoth::Right((_, new_other_heigth)) => other_height = *new_other_heigth,
            }

            self_higher_than_other |= self_height > other_height;
            other_higher_than_self |= other_height > self_height;
        }

        (self_higher_than_other, other_higher_than_self)
    }

    pub(in crate::solvers::simulator2) fn max_height(&self) -> usize {
        self.updates
            .iter()
            .map(|(_, height)| *height)
            .max()
            .unwrap_or(0)
    }
}

impl From<Slice> for Skyline {
    fn from(slice: Slice) -> Self {
        Skyline {
            updates: vec![(slice.start, 1), (slice.end, 0)],
        }
    }
}

#[derive(Debug)]
enum HeightUpdate {
    Add(usize),
    Remove(usize),
}

/// Skyline builder builds a new skyline out of supplied intervals
#[derive(Default, Debug)]
pub(in crate::solvers::simulator2) struct SkylineBuilder {
    /// List of updates, currently unsorted.
    unsorted_updates: Vec<(Width, HeightUpdate)>,
}

impl SkylineBuilder {
    pub(in crate::solvers::simulator2) fn add_slice(&mut self, slice: Slice, height: usize) {
        self.unsorted_updates
            .push((slice.start, HeightUpdate::Add(height)));
        self.unsorted_updates
            .push((slice.end, HeightUpdate::Remove(height)));
    }

    pub(in crate::solvers::simulator2) fn add_skyline(
        &mut self,
        skyline: &Skyline,
        height_delta: usize,
    ) {
        for (slice, height) in skyline.non_zero_height_slices_iter() {
            self.add_slice(slice, height + height_delta);
        }
    }

    pub(in crate::solvers::simulator2) fn build(mut self) -> Skyline {
        self.unsorted_updates.sort_by_key(|(offset, _)| *offset);

        let mut heap = LazyRemovalHeap::default();
        let mut updates = vec![];
        let mut last_height = 0;
        let mut last_offset = 0;
        let mut last_pushed_height = 0;

        for (new_offset, new_update) in self.unsorted_updates {
            match new_update {
                HeightUpdate::Add(elem) => heap.insert(elem),
                HeightUpdate::Remove(elem) => heap.remove(elem),
            }

            let new_height = heap.peek_max().cloned().unwrap_or(0);
            if last_offset != new_offset {
                if last_pushed_height != last_height {
                    updates.push((last_offset, last_height));
                    last_pushed_height = last_height;
                }

                last_offset = new_offset;
            }

            last_height = new_height;
        }

        assert_eq!(last_height, 0); // After all the removals, the last height we should have seen is 0
        updates.push((last_offset, last_height));
        Skyline { updates }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_interval_build_simple() {
        let mut builder = SkylineBuilder::default();
        builder.add_slice((1..3).into(), 5);
        builder.add_slice((2..4).into(), 3);

        let skyline = builder.build();
        assert_eq!(skyline.updates, vec![(1, 5), (3, 3), (4, 0)]);
    }

    #[test]
    fn test_add_interval_build_non_overlapping() {
        let mut builder = SkylineBuilder::default();
        builder.add_slice((0..2).into(), 2);
        builder.add_slice((5..7).into(), 4);

        let skyline = builder.build();
        assert_eq!(skyline.updates, vec![(0, 2), (2, 0), (5, 4), (7, 0)]);
    }

    #[test]
    fn test_adjacent_intervals() {
        let mut builder = SkylineBuilder::default();
        builder.add_slice((0..2).into(), 2);
        builder.add_slice((2..4).into(), 2);

        let skyline = builder.build();
        assert_eq!(skyline.updates, vec![(0, 2), (4, 0)]);
    }

    #[test]
    fn test_non_zero_slice_iter() {
        let mut builder = SkylineBuilder::default();
        builder.add_slice((1..3).into(), 5);
        builder.add_slice((2..4).into(), 3);

        let skyline = builder.build();

        assert_eq!(
            skyline.non_zero_height_slices_iter().collect::<Vec<_>>(),
            vec![((1..3).into(), 5), ((3..4).into(), 3)]
        );
    }
}
