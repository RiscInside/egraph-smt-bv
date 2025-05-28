use crate::solvers::Width;

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
    pub(in crate::solvers) fn subslice(self, subslice: Slice) -> Self {
        Self {
            start: self.start + subslice.start,
            end: self.start + subslice.end,
        }
    }

    pub(in crate::solvers) fn width(self) -> Width {
        self.end - self.start
    }
}
