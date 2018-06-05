// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of the Rust distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

pub use std::collections::Bound::{self, Excluded, Included, Unbounded};
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};

pub trait RangeBounds<T: ?Sized> {
    fn start_bound(&self) -> Bound<&T>;
    fn end_bound(&self) -> Bound<&T>;
}

impl<T: ?Sized> RangeBounds<T> for RangeFull {
    fn start_bound(&self) -> Bound<&T> {
        Unbounded
    }

    fn end_bound(&self) -> Bound<&T> {
        Unbounded
    }
}

impl<T> RangeBounds<T> for RangeFrom<T> {
    fn start_bound(&self) -> Bound<&T> {
        Included(&self.start)
    }

    fn end_bound(&self) -> Bound<&T> {
        Unbounded
    }
}

impl<T> RangeBounds<T> for RangeTo<T> {
    fn start_bound(&self) -> Bound<&T> {
        Unbounded
    }

    fn end_bound(&self) -> Bound<&T> {
        Excluded(&self.end)
    }
}

impl<T> RangeBounds<T> for Range<T> {
    fn start_bound(&self) -> Bound<&T> {
        Included(&self.start)
    }

    fn end_bound(&self) -> Bound<&T> {
        Excluded(&self.end)
    }
}
