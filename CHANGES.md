# vob 3.0.3 (2022-08-02)

* Update dependencies.


# vob 3.0.2 (2022-07-25)

* Add `from_elem_with_storage_type` as a dual of `new_with_storage_type`.


# vob 3.0.1 (2021-10-22)

* Implement `std::ops::{BitOrAssign, BitOr, BitAndAssign, BitAnd, BitXorAssign,
  BitXor}`. Note that, as with `Vob`'s other bit-wise operations, these will
  panic if the two `Vob`s in question are not of equal length.


# vob 3.0.0 (2021-09-20)

## Breaking changes

* `Vob::from_elem(value: bool, len: usize)` now takes the value first and the
  number of repetitions of that value second to mirror the most common way this
  function is defined elsewhere.

* The `vob!` macro's repetition form now mirrors `vec!`, so `vob![val; len]` is
  equivalent to `Vec::from_elem(val, len)`.


# vob 2.0.6 (2021-01-25)

* Add `get_storage` to the `unsafe_internals` portion of the API.
* Clearly document the invariants users must maintain when using the `unsafe`
  parts of the API.


# vob 2.0.5 (2020-09-02)

* Use rustfmt stable.
* Remove unnecessary ``fn main`` wrappers in doctest examples.
* Clean up two remaining ``#[macro use] extern crate vob;`` lines from examples.


# vob 2.0.4 (2019-11-21)

* License as dual Apache-2.0/MIT (instead of a more complex, and little
  understood, triple license of Apache-2.0/MIT/UPL-1.0).


# vob 2.0.3 (2019-08-21)

* Port to Rust 2018.
* Remove local copy of `Bounds` since it is now part of stable Rust.
* On rustc-1.37 and later, automatically use `reverse_bits` (this automatically
  includes the current nightly version of rustc).


# vob 2.0.2 (2018-12-18)

* Further speed up `iter_\[set|unset\]_bits` for cases where set/unset bits are
  fairly randomly distributed (by approximately 10%).


# vob 2.0.1 (2018-12-11)

* Substantially speed up `iter_\[set|unset\]_bits` for the common case where all
  bits are set/unset (respectively). This leads to a 3x improvement in such
  cases, with no measurable slowdown in the general case.


# vob 2.0.0 (2018-10-10)

* Change `set` so that if passed an out of bounds index it panics (previously it
  returned None, but since one doesn't generally check the return value of
  `set`, this led to errors being overlooked).


# vob 1.3.2 (2018-06-30)

* Improve performance of the `xor`, `and`, and `or` functions.
* Add `fast_reverse` feature: on nightly, we automatically try to use the
  `fast_reverse` function to improve performance.


# vob 1.3.1 (2018-06-20)

* Don't overallocate memory in `new_with_storage_type`.


# vob 1.3.0 (2018-06-11)

* Add `extend_from_vob` function.
* Add `unsafe_internals` feature, which allows external crates unsafe access to
  Vob's internal (useful for speed, but bad for forwards compatibility!).
* Various performance improvements.
* Use `rustfmt`.


# vob 1.2.0 (2018-05-08)

* Add `from_bytes` function.


# vob 1.1.0 (2018-03-29)

* Add `serde` feature to enable [Serde](https://serde.rs/) support.


# vob 1.0.0 (2018-03-14)

First stable release.
