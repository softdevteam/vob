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
