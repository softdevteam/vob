[![Latest version](https://img.shields.io/crates/v/vob.svg)](https://crates.io/crates/vob)
[![Documentation](https://docs.rs/vob/badge.svg)](https://docs.rs/vob)

# Vector of Bits (Vob)

A Vob is a "vector of bits": a sequence of bits which exposes a `Vec`-like
interface. Whereas `Vec<bool>` requires 1 byte of storage per bit, `Vob`
requires only 1 bit of storage per bit. `Vob` is broadly
similar to [BitVec](https://crates.io/crates/bit-vec), but has an API more
closely aligned to `Vec<bool>` and allows non-32-bit backing storage. On 64-bit
systems this can lead to a substantial performance increase, particularly
when functions such as
[`iter_set_bits`](https://docs.rs/vob/0.1.0/vob/struct.Vob.html#method.iter_set_bits)
are used.

## Usage

```rust
use vob::vob;

let mut v = vob![false, true, false];
assert_eq!(v[2], false);
v.set(2, true);
assert_eq!(v[2], true);
assert_eq!(v.iter_set_bits(..).collect::<Vec<_>>(), vec![1, 2]);
```

## Migrating from `Vec<bool>`

As far as possible, `Vob` is intended to have a superset of `Vec<bool>`'s interface, which
should make porting most code fairly simple. However, `Vec<bool>` contains several functions
which are not yet implemented in `Vob`: these are missing simply due to a lack of a current
use-case rather than because of any fundamental incompatibilities.

There is one missing feature which, currently, is impossible to implement: assignment to an
index. In other words one cannot currently express `v[0] = true` for a `Vob` `v`. Until
[`IndexGet` / `IndexMove` and equivalents](https://github.com/rust-lang/rfcs/issues/997) are
implemented in `rustc`, this restriction appears to be inevitable. Note that referencing by
index works (though via a hack identical to that used in `BitVec`): one can write
`println!("{}", v[0])` for a `Vob` `v`, for example.


## Migrating from `BitVec`

`Vob` is directly inspired by the [`BitVec`](https://crates.io/crates/bit-vec) crate, but
aims to provide an interface more closely aligned to `Vec<bool>`. Several functions in
`BitVec` have different names in `Vob`, but porting is in general fairly simple. The main
semantic difference is that `Vob`s `clear()` function empties the `Vob` of contents
(i.e. sets its length to 0), whereas `BitVec`'s function of the same name unsets all bits
(keeping the length unchanged). The same effect as `BitVec`'s `clear` can be achieved by
using `Vob`'s `set_all(false)` function.
