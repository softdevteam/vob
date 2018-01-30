# Vector of Bits (Vob)

A Vob is a "vector of bits": a sequence of bits which exposes a `Vec`-like
interface. Whereas `Vec<bool>` requires 1 byte of storage per bit, `Vob`
requires only 1 bit of storage per bit. For larger numbers of bits, Vobs can
lead to a significant memory decrease and performance increase. `Vob` is broadly
similar to [BitVec](https://crates.io/crates/bitvec-rs), but has an API more
closely aligned to `Vec<bool>` and allows non-32-bit backing storage. On 64-bit
systems this can lead to a substantial performance increase.

`Vob` currently doesn't implement all of the same functions one would find in
`Vec<bool>`. We welcome contributions!
