//! A vector of bits ("Vob") is a sequence of bits which exposes a `Vec`-like interface. Whereas
//! `Vec<bool>` requires 1 byte of storage per bit, `Vob` requires only 1 bit of storage per bit.
//!
//! The main documentation for this crate can be found in the [`Vob`](struct.Vob.html) struct.

use std::{
    cmp::{min, PartialEq},
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    iter::FromIterator,
    mem::{replace, size_of},
    ops::{
        Bound::{Excluded, Included, Unbounded},
        Index, Range, RangeBounds,
    },
    slice,
};

use num_traits::{One, PrimInt, Zero};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A Vob is a "vector of bits": a sequence of bits which exposes a `Vec`-like interface. Whereas
/// `Vec<bool>` requires 1 byte of storage per bit, `Vob` requires only 1 bit of storage per bit.
/// For larger numbers of bits, Vobs can lead to a significant memory decrease and performance
/// increase.
///
/// # Examples
/// The `vob!` macro makes creating small `Vob`s easy:
///
/// ```rust
/// use vob::vob;
/// let mut v = vob![true, false, true];
/// assert_eq!(v[1], false);
/// ```
///
/// Operations such as `and`ing two `Vob`s together are quick; one can also quickly identify which
/// bits are set:
///
/// ```rust
/// use vob::Vob;
/// let mut v1 = Vob::from_elem(false, 256);
/// let mut v2 = Vob::from_elem(false, 256);
/// v1.set(67, true);
/// v2.set(67, true);
/// v1.set(188, true);
/// v1.and(&v2);
/// let num_bits_set = v1.iter_set_bits(..).count();
/// assert_eq!(num_bits_set, 1);
/// ```
///
///
/// ## Storage backing type
///
/// `Vob`s default to using `usize` as a storage backing type. This is generally a substantial win
/// over using smaller storage types if you use functions such as
/// [`or()`](struct.Vob.html#method.or). In such cases, `usize` on a 64-bit machine is almost
/// exactly twice as fast as using `u32`. If you only ever set and get individual bits, a smaller
/// data type might be marginally more effective: for such use cases `u32` is around 1% faster than
/// `usize` on a 64-bit machine. You can choose your own storage type with the
/// [`new_with_storage_type()`](struct.Vob.html#method.new_with_storage_type) constructor. In
/// general we recommend using the default `usize` backing storage unless you have rigorously
/// benchmarked your particular use case and are sure that a different storage type is superior.
///
///
/// ## Migrating from `Vec<bool>`
///
/// As far as possible, `Vob` is intended to have a superset of `Vec<bool>`'s interface, which
/// should make porting most code fairly simple. However, `Vec<bool>` contains several functions
/// which are not yet implemented in `Vob`: these are missing simply due to a lack of a current
/// use-case rather than because of any fundamental incompatibilities.
///
/// There is one missing feature which, currently, is impossible to implement: assignment to an
/// index. In other words one cannot currently express `v[0] = true` for a `Vob` `v`. Until
/// [`IndexGet` / `IndexMove` and equivalents](https://github.com/rust-lang/rfcs/issues/997) are
/// implemented in `rustc`, this restriction appears to be inevitable. Note that referencing by
/// index works (though via a hack identical to that used in `BitVec`): one can write
/// `println!("{}", v[0])` for a `Vob` `v`, for example.
///
///
/// ## Migrating from `BitVec`
///
/// `Vob` is directly inspired by the [`BitVec`](https://crates.io/crates/bit-vec), but aims to
/// provide an interface more closely aligned to `Vec<bool>` Several functions in `BitVec` have
/// different names in `Vob`, but porting is in general fairly simple. The main semantic difference
/// is that `Vob`s [`clear()`](struct.Vob.html#method.clear) function empties the `Vob` of contents
/// (i.e. sets its length to 0), whereas `BitVec`'s function of the same name unsets all bits
/// (keeping the length unchanged). The same effect as `BitVec`'s `clear` can be achieved by using
/// `Vob`'s [`set_all(false)`](struct.Vob.html#method.set_all) function.
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Vob<T = usize> {
    /// How many bits are stored in this Vob?
    len: usize,
    /// The underlying storage. We refer to a single instance of `T` as a block. Since the storage
    /// consists of (potentially multiple-byte) blocks, there may be "unused" bits in the final
    /// block. We guarantee that, at all points visible to the user, the "unused" bits are set to
    /// 0.
    vec: Vec<T>,
}

// In an ideal world, Rust's type defaults would allow us to fold the two impl blocks into one and
// say "impl Vob<T: usize>", but currently that doesn't work.
impl Vob<usize> {
    /// Constructs a new, empty Vob (with `usize` backing storage, which is likely to be the best
    /// choice in nearly all situations).
    ///
    /// The Vob will not allocate until elements are pushed onto it.
    pub fn new() -> Vob<usize> {
        Default::default()
    }

    /// Constructs a new, empty Vob (with `usize` backing storage, which is likely to be the best
    /// choice in nearly all situations) with the specified capacity.
    ///
    /// The Vob will be able to hold at least `capacity` elements without reallocating. If
    /// `capacity` is 0, the vector will not allocate.
    pub fn with_capacity(capacity: usize) -> Vob<usize> {
        Vob {
            len: 0,
            vec: Vec::with_capacity(blocks_required::<usize>(capacity)),
        }
    }

    /// Creates a Vob that holds `len` elements, setting each element to `value`.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let v = Vob::from_elem(true, 2);
    /// assert_eq!(v.len(), 2);
    /// assert_eq!(v.get(0), Some(true));
    /// ```
    pub fn from_elem(value: bool, len: usize) -> Vob<usize> {
        let mut v = Vob {
            len,
            vec: vec![if value { !0 } else { 0 }; blocks_required::<usize>(len)],
        };
        v.mask_last_block();
        v
    }

    /// Create a Vob from a `u8` slice. The most significant bit of each byte comes first in the
    /// resulting Vob.
    ///
    /// # Examples
    ///
    /// ```
    /// use vob::{Vob, vob};
    /// let v = Vob::from_bytes(&[0b10100000, 0b00010010]);
    /// assert_eq!(v, vob![true, false, true, false, false, false, false, false,
    ///                    false, false, false, true, false, false, true, false]);
    /// ```
    pub fn from_bytes(slice: &[u8]) -> Vob<usize> {
        let new_len = slice.len().checked_mul(8).expect("Overflow detected");
        let mut v = Vob::with_capacity(new_len);
        for i in 0..blocks_required::<usize>(new_len) {
            let mut w = usize::zero();
            for j in 0..bytes_per_block::<usize>() {
                let off = i * bytes_per_block::<usize>() + j;
                if off >= slice.len() {
                    // If slice doesn't contain a whole number of words, we'll end up with one
                    // block at the end with "missing" bytes; since these are equivalent to 0, we
                    // can simply ignore the fact they're missing.
                    continue;
                }
                let b = slice[off];
                #[cfg(not(reverse_bits))]
                {
                    if b != 0 {
                        {
                            let mut rb: u8 = 0; // the byte b with its bits in reverse order
                            for k in 0..8 {
                                rb |= ((b >> k) & 1) << (8 - k - 1);
                            }
                            w |= (rb as usize) << (j * 8);
                        }
                    }
                }
                #[cfg(reverse_bits)]
                {
                    w |= (b.reverse_bits() as usize) << (j * 8);
                }
            }
            v.vec.push(w);
        }
        v.len = new_len;
        v
    }
}

impl<T: Debug + PrimInt + One + Zero> Vob<T> {
    /// Constructs a new, empty Vob (with a user-defined backing storage type) with the given
    /// capacity.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::<u32>::new_with_storage_type(0);
    /// v.push(true);
    /// assert_eq!(v[0], true);
    /// ```
    pub fn new_with_storage_type(capacity: usize) -> Vob<T> {
        Vob {
            len: 0,
            vec: Vec::with_capacity(blocks_required::<T>(capacity)),
        }
    }

    /// Returns the number of bits the Vob can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// assert_eq!(Vob::new().capacity(), 0);
    /// assert!(Vob::with_capacity(1).capacity() >= 1);
    /// ```
    pub fn capacity(&self) -> usize {
        // This multiplication can't overflow because of the checks in reserve()
        self.vec.capacity() * bits_per_block::<T>()
    }

    /// Reserves capacity for at least `additional` more bits to be inserted in the Vob. The Vob
    /// may reserve more space to avoid frequent reallocations. After calling `reserve`, capacity
    /// will be greater than or equal to `self.len() + additional`. Does nothing if capacity is
    /// already sufficient.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.reserve(1);
    /// assert!(v.capacity() >= 1);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let unused_bits: usize = self.capacity() - self.len();
        if additional > unused_bits {
            // Will never overflow because additional > current
            let needed_extra_bits = additional - unused_bits;
            // still need to check if we won't overflow the capacity() computation
            self.capacity()
                .checked_add(needed_extra_bits)
                .expect("Overflow detected");
            self.vec.reserve(blocks_required::<T>(needed_extra_bits));
        }
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// vector that there is space for a few more elements.
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit();
    }

    /// Shortens the Vob, keeping the first `len` elements and dropping the rest.
    ///
    /// If len is greater than the vector's current length, this has no effect.
    ///
    /// The drain method can emulate truncate, but causes the excess elements to be returned
    /// instead of dropped.
    ///
    /// Note that this method has no effect on the allocated capacity of the vector.
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v = vob![true, false, true];
    /// v.truncate(2);
    /// assert_eq!(v, vob![true, false]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if len > self.len {
            return;
        }
        self.len = len;
        self.vec.truncate(blocks_required::<T>(len));
        self.mask_last_block();
    }

    /// Appends a bool to the back of the Vob.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(true);
    /// v.push(false);
    /// assert_eq!(v.get(0), Some(true));
    /// assert_eq!(v.get(1), Some(false));
    /// ```
    pub fn push(&mut self, value: bool) {
        debug_assert_eq!(self.vec.len(), blocks_required::<T>(self.len));
        if self.len % bits_per_block::<T>() == 0 {
            self.vec.push(T::zero());
        }
        let i = self.len;
        self.len = i.checked_add(1).expect("Overflow detected");
        self.set(i, value);
    }

    /// Removes the last element from the Vob and returns it, or `None` if it is empty.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(true);
    /// assert_eq!(v.pop(), Some(true));
    /// assert_eq!(v.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<bool> {
        if self.len == 0 {
            return None;
        }
        // The subtraction can't underflow because self.len > 0.
        let v = self.get(self.len - 1);
        debug_assert!(v.is_some());
        let new_len = self.len - 1;
        self.truncate(new_len);
        v
    }

    /// Returns the number of elements in the Vob.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the Vob has a length of 0.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// assert_eq!(Vob::from_elem(true, 2).is_empty(), false);
    /// assert_eq!(Vob::new().is_empty(), true);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated Self. self contains elements [0, at), and the returned Self
    /// contains elements [at, len).
    ///
    /// Note that the capacity of self does not change.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v1 = Vob::new();
    /// v1.push(true);
    /// v1.push(false);
    /// let v2 = v1.split_off(1);
    /// assert_eq!(v1, Vob::from_elem(true, 1));
    /// assert_eq!(v2, Vob::from_elem(false, 1));
    /// ```
    pub fn split_off(&mut self, at: usize) -> Vob<T> {
        debug_assert_eq!(self.vec.len(), blocks_required::<T>(self.len));
        if at >= self.len {
            // Return empty Vob
            return Vob::<T>::new_with_storage_type(0);
        } else if at == 0 {
            // efficiently swap structs
            let mut result = Vob::<T>::new_with_storage_type(0);
            result.vec = replace(&mut self.vec, result.vec);
            result.len = replace(&mut self.len, result.len);
            debug_assert_eq!(self.len, 0);
            debug_assert_eq!(self.vec.len(), 0);
            return result;
        }

        let block_to_split = blocks_required::<T>(at) - 1;
        let ub = at % bits_per_block::<T>();

        let mut nv = Vob::<T>::new_with_storage_type(self.len - at);

        // If ub == 0, we shouldn't copy block_to_split into the new Vob, because it fully fits
        // into the old Vob.
        if ub > 0 {
            // The number of bits from block_to_split that end up in the new Vob
            let first_block_len = if bits_per_block::<T>() - ub > self.len - at {
                self.len - at
            } else {
                bits_per_block::<T>() - ub
            };

            nv.vec.push(self.vec[block_to_split] >> ub);
            nv.len = first_block_len;
            nv.mask_last_block();
        }

        // We only need to do this if there are blocks remaining
        if self.vec.len() > block_to_split + 1 {
            nv.extend_blocks(self, block_to_split + 1);
        }

        self.truncate(at);
        nv
    }

    /// Returns the value of the element at position `index` or `None` if out of bounds.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// assert_eq!(v.get(0), Some(false));
    /// assert_eq!(v.get(1), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len {
            return None;
        }
        let blk = self.vec[block_offset::<T>(index)];
        Some(blk & (T::one() << (index % bits_per_block::<T>())) != T::zero())
    }

    /// Sets the value of the element at position `index`. Returns `true` if this led to a change
    /// in the underlying storage or `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.set(0, true);
    /// assert_eq!(v.get(0), Some(true));
    /// assert_eq!(v.set(0, false), true);
    /// assert_eq!(v.set(0, false), false);
    /// ```
    ///
    /// # Panics
    ///
    /// If `index` is out of bounds.
    pub fn set(&mut self, index: usize, value: bool) -> bool {
        if index >= self.len {
            panic!(
                "Index out of bounds: the len is {} but the index is {}",
                self.len, index
            );
        }
        let msk = T::one() << (index % bits_per_block::<T>());
        let off = block_offset::<T>(index);
        let old_v = self.vec[off];
        let new_v = if value { old_v | msk } else { old_v & !msk };
        if new_v != old_v {
            self.vec[off] = new_v;
            true
        } else {
            false
        }
    }

    /// Returns an iterator over the slice.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.push(true);
    /// let mut iterator = v.iter();
    /// assert_eq!(iterator.next(), Some(false));
    /// assert_eq!(iterator.next(), Some(true));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            vob: self,
            range: 0..self.len,
        }
    }

    /// Convert a `RangeBounds` into a `Range`, taking into account this `Vob`'s length.
    fn process_range<R>(&self, range: R) -> Range<usize>
    where
        R: RangeBounds<usize>,
    {
        let start = match range.start_bound() {
            Included(t) => min(*t, self.len),
            Excluded(t) => min(*t + 1, self.len),
            Unbounded => 0,
        };
        let end = match range.end_bound() {
            Included(t) => min(*t + 1, self.len()),
            Excluded(t) => min(*t, self.len()),
            Unbounded => self.len,
        };
        Range { start, end }
    }

    /// Returns an iterator which efficiently produces the index of each set bit in the specified
    /// range. Assuming appropriate support from your CPU, this is much more efficient than
    /// checking each bit individually.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.push(true);
    /// let mut iterator = v.iter_set_bits(..);
    /// assert_eq!(iterator.next(), Some(1));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter_set_bits<R>(&self, range: R) -> IterSetBits<T>
    where
        R: RangeBounds<usize>,
    {
        IterSetBits {
            vob: self,
            range: self.process_range(range),
        }
    }

    /// Returns an iterator which efficiently produces the index of each unset bit in the specified
    /// range. Assuming appropriate support from your CPU, this is much more efficient than
    /// checking each bit individually.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.push(true);
    /// let mut iterator = v.iter_unset_bits(..);
    /// assert_eq!(iterator.next(), Some(0));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter_unset_bits<R>(&self, range: R) -> IterUnsetBits<T>
    where
        R: RangeBounds<usize>,
    {
        IterUnsetBits {
            vob: self,
            range: self.process_range(range),
        }
    }

    /// Return an iterator over the underlying storage blocks. The last block is guaranteed to have
    /// "unused" bits (i.e. those past `self.len()`) set to 0.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let v1 = Vob::from_elem(true, 10);
    /// assert_eq!(v1.iter_storage().next(), Some((1 << 10) - 1));
    /// let v2 = Vob::from_elem(true, 129);
    /// assert_eq!(v2.iter_storage().last(), Some(1));
    /// ```
    pub fn iter_storage(&self) -> StorageIter<T> {
        StorageIter {
            iter: self.vec.iter(),
        }
    }

    /// Resizes the Vob in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the Vob is extended by the difference, with each
    /// additional slot filled with `value`. If `new_len` is less than `len`, the vob is simply
    /// truncated.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.resize(129, true);
    /// assert_eq!(v.len(), 129);
    /// assert_eq!(v.get(0), Some(false));
    /// assert_eq!(v.get(128), Some(true));
    /// ```
    pub fn resize(&mut self, new_len: usize, value: bool) {
        if new_len <= self.len {
            self.truncate(new_len);
            return;
        }
        if value && self.len > 0 {
            // If we're resizing with trues, we need to extend the last block with true bits. We
            // can rely on mask_last_block to trim any unwanted bits we add in this process.
            let off = block_offset::<T>(self.len);
            let v = self.vec[off];
            self.vec[off] = v | (T::max_value() << (self.len % bits_per_block::<T>()));
        }
        self.vec.resize(
            blocks_required::<T>(new_len),
            if value { T::max_value() } else { T::zero() },
        );
        self.len = new_len;
        self.mask_last_block();
    }

    /// Appends all elements in a slice to the Vob.
    ///
    /// Iterates over the slice `other` and appends elements in order.
    ///
    /// Note that this function is same as extend except that it is specialized to work with slices
    /// instead. If and when Rust gets specialization this function will likely be deprecated (but
    /// still available).
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v = vob![true];
    /// v.extend_from_slice(&vec![false, true]);
    /// assert_eq!(v, vob![true, false, true]);
    /// ```
    pub fn extend_from_slice(&mut self, other: &[bool]) {
        for &blk in other.iter() {
            self.push(blk);
        }
    }

    /// Append all elements from a second Vob to this Vob.
    ///
    /// Use this instead of `extend()` when extending with a Vob, because this method is a lot
    /// faster.
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v1 = vob![true];
    /// let v2 = vob![false, false];
    /// v1.extend_from_vob(&v2);
    /// assert_eq!(v1, vob![true, false, false]);
    /// ```
    pub fn extend_from_vob(&mut self, other: &Vob<T>) {
        self.extend_blocks(other, 0);
    }

    /// Copy entire blocks from other into self, respecting offset.
    ///
    /// block_offset * bits_per_block should be less than other.len
    fn extend_blocks(&mut self, other: &Vob<T>, block_offset: usize) {
        debug_assert!(block_offset * bits_per_block::<T>() <= other.len(),);
        debug_assert_eq!(self.vec.len(), blocks_required::<T>(self.len));
        self.reserve(other.len());
        // used bits in last block
        let ub = self.len % bits_per_block::<T>();
        if ub == 0 {
            // If there are no unused bits, we can just push the new blocks
            self.vec.extend(other.vec.iter().skip(block_offset));
        } else {
            // We need to do things very carefully here. We need to shift each block ub to the
            // left. We use rotate to move those bits to the bottom part of the integer. Then we
            // add the bytes to the last block of this one.
            //
            // We're relying on the bit ordering here. We're also relying on the last bits to be 0.

            // this mask has the last ub bits set
            let msk = (T::one() << ub) - T::one();

            for block in other.vec.iter().skip(block_offset) {
                // rotate block to the left
                let new_block: T = block.rotate_left(ub as u32);
                {
                    let last = self.vec.last_mut().unwrap();
                    debug_assert_eq!(*last & !msk, T::zero());
                    // add the last (upper) bits of new_block
                    // ex: ub=4; 0000101 | 1110111 & !(0001111)
                    //   =>      0000101 | 1110000 => 1110101
                    *last = *last | new_block & !msk;
                }
                // add the last block with the lower (first) bits set
                self.vec.push(new_block & msk);
            }
        }

        // Compute new length for self.
        let new_len = self
            .len
            //  the subtraction won't overflow because of the bounds assumption above.
            .checked_add(other.len() - block_offset * bits_per_block::<T>())
            .expect("Overflow detected");

        // We need to truncate because we always push the last block from other even if it's empty.
        self.vec.truncate(blocks_required::<T>(new_len));

        // correct len
        self.len = new_len;
        self.mask_last_block();
    }

    /// Clears the Vob, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the Vob.
    pub fn clear(&mut self) {
        self.len = 0;
        self.vec.clear();
    }

    /// Sets all bits in the Vob to `value`. Notice that this does not change the number of bits
    /// stored in the Vob.
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v = vob![true, false, true];
    /// v.set_all(false);
    /// assert_eq!(v, vob![false, false, false]);
    /// ```
    pub fn set_all(&mut self, value: bool) {
        for blk in self.vec.iter_mut() {
            *blk = if value { T::max_value() } else { T::zero() };
        }
        self.mask_last_block();
    }

    /// Negates all bits in the Vob.
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v = vob![true, false];
    /// v.negate();
    /// assert_eq!(v, vob![false, true]);
    /// ```
    pub fn negate(&mut self) {
        for blk in self.vec.iter_mut() {
            *blk = !*blk;
        }
        self.mask_last_block();
    }

    /// For each bit in this Vob, `and` it with the corresponding bit in `other`, returning `true`
    /// if this led to any changes or `false` otherwise. The two Vobs must have the same number of
    /// bits.
    ///
    /// # Panics
    ///
    /// If the two Vobs are of different length.
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v1 = vob![true, false, false];
    /// let v2 = vob![true, true, false];
    /// assert_eq!(v1.and(&v2), false);
    /// assert_eq!(v1, vob![true, false, false]);
    /// ```
    pub fn and(&mut self, other: &Vob<T>) -> bool {
        if self.len != other.len {
            panic!(
                "Cannot 'and' two Vobs of different length ({}  {})",
                self.len, other.len
            );
        }
        let mut chngd = false;
        for (self_blk, other_blk) in self.vec.iter_mut().zip(other.vec.iter()) {
            let old_v = *self_blk;
            let new_v = old_v & *other_blk;
            *self_blk = new_v;
            chngd |= old_v != new_v;
        }
        // We don't need to mask the last block as those bits can't be set by "&" by definition.
        chngd
    }

    /// For each bit in this Vob, `or` it with the corresponding bit in `other`, returning `true`
    /// if this led to any changes or `false` otherwise. The two Vobs must have the same number of
    /// bits.
    ///
    /// # Panics
    ///
    /// If the two Vobs are of different length.
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v1 = vob![true, false, false];
    /// let v2 = vob![false, true, false];
    /// assert_eq!(v1.or(&v2), true);
    /// assert_eq!(v1, vob![true, true, false]);
    /// ```
    pub fn or(&mut self, other: &Vob<T>) -> bool {
        if self.len != other.len {
            panic!(
                "Cannot 'or' two Vobs of different length ({}  {})",
                self.len, other.len
            );
        }
        let mut chngd = false;
        for (self_blk, other_blk) in self.vec.iter_mut().zip(other.vec.iter()) {
            let old_v = *self_blk;
            let new_v = old_v | *other_blk;
            *self_blk = new_v;
            chngd |= old_v != new_v;
        }
        // We don't need to mask the last block per our assumptions
        chngd
    }

    /// For each bit in this Vob, `xor` it with the corresponding bit in `other`, returning `true`
    /// if this led to any changes or `false` otherwise. The two Vobs must have the same number of
    /// bits.
    ///
    /// # Panics
    ///
    /// If the two Vobs are of different length.
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v1 = vob![true, false, true];
    /// let v2 = vob![false, true, true];
    /// assert_eq!(v1.xor(&v2), true);
    /// assert_eq!(v1, vob![true, true, false]);
    /// ```
    pub fn xor(&mut self, other: &Vob<T>) -> bool {
        if self.len != other.len {
            panic!(
                "Cannot 'xor' two Vobs of different length ({}  {})",
                self.len, other.len
            );
        }
        let mut chngd = false;
        for (self_blk, other_blk) in self.vec.iter_mut().zip(other.vec.iter()) {
            let old_v = *self_blk;
            let new_v = old_v ^ *other_blk;
            *self_blk = new_v;
            chngd |= old_v != new_v;
        }
        // We don't need to mask the last block per our assumptions
        chngd
    }

    // contents for the feature-guarded implementations next.
    #[inline]
    fn _mask_last_block(&mut self) {
        debug_assert_eq!(self.vec.len(), blocks_required::<T>(self.len));
        let ub = self.len % bits_per_block::<T>();
        // If there are no unused bits, there's no need to perform masking.
        if ub > 0 {
            let msk = (T::one() << ub) - T::one();
            let off = block_offset::<T>(self.len);
            let old_v = self.vec[off];
            let new_v = old_v & msk;
            if new_v != old_v {
                self.vec[off] = new_v;
            }
        }
    }

    /// We guarantee that the last storage block has no bits set past the "last" bit: this function
    /// clears any such bits.
    #[cfg(not(feature = "unsafe_internals"))]
    // see also the public implementation next.
    fn mask_last_block(&mut self) {
        self._mask_last_block()
    }

    /// We guarantee that the last storage block has no bits set past the "last" bit: this function
    /// clears any such bits.
    ///
    /// This otherwise private function is exposed when `unsafe_internals` is enabled, to help
    /// callers maintain the internal assumptions.
    #[cfg(feature = "unsafe_internals")]
    pub fn mask_last_block(&mut self) {
        self._mask_last_block()
    }
}

#[cfg(feature = "unsafe_internals")]
impl<T> Vob<T> {
    /// Get a mutable reference to the underlying data structure
    ///
    /// This is marked as unsafe as it allows to invalidate the assumptions made by this module.
    /// It is not in itself unsafe.
    ///
    /// # Assumptions:
    ///
    /// * `Vob` stores the bits in a little-endian order.
    /// * The length can't change, or must be updated using `Vob::set_len()`.
    /// * Any bits past `self.len()` must be set to 0 in the last block.
    ///   `Vob::mask_last_block()` can help you with that.
    /// * `storage.len()` can not be larger than `ceil(self.len() / (8 * size_of::<T>))`
    ///
    /// # Examples
    /// ```
    /// use vob::vob;
    /// let mut v1 = vob![true, false, true];
    /// let storage = unsafe { v1.get_storage_mut() };
    /// assert_eq!(storage[0], 0b101);
    /// ```
    pub unsafe fn get_storage_mut(&mut self) -> &mut Vec<T> {
        &mut self.vec
    }

    /// Get a reference to the underlying data structure
    ///
    /// `Vob` stores the bits in little-endian order. Any bits beyond `self.len()` in the last
    /// block are `0`.
    ///
    /// ```
    /// use vob::vob;
    /// let v1 = vob![true, true, false];
    /// let storage = unsafe { v1.get_storage() };
    /// assert_eq!(storage[0], 0b011);
    /// ```
    pub fn get_storage(&self) -> &[T] {
        self.vec.as_ref()
    }

    /// Set the length of the `Vob`.
    ///
    /// This will explicitly set the length of the Vob,
    /// without actually modifying the underlying data structure
    /// or doing any checks.
    ///
    /// If you want to shorten your `Vob`, you're probably looking
    /// for `truncate`.
    ///
    /// See `Vob::get_storage_mut()` for the other requirements.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v1 = Vob::<u8>::new_with_storage_type(9);
    /// v1.push(true);
    /// v1.push(false);
    /// {
    ///     let mut storage = unsafe { v1.get_storage_mut() };
    ///     // push another block
    ///     storage.push(0b1);
    /// }
    /// // we know that 9 bits are initialised now as the previously-unused remainder of block 0 must be zero.
    /// unsafe { v1.set_len(9); }
    /// assert_eq!(v1[0], true);
    /// assert_eq!(v1[1], false);
    /// assert_eq!(v1[2], false);
    /// assert_eq!(v1[8], true);
    /// ```
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }
}

impl Default for Vob<usize> {
    fn default() -> Self {
        Vob {
            len: 0,
            vec: Vec::new(),
        }
    }
}

impl<T: Debug + One + PrimInt + Zero> Debug for Vob<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Vob[")?;
        for blk in self {
            write!(fmt, "{}", if blk { 1 } else { 0 })?;
        }
        write!(fmt, "]")?;
        Ok(())
    }
}

impl<T: Debug + One + PrimInt + Zero> Extend<bool> for Vob<T> {
    fn extend<I: IntoIterator<Item = bool>>(&mut self, iterable: I) {
        let iterator = iterable.into_iter();
        let (min, _) = iterator.size_hint();
        self.reserve(min);
        for e in iterator {
            self.push(e)
        }
    }
}

impl FromIterator<bool> for Vob<usize> {
    /// Create a Vob from an iterator.
    ///
    /// # Examples
    /// ```
    /// use std::iter::FromIterator;
    /// use vob::Vob;
    /// let v = Vob::from_iter(vec![true, false]);
    /// assert_eq!(v, Vob::from_iter(vec![true, false]));
    /// ```
    fn from_iter<I: IntoIterator<Item = bool>>(iter: I) -> Self {
        let mut v = Vob::new();
        v.extend(iter);
        v
    }
}

// This is based on the `BitVec` approach to indices. It's clearly a horrible way of doing things,
// but until `IndexGet` is implemented, we're stuck.
static TRUE: bool = true;
static FALSE: bool = false;

impl<T: Debug + One + PrimInt + Zero> Index<usize> for Vob<T> {
    type Output = bool;

    fn index(&self, index: usize) -> &bool {
        match self.get(index) {
            Some(true) => &TRUE,
            Some(false) => &FALSE,
            None => panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len, index
            ),
        }
    }
}

#[derive(Clone)]
pub struct Iter<'a, T: 'a> {
    vob: &'a Vob<T>,
    range: Range<usize>,
}

impl<'a, T: Debug + One + PrimInt + Zero> Iterator for Iter<'a, T> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        self.range.next().map(|i| self.vob.get(i).unwrap())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

impl<'a, T: Debug + One + PrimInt + Zero> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<bool> {
        self.range.next_back().map(|i| self.vob.get(i).unwrap())
    }
}

impl<'a, T: Debug + One + PrimInt + Zero> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T: Debug + One + PrimInt + Zero> IntoIterator for &'a Vob<T> {
    type Item = bool;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[derive(Clone)]
pub struct IterSetBits<'a, T: 'a> {
    vob: &'a Vob<T>,
    range: Range<usize>,
}

impl<'a, T: Debug + One + PrimInt + Zero> Iterator for IterSetBits<'a, T> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        debug_assert!(self.range.end <= self.vob.len);
        if let Some(i) = self.range.next() {
            // This is a long, but fairly fast, way of finding out what the next set bit is. The
            // basic problem is that we have no idea where the next set bit is -- but different
            // patterns of set bits are most efficiently handled by different code paths. This code
            // is thus a compromise: we prioritise two special cases (all bits set; all bits unset)
            // for efficiency, and try and make the other possible cases reasonably fast.
            let mut b = block_offset::<T>(i);
            let mut v = self.vob.vec[b];
            // If all bits are set, we don't need to do any complicated checks.
            if v == T::max_value() {
                return Some(i);
            }
            // At this point we've got a block which might or might not have some bits set. We now
            // fall back to the general case.
            let mut i_off = i % bits_per_block::<T>();
            loop {
                let tz = (v >> i_off).trailing_zeros() as usize;
                if tz < bits_per_block::<T>() {
                    // There is a bit set after i_off in the block.
                    let bs = b * bits_per_block::<T>() + i_off + tz;
                    self.range.start = bs + 1;
                    if bs >= self.range.end {
                        break;
                    }
                    return Some(bs);
                }
                b += 1;
                if b == blocks_required::<T>(self.range.end) {
                    // We've exhausted the iterator.
                    self.range.start = self.range.end;
                    break;
                }
                v = self.vob.vec[b];
                i_off = 0;
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

#[derive(Clone)]
pub struct IterUnsetBits<'a, T: 'a> {
    vob: &'a Vob<T>,
    range: Range<usize>,
}

impl<'a, T: Debug + One + PrimInt + Zero> Iterator for IterUnsetBits<'a, T> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        debug_assert!(self.range.end <= self.vob.len);
        if let Some(i) = self.range.next() {
            // This is a long, but fairly fast, way of finding out what the next usset bit is. The
            // basic problem is that we have no idea where the next set bit is -- but different
            // patterns of set bits are most efficiently handled by different code paths. This code
            // is thus a compromise: we prioritise two special cases (all bits set; all bits unset)
            // for efficiency, and try and make the other possible cases reasonably fast.
            let mut b = block_offset::<T>(i);
            let mut v = self.vob.vec[b];
            // If no bits are set, we don't need to do any complicated checks.
            if v == T::zero() {
                return Some(i);
            }
            // At this point we've got a block which might or might not have some bits unset. We
            // now fall back to the general case.
            let mut i_off = i % bits_per_block::<T>();
            loop {
                let tz = (!v >> i_off).trailing_zeros() as usize;
                if tz < bits_per_block::<T>() {
                    // There is another bit unset after i_off in the block.
                    let bs = b * bits_per_block::<T>() + i_off + tz;
                    self.range.start = bs + 1;
                    if bs >= self.range.end {
                        // The unset bit is after the range we're looking for, so we've reached
                        // the end of the iterator.
                        break;
                    }
                    return Some(bs);
                }
                b += 1;
                if b == blocks_required::<T>(self.range.end) {
                    // We've exhausted the iterator.
                    self.range.start = self.range.end;
                    break;
                }
                v = self.vob.vec[b];
                i_off = 0;
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

impl<T: Debug + One + PrimInt + Zero> PartialEq for Vob<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        self.iter_storage()
            .zip(other.iter_storage())
            .all(|(w1, w2)| w1 == w2)
    }
}

impl<T: Debug + One + PrimInt + Zero> Eq for Vob<T> {}

impl<T: Debug + Hash + One + PrimInt + Zero> Hash for Vob<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for blk in self.iter_storage() {
            blk.hash(state);
        }
    }
}

#[derive(Clone)]
pub struct StorageIter<'a, B: 'a> {
    iter: slice::Iter<'a, B>,
}

impl<'a, T: Debug + One + PrimInt + Zero> Iterator for StorageIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.iter.next().cloned()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// How many bits are stored in each underlying storage block?
fn bits_per_block<T>() -> usize {
    bytes_per_block::<T>() * 8
}

/// How many bytes are stored in each underlying storage block?
fn bytes_per_block<T>() -> usize {
    size_of::<T>()
}

/// Return the offset in the vector of the storage block storing the bit `off`.
fn block_offset<T>(off: usize) -> usize {
    off / bits_per_block::<T>()
}

/// Takes as input a number of bits requiring storage; returns an aligned number of blocks needed
/// to store those bits.
fn blocks_required<T>(num_bits: usize) -> usize {
    num_bits / bits_per_block::<T>()
        + if num_bits % bits_per_block::<T>() == 0 {
            0
        } else {
            1
        }
}

#[macro_export]
/// Create a `Vob` from a list of boolean values.
///
/// # Examples
///
/// ```
/// use vob::{vob, Vob};
///
/// let v1 = vob![true, false];
/// let mut v2 = Vob::new();
/// v2.push(true);
/// v2.push(false);
/// assert_eq!(v1, v2);
/// println!("{:?}", vob![10; true]);
/// ```
macro_rules! vob {
    (@single $($x:tt)*) => (());
    // handle trailing comma until https://github.com/rust-lang/rust/issues/48075
    // (macro_at_most_once_rep) stabilises
    ($($rest:expr),+,) => ( vob!($($rest),+) );
    (@count $($rest:expr),*) => (<[()]>::len(&[$(vob!(@single $rest)),*]));
    ($elem:expr; $n:expr) => (
        $crate::Vob::from_elem($n, $elem)
    );
    () => (Vob::new());
    ($($x:expr),*) => ({
        let c = vob!(@count $($x),*);
        let mut vob = $crate::Vob::with_capacity(c);
        $(
            vob.push($x);
        )*
        vob
    });
}

#[cfg(test)]
mod tests {
    use super::{block_offset, blocks_required, Vob};
    use rand::{self, Rng};
    use std::{
        collections::hash_map::DefaultHasher,
        hash::{Hash, Hasher},
        iter::FromIterator,
        mem::size_of,
    };

    #[test]
    fn test_block_offset() {
        assert_eq!(block_offset::<usize>(0), 0);
        assert_eq!(block_offset::<usize>(1), 0);
        assert_eq!(block_offset::<usize>(2), 0);
        assert_eq!(block_offset::<usize>(size_of::<usize>() * 8 - 1), 0);
        assert_eq!(block_offset::<usize>(size_of::<usize>() * 8), 1);
    }

    #[test]
    fn test_blocks_required() {
        assert_eq!(blocks_required::<usize>(0), 0);
        assert_eq!(blocks_required::<usize>(1), 1);
        assert_eq!(blocks_required::<usize>(2), 1);
        assert_eq!(blocks_required::<usize>(size_of::<usize>() * 8), 1);
        assert_eq!(blocks_required::<usize>(size_of::<usize>() * 8 + 1), 2);
    }

    #[test]
    fn test_non_usize_storage() {
        let mut v = Vob::<u8>::new_with_storage_type(0);
        for _ in 0..size_of::<u8>() * 8 {
            v.push(true);
        }
        assert_eq!(v.get(0), Some(true));
        assert_eq!(v.get(size_of::<u8>() * 8 - 1), Some(true));
        assert_eq!(v.get(size_of::<u8>() * 8), None);
        v.push(true);
        assert_eq!(v.get(size_of::<u8>() * 8), Some(true));
        v.set(size_of::<u8>() * 8, false);
        assert_eq!(v.get(size_of::<u8>() * 8), Some(false));
        assert_eq!(v.get(size_of::<u8>() * 8 + 1), None);
        assert_eq!(v.set(size_of::<u8>() * 8, true), true);
        assert_eq!(v.set(size_of::<u8>() * 8, true), false);
        assert_eq!(v.get(size_of::<u8>() * 8 - 1), Some(true));
        assert_eq!(v.get(size_of::<u8>() * 8 - 2), Some(true));
    }

    #[test]
    fn test_capacity() {
        assert_eq!(Vob::new().capacity(), 0);
        assert_eq!(
            Vob::with_capacity(size_of::<usize>() * 8 + 1).capacity(),
            size_of::<usize>() * 8 * 2
        );
    }

    #[test]
    fn test_reserve() {
        let mut v = Vob::new();
        v.reserve(10);
        assert!(v.capacity() >= size_of::<usize>() * 8);
        v.reserve(10);
        assert!(v.capacity() >= size_of::<usize>() * 8, "over-reserved");
        v.push(true); // make sure there's less space than 64 still available
        v.reserve(size_of::<usize>() * 8);
        assert!(v.capacity() >= size_of::<usize>() * 8 * 2);
    }

    #[test]
    #[should_panic(expected = "Overflow detected")]
    fn test_reserve_panic() {
        let mut v = Vob::new();
        v.push(true);
        v.push(true);
        v.reserve(usize::max_value());
    }

    #[test]
    fn test_beyond_a_word() {
        let mut v = Vob::new();
        for _ in 0..size_of::<usize>() * 8 {
            v.push(true);
        }
        assert_eq!(v.get(0), Some(true));
        assert_eq!(v.get(size_of::<usize>() * 8 - 1), Some(true));
        assert_eq!(v.get(size_of::<usize>() * 8), None);
        v.push(true);
        assert_eq!(v.get(size_of::<usize>() * 8), Some(true));
        v.set(size_of::<usize>() * 8, false);
        assert_eq!(v.get(size_of::<usize>() * 8), Some(false));
        assert_eq!(v.get(size_of::<usize>() * 8 + 1), None);
        assert_eq!(v.set(size_of::<usize>() * 8, true), true);
        assert_eq!(v.set(size_of::<usize>() * 8, true), false);
        assert_eq!(v.get(size_of::<usize>() * 8 - 1), Some(true));
        assert_eq!(v.get(size_of::<usize>() * 8 - 2), Some(true));
    }

    #[test]
    #[should_panic]
    fn test_set_beyond_a_word() {
        let mut v = vob![true];
        assert!(v.set(0, false), true);
        v.set(1, true);
    }

    #[test]
    fn test_from_bytes() {
        let v = Vob::from_bytes(&[]);
        assert_eq!(v, vob![]);

        // Example adopted from BitVec
        let v = Vob::from_bytes(&[0b10100000, 0b00010010]);
        assert_eq!(
            v,
            vob![
                true, false, true, false, false, false, false, false, false, false, false, true,
                false, false, true, false
            ]
        );

        // On a 64-bit machine, make sure we test that a complete word is dealt with correctly.
        let v = Vob::from_bytes(&[
            0b10100000, 0b00010010, 0b00110101, 0b11001010, 0b00110001, 0b10010101, 0b01111100,
            0b01010001,
        ]);
        assert_eq!(
            v,
            vob![
                true, false, true, false, false, false, false, false, false, false, false, true,
                false, false, true, false, false, false, true, true, false, true, false, true,
                true, true, false, false, true, false, true, false, false, false, true, true,
                false, false, false, true, true, false, false, true, false, true, false, true,
                false, true, true, true, true, true, false, false, false, true, false, true, false,
                false, false, true
            ]
        );
    }

    #[test]
    fn test_truncate() {
        let mut v = Vob::from_elem(true, 2 * size_of::<usize>() * 8 + 1);
        assert_eq!(v, Vob::from_elem(true, 2 * size_of::<usize>() * 8 + 1));
        v.truncate(2 * size_of::<usize>() * 8 + 1);
        assert_eq!(v, Vob::from_elem(true, 2 * size_of::<usize>() * 8 + 1));
        v.truncate(3 * size_of::<usize>() * 8 + 1);
        assert_eq!(v, Vob::from_elem(true, 2 * size_of::<usize>() * 8 + 1));
        v.truncate(0);
        assert_eq!(v, Vob::new());
    }

    #[test]
    fn test_is_empty() {
        assert_eq!(vob![].is_empty(), true);
        assert_eq!(vob![true].is_empty(), false);
    }

    #[test]
    fn test_resize() {
        let mut v = Vob::new();
        v.resize(1, true);
        assert_eq!(v[0], true);

        let mut v = Vob::new();
        v.push(false);
        v.resize(129, true);
        assert_eq!(v.len(), 129);
        assert_eq!(v.get(0), Some(false));
        assert_eq!(v.get(1), Some(true));
        assert_eq!(v.get(128), Some(true));
        v.resize(1, true);
        assert_eq!(v.len(), 1);
        assert_eq!(v.get(0), Some(false));

        let mut v = Vob::new();
        v.push(false);
        v.resize(2, true);
        assert_eq!(v.len(), 2);
        assert_eq!(v.get(0), Some(false));
        assert_eq!(v.get(1), Some(true));
    }

    #[test]
    fn test_mask_last_block1() {
        let mut v = Vob::<u64>::new_with_storage_type(0);
        v.extend(vob![true, true].iter());
        assert_eq!(v.vec, vec![3]);

        v.vec[0] = 0xaaaaaaaa;
        v.len = 7;
        v.mask_last_block();
        assert_eq!(v.vec, vec![42]);

        v.len = 30;
        v.vec[0] = 0xffffaaaa;
        v.mask_last_block();
        assert_eq!(v.vec, vec![1073719978]);
    }

    #[test]
    fn test_mask_last_block2() {
        let mut v = Vob::<u64>::new_with_storage_type(128);
        for _ in 0..128 {
            v.push(true);
        }
        let full_block = 0xffffffffffffffff;
        assert_eq!(v.vec, vec![full_block, full_block]);

        let one_zero = 0xaaaaaaaaaaaaaaaa;
        v.len = 68;
        v.vec[0] = one_zero;
        v.vec[1] = v.vec[0];
        v.mask_last_block();
        assert_eq!(v.vec, vec![one_zero, 0b1010]);
    }

    #[test]
    fn test_index() {
        let v1 = vob![false, true];
        assert_eq!(v1[0], false);
        assert_eq!(v1[1], true);
    }

    #[test]
    fn test_iter_set_bits() {
        let mut v1 = vob![false, true, false, true];
        assert_eq!(v1.iter_set_bits(..).collect::<Vec<usize>>(), vec![1, 3]);
        v1.resize(127, false);
        v1.push(true);
        v1.push(false);
        v1.push(true);
        v1.push(true);
        v1.resize(256, false);
        v1.push(true);
        assert_eq!(
            v1.iter_set_bits(..).collect::<Vec<usize>>(),
            vec![1, 3, 127, 129, 130, 256]
        );
        assert_eq!(
            v1.iter_set_bits(2..256).collect::<Vec<usize>>(),
            vec![3, 127, 129, 130]
        );
        assert_eq!(
            v1.iter_set_bits(2..).collect::<Vec<usize>>(),
            vec![3, 127, 129, 130, 256]
        );
        assert_eq!(v1.iter_set_bits(..3).collect::<Vec<usize>>(), vec![1]);
    }

    #[test]
    fn test_iter_unset_bits() {
        let mut v1 = vob![false, true, false, false];
        assert_eq!(
            v1.iter_unset_bits(..).collect::<Vec<usize>>(),
            vec![0, 2, 3]
        );
        assert_eq!(
            v1.iter_unset_bits(..10).collect::<Vec<usize>>(),
            vec![0, 2, 3]
        );
        v1.resize(127, true);
        v1.push(false);
        v1.push(true);
        v1.push(false);
        v1.push(false);
        v1.resize(256, true);
        v1.push(false);
        assert_eq!(
            v1.iter_unset_bits(..).collect::<Vec<usize>>(),
            vec![0, 2, 3, 127, 129, 130, 256]
        );
        assert_eq!(
            v1.iter_unset_bits(3..256).collect::<Vec<usize>>(),
            vec![3, 127, 129, 130]
        );
    }

    #[test]
    fn test_eq() {
        let v1 = Vob::from_iter(vec![true, false]);
        let v2 = Vob::from_iter(vec![true, false]);
        assert_eq!(v1, v2);
        let v3 = Vob::from_iter(vec![true, true]);
        assert_ne!(v1, v3);
        let v4 = Vob::from_iter(vec![true, false, true]);
        assert_ne!(v1, v4);
    }

    #[test]
    fn test_hash() {
        fn hash<T: Hash>(t: &T) -> u64 {
            let mut s = DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }
        let v1 = vob![true, false];
        let v2 = vob![false, true];
        let v3 = vob![true, false];
        assert_eq!(hash(&v1), hash(&v3));
        assert_ne!(hash(&v1), hash(&v2));
        assert_ne!(hash(&v2), hash(&v3));
    }

    #[test]
    fn test_macros() {
        let v1 = vob![true, false];
        let mut v2 = Vob::new();
        v2.push(true);
        v2.push(false);
        assert_eq!(v1, v2);
        v2.set(1, true);
        assert_eq!(v2, vob![2; true]);
        assert_ne!(v2, vob![2; false]);
    }

    fn random_vob(len: usize) -> Vob {
        let mut rng = rand::thread_rng();
        let mut vob = Vob::with_capacity(len);
        for _ in 0..len {
            vob.push(rng.gen());
        }
        vob
    }

    #[test]
    fn test_extend_from_vob() {
        let mut rng = rand::thread_rng();
        for _ in 0..200 {
            let len_a: u8 = rng.gen();
            let len_b: u8 = rng.gen();
            let mut a = random_vob(len_a as usize);
            let mut a_copy = a.clone();
            let b = random_vob(len_b as usize);
            a.extend_from_vob(&b);
            a_copy.extend(b.iter());
            assert_eq!(a_copy, a);
            assert_eq!(a_copy.vec, a.vec);
        }
    }

    #[test]
    #[cfg(feature = "unsafe_internals")]
    fn test_storage_mut() {
        let mut v1 = vob![true, false, true];
        {
            let storage = unsafe { v1.get_storage_mut() };
            assert_eq!(storage[0], 0b101);
            storage[0] = 0b111;
        }
        assert_eq!(v1.get(1), Some(true));
    }

    #[test]
    fn test_split_off() {
        for len_a in 0..128 {
            for len_b in 0..128 {
                let a = random_vob(len_a as usize);
                let b = random_vob(len_b as usize);
                let mut joined = a.clone();
                joined.extend_from_vob(&b);
                assert_eq!(joined.len(), len_a + len_b);
                let b_ = joined.split_off(len_a as usize);
                assert_eq!(a, joined, "lower part for {}, {}", len_a, len_b);
                assert_eq!(b, b_, "upper part for {}, {}", len_a, len_b);
            }
        }
    }

    #[test]
    fn push_adjusts_vec_correctly() {
        let mut v = Vob::new();
        v.push(false);
        assert_eq!(v.vec.len(), 1);
        v.pop();
        v.push(true);
        assert_eq!(v.vec.len(), 1);
    }
}
