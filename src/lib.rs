// Copyright (c) 2018 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

//! A vector of bits ("Vob") is a sequence of bits which exposes a `Vec`-like interface. Whereas
//! `Vec<bool>` requires 1 byte of storage per bit, `Vob` requires only 1 bit of storage per bit.
//!
//! The main documentation for this crate can be found in the [`Vob`](struct.Vob.html) struct.

extern crate num_traits;

use std::cmp::PartialEq;
use std::fmt;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::mem::size_of;
use std::ops::{Index, Range};
use std::slice;

use num_traits::{PrimInt, One, Zero};


/// A Vob is a "vector of bits": a sequence of bits which exposes a `Vec`-like interface. Whereas
/// `Vec<bool>` requires 1 byte of storage per bit, `Vob` requires only 1 bit of storage per bit.
/// For larger numbers of bits, Vobs can lead to a significant memory decrease and performance
/// increase.
///
/// # Examples
/// The `vob!` macro makes creating small `Vob`s easy:
///
/// ```rust
/// # #[macro_use] extern crate vob;
/// # fn main() {
/// let mut v = vob![true, false, true];
/// assert_eq!(v[1], false);
/// # }
/// ```
///
/// Operations such as `and`ing two `Vob`s together are quick; one can also quickly identify which
/// bits are set:
///
/// ```rust
/// use vob::Vob;
/// let mut v1 = Vob::from_elem(256, false);
/// let mut v2 = Vob::from_elem(256, false);
/// v1.set(67, true);
/// v2.set(67, true);
/// v1.set(188, true);
/// v1.and(&v2);
/// let num_bits_set = v1.iter_set_bits().count();
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
/// `Vob` is directly inspired by `BitVec`, but aims to provide an interface more closely aligned
/// to `Vec<bool>` Several functions in `BitVec` have different names in `Vob`, but porting is in
/// general fairly simple. The main semantic difference is that `Vob`s
/// [`clear()`](struct.Vob.html#method.clear) function empties the `Vob` of contents (i.e. sets its
/// length to 0), whereas `BitVec`'s function of the same name unsets all bits (keeping the length
/// unchanged). The same effect as `BitVec`'s `clear` can be achieved by using `Vob`'s
/// [`set_all(false)`](struct.Vob.html#method.set_all) function.
#[derive(Clone)]
pub struct Vob<T=usize> {
    /// How many bits are stored in this Vob?
    len: usize,
    /// The underlying storage. We refer to a single instance of `T` as a block. Since the storage
    /// consists of (potentially multiple-byte) blocks, there may be "unused" bits in the final
    /// block. We guarantee that, at all points visible to the user, the "unused" bits are set to
    /// 0.
    vec: Vec<T>
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
            vec: Vec::with_capacity(blocks_required::<usize>(capacity))
        }
    }

    /// Creates a BitVec that holds `len` elements, setting each element to `value`.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let v = Vob::from_elem(2, true);
    /// assert_eq!(v.len(), 2);
    /// assert_eq!(v.get(0), Some(true));
    /// ```
    pub fn from_elem(len: usize, value: bool) -> Vob<usize> {
        let mut v = Vob::with_capacity(len);
        for _ in 0..blocks_required::<usize>(len) {
            v.vec.push(if value { !0 } else { 0 });
        }
        v.len = len;
        v.mask_last_block();
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
            vec: Vec::with_capacity(capacity)
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
        // Repeatedly calling this will over-reserve, since we only record how many bits we've
        // used, not how many bits of capacity the user thinks we have. For example, repeatedly
        // asking for storage for one extra bit will repeatedly add a whole extra machine word.
        // Fixing this would require an extra machine word in the Vob struct, which hardly seems
        // worth it for an unlikely, and probably silly, use case.
        let cap = self.vec.capacity()
                          .checked_mul(bits_per_block::<T>())
                          .and_then(|x| x.checked_add(additional))
                          .expect("Overflow detected");
        self.vec.reserve(blocks_required::<T>(cap));
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
    /// #[macro_use] extern crate vob;
    /// fn main() {
    ///     let mut v = vob![true, false, true];
    ///     v.truncate(2);
    ///     assert_eq!(v, vob![true, false]);
    /// }
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
        self.len -= 1;
        self.mask_last_block();
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
    /// assert_eq!(Vob::from_elem(2, true).is_empty(), false);
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
    /// assert_eq!(v1, Vob::from_elem(1, true));
    /// assert_eq!(v2, Vob::from_elem(1, false));
    /// ```
    pub fn split_off(&mut self, at: usize) -> Vob<T> {
        if at >= self.len {
            return Vob::<T>::new_with_storage_type(0);
        }
        let mut nv = Vob::<T>::new_with_storage_type(self.len - at);
        // This could easily be made more efficient.
        for blk in self.iter().skip(at) {
            nv.push(blk);
        }
        self.len = at;
        self.mask_last_block();
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

    /// Sets the value of the element at position `index` or `None` if out of bounds. Returns
    /// `true` if this led to a change in the underlying storage or `None` if out of bounds.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.set(0, true);
    /// assert_eq!(v.get(0), Some(true));
    /// assert_eq!(v.set(0, false), Some(true));
    /// assert_eq!(v.set(0, false), Some(false));
    /// ```
    pub fn set(&mut self, index: usize, value: bool) -> Option<bool> {
        if index >= self.len {
            return None;
        }
        let msk = T::one() << (index % bits_per_block::<T>());
        let off = block_offset::<T>(index);
        let old_v = self.vec[off];
        let new_v = if value {
                        old_v | msk
                    } else {
                        old_v & !msk
                    };
        if new_v != old_v {
            self.vec[off] = new_v;
            Some(true)
        } else {
            Some(false)
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
            range: 0..self.len
        }
    }


    /// Returns an iterator which produces the index of each bit set in the Vob.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.push(true);
    /// let mut iterator = v.iter_set_bits();
    /// assert_eq!(iterator.next(), Some(1));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter_set_bits(&self) -> IterSetBits<T> {
        IterSetBits {
            vob: self,
            range: 0..self.len
        }
    }

    /// Returns an iterator which produces the index of each bit set in the Vob.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let mut v = Vob::new();
    /// v.push(false);
    /// v.push(true);
    /// let mut iterator = v.iter_unset_bits();
    /// assert_eq!(iterator.next(), Some(0));
    /// assert_eq!(iterator.next(), None);
    /// ```
    pub fn iter_unset_bits(&self) -> IterUnsetBits<T> {
        IterUnsetBits {
            vob: self,
            range: 0..self.len
        }
    }

    /// Return an iterator over the underlying storage blocks. The last block is guaranteed to have
    /// "unused" bits (i.e. those past `self.len()`) set to 0.
    ///
    /// # Examples
    /// ```
    /// use vob::Vob;
    /// let v1 = Vob::from_elem(10, true);
    /// assert_eq!(v1.iter_storage().next(), Some((1 << 10) - 1));
    /// let v2 = Vob::from_elem(129, true);
    /// assert_eq!(v2.iter_storage().last(), Some(1));
    /// ```
    pub fn iter_storage(&self) -> StorageIter<T> {
        StorageIter{iter: self.vec.iter()}
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
            return
        }
        if value && self.len > 0 {
            // If we're resizing with trues, we need to extend the last block with true bits. We
            // can rely on mask_last_block to trim any unwanted bits we add in this process.
            let off = block_offset::<T>(self.len);
            let v = self.vec[off];
            self.vec[off] = v | (T::max_value() << (self.len % bits_per_block::<T>()));
        }
        self.vec.resize(blocks_required::<T>(new_len), if value {
                                                           T::max_value()
                                                       } else {
                                                           T::zero()
                                                       });
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
    /// #[macro_use] extern crate vob;
    /// fn main() {
    ///     let mut v = vob![true];
    ///     v.extend_from_slice(&vec![false, true]);
    ///     assert_eq!(v, vob![true, false, true]);
    /// }
    pub fn extend_from_slice(&mut self, other: &[bool]) {
        for &blk in other.iter() {
            self.push(blk);
        }
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
    /// #[macro_use] extern crate vob;
    /// fn main() {
    ///     let mut v = vob![true, false, true];
    ///     v.set_all(false);
    ///     assert_eq!(v, vob![false, false, false]);
    /// }
    /// ```
    pub fn set_all(&mut self, value: bool) {
        for blk in self.vec.iter_mut() {
            *blk = if value {
                       T::max_value()
                   } else {
                       T::zero()
                   };
        }
        self.mask_last_block();
    }

    /// Negates all bits in the Vob.
    ///
    /// # Examples
    /// ```
    /// #[macro_use] extern crate vob;
    /// fn main() {
    ///     let mut v = vob![true, false];
    ///     v.negate();
    ///     assert_eq!(v, vob![false, true]);
    /// }
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
    /// #[macro_use] extern crate vob;
    /// fn main() {
    ///     let mut v1 = vob![true, false, false];
    ///     let v2 = vob![true, true, false];
    ///     v1.and(&v2);
    ///     assert_eq!(v1, vob![true, false, false]);
    /// }
    /// ```
    pub fn and(&mut self, other: &Vob<T>) -> bool {
        if self.len != other.len {
            panic!("Cannot 'and' two Vobs of different length ({}  {})", self.len, other.len);
        }
        let mut chngd = false;
        for (self_blk, other_blk) in self.vec.iter_mut().zip(other.vec.iter()) {
            let old_v = *self_blk;
            let new_v = old_v & *other_blk;
            if old_v != new_v {
                *self_blk = new_v;
                chngd = true;
            }
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
    /// #[macro_use] extern crate vob;
    /// fn main() {
    ///     let mut v1 = vob![true, false, false];
    ///     let v2 = vob![false, true, false];
    ///     v1.or(&v2);
    ///     assert_eq!(v1, vob![true, true, false]);
    /// }
    /// ```
    pub fn or(&mut self, other: &Vob<T>) -> bool {
        if self.len != other.len {
            panic!("Cannot 'or' two Vobs of different length ({}  {})", self.len, other.len);
        }
        let mut chngd = false;
        for (self_blk, other_blk) in self.vec.iter_mut().zip(other.vec.iter()) {
            let old_v = *self_blk;
            let new_v = old_v | *other_blk;
            if old_v != new_v {
                *self_blk = new_v;
                chngd = true;
            }
        }
        // We don't need to mask the last block as those bits can't be set by "|" by definition.
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
    /// #[macro_use] extern crate vob;
    /// fn main() {
    ///     let mut v1 = vob![true, false, true];
    ///     let v2 = vob![false, true, true];
    ///     v1.xor(&v2);
    ///     assert_eq!(v1, vob![true, true, false]);
    /// }
    /// ```
    pub fn xor(&mut self, other: &Vob<T>) -> bool {
        if self.len != other.len {
            panic!("Cannot 'xor' two Vobs of different length ({}  {})", self.len, other.len);
        }
        let mut chngd = false;
        for (self_blk, other_blk) in self.vec.iter_mut().zip(other.vec.iter()) {
            let old_v = *self_blk;
            let new_v = old_v ^ *other_blk;
            if old_v != new_v {
                *self_blk = new_v;
                chngd = true;
            }
        }
        self.mask_last_block();
        chngd
    }

    /// We guarantee that the last storage block has no bits set past the "last" bit: this function
    /// clears any such bits.
    fn mask_last_block(&mut self) {
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
}

impl Default for Vob<usize> {
    fn default() -> Self {
        Vob {
            len: 0,
            vec: Vec::new()
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
    fn extend<I: IntoIterator<Item=bool>>(&mut self, iterable: I) {
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
    fn from_iter<I: IntoIterator<Item=bool>>(iter: I) -> Self {
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
            None => panic!("index out of bounds: the len is {} but the index is {}",
                           self.len,
                           index)
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
        self.range.next()
                  .map(|i| self.vob.get(i).unwrap())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

impl<'a, T: Debug + One + PrimInt + Zero> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<bool> {
        self.range.next_back()
                  .map(|i| self.vob.get(i).unwrap())
    }
}

impl<'a, T: Debug + One + PrimInt + Zero> ExactSizeIterator for Iter<'a, T> { }

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
        if let Some(mut i) = self.range.next() {
            // Bear in mind that i might not be aligned.
            for b in block_offset::<T>(i) .. blocks_required::<T>(self.vob.len) {
                let v = self.vob.vec[b];
                if v != T::zero() {
                    // We have a block with a bit set. Find the next bit set after 'i %
                    // bits_per_block()', bearing in mind that it may have been the last bit set
                    // (and we thus need to move to the next block).
                    let i_off = i % bits_per_block::<T>();
                    let tz = (v >> i_off).trailing_zeros() as usize;
                    if tz < bits_per_block::<T>() {
                        // There is another bit set after i in the block.
                        let bs = b * bits_per_block::<T>() + i_off + tz;
                        self.range.start = bs + 1;
                        return Some(bs);
                    }
                }
                i = b * bits_per_block::<T>();
            }
        }
        self.range.start = self.range.end;
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
        if let Some(mut i) = self.range.next() {
            // Bear in mind that i might not be aligned.
            for b in block_offset::<T>(i) .. blocks_required::<T>(self.vob.len) {
                let v = self.vob.vec[b];
                if v != T::max_value() {
                    // We have a block with a bit unset. Find the next bit unset after 'i %
                    // bits_per_block()', bearing in mind that it may have been the last bit unset
                    // (and we thus need to move to the next block).
                    let i_off = i % bits_per_block::<T>();
                    let tz = (!v >> i_off).trailing_zeros() as usize;
                    if tz < bits_per_block::<T>() {
                        // There is another bit unset after i in the block.
                        let bs = b * bits_per_block::<T>() + i_off + tz;
                        self.range.start = bs + 1;
                        if bs >= self.vob.len {
                            // This is the last block and the unset bit we thought we'd found is
                            // actually an unused bit; we've thus reached the end of the Vob.
                            break;
                        }
                        return Some(bs);
                    }
                }
                i = b * bits_per_block::<T>();
            }
        }
        self.range.start = self.range.end;
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

impl<T :Debug + Hash + One + PrimInt + Zero> Hash for Vob<T> {
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
    size_of::<T>() * 8
}

/// Return the offset in the vector of the storage block storing the bit `off`.
fn block_offset<T>(off: usize) -> usize {
    off / bits_per_block::<T>()
}

/// Takes as input a number of bits requiring storage; returns an aligned number of blocks needed
/// to store those bits.
fn blocks_required<T>(num_bits: usize) -> usize {
    num_bits / bits_per_block::<T>() + if num_bits % bits_per_block::<T>() == 0 {
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
/// #[macro_use] extern crate vob;
/// use vob::Vob;
///
/// fn main() {
///     let v1 = vob![true, false];
///     let mut v2 = Vob::new();
///     v2.push(true);
///     v2.push(false);
///     assert_eq!(v1, v2);
///     println!("{:?}", vob![10; true]);
/// }
/// ```
macro_rules! vob {
    (@single $($x:tt)*) => (());
    (@count $($rest:expr),*) => (<[()]>::len(&[$(vob!(@single $rest)),*]));
    ($elem:expr; $n:expr) => (
        $crate::Vob::from_elem($elem, $n)
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
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use std::iter::FromIterator;
    use std::mem::size_of;
    use super::{block_offset, blocks_required, Vob};

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
        assert_eq!(v.set(size_of::<u8>() * 8, true), Some(true));
        assert_eq!(v.set(size_of::<u8>() * 8, true), Some(false));
        assert_eq!(v.get(size_of::<u8>() * 8 - 1), Some(true));
        assert_eq!(v.get(size_of::<u8>() * 8 - 2), Some(true));
    }

    #[test]
    fn test_capacity() {
        assert_eq!(Vob::new().capacity(), 0);
        assert_eq!(Vob::with_capacity(size_of::<usize>() * 8 + 1).capacity(),
                                      size_of::<usize>() * 8 * 2);
    }

    #[test]
    fn test_reserve() {
        let mut v = Vob::new();
        v.reserve(10);
        assert_eq!(v.capacity(), size_of::<usize>() * 8);
        v.reserve(size_of::<usize>() * 8);
        assert_eq!(v.capacity(), size_of::<usize>() * 8 * 2);
    }

    #[test]
    #[should_panic(expected = "Overflow detected")]
    fn test_reserve_panic() {
        let mut v = Vob::new();
        v.reserve(5);
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
        assert_eq!(v.set(size_of::<usize>() * 8, true), Some(true));
        assert_eq!(v.set(size_of::<usize>() * 8, true), Some(false));
        assert_eq!(v.get(size_of::<usize>() * 8 - 1), Some(true));
        assert_eq!(v.get(size_of::<usize>() * 8 - 2), Some(true));
    }

    #[test]
    fn test_truncate() {
        let mut v = Vob::from_elem(2 * size_of::<usize>() * 8 + 1, true);
        assert_eq!(v, Vob::from_elem(2 * size_of::<usize>() * 8 + 1, true));
        v.truncate(2 * size_of::<usize>() * 8 + 1);
        assert_eq!(v, Vob::from_elem(2 * size_of::<usize>() * 8 + 1, true));
        v.truncate(3 * size_of::<usize>() * 8 + 1);
        assert_eq!(v, Vob::from_elem(2 * size_of::<usize>() * 8 + 1, true));
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
        assert_eq!(v1.iter_set_bits().collect::<Vec<usize>>(), vec![1, 3]);
        v1.resize(127, false);
        v1.push(true);
        v1.push(false);
        v1.push(true);
        v1.push(true);
        v1.resize(256, false);
        v1.push(true);
        assert_eq!(v1.iter_set_bits().collect::<Vec<usize>>(), vec![1, 3, 127, 129, 130, 256]);
    }

    #[test]
    fn test_iter_unset_bits() {
        let mut v1 = vob![false, true, false, false];
        assert_eq!(v1.iter_unset_bits().collect::<Vec<usize>>(), vec![0, 2, 3]);
        v1.resize(127, true);
        v1.push(false);
        v1.push(true);
        v1.push(false);
        v1.push(false);
        v1.resize(256, true);
        v1.push(false);
        assert_eq!(v1.iter_unset_bits().collect::<Vec<usize>>(), vec![0, 2, 3, 127, 129, 130, 256]);
    }

    #[test]
    fn test_eq() {
        let v1 = Vob::<usize>::from_iter(vec![true, false]);
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
}
