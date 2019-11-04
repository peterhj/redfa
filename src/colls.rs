use std::cmp::min;
use std::mem::replace;
use std::ops::Index;

/* VecMap is based on the vec_map crate:

Copyright 2012-2018 The Rust Project Developers. See the COPYRIGHT
file at the top-level directory of this distribution and at
http://rust-lang.org/COPYRIGHT.

Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
<LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
option. This file may not be copied, modified, or distributed
except according to those terms.
*/

pub struct VecMap<V> {
    n: usize,
    v: Vec<Option<V>>
}

impl<V> VecMap<V> {
    pub fn new() -> VecMap<V> {
        VecMap{
            n: 0,
            v: Vec::new()
        }
    }

    pub fn with_capacity(capacity: usize) -> VecMap<V> {
        VecMap{
            n: 0,
            v: Vec::with_capacity(capacity)
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.n
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }

    pub fn insert(&mut self, key: usize, new_value: V) -> Option<V> {
        if self.v.len() < key + 1 {
            self.v.resize_with(key + 1, || None);
        }
        let old_value = replace(&mut self.v[key], Some(new_value));
        if old_value.is_none() {
            self.n += 1;
        }
        old_value
    }
}

impl<V> Index<usize> for VecMap<V> {
    type Output = V;

    fn index(&self, key: usize) -> &V {
        if key < self.v.len() {
            self.v[key].as_ref()
        } else {
            None
        }.expect("key not present")
    }
}

/* BitSet is based on the bit_set and bit_vec crates:

Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
file at the top-level directory of this distribution and at
http://rust-lang.org/COPYRIGHT.

Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
<LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
option. This file may not be copied, modified, or distributed
except according to those terms.
*/

// Computes how many blocks are needed to store that many bits
fn blocks_for_bits_u32(bits: usize) -> usize {
    // If we want 17 bits, dividing by 32 will produce 0. So we add 1 to make sure we
    // reserve enough. But if we want exactly a multiple of 32, this will actually allocate
    // one too many. So we need to check if that's the case. We can do that by computing if
    // bitwise AND by `32 - 1` is 0. But LLVM should be able to optimize the semantically
    // superior modulo operator on a power of two to this.
    //
    // Note that we can technically avoid this branch with the expression
    // `(nbits + U32_BITS - 1) / 32::BITS`, but if nbits is almost usize::MAX this will overflow.
    if bits % 32 == 0 {
        bits / 32
    } else {
        bits / 32 + 1
    }
}

pub struct BitSet {
    nbits: usize,
    storage: Vec<u32>
}

impl BitSet {
    pub fn new() -> BitSet {
        BitSet{
            nbits: 0,
            storage: Vec::new()
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.storage.iter().fold(0, |acc, n| acc + n.count_ones() as usize)
    }

    #[inline]
    fn get(&self, value: usize) -> Option<bool> {
        if value >= self.nbits {
            return None;
        }
        let (w, b) = (value / 32, value % 32);
        self.storage.get(w).map(|&block| {
            (block & (1 << b)) != 0
        })
    }

    #[inline]
    fn index(&self, value: usize) -> bool {
        self.get(value).expect("index out of bounds")
    }

    #[inline]
    fn contains(&self, value: usize) -> bool {
        value < self.nbits && self.index(value)
    }

    #[inline]
    fn set(&mut self, i: usize, x: bool) {
        assert!(i < self.nbits, "index out of bounds: {:?} >= {:?}", i, self.nbits);
        let (w, b) = (i / 32, i % 32);
        let flag = 1 << b;
        let block = &mut self.storage[w];
        let val = if x { *block | flag }
                  else { *block & !flag };
        *block = val;
    }

    fn grow(&mut self, n: usize, value: bool) {
        // Note: we just bulk set all the bits in the last word in this fn in multiple places
        // which is technically wrong if not all of these bits are to be used. However, at the end
        // of this fn we call `fix_last_block` at the end of this fn, which should fix this.

        let new_nbits = self.nbits.checked_add(n).expect("capacity overflow");
        let new_nblocks = blocks_for_bits_u32(new_nbits);
        let full_value = if value { !0 } else { 0 };

        // Correct the old tail word, setting or clearing formerly unused bits
        let cur_nblocks = blocks_for_bits_u32(self.nbits);
        let cur_extra_bits = self.nbits % 32;
        if cur_extra_bits > 0 {
            if value {
                let mask = (1 << cur_extra_bits) - 1;
                let block = &mut self.storage[cur_nblocks - 1];
                *block = *block | !mask;
            } else {
                // Extra bits are already zero by invariant.
            }
        }

        // Fill in words after the old tail word
        let stop_idx = min(self.storage.len(), new_nblocks);
        for idx in cur_nblocks .. stop_idx {
            self.storage[idx] = full_value;
        }

        // Allocate new words, if needed
        if new_nblocks > self.storage.len() {
            self.storage.resize_with(new_nblocks, || full_value);
        }

        // Adjust internal bit count
        self.nbits = new_nbits;

        // Maintain invariant (was call `fix_last_block`:
        // An operation might screw up the unused bits in the last block of the
        // `BitVec`. As per (3), it's assumed to be all 0s. This method fixes it up.)
        let new_extra_bits = self.nbits % 32;
        if new_extra_bits > 0 {
            let mask = (1 << new_extra_bits) - 1;
            let storage_len = self.storage.len();
            let last_block = &mut self.storage[storage_len - 1];
            *last_block = *last_block & mask;
        }
    }

    pub fn insert(&mut self, value: usize) -> bool {
        if self.contains(value) {
            return false;
        }
        let n = self.nbits;
        if value >= n {
            self.grow(value - n + 1, false);
        }
        self.set(value, true);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::{BitSet, VecMap};

    #[test]
    fn test_vec_map_insert() {
        let mut m = VecMap::new();
        assert_eq!(m.insert(1, 2), None);
        assert_eq!(m.insert(1, 3), Some(2));
        assert_eq!(m.insert(1, 4), Some(3));
    }

    #[test]
    fn test_vec_map_index() {
        let mut map = VecMap::new();
        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);
        assert_eq!(map[3], 4);
    }

    #[test]
    #[should_panic]
    fn test_vec_map_index_nonexistent() {
        let mut map = VecMap::new();
        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);
        map[4];
    }

    #[test]
    fn test_vec_map_len() {
        let mut map = VecMap::new();
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert!(map.insert(5, 20).is_none());
        assert_eq!(map.len(), 1);
        assert!(!map.is_empty());
        assert!(map.insert(11, 12).is_none());
        assert_eq!(map.len(), 2);
        assert!(!map.is_empty());
        assert!(map.insert(14, 22).is_none());
        assert_eq!(map.len(), 3);
        assert!(!map.is_empty());
    }

    #[test]
    fn test_bit_set_basic_0() {
        let mut s = BitSet::new();
        s.insert(1);
        s.insert(10);
        s.insert(50);
        s.insert(2);
        assert_eq!(s.len(), 4);
        assert!(s.contains(1));
        assert!(s.contains(2));
        assert!(s.contains(10));
        assert!(s.contains(50));
    }

    #[test]
    fn test_bit_set_basic_1() {
        let mut b = BitSet::new();
        assert!(b.insert(3));
        assert!(!b.insert(3));
        assert!(b.contains(3));
        assert!(b.insert(4));
        assert!(!b.insert(4));
        assert!(b.contains(3));
        assert!(b.insert(400));
        assert!(!b.insert(400));
        assert!(b.contains(400));
        assert_eq!(b.len(), 3);
    }
}
