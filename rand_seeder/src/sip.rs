// Copyright 2012-2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! An implementation of SipHash.
//! 
//! Shamelessly stolen from the Rust std lib (libcore/hash/sip.rs) and adapted.
//! 
//! Only the official variant, SipHash 2-4, is included. Other variants such
//! as the reduced 1-3 (used by libstd's `DefaultHasher`) could be added easily.

use core::marker::PhantomData;
use core::{cmp, hash, mem, ptr, slice};

/// A portable implementation of SipHash 2-4.
/// 
/// This implementation will produce 8-byte (`u64`) output compliant with the
/// reference implementation. Additionally, it can be extended into an RNG able
/// to produce unlimited output, `SipRng`.
///
/// See: <https://131002.net/siphash/>
///
/// SipHash is a general-purpose hashing function: it runs at a good
/// speed (competitive with Spooky and City) and permits strong _keyed_
/// hashing. This lets you key your hashtables from a strong RNG, such as
/// [`rand::os::OsRng`](https://doc.rust-lang.org/rand/rand/os/struct.OsRng.html).
///
/// Although the SipHash algorithm is considered to be generally strong,
/// it is not intended for cryptographic purposes. As such, all
/// cryptographic uses of this implementation are _strongly discouraged_.
#[derive(Debug, Clone, Default)]
pub struct SipHasher {
    hasher: Hasher<Sip24Rounds>,
}

#[derive(Debug)]
struct Hasher<S: Sip> {
    k0: u64,
    k1: u64,
    length: usize, // how many bytes we've processed
    state: State, // hash State
    tail: u64, // unprocessed bytes le
    ntail: usize, // how many bytes in tail are valid
    _marker: PhantomData<S>,
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
struct State {
    // v0, v2 and v1, v3 show up in pairs in the algorithm,
    // and simd implementations of SipHash will use vectors
    // of v02 and v13. By placing them in this order in the struct,
    // the compiler can pick up on just a few simd optimizations by itself.
    v0: u64,
    v2: u64,
    v1: u64,
    v3: u64,
}

macro_rules! compress {
    ($state:expr) => ({
        compress!($state.v0, $state.v1, $state.v2, $state.v3)
    });
    ($v0:expr, $v1:expr, $v2:expr, $v3:expr) =>
    ({
        $v0 = $v0.wrapping_add($v1); $v1 = $v1.rotate_left(13); $v1 ^= $v0;
        $v0 = $v0.rotate_left(32);
        $v2 = $v2.wrapping_add($v3); $v3 = $v3.rotate_left(16); $v3 ^= $v2;
        $v0 = $v0.wrapping_add($v3); $v3 = $v3.rotate_left(21); $v3 ^= $v0;
        $v2 = $v2.wrapping_add($v1); $v1 = $v1.rotate_left(17); $v1 ^= $v2;
        $v2 = $v2.rotate_left(32);
    });
}

/// Load an u64 using up to 8 bytes of a byte slice.
///
/// Unsafe because: unchecked indexing at start..start+len
#[inline]
unsafe fn u8to64_le(buf: &[u8], start: usize, len: usize) -> u64 {
    debug_assert!(len <= 8);
    debug_assert!(start + len  <= buf.len());
    let mut out = 0u64;
    ptr::copy_nonoverlapping(buf.get_unchecked(start),
                                &mut out as *mut u64 as *mut u8,
                                len);
    out.to_le()
}

impl SipHasher {
    /// Creates a new `SipHasher` with the two initial keys set to 0.
    #[inline]
    pub fn new() -> Self {
        SipHasher::new_with_keys(0, 0)
    }

    /// Creates a `SipHasher` that is keyed off the provided keys.
    #[inline]
    pub fn new_with_keys(key0: u64, key1: u64) -> Self {
        SipHasher {
            hasher: Hasher::new_with_keys(key0, key1)
        }
    }
}

impl<S: Sip> Hasher<S> {
    #[inline]
    fn new_with_keys(key0: u64, key1: u64) -> Hasher<S> {
        let mut state = Hasher {
            k0: key0,
            k1: key1,
            length: 0,
            state: State {
                v0: 0,
                v1: 0,
                v2: 0,
                v3: 0,
            },
            tail: 0,
            ntail: 0,
            _marker: PhantomData,
        };
        state.reset();
        state
    }

    #[inline]
    fn reset(&mut self) {
        self.length = 0;
        self.state.v0 = self.k0 ^ 0x736f6d6570736575;
        self.state.v1 = self.k1 ^ 0x646f72616e646f6d;
        self.state.v2 = self.k0 ^ 0x6c7967656e657261;
        self.state.v3 = self.k1 ^ 0x7465646279746573;
        self.ntail = 0;
    }

    // Specialized write function that is only valid for buffers with len <= 8.
    // It's used to force inlining of write_u8 and write_usize, those would normally be inlined
    // except for composite types (that includes slices and str hashing because of delimiter).
    // Without this extra push the compiler is very reluctant to inline delimiter writes,
    // degrading performance substantially for the most common use cases.
    #[inline]
    fn short_write(&mut self, msg: &[u8]) {
        debug_assert!(msg.len() <= 8);
        let length = msg.len();
        self.length += length;

        let needed = 8 - self.ntail;
        let fill = cmp::min(length, needed);
        if fill == 8 {
            self.tail = unsafe { u8to64_le(msg, 0, 8) };
        } else {
            self.tail |= unsafe { u8to64_le(msg, 0, fill) } << (8 * self.ntail);
            if length < needed {
                self.ntail += length;
                return;
            }
        }
        self.state.v3 ^= self.tail;
        S::c_rounds(&mut self.state);
        self.state.v0 ^= self.tail;

        // Buffered tail is now flushed, process new input.
        self.ntail = length - needed;
        self.tail = unsafe { u8to64_le(msg, needed, self.ntail) };
    }
}

impl hash::Hasher for SipHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.hasher.finish()
    }
    
    #[inline]
    fn write(&mut self, msg: &[u8]) {
        self.hasher.write(msg)
    }
    
    // the following default implementation is portable: write_u8
    // all i* default implementations simply convert to u*
    
    // the following must be re-implemented for portability:
    
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.write(&unsafe { mem::transmute::<_, [u8; 2]>(i.to_le()) })
    }
    
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.write(&unsafe { mem::transmute::<_, [u8; 4]>(i.to_le()) })
    }
    
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.write(&unsafe { mem::transmute::<_, [u8; 8]>(i.to_le()) })
    }
    
    #[inline]
    fn write_u128(&mut self, i: u128) {
        self.write(&unsafe { mem::transmute::<_, [u8; 16]>(i.to_le()) })
    }
    
    #[inline]
    fn write_usize(&mut self, i: usize) {
        // standardise the size for portability
        // `u128` is big enough for most platforms
        self.write_u128(i as u128);
    }
}

impl<S: Sip> hash::Hasher for Hasher<S> {
    // see short_write comment for explanation
    #[inline]
    fn write_usize(&mut self, i: usize) {
        let bytes = unsafe {
            slice::from_raw_parts(&i as *const usize as *const u8, mem::size_of::<usize>())
        };
        self.short_write(bytes);
    }

    // see short_write comment for explanation
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.short_write(&[i]);
    }

    #[inline]
    fn write(&mut self, msg: &[u8]) {
        let length = msg.len();
        self.length += length;

        let mut needed = 0;

        if self.ntail != 0 {
            needed = 8 - self.ntail;
            self.tail |= unsafe { u8to64_le(msg, 0, cmp::min(length, needed)) } << 8 * self.ntail;
            if length < needed {
                self.ntail += length;
                return
            } else {
                self.state.v3 ^= self.tail;
                S::c_rounds(&mut self.state);
                self.state.v0 ^= self.tail;
                self.ntail = 0;
            }
        }

        // Buffered tail is now flushed, process new input.
        let len = length - needed;
        let left = len & 0x7;

        let mut i = needed;
        while i < len - left {
            let mi = unsafe { u8to64_le(msg, i, 8) };

            self.state.v3 ^= mi;
            S::c_rounds(&mut self.state);
            self.state.v0 ^= mi;

            i += 8;
        }

        self.tail = unsafe { u8to64_le(msg, i, left) };
        self.ntail = left;
    }

    /// Reduces the state to a `u64` value, as in the reference implementation.
    #[inline]
    fn finish(&self) -> u64 {
        let mut state = self.state;

        let b: u64 = ((self.length as u64 & 0xff) << 56) | self.tail;

        state.v3 ^= b;
        S::c_rounds(&mut state);
        state.v0 ^= b;

        state.v2 ^= 0xff;
        S::d_rounds(&mut state);

        state.v0 ^ state.v1 ^ state.v2 ^ state.v3
    }
}

impl<H: hash::Hash> From<H> for SipHasher {
    #[inline]
    fn from(h: H) -> SipHasher {
        let mut hasher = SipHasher::new();
        h.hash(&mut hasher);
        hasher
    }
}

impl<S: Sip> Clone for Hasher<S> {
    #[inline]
    fn clone(&self) -> Hasher<S> {
        Hasher {
            k0: self.k0,
            k1: self.k1,
            length: self.length,
            state: self.state,
            tail: self.tail,
            ntail: self.ntail,
            _marker: self._marker,
        }
    }
}

impl<S: Sip> Default for Hasher<S> {
    /// Creates a `Hasher<S>` with the two initial keys set to 0.
    #[inline]
    fn default() -> Hasher<S> {
        Hasher::new_with_keys(0, 0)
    }
}

#[doc(hidden)]
trait Sip {
    fn c_rounds(_: &mut State);
    fn d_rounds(_: &mut State);
}

#[derive(Debug, Clone, Default)]
struct Sip24Rounds;

impl Sip for Sip24Rounds {
    #[inline]
    fn c_rounds(state: &mut State) {
        compress!(state);
        compress!(state);
    }

    #[inline]
    fn d_rounds(state: &mut State) {
        compress!(state);
        compress!(state);
        compress!(state);
        compress!(state);
    }
}

#[cfg(test)]
mod test {
    use core::hash::Hasher;
    use super::*;
    
    #[test]
    fn test_hash_vectors() {
        let k_bytes = [0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let (k0, k1) = unsafe{ (u8to64_le(&k_bytes, 0, 8), u8to64_le(&k_bytes, 8, 8)) };
        
        let mut msg = [0u8; 64];
        for (pos, i) in msg.iter_mut().zip(0u8..64) {
            *pos = i;
        }
        
        // From reference vectors, converted to u64:
        let tests = [(0, 0x726fdb47dd0e0e31),
                     (1, 0x74f839c593dc67fd),
                     (63, 0x958a324ceb064572)];
        
        for (len, val) in &tests {
            let mut hasher = SipHasher::new_with_keys(k0, k1);
            hasher.write(&msg[0..*len]);
            assert_eq!(hasher.finish(), *val, "mismatch with reference vector for i={}", *len);
        }
    }
}
