// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A wrapper around any Read to treat it as an RNG.

use std::fmt::Debug;
use std::io::Read;
use std::mem;

use {Rng, Error, Result};

/// An RNG that reads random bytes straight from a `Read`. This will
/// work best with an infinite reader, but this is not required.
///
/// # Panics
///
/// It will panic if it there is insufficient data to fulfill a request.
///
/// # Example
///
/// ```rust
/// use rand::{ReadRng, distributions};
///
/// let data = vec![1, 2, 3, 4, 5, 6, 7, 8];
/// let mut rng = ReadRng::new(&data[..]);
/// println!("{:x}", distributions::uniform::<u32, _>(&mut rng));
/// ```
#[derive(Debug)]
pub struct ReadRng<R: Debug> {
    reader: R
}

impl<R: Read + Debug> ReadRng<R> {
    /// Create a new `ReadRng` from a `Read`.
    pub fn new(r: R) -> ReadRng<R> {
        ReadRng {
            reader: r
        }
    }
}

macro_rules! impl_uint_from_fill {
    ($ty:ty, $N:expr, $self:expr) => ({
        // Transmute and convert from LE (i.e. byte-swap on BE)
        assert_eq!($N, ::core::mem::size_of::<$ty>());
        let mut buf = [0u8; $N];
        fill(&mut $self.reader, &mut buf).unwrap();
        unsafe{ *(buf.as_ptr() as *const $ty) }.to_le()
    });
}

impl<R: Read + Debug> Rng for ReadRng<R> {
    fn next_u32(&mut self) -> u32 {
        impl_uint_from_fill!(u32, 4, self)
    }
    fn next_u64(&mut self) -> u64 {
        impl_uint_from_fill!(u64, 8, self)
    }
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        impl_uint_from_fill!(u128, 16, self)
    }
    
    fn try_fill(&mut self, v: &mut [u8]) -> Result<()> {
        if v.len() == 0 { return Ok(()); }
        fill(&mut self.reader, v)
    }
}

fn fill(r: &mut Read, mut buf: &mut [u8]) -> Result<()> {
    while buf.len() > 0 {
        match r.read(buf)? {
            0 => return Err(Error),
            n => buf = &mut mem::replace(&mut buf, &mut [])[n..],
        }
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::ReadRng;
    use Rng;

    #[test]
    fn test_reader_rng_u64() {
        // transmute from the target to avoid endianness concerns.
        let v = vec![0u8, 0, 0, 0, 0, 0, 0, 1,
                     0  , 0, 0, 0, 0, 0, 0, 2,
                     0,   0, 0, 0, 0, 0, 0, 3];
        let mut rng = ReadRng::new(&v[..]);

        assert_eq!(rng.next_u64(), 1_u64.to_be());
        assert_eq!(rng.next_u64(), 2_u64.to_be());
        assert_eq!(rng.next_u64(), 3_u64.to_be());
    }
    #[test]
    fn test_reader_rng_u32() {
        let v = vec![0u8, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3];
        let mut rng = ReadRng::new(&v[..]);

        assert_eq!(rng.next_u32(), 1_u32.to_be());
        assert_eq!(rng.next_u32(), 2_u32.to_be());
        assert_eq!(rng.next_u32(), 3_u32.to_be());
    }
    #[test]
    fn test_reader_rng_try_fill() {
        let v = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let mut w = [0u8; 8];

        let mut rng = ReadRng::new(&v[..]);
        rng.try_fill(&mut w).unwrap();

        assert!(v == w);
    }

    #[test]
    fn test_reader_rng_insufficient_bytes() {
        let mut rng = ReadRng::new(&[][..]);
        let mut v = [0u8; 3];
        assert!(rng.try_fill(&mut v).is_err());
    }
}
