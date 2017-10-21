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

use std::io;
use std::io::Read;

use {Rng, Error, ErrorKind};

/// An RNG that reads random bytes straight from a `Read`. This will
/// work best with an infinite reader, but this is not required.
///
/// # Panics
///
/// Only the `try_fill` method will report errors. All other methods will panic
/// if the underlying reader encounters an error. They will also panic if there
/// is insufficient data to fulfill a request.
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
// Do not derive Clone, because it could share the underlying reader
pub struct ReadRng<R> {
    reader: R
}

impl<R: Read> ReadRng<R> {
    /// Create a new `ReadRng` from a `Read`.
    pub fn new(r: R) -> ReadRng<R> {
        ReadRng {
            reader: r
        }
    }
}

impl<R: Read> Rng for ReadRng<R> {
    fn next_u32(&mut self) -> u32 {
        ::rand_core::impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        ::rand_core::impls::next_u64_via_fill(self)
    }

    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.try_fill(dest).unwrap();
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        if dest.len() == 0 { return Ok(()); }
        // Use `std::io::read_exact`, which retries on `ErrorKind::Interrupted`.
        self.reader.read_exact(dest).map_err(map_err)
    }
}

fn map_err(err: io::Error) -> Error {
    let kind = match err.kind() {
        io::ErrorKind::UnexpectedEof => ErrorKind::Unavailable,
        _ => ErrorKind::Other,
    };
    Error::new(kind, Some(Box::new(err)))
}

#[cfg(test)]
mod test {
    use super::ReadRng;
    use {Rng, ErrorKind};

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
    fn test_reader_rng_fill_bytes() {
        let v = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let mut w = [0u8; 8];

        let mut rng = ReadRng::new(&v[..]);
        rng.fill_bytes(&mut w);

        assert!(v == w);
    }

    #[test]
    fn test_reader_rng_insufficient_bytes() {
        let v = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let mut w = [0u8; 9];

        let mut rng = ReadRng::new(&v[..]);

        assert!(rng.try_fill(&mut w).err().unwrap().kind == ErrorKind::Unavailable);
    }
}
