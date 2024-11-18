// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Mock random number generator

use rand_core::{impls, RngCore};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A mock generator yielding very predictable output
///
/// This generates an arithmetic sequence (i.e. adds a constant each step)
/// over a `u64` number, using wrapping arithmetic. If the increment is 0
/// the generator yields a constant.
///
/// Other integer types (64-bit and smaller) are produced via cast from `u64`.
///
/// Other types are produced via their implementation of [`Rng`](crate::Rng) or
/// [`Distribution`](crate::distr::Distribution).
/// Output values may not be intuitive and may change in future releases but
/// are considered
/// [portable](https://rust-random.github.io/book/portability.html).
/// (`bool` output is true when bit `1u64 << 31` is set.)
///
/// # Example
///
/// ```
/// use rand::Rng;
/// use rand::rngs::mock::StepRng;
///
/// let mut my_rng = StepRng::new(2, 1);
/// let sample: [u64; 3] = my_rng.random();
/// assert_eq!(sample, [2, 3, 4]);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StepRng {
    v: u64,
    a: u64,
}

impl StepRng {
    /// Create a `StepRng`, yielding an arithmetic sequence starting with
    /// `initial` and incremented by `increment` each time.
    pub fn new(initial: u64, increment: u64) -> Self {
        StepRng {
            v: initial,
            a: increment,
        }
    }
}

impl RngCore for StepRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        let res = self.v;
        self.v = self.v.wrapping_add(self.a);
        res
    }

    #[inline]
    fn fill_bytes(&mut self, dst: &mut [u8]) {
        impls::fill_bytes_via_next(self, dst)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(any(feature = "alloc", feature = "serde"))]
    use super::StepRng;

    #[test]
    #[cfg(feature = "serde")]
    fn test_serialization_step_rng() {
        let some_rng = StepRng::new(42, 7);
        let de_some_rng: StepRng =
            bincode::deserialize(&bincode::serialize(&some_rng).unwrap()).unwrap();
        assert_eq!(some_rng.v, de_some_rng.v);
        assert_eq!(some_rng.a, de_some_rng.a);
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_bool() {
        use crate::{distr::StandardUniform, Rng};

        // If this result ever changes, update doc on StepRng!
        let rng = StepRng::new(0, 1 << 31);
        let result: alloc::vec::Vec<bool> = rng.sample_iter(StandardUniform).take(6).collect();
        assert_eq!(&result, &[false, true, false, true, false, true]);
    }
}
