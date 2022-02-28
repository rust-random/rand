// Copyright 2018-2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{SampleBorrow, SampleUniform, Uniform, UniformInt, UniformSampler};
use crate::distributions::Distribution;
use crate::Rng;
use core::time::Duration;
#[cfg(feature = "serde1")] use serde::{Deserialize, Serialize};

impl SampleUniform for char {
    type Sampler = UniformChar;
}

/// The back-end implementing [`UniformSampler`] for `char`.
///
/// Unless you are implementing [`UniformSampler`] for your own type, this type
/// should not be used directly, use [`Uniform`] instead.
///
/// This differs from integer range sampling since the range `0xD800..=0xDFFF`
/// are used for surrogate pairs in UCS and UTF-16, and consequently are not
/// valid Unicode code points. We must therefore avoid sampling values in this
/// range.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformChar {
    sampler: UniformInt<u32>,
}

/// UTF-16 surrogate range start
const CHAR_SURROGATE_START: u32 = 0xD800;
/// UTF-16 surrogate range size
const CHAR_SURROGATE_LEN: u32 = 0xE000 - CHAR_SURROGATE_START;

/// Convert `char` to compressed `u32`
fn char_to_comp_u32(c: char) -> u32 {
    match c as u32 {
        c if c >= CHAR_SURROGATE_START => c - CHAR_SURROGATE_LEN,
        c => c,
    }
}

impl UniformSampler for UniformChar {
    type X = char;

    #[inline] // if the range is constant, this helps LLVM to do the
              // calculations at compile-time.
    fn new<B1, B2>(low_b: B1, high_b: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = char_to_comp_u32(*low_b.borrow());
        let high = char_to_comp_u32(*high_b.borrow());
        let sampler = UniformInt::<u32>::new(low, high);
        UniformChar { sampler }
    }

    #[inline] // if the range is constant, this helps LLVM to do the
              // calculations at compile-time.
    fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = char_to_comp_u32(*low_b.borrow());
        let high = char_to_comp_u32(*high_b.borrow());
        let sampler = UniformInt::<u32>::new_inclusive(low, high);
        UniformChar { sampler }
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        let mut x = self.sampler.sample(rng);
        if x >= CHAR_SURROGATE_START {
            x += CHAR_SURROGATE_LEN;
        }
        // SAFETY: x must not be in surrogate range or greater than char::MAX.
        // This relies on range constructors which accept char arguments.
        // Validity of input char values is assumed.
        unsafe { core::char::from_u32_unchecked(x) }
    }
}

/// The back-end implementing [`UniformSampler`] for `Duration`.
///
/// Unless you are implementing [`UniformSampler`] for your own types, this type
/// should not be used directly, use [`Uniform`] instead.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformDuration {
    mode: UniformDurationMode,
    offset: u32,
}

#[derive(Debug, Copy, Clone, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
enum UniformDurationMode {
    Small {
        secs: u64,
        nanos: Uniform<u32>,
    },
    Medium {
        nanos: Uniform<u64>,
    },
    Large {
        max_secs: u64,
        max_nanos: u32,
        secs: Uniform<u64>,
    },
}

impl SampleUniform for Duration {
    type Sampler = UniformDuration;
}

impl UniformSampler for UniformDuration {
    type X = Duration;

    #[inline]
    fn new<B1, B2>(low_b: B1, high_b: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = *low_b.borrow();
        let high = *high_b.borrow();
        assert!(low < high, "Uniform::new called with `low >= high`");
        UniformDuration::new_inclusive(low, high - Duration::new(0, 1))
    }

    #[inline]
    fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = *low_b.borrow();
        let high = *high_b.borrow();
        assert!(
            low <= high,
            "Uniform::new_inclusive called with `low > high`"
        );

        let low_s = low.as_secs();
        let low_n = low.subsec_nanos();
        let mut high_s = high.as_secs();
        let mut high_n = high.subsec_nanos();

        if high_n < low_n {
            high_s -= 1;
            high_n += 1_000_000_000;
        }

        let mode = if low_s == high_s {
            UniformDurationMode::Small {
                secs: low_s,
                nanos: Uniform::new_inclusive(low_n, high_n),
            }
        } else {
            let max = high_s
                .checked_mul(1_000_000_000)
                .and_then(|n| n.checked_add(u64::from(high_n)));

            if let Some(higher_bound) = max {
                let lower_bound = low_s * 1_000_000_000 + u64::from(low_n);
                UniformDurationMode::Medium {
                    nanos: Uniform::new_inclusive(lower_bound, higher_bound),
                }
            } else {
                // An offset is applied to simplify generation of nanoseconds
                let max_nanos = high_n - low_n;
                UniformDurationMode::Large {
                    max_secs: high_s,
                    max_nanos,
                    secs: Uniform::new_inclusive(low_s, high_s),
                }
            }
        };
        UniformDuration {
            mode,
            offset: low_n,
        }
    }

    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Duration {
        match self.mode {
            UniformDurationMode::Small { secs, nanos } => {
                let n = nanos.sample(rng);
                Duration::new(secs, n)
            }
            UniformDurationMode::Medium { nanos } => {
                let nanos = nanos.sample(rng);
                Duration::new(nanos / 1_000_000_000, (nanos % 1_000_000_000) as u32)
            }
            UniformDurationMode::Large {
                max_secs,
                max_nanos,
                secs,
            } => {
                // constant folding means this is at least as fast as `Rng::sample(Range)`
                let nano_range = Uniform::new(0, 1_000_000_000);
                loop {
                    let s = secs.sample(rng);
                    let n = nano_range.sample(rng);
                    if !(s == max_secs && n > max_nanos) {
                        let sum = n + self.offset;
                        break Duration::new(s, sum);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distributions::uniform::tests::test_samples;

    #[test]
    #[cfg(feature = "serde1")]
    fn test_serialization_uniform_duration() {
        let distr = UniformDuration::new(Duration::from_secs(10), Duration::from_secs(60));
        let de_distr: UniformDuration =
            bincode::deserialize(&bincode::serialize(&distr).unwrap()).unwrap();
        assert_eq!(distr.offset, de_distr.offset);
        match (distr.mode, de_distr.mode) {
            (
                UniformDurationMode::Small {
                    secs: a_secs,
                    nanos: a_nanos,
                },
                UniformDurationMode::Small { secs, nanos },
            ) => {
                assert_eq!(a_secs, secs);
                assert_eq!(a_nanos, nanos);
            }
            (
                UniformDurationMode::Medium { nanos: a_nanos },
                UniformDurationMode::Medium { nanos },
            ) => {
                assert_eq!(a_nanos, nanos);
            }
            (
                UniformDurationMode::Large {
                    max_secs: a_max_secs,
                    max_nanos: a_max_nanos,
                    secs: a_secs,
                },
                UniformDurationMode::Large {
                    max_secs,
                    max_nanos,
                    secs,
                },
            ) => {
                assert_eq!(a_max_secs, max_secs);
                assert_eq!(a_max_nanos, max_nanos);
                assert_eq!(a_secs, secs);
            }
            _ => panic!("`UniformDurationMode` was not serialized/deserialized correctly"),
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_char() {
        let mut rng = crate::test::rng(891);
        let mut max = core::char::from_u32(0).unwrap();
        for _ in 0..100 {
            let c = rng.gen_range('A'..='Z');
            assert!(('A'..='Z').contains(&c));
            max = max.max(c);
        }
        assert_eq!(max, 'Z');
        let d = Uniform::new(
            core::char::from_u32(0xD7F0).unwrap(),
            core::char::from_u32(0xE010).unwrap(),
        );
        for _ in 0..100 {
            let c = d.sample(&mut rng);
            assert!((c as u32) < 0xD800 || (c as u32) > 0xDFFF);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_durations() {
        let mut rng = crate::test::rng(253);

        let v = &[
            (Duration::new(10, 50000), Duration::new(100, 1234)),
            (Duration::new(0, 100), Duration::new(1, 50)),
            (
                Duration::new(0, 0),
                Duration::new(u64::max_value(), 999_999_999),
            ),
        ];
        for &(low, high) in v.iter() {
            let my_uniform = Uniform::new(low, high);
            for _ in 0..1000 {
                let v = rng.sample(my_uniform);
                assert!(low <= v && v < high);
            }
        }
    }

    #[test]
    fn value_stability() {
        test_samples(
            Duration::new(2, 0),
            Duration::new(4, 0),
            &[
                Duration::new(2, 532615131),
                Duration::new(3, 638826742),
                Duration::new(3, 485707508),
            ],
            &[
                Duration::new(3, 117337521),
                Duration::new(3, 191764285),
                Duration::new(3, 236507617),
            ],
        );

        test_samples('a', 'z', &['a', 'g', 'y'], &['u', 'j', 's']);
    }

    #[test]
    fn uniform_distributions_can_be_compared() {
        assert_eq!(Uniform::new('a', 'g'), Uniform::new('a', 'g'));
        assert_eq!(
            Uniform::new(Duration::from_millis(10), Duration::from_millis(20)),
            Uniform::new(Duration::from_millis(10), Duration::from_millis(20)),
        );
    }
}
