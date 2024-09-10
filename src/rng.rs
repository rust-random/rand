// Copyright 2018 Developers of the Rand project.
// Copyright 2013-2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [`Rng`] trait

use crate::distr::uniform::{SampleRange, SampleUniform};
use crate::distr::{self, Distribution, Standard};
use core::num::Wrapping;
use core::{mem, slice};
use rand_core::RngCore;

/// User-level interface for RNGs
///
/// [`RngCore`] is the `dyn`-safe implementation-level interface for Random
/// (Number) Generators. This trait, `Rng`, provides a user-level interface on
/// RNGs. It is implemented automatically for any `R: RngCore`.
///
/// This trait must usually be brought into scope via `use rand::Rng;` or
/// `use rand::prelude::*;`.
///
/// # Generic usage
///
/// The basic pattern is `fn foo<R: Rng + ?Sized>(rng: &mut R)`. Some
/// things are worth noting here:
///
/// - Since `Rng: RngCore` and every `RngCore` implements `Rng`, it makes no
///   difference whether we use `R: Rng` or `R: RngCore`.
/// - The `+ ?Sized` un-bounding allows functions to be called directly on
///   type-erased references; i.e. `foo(r)` where `r: &mut dyn RngCore`. Without
///   this it would be necessary to write `foo(&mut r)`.
///
/// An alternative pattern is possible: `fn foo<R: Rng>(rng: R)`. This has some
/// trade-offs. It allows the argument to be consumed directly without a `&mut`
/// (which is how `from_rng(thread_rng())` works); also it still works directly
/// on references (including type-erased references). Unfortunately within the
/// function `foo` it is not known whether `rng` is a reference type or not,
/// hence many uses of `rng` require an extra reference, either explicitly
/// (`distr.sample(&mut rng)`) or implicitly (`rng.random()`); one may hope the
/// optimiser can remove redundant references later.
///
/// Example:
///
/// ```
/// # use rand::thread_rng;
/// use rand::Rng;
///
/// fn foo<R: Rng + ?Sized>(rng: &mut R) -> f32 {
///     rng.random()
/// }
///
/// # let v = foo(&mut thread_rng());
/// ```
pub trait Rng: RngCore {
    /// Return a random value via the [`Standard`] distribution.
    ///
    /// # Example
    ///
    /// ```
    /// let mut rng = rand::thread_rng();
    /// let x: u32 = rng.random();
    /// println!("{}", x);
    /// println!("{:?}", rng.random::<(f64, bool)>());
    /// ```
    ///
    /// # Arrays and tuples
    ///
    /// The `rng.random()` method is able to generate arrays
    /// and tuples (up to 12 elements), so long as all element types can be
    /// generated.
    ///
    /// For arrays of integers, especially for those with small element types
    /// (< 64 bit), it will likely be faster to instead use [`Rng::fill`],
    /// though note that generated values will differ.
    ///
    /// ```
    /// let mut rng = rand::thread_rng();
    /// let tuple: (u8, i32, char) = rng.random(); // arbitrary tuple support
    ///
    /// let arr1: [f32; 32] = rng.random();        // array construction
    /// let mut arr2 = [0u8; 128];
    /// rng.fill(&mut arr2);                    // array fill
    /// ```
    ///
    /// [`Standard`]: distr::Standard
    #[inline]
    fn random<T>(&mut self) -> T
    where
        Standard: Distribution<T>,
    {
        Standard.sample(self)
    }

    /// Return an iterator over [`random`](Self::random) variates
    ///
    /// This is a just a wrapper over [`Rng::sample_iter`] using
    /// [`distr::Standard`].
    ///
    /// Note: this method consumes its argument. Use
    /// `(&mut rng).random_iter()` to avoid consuming the RNG.
    ///
    /// # Example
    ///
    /// ```
    /// let rng = rand::rngs::mock::StepRng::new(1, 1);
    /// let v: Vec<i32> = rng.random_iter().take(5).collect();
    /// assert_eq!(&v, &[1, 2, 3, 4, 5]);
    /// ```
    #[inline]
    fn random_iter<T>(self) -> distr::DistIter<Standard, Self, T>
    where
        Self: Sized,
        Standard: Distribution<T>,
    {
        Standard.sample_iter(self)
    }

    /// Sample a new value, using the given distribution.
    ///
    /// ### Example
    ///
    /// ```
    /// use rand::distr::Uniform;
    ///
    /// let mut rng = rand::thread_rng();
    /// let x = rng.sample(Uniform::new(10u32, 15).unwrap());
    /// // Type annotation requires two types, the type and distribution; the
    /// // distribution can be inferred.
    /// let y = rng.sample::<u16, _>(Uniform::new(10, 15).unwrap());
    /// ```
    fn sample<T, D: Distribution<T>>(&mut self, distr: D) -> T {
        distr.sample(self)
    }

    /// Create an iterator that generates values using the given distribution.
    ///
    /// Note: this method consumes its arguments. Use
    /// `(&mut rng).sample_iter(..)` to avoid consuming the RNG.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    /// use rand::distr::{Alphanumeric, Uniform, Standard};
    ///
    /// let mut rng = thread_rng();
    ///
    /// // Vec of 16 x f32:
    /// let v: Vec<f32> = (&mut rng).sample_iter(Standard).take(16).collect();
    ///
    /// // String:
    /// let s: String = (&mut rng).sample_iter(Alphanumeric)
    ///     .take(7)
    ///     .map(char::from)
    ///     .collect();
    ///
    /// // Combined values
    /// println!("{:?}", (&mut rng).sample_iter(Standard).take(5)
    ///                              .collect::<Vec<(f64, bool)>>());
    ///
    /// // Dice-rolling:
    /// let die_range = Uniform::new_inclusive(1, 6).unwrap();
    /// let mut roll_die = (&mut rng).sample_iter(die_range);
    /// while roll_die.next().unwrap() != 6 {
    ///     println!("Not a 6; rolling again!");
    /// }
    /// ```
    fn sample_iter<T, D>(self, distr: D) -> distr::DistIter<D, Self, T>
    where
        D: Distribution<T>,
        Self: Sized,
    {
        distr.sample_iter(self)
    }

    /// Fill any type implementing [`Fill`] with random data
    ///
    /// This method is implemented for types which may be safely reinterpreted
    /// as an (aligned) `[u8]` slice then filled with random data. It is often
    /// faster than using [`Rng::random`] but not value-equivalent.
    ///
    /// The distribution is expected to be uniform with portable results, but
    /// this cannot be guaranteed for third-party implementations.
    ///
    /// # Example
    ///
    /// ```
    /// let mut arr = [0i8; 20];
    /// rand::thread_rng().fill(&mut arr[..]);
    /// ```
    ///
    /// [`fill_bytes`]: RngCore::fill_bytes
    #[track_caller]
    fn fill<T: Fill + ?Sized>(&mut self, dest: &mut T) {
        dest.fill(self)
    }

    /// Generate a random value in the given range.
    ///
    /// This function is optimised for the case that only a single sample is
    /// made from the given range. See also the [`Uniform`] distribution
    /// type which may be faster if sampling from the same range repeatedly.
    ///
    /// All types support `low..high_exclusive` and `low..=high` range syntax.
    /// Unsigned integer types also support `..high_exclusive` and `..=high` syntax.
    ///
    /// # Panics
    ///
    /// Panics if the range is empty, or if `high - low` overflows for floats.
    ///
    /// # Example
    ///
    /// ```
    /// let mut rng = rand::thread_rng();
    ///
    /// // Exclusive range
    /// let n: u32 = rng.gen_range(..10);
    /// println!("{}", n);
    /// let m: f64 = rng.gen_range(-40.0..1.3e5);
    /// println!("{}", m);
    ///
    /// // Inclusive range
    /// let n: u32 = rng.gen_range(..=10);
    /// println!("{}", n);
    /// ```
    ///
    /// [`Uniform`]: distr::uniform::Uniform
    #[track_caller]
    fn gen_range<T, R>(&mut self, range: R) -> T
    where
        T: SampleUniform,
        R: SampleRange<T>,
    {
        assert!(!range.is_empty(), "cannot sample empty range");
        range.sample_single(self).unwrap()
    }

    /// Return a bool with a probability `p` of being true.
    ///
    /// See also the [`Bernoulli`] distribution, which may be faster if
    /// sampling from the same probability repeatedly.
    ///
    /// # Example
    ///
    /// ```
    /// let mut rng = rand::thread_rng();
    /// println!("{}", rng.gen_bool(1.0 / 3.0));
    /// ```
    ///
    /// # Panics
    ///
    /// If `p < 0` or `p > 1`.
    ///
    /// [`Bernoulli`]: distr::Bernoulli
    #[inline]
    #[track_caller]
    fn gen_bool(&mut self, p: f64) -> bool {
        match distr::Bernoulli::new(p) {
            Ok(d) => self.sample(d),
            Err(_) => panic!("p={:?} is outside range [0.0, 1.0]", p),
        }
    }

    /// Return a bool with a probability of `numerator/denominator` of being
    /// true. I.e. `gen_ratio(2, 3)` has chance of 2 in 3, or about 67%, of
    /// returning true. If `numerator == denominator`, then the returned value
    /// is guaranteed to be `true`. If `numerator == 0`, then the returned
    /// value is guaranteed to be `false`.
    ///
    /// See also the [`Bernoulli`] distribution, which may be faster if
    /// sampling from the same `numerator` and `denominator` repeatedly.
    ///
    /// # Panics
    ///
    /// If `denominator == 0` or `numerator > denominator`.
    ///
    /// # Example
    ///
    /// ```
    /// let mut rng = rand::thread_rng();
    /// println!("{}", rng.gen_ratio(2, 3));
    /// ```
    ///
    /// [`Bernoulli`]: distr::Bernoulli
    #[inline]
    #[track_caller]
    fn gen_ratio(&mut self, numerator: u32, denominator: u32) -> bool {
        match distr::Bernoulli::from_ratio(numerator, denominator) {
            Ok(d) => self.sample(d),
            Err(_) => panic!(
                "p={}/{} is outside range [0.0, 1.0]",
                numerator, denominator
            ),
        }
    }

    /// Alias for [`Rng::random`].
    #[inline]
    #[deprecated(
        since = "0.9.0",
        note = "Renamed to `random` to avoid conflict with the new `gen` keyword in Rust 2024."
    )]
    fn r#gen<T>(&mut self) -> T
    where
        Standard: Distribution<T>,
    {
        self.random()
    }
}

impl<R: RngCore + ?Sized> Rng for R {}

/// Implement [`Rng`] methods on `$target` as inherent methods
///
/// Parameters:
///
/// -   `$target` is the type to implement for (no support for generics)
/// -   `$rand` is `rand` (or `crate` within `rand`, or whatever `rand` is renamed to)
/// -   `$rng` is a constructor for the RNG (used in doc examples)
macro_rules! impl_rng_methods_as_inherent {
    ($target:ty, $rand:path, $rng:expr) => {
        #[doc = concat!("Implement [`rand::Rng`](", stringify!($rand), "::Rng) methods as inherent methods")]
        ///
        /// # Example
        ///
        /// ```
        /// use rand::distr::{Alphanumeric, Bernoulli};
        #[doc = concat!("let mut rng = ", stringify!($rng), ";")]
        ///
        /// let x: u32 = rng.random();
        /// let y = rng.gen_range(1..=6);
        /// let z: usize = rng.gen_range(..50);
        /// println!("{x}, {y}, {z}");
        ///
        /// let _ = rng.sample(Alphanumeric);
        ///
        /// // Simulate a Poisson process:
        /// let b = Bernoulli::new(0.2).unwrap();
        #[doc = concat!("let n = ", stringify!($rng))]
        ///     .sample_iter(b)
        ///     .take(50)
        ///     .filter(|r| *r)
        ///     .count();
        /// assert!(n <= 50);
        ///
        /// let mut arr = [0i8; 20];
        /// rng.fill(&mut arr[..]);
        /// ```
        impl $target {
            #[doc = concat!("Return a random variate from the [`rand::distr::Standard`](", stringify!($rand), "::distr::Standard) distribution")]
            #[inline]
            pub fn random<T>(&mut self) -> T
            where
                $crate::distr::Standard: $crate::distr::Distribution<T>,
            {
                use $crate::distr::Distribution;
                $crate::distr::Standard.sample(self)
            }

            /// Return an iterator over [`random`](Self::random) variates
            #[inline]
            pub fn random_iter<T>(self) -> $crate::distr::DistIter<$crate::distr::Standard, Self, T>
            where
                Self: Sized,
                $crate::distr::Standard: $crate::distr::Distribution<T>,
            {
                use $crate::distr::Distribution;
                $crate::distr::Standard.sample_iter(self)
            }

            /// Sample a new value, using the given distribution.
            #[inline]
            pub fn sample<T, D: $crate::distr::Distribution<T>>(&mut self, distr: D) -> T {
                distr.sample(self)
            }

            /// Create an iterator that generates values using the given distribution.
            #[inline]
            pub fn sample_iter<T, D>(self, distr: D) -> $crate::distr::DistIter<D, Self, T>
            where
                D: $crate::distr::Distribution<T>,
                Self: Sized,
            {
                distr.sample_iter(self)
            }

            #[doc = concat!("Fill any type implementing [`rand::Fill`](", stringify!($rand), "::Fill) with random data")]
            #[track_caller]
            pub fn fill<T: $crate::Fill + ?Sized>(&mut self, dest: &mut T) {
                dest.fill(self)
            }

            /// Generate a random value in the given range.
            #[track_caller]
            pub fn gen_range<T, R>(&mut self, range: R) -> T
            where
                T: $crate::distr::uniform::SampleUniform,
                R: $crate::distr::uniform::SampleRange<T>,
            {
                assert!(!range.is_empty(), "cannot sample empty range");
                range.sample_single(self).unwrap()
            }

            /// Return a bool with a probability `p` of being true.
            #[inline]
            #[track_caller]
            pub fn gen_bool(&mut self, p: f64) -> bool {
                <Self as $crate::Rng>::gen_bool(self, p)
            }

            /// Return a bool with a probability of `numerator/denominator` of being true.
            #[inline]
            #[track_caller]
            pub fn gen_ratio(&mut self, numerator: u32, denominator: u32) -> bool {
                <Self as $crate::Rng>::gen_ratio(self, numerator, denominator)
            }
        }
    };
}

/// Types which may be filled with random data
///
/// This trait allows arrays to be efficiently filled with random data.
///
/// Implementations are expected to be portable across machines unless
/// clearly documented otherwise (see the
/// [Chapter on Portability](https://rust-random.github.io/book/portability.html)).
pub trait Fill {
    /// Fill self with random data
    fn fill<R: Rng + ?Sized>(&mut self, rng: &mut R);
}

macro_rules! impl_fill_each {
    () => {};
    ($t:ty) => {
        impl Fill for [$t] {
            fn fill<R: Rng + ?Sized>(&mut self, rng: &mut R) {
                for elt in self.iter_mut() {
                    *elt = rng.random();
                }
            }
        }
    };
    ($t:ty, $($tt:ty,)*) => {
        impl_fill_each!($t);
        impl_fill_each!($($tt,)*);
    };
}

impl_fill_each!(bool, char, f32, f64,);

impl Fill for [u8] {
    fn fill<R: Rng + ?Sized>(&mut self, rng: &mut R) {
        rng.fill_bytes(self)
    }
}

macro_rules! impl_fill {
    () => {};
    ($t:ty) => {
        impl Fill for [$t] {
            #[inline(never)] // in micro benchmarks, this improves performance
            fn fill<R: Rng + ?Sized>(&mut self, rng: &mut R) {
                if self.len() > 0 {
                    rng.fill_bytes(unsafe {
                        slice::from_raw_parts_mut(self.as_mut_ptr()
                            as *mut u8,
                            mem::size_of_val(self)
                        )
                    });
                    for x in self {
                        *x = x.to_le();
                    }
                }
            }
        }

        impl Fill for [Wrapping<$t>] {
            #[inline(never)]
            fn fill<R: Rng + ?Sized>(&mut self, rng: &mut R) {
                if self.len() > 0 {
                    rng.fill_bytes(unsafe {
                        slice::from_raw_parts_mut(self.as_mut_ptr()
                            as *mut u8,
                            self.len() * mem::size_of::<$t>()
                        )
                    });
                    for x in self {
                    *x = Wrapping(x.0.to_le());
                    }
                }
            }
        }
    };
    ($t:ty, $($tt:ty,)*) => {
        impl_fill!($t);
        // TODO: this could replace above impl once Rust #32463 is fixed
        // impl_fill!(Wrapping<$t>);
        impl_fill!($($tt,)*);
    }
}

impl_fill!(u16, u32, u64, u128,);
impl_fill!(i8, i16, i32, i64, i128,);

impl<T, const N: usize> Fill for [T; N]
where
    [T]: Fill,
{
    fn fill<R: Rng + ?Sized>(&mut self, rng: &mut R) {
        <[T] as Fill>::fill(self, rng)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::rngs::mock::StepRng;
    use crate::test::rng;
    #[cfg(feature = "alloc")]
    use alloc::boxed::Box;

    #[test]
    fn test_fill_bytes_default() {
        let mut r = StepRng::new(0x11_22_33_44_55_66_77_88, 0);

        // check every remainder mod 8, both in small and big vectors.
        let lengths = [0, 1, 2, 3, 4, 5, 6, 7, 80, 81, 82, 83, 84, 85, 86, 87];
        for &n in lengths.iter() {
            let mut buffer = [0u8; 87];
            let v = &mut buffer[0..n];
            r.fill_bytes(v);

            // use this to get nicer error messages.
            for (i, &byte) in v.iter().enumerate() {
                if byte == 0 {
                    panic!("byte {} of {} is zero", i, n)
                }
            }
        }
    }

    #[test]
    fn test_fill() {
        let x = 9041086907909331047; // a random u64
        let mut rng = StepRng::new(x, 0);

        // Convert to byte sequence and back to u64; byte-swap twice if BE.
        let mut array = [0u64; 2];
        rng.fill(&mut array[..]);
        assert_eq!(array, [x, x]);
        assert_eq!(rng.next_u64(), x);

        // Convert to bytes then u32 in LE order
        let mut array = [0u32; 2];
        rng.fill(&mut array[..]);
        assert_eq!(array, [x as u32, (x >> 32) as u32]);
        assert_eq!(rng.next_u32(), x as u32);

        // Check equivalence using wrapped arrays
        let mut warray = [Wrapping(0u32); 2];
        rng.fill(&mut warray[..]);
        assert_eq!(array[0], warray[0].0);
        assert_eq!(array[1], warray[1].0);

        // Check equivalence for generated floats
        let mut array = [0f32; 2];
        rng.fill(&mut array);
        let arr2: [f32; 2] = rng.random();
        assert_eq!(array, arr2);
    }

    #[test]
    fn test_fill_empty() {
        let mut array = [0u32; 0];
        let mut rng = StepRng::new(0, 1);
        rng.fill(&mut array);
        rng.fill(&mut array[..]);
    }

    #[test]
    fn test_gen_range_int() {
        let mut r = rng(101);
        for _ in 0..1000 {
            let a = r.gen_range(-4711..17);
            assert!((-4711..17).contains(&a));
            let a: i8 = r.gen_range(-3..42);
            assert!((-3..42).contains(&a));
            let a: u16 = r.gen_range(10..99);
            assert!((10..99).contains(&a));
            let a: i32 = r.gen_range(-100..2000);
            assert!((-100..2000).contains(&a));
            let a: u32 = r.gen_range(12..=24);
            assert!((12..=24).contains(&a));

            assert_eq!(r.gen_range(..1u32), 0u32);
            assert_eq!(r.gen_range(-12i64..-11), -12i64);
            assert_eq!(r.gen_range(3_000_000..3_000_001), 3_000_000);
        }
    }

    #[test]
    fn test_gen_range_float() {
        let mut r = rng(101);
        for _ in 0..1000 {
            let a = r.gen_range(-4.5..1.7);
            assert!((-4.5..1.7).contains(&a));
            let a = r.gen_range(-1.1..=-0.3);
            assert!((-1.1..=-0.3).contains(&a));

            assert_eq!(r.gen_range(0.0f32..=0.0), 0.);
            assert_eq!(r.gen_range(-11.0..=-11.0), -11.);
            assert_eq!(r.gen_range(3_000_000.0..=3_000_000.0), 3_000_000.);
        }
    }

    #[test]
    #[should_panic]
    #[allow(clippy::reversed_empty_ranges)]
    fn test_gen_range_panic_int() {
        let mut r = rng(102);
        r.gen_range(5..-2);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::reversed_empty_ranges)]
    fn test_gen_range_panic_usize() {
        let mut r = rng(103);
        r.gen_range(5..2);
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn test_gen_bool() {
        let mut r = rng(105);
        for _ in 0..5 {
            assert_eq!(r.gen_bool(0.0), false);
            assert_eq!(r.gen_bool(1.0), true);
        }
    }

    #[test]
    fn test_rng_mut_ref() {
        fn use_rng(mut r: impl Rng) {
            let _ = r.next_u32();
        }

        let mut rng = rng(109);
        use_rng(&mut rng);
    }

    #[test]
    fn test_rng_trait_object() {
        use crate::distr::{Distribution, Standard};
        let mut rng = rng(109);
        let mut r = &mut rng as &mut dyn RngCore;
        r.next_u32();
        r.random::<i32>();
        assert_eq!(r.gen_range(0..1), 0);
        let _c: u8 = Standard.sample(&mut r);
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_rng_boxed_trait() {
        use crate::distr::{Distribution, Standard};
        let rng = rng(110);
        let mut r = Box::new(rng) as Box<dyn RngCore>;
        r.next_u32();
        r.random::<i32>();
        assert_eq!(r.gen_range(0..1), 0);
        let _c: u8 = Standard.sample(&mut r);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_gen_ratio_average() {
        const NUM: u32 = 3;
        const DENOM: u32 = 10;
        const N: u32 = 100_000;

        let mut sum: u32 = 0;
        let mut rng = rng(111);
        for _ in 0..N {
            if rng.gen_ratio(NUM, DENOM) {
                sum += 1;
            }
        }
        // Have Binomial(N, NUM/DENOM) distribution
        let expected = (NUM * N) / DENOM; // exact integer
        assert!(((sum - expected) as i32).abs() < 500);
    }
}
