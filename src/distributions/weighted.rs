// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use Rng;
use distributions::Distribution;
use distributions::uniform::{UniformSampler, SampleUniform, SampleBorrow};
use ::core::cmp::PartialOrd;
use core::fmt;
use core::iter::Sum;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

// Note that this whole module is only imported if feature="alloc" is enabled.
#[cfg(not(feature="std"))] use alloc::vec::Vec;

/// A distribution using weighted sampling to pick a discretely selected
/// item.
///
/// Sampling a `WeightedIndex` distribution returns the index of a randomly
/// selected element from the iterator used when the `WeightedIndex` was
/// created. The chance of a given element being picked is proportional to the
/// value of the element. The weights can use any type `X` for which an
/// implementation of [`Uniform<X>`] exists.
///
/// # Performance
///
/// A `WeightedIndex<X>` contains a `Vec<X>` and a [`Uniform<X>`] and so its
/// size is the sum of the size of those objects, possibly plus some alignment.
///
/// Creating a `WeightedIndex<X>` will allocate enough space to hold `N - 1`
/// weights of type `X`, where `N` is the number of weights. However, since
/// `Vec` doesn't guarantee a particular growth strategy, additional memory
/// might be allocated but not used. Since the `WeightedIndex` object also
/// contains, this might cause additional allocations, though for primitive
/// types, ['Uniform<X>`] doesn't allocate any memory.
///
/// Time complexity of sampling from `WeightedIndex` is `O(log N)` where
/// `N` is the number of weights.
///
/// Sampling from `WeightedIndex` will result in a single call to
/// `Uniform<X>::sample` (method of the [`Distribution`] trait), which typically
/// will request a single value from the underlying [`RngCore`], though the
/// exact number depends on the implementaiton of `Uniform<X>::sample`.
///
/// # Example
///
/// ```
/// use rand::prelude::*;
/// use rand::distributions::WeightedIndex;
///
/// let choices = ['a', 'b', 'c'];
/// let weights = [2,   1,   1];
/// let dist = WeightedIndex::new(&weights).unwrap();
/// let mut rng = thread_rng();
/// for _ in 0..100 {
///     // 50% chance to print 'a', 25% chance to print 'b', 25% chance to print 'c'
///     println!("{}", choices[dist.sample(&mut rng)]);
/// }
///
/// let items = [('a', 0), ('b', 3), ('c', 7)];
/// let dist2 = WeightedIndex::new(items.iter().map(|item| item.1)).unwrap();
/// for _ in 0..100 {
///     // 0% chance to print 'a', 30% chance to print 'b', 70% chance to print 'c'
///     println!("{}", items[dist2.sample(&mut rng)].0);
/// }
/// ```
///
/// [`Uniform<X>`]: crate::distributions::uniform::Uniform
/// [`RngCore`]: rand_core::RngCore
#[derive(Debug, Clone)]
pub struct WeightedIndex<X: SampleUniform + PartialOrd> {
    cumulative_weights: Vec<X>,
    weight_distribution: X::Sampler,
}

impl<X: SampleUniform + PartialOrd> WeightedIndex<X> {
    /// Creates a new a `WeightedIndex` [`Distribution`] using the values
    /// in `weights`. The weights can use any type `X` for which an
    /// implementation of [`Uniform<X>`] exists.
    ///
    /// Returns an error if the iterator is empty, if any weight is `< 0`, or
    /// if its total value is 0.
    ///
    /// [`Uniform<X>`]: crate::distributions::uniform::Uniform
    pub fn new<I>(weights: I) -> Result<WeightedIndex<X>, WeightedError>
        where I: IntoIterator,
              I::Item: SampleBorrow<X>,
              X: for<'a> ::core::ops::AddAssign<&'a X> +
                 Clone +
                 Default {
        let mut iter = weights.into_iter();
        let mut total_weight: X = iter.next()
                                      .ok_or(WeightedError::NoItem)?
                                      .borrow()
                                      .clone();

        let zero = <X as Default>::default();
        if total_weight < zero {
            return Err(WeightedError::NegativeWeight);
        }

        let mut weights = Vec::<X>::with_capacity(iter.size_hint().0);
        for w in iter {
            if *w.borrow() < zero {
                return Err(WeightedError::NegativeWeight);
            }
            weights.push(total_weight.clone());
            total_weight += w.borrow();
        }

        if total_weight == zero {
            return Err(WeightedError::AllWeightsZero);
        }
        let distr = X::Sampler::new(zero, total_weight);

        Ok(WeightedIndex { cumulative_weights: weights, weight_distribution: distr })
    }
}

impl<X> Distribution<usize> for WeightedIndex<X> where
    X: SampleUniform + PartialOrd {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        use ::core::cmp::Ordering;
        let chosen_weight = self.weight_distribution.sample(rng);
        // Find the first item which has a weight *higher* than the chosen weight.
        self.cumulative_weights.binary_search_by(
            |w| if *w <= chosen_weight { Ordering::Less } else { Ordering::Greater }).unwrap_err()
    }
}

#[allow(missing_docs)] // todo: add docs
pub struct AliasMethodWeightedIndex<W: AliasMethodWeight> {
    aliases: Vec<usize>,
    no_alias_odds: Vec<W>,
    uniform_index: super::Uniform<usize>,
    uniform_within_weight_sum: super::Uniform<W>,
}

impl<W: AliasMethodWeight> AliasMethodWeightedIndex<W> {
    #[allow(missing_docs)] // todo: add docs
    pub fn new(weights: Vec<W>) -> Result<Self, AliasMethodWeightedIndexError> {
        let n = weights.len();
        if n == 0 {
            return Err(AliasMethodWeightedIndexError::NoItem);
        }

        let max_weight_size = W::try_from_usize_lossy(n)
            .map(|n| W::MAX / n)
            .unwrap_or(W::ZERO);
        if !weights
            .iter()
            .all(|&w| W::ZERO <= w && w <= max_weight_size)
        {
            return Err(AliasMethodWeightedIndexError::InvalidWeight);
        }

        // The sum of weights will represent 100% of no alias odds.
        let weight_sum = pairwise_sum(weights.as_slice());
        // Prevent floating point overflow due to rounding errors.
        let weight_sum = if weight_sum > W::MAX {
            W::MAX
        } else {
            weight_sum
        };
        if weight_sum == W::ZERO {
            return Err(AliasMethodWeightedIndexError::AllWeightsZero);
        }

        // `weight_sum` would have been zero if `try_from_lossy` causes an error here.
        let n_converted = W::try_from_usize_lossy(n).unwrap();

        let mut no_alias_odds = weights;
        for odds in no_alias_odds.iter_mut() {
            *odds *= n_converted;
            // Prevent floating point overflow due to rounding errors.
            *odds = if *odds > W::MAX { W::MAX } else { *odds };
        }

        /// This struct is designed to contain three data structures at once,
        /// sharing the same memory. More precisely it contains two
        /// linked lists and an alias map, which will be the output of this
        /// method. To keep the three data structures from getting in
        /// each other's way, it must be ensured that a single index is only
        /// ever in one of them at the same time.
        struct Aliases {
            aliases: Vec<usize>,
            smalls_head: usize,
            bigs_head: usize,
        }

        impl Aliases {
            fn new(size: usize) -> Self {
                Aliases {
                    aliases: vec![0; size],
                    smalls_head: ::core::usize::MAX,
                    bigs_head: ::core::usize::MAX,
                }
            }

            fn push_small(&mut self, idx: usize) {
                self.aliases[idx] = self.smalls_head;
                self.smalls_head = idx;
            }

            fn push_big(&mut self, idx: usize) {
                self.aliases[idx] = self.bigs_head;
                self.bigs_head = idx;
            }

            fn pop_small(&mut self) -> usize {
                let popped = self.smalls_head;
                self.smalls_head = self.aliases[popped];
                popped
            }

            fn pop_big(&mut self) -> usize {
                let popped = self.bigs_head;
                self.bigs_head = self.aliases[popped];
                popped
            }

            fn smalls_is_empty(&self) -> bool {
                self.smalls_head == ::core::usize::MAX
            }

            fn bigs_is_empty(&self) -> bool {
                self.bigs_head == ::core::usize::MAX
            }

            fn set_alias(&mut self, idx: usize, alias: usize) {
                self.aliases[idx] = alias;
            }
        }

        let mut aliases = Aliases::new(n);

        // Split indices into those with small weights and those with big weights.
        for (index, &odds) in no_alias_odds.iter().enumerate() {
            if odds < weight_sum {
                aliases.push_small(index);
            } else {
                aliases.push_big(index);
            }
        }

        // Build the alias map by finding an alias with big weight for each index with
        // small weight.
        while !aliases.smalls_is_empty() && !aliases.bigs_is_empty() {
            let s = aliases.pop_small();
            let b = aliases.pop_big();

            aliases.set_alias(s, b);
            no_alias_odds[b] = no_alias_odds[b] - weight_sum + no_alias_odds[s];

            if no_alias_odds[b] < weight_sum {
                aliases.push_small(b);
            } else {
                aliases.push_big(b);
            }
        }

        // The remaining indices should have no alias odds of about 100%. This is due to
        // numeric accuracy. Otherwise they would be exactly 100%.
        while !aliases.smalls_is_empty() {
            no_alias_odds[aliases.pop_small()] = weight_sum;
        }
        while !aliases.bigs_is_empty() {
            no_alias_odds[aliases.pop_big()] = weight_sum;
        }

        // Prepare distributions for sampling. Creating them beforehand improves
        // sampling performance.
        let uniform_index = super::Uniform::new(0, n);
        let uniform_within_weight_sum = super::Uniform::new(W::ZERO, weight_sum);

        Ok(Self {
            aliases: aliases.aliases,
            no_alias_odds,
            uniform_index,
            uniform_within_weight_sum,
        })
    }
}

impl<W: AliasMethodWeight> Distribution<usize> for AliasMethodWeightedIndex<W> {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        let candidate = rng.sample(self.uniform_index);
        if rng.sample(&self.uniform_within_weight_sum) < self.no_alias_odds[candidate] {
            candidate
        } else {
            self.aliases[candidate]
        }
    }
}

impl<W: AliasMethodWeight> fmt::Debug for AliasMethodWeightedIndex<W>
where
    W: fmt::Debug,
    super::Uniform<W>: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("AliasMethodWeightedIndex")
            .field("aliases", &self.aliases)
            .field("no_alias_odds", &self.no_alias_odds)
            .field("uniform_index", &self.uniform_index)
            .field("uniform_within_weight_sum", &self.uniform_within_weight_sum)
            .finish()
    }
}

impl<W: AliasMethodWeight> Clone for AliasMethodWeightedIndex<W>
where
    super::Uniform<W>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            aliases: self.aliases.clone(),
            no_alias_odds: self.no_alias_odds.clone(),
            uniform_index: self.uniform_index.clone(),
            uniform_within_weight_sum: self.uniform_within_weight_sum.clone(),
        }
    }
}

/// In comparision to naive accumulation, the pairwise sum algorithm reduces
/// rounding errors when there are many floating point values.
fn pairwise_sum<T: AliasMethodWeight>(values: &[T]) -> T {
    if values.len() <= 32 {
        values.iter().map(|x| *x).sum()
    } else {
        let mid = values.len() / 2;
        let (a, b) = values.split_at(mid);
        pairwise_sum(a) + pairwise_sum(b)
    }
}

pub trait AliasMethodWeight:
    Sized
    + Copy
    + SampleUniform
    + PartialOrd
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + Sum
{
    const MAX: Self;
    const ZERO: Self;

    fn try_from_usize_lossy(n: usize) -> Option<Self>;
}

macro_rules! impl_alias_method_weight_for_float {
    ($T: ident) => {
        impl AliasMethodWeight for $T {
            const MAX: Self = ::core::$T::MAX;
            const ZERO: Self = 0.0;

            fn try_from_usize_lossy(n: usize) -> Option<Self> {
                Some(n as $T)
            }
        }
    };
}

macro_rules! impl_alias_method_weight_for_int {
    ($T: ident) => {
        impl AliasMethodWeight for $T {
            const MAX: Self = ::core::$T::MAX;
            const ZERO: Self = 0;

            fn try_from_usize_lossy(n: usize) -> Option<Self> {
                let n_converted = n as Self;
                if n_converted >= Self::ZERO && n_converted as usize == n {
                    Some(n_converted)
                } else {
                    None
                }
            }
        }
    };
}

impl_alias_method_weight_for_float!(f64);
impl_alias_method_weight_for_float!(f32);
impl_alias_method_weight_for_int!(usize);
#[cfg(all(rustc_1_26, not(target_os = "emscripten")))]
impl_alias_method_weight_for_int!(u128);
impl_alias_method_weight_for_int!(u64);
impl_alias_method_weight_for_int!(u32);
impl_alias_method_weight_for_int!(u16);
impl_alias_method_weight_for_int!(u8);
impl_alias_method_weight_for_int!(isize);
#[cfg(all(rustc_1_26, not(target_os = "emscripten")))]
impl_alias_method_weight_for_int!(i128);
impl_alias_method_weight_for_int!(i64);
impl_alias_method_weight_for_int!(i32);
impl_alias_method_weight_for_int!(i16);
impl_alias_method_weight_for_int!(i8);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_weightedindex() {
        let mut r = ::test::rng(700);
        const N_REPS: u32 = 5000;
        let weights = [1u32, 2, 3, 0, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7];
        let total_weight = weights.iter().sum::<u32>() as f32;

        let verify = |result: [i32; 14]| {
            for (i, count) in result.iter().enumerate() {
                let exp = (weights[i] * N_REPS) as f32 / total_weight;
                let mut err = (*count as f32 - exp).abs();
                if err != 0.0 {
                    err /= exp;
                }
                assert!(err <= 0.25);
            }
        };

        // WeightedIndex from vec
        let mut chosen = [0i32; 14];
        let distr = WeightedIndex::new(weights.to_vec()).unwrap();
        for _ in 0..N_REPS {
            chosen[distr.sample(&mut r)] += 1;
        }
        verify(chosen);

        // WeightedIndex from slice
        chosen = [0i32; 14];
        let distr = WeightedIndex::new(&weights[..]).unwrap();
        for _ in 0..N_REPS {
            chosen[distr.sample(&mut r)] += 1;
        }
        verify(chosen);

        // WeightedIndex from iterator
        chosen = [0i32; 14];
        let distr = WeightedIndex::new(weights.iter()).unwrap();
        for _ in 0..N_REPS {
            chosen[distr.sample(&mut r)] += 1;
        }
        verify(chosen);

        for _ in 0..5 {
            assert_eq!(WeightedIndex::new(&[0, 1]).unwrap().sample(&mut r), 1);
            assert_eq!(WeightedIndex::new(&[1, 0]).unwrap().sample(&mut r), 0);
            assert_eq!(WeightedIndex::new(&[0, 0, 0, 0, 10, 0]).unwrap().sample(&mut r), 4);
        }

        assert_eq!(WeightedIndex::new(&[10][0..0]).unwrap_err(), WeightedError::NoItem);
        assert_eq!(WeightedIndex::new(&[0]).unwrap_err(), WeightedError::AllWeightsZero);
        assert_eq!(WeightedIndex::new(&[10, 20, -1, 30]).unwrap_err(), WeightedError::NegativeWeight);
        assert_eq!(WeightedIndex::new(&[-10, 20, 1, 30]).unwrap_err(), WeightedError::NegativeWeight);
        assert_eq!(WeightedIndex::new(&[-10]).unwrap_err(), WeightedError::NegativeWeight);
    }

    #[test]
    fn test_alias_method_weighted_index_f32() {
        test_alias_method_weighted_index(f32::into);

        // Floating point special cases
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![::core::f32::INFINITY]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![-0_f32]).unwrap_err(),
            AliasMethodWeightedIndexError::AllWeightsZero
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![-1_f32]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![-::core::f32::INFINITY]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![::core::f32::NAN]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
    }

    #[cfg(all(rustc_1_26, not(target_os = "emscripten")))]
    #[test]
    fn test_alias_method_weighted_index_u128() {
        test_alias_method_weighted_index(|x: u128| x as f64);
    }

    #[cfg(all(rustc_1_26, not(target_os = "emscripten")))]
    #[test]
    fn test_alias_method_weighted_index_i128() {
        test_alias_method_weighted_index(|x: i128| x as f64);

        // Signed integer special cases
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![-1_i128]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![::core::i128::MIN]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
    }

    #[test]
    fn test_alias_method_weighted_index_u8() {
        test_alias_method_weighted_index(u8::into);
    }

    #[test]
    fn test_alias_method_weighted_index_i8() {
        test_alias_method_weighted_index(i8::into);

        // Signed integer special cases
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![-1_i8]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![::core::i8::MIN]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
    }

    fn test_alias_method_weighted_index<W: AliasMethodWeight, F: Fn(W) -> f64>(w_to_f64: F)
    where
        AliasMethodWeightedIndex<W>: fmt::Debug,
    {
        const NUM_WEIGHTS: usize = 10;
        const ZERO_WEIGHT_INDEX: usize = 3;
        const NUM_SAMPLES: u32 = 15000;
        let mut rng = ::test::rng(0x9c9fa0b0580a7031);

        let weights = {
            let mut weights = Vec::with_capacity(NUM_WEIGHTS);
            let random_weight_distribution = ::distributions::Uniform::new_inclusive(
                W::ZERO,
                W::MAX / W::try_from_usize_lossy(NUM_WEIGHTS).unwrap(),
            );
            for _ in 0..NUM_WEIGHTS {
                weights.push(rng.sample(&random_weight_distribution));
            }
            weights[ZERO_WEIGHT_INDEX] = W::ZERO;
            weights
        };
        let weight_sum = weights.iter().map(|w| *w).sum::<W>();
        let expected_counts = weights
            .iter()
            .map(|&w| w_to_f64(w) / w_to_f64(weight_sum) * NUM_SAMPLES as f64)
            .collect::<Vec<f64>>();
        let weight_distribution = AliasMethodWeightedIndex::new(weights).unwrap();

        let mut counts = vec![0_usize; NUM_WEIGHTS];
        for _ in 0..NUM_SAMPLES {
            counts[rng.sample(&weight_distribution)] += 1;
        }

        assert_eq!(counts[ZERO_WEIGHT_INDEX], 0);
        for (count, expected_count) in counts.into_iter().zip(expected_counts) {
            let difference = (count as f64 - expected_count).abs();
            let max_allowed_difference = NUM_SAMPLES as f64 / NUM_WEIGHTS as f64 * 0.1;
            assert!(difference <= max_allowed_difference);
        }

        assert_eq!(
            AliasMethodWeightedIndex::<W>::new(vec![]).unwrap_err(),
            AliasMethodWeightedIndexError::NoItem
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![W::ZERO]).unwrap_err(),
            AliasMethodWeightedIndexError::AllWeightsZero
        );
        assert_eq!(
            AliasMethodWeightedIndex::new(vec![W::MAX, W::MAX]).unwrap_err(),
            AliasMethodWeightedIndexError::InvalidWeight
        );
    }
}

/// Error type returned from `WeightedIndex::new`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WeightedError {
    /// The provided iterator contained no items.
    NoItem,

    /// A weight lower than zero was used.
    NegativeWeight,

    /// All items in the provided iterator had a weight of zero.
    AllWeightsZero,
}

impl WeightedError {
    fn msg(&self) -> &str {
        match *self {
            WeightedError::NoItem => "No items found",
            WeightedError::NegativeWeight => "Item has negative weight",
            WeightedError::AllWeightsZero => "All items had weight zero",
        }
    }
}

#[cfg(feature="std")]
impl ::std::error::Error for WeightedError {
    fn description(&self) -> &str {
        self.msg()
    }
    fn cause(&self) -> Option<&::std::error::Error> {
        None
    }
}

impl fmt::Display for WeightedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.msg())
    }
}

#[allow(missing_docs)] // todo: add docs
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AliasMethodWeightedIndexError {
    NoItem,
    InvalidWeight,
    AllWeightsZero,
}

impl AliasMethodWeightedIndexError {
    fn msg(&self) -> &str {
        match *self {
            AliasMethodWeightedIndexError::NoItem => "No items found.",
            AliasMethodWeightedIndexError::InvalidWeight => "An item has an invalid weight.",
            AliasMethodWeightedIndexError::AllWeightsZero => "All weights are zero.",
        }
    }
}

impl fmt::Display for AliasMethodWeightedIndexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.msg())
    }
}

#[cfg(feature = "std")]
impl ::std::error::Error for AliasMethodWeightedIndexError {
    fn description(&self) -> &str {
        self.msg()
    }
    fn cause(&self) -> Option<&::std::error::Error> {
        None
    }
}
