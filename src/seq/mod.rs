// Copyright 2018-2023 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Sequence-related functionality
//!
//! This module provides:
//!
//! *   [`IndexedRandom`] for sampling slices and other indexable lists
//! *   [`IndexedMutRandom`] for sampling slices and other mutably indexable lists
//! *   [`SliceRandom`] for mutating slices
//! *   [`IteratorRandom`] for sampling iterators
//! *   [`index::sample`] low-level API to choose multiple indices from
//!     `0..length`
//!
//! Also see:
//!
//! *   [`crate::distributions::WeightedIndex`] distribution which provides
//!     weighted index sampling.
//!
//! In order to make results reproducible across 32-64 bit architectures, all
//! `usize` indices are sampled as a `u32` where possible (also providing a
//! small performance boost in some cases).

mod coin_flipper;
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
pub mod index;

mod increasing_uniform;

#[cfg(feature = "alloc")]
#[doc(no_inline)]
pub use crate::distributions::WeightError;

use core::ops::{Index, IndexMut};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "alloc")]
use crate::distributions::uniform::{SampleBorrow, SampleUniform};
#[cfg(feature = "alloc")] use crate::distributions::Weight;
use crate::Rng;

use self::coin_flipper::CoinFlipper;
use self::increasing_uniform::IncreasingUniform;

/// Extension trait on indexable lists, providing random sampling methods.
///
/// This trait is implemented on `[T]` slice types. Other types supporting
/// [`std::ops::Index<usize>`] may implement this (only [`Self::len`] must be
/// specified).
pub trait IndexedRandom: Index<usize> {
    /// The length
    fn len(&self) -> usize;

    /// True when the length is zero
    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Uniformly sample one element
    ///
    /// Returns a reference to one uniformly-sampled random element of
    /// the slice, or `None` if the slice is empty.
    ///
    /// For slices, complexity is `O(1)`.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::thread_rng;
    /// use rand::seq::IndexedRandom;
    ///
    /// let choices = [1, 2, 4, 8, 16, 32];
    /// let mut rng = thread_rng();
    /// println!("{:?}", choices.choose(&mut rng));
    /// assert_eq!(choices[..0].choose(&mut rng), None);
    /// ```
    fn choose<R>(&self, rng: &mut R) -> Option<&Self::Output>
    where
        R: Rng + ?Sized,
    {
        if self.is_empty() {
            None
        } else {
            Some(&self[gen_index(rng, self.len())])
        }
    }

    /// Uniformly sample `amount` distinct elements
    ///
    /// Chooses `amount` elements from the slice at random, without repetition,
    /// and in random order. The returned iterator is appropriate both for
    /// collection into a `Vec` and filling an existing buffer (see example).
    ///
    /// In case this API is not sufficiently flexible, use [`index::sample`].
    ///
    /// For slices, complexity is the same as [`index::sample`].
    ///
    /// # Example
    /// ```
    /// use rand::seq::IndexedRandom;
    ///
    /// let mut rng = &mut rand::thread_rng();
    /// let sample = "Hello, audience!".as_bytes();
    ///
    /// // collect the results into a vector:
    /// let v: Vec<u8> = sample.choose_multiple(&mut rng, 3).cloned().collect();
    ///
    /// // store in a buffer:
    /// let mut buf = [0u8; 5];
    /// for (b, slot) in sample.choose_multiple(&mut rng, buf.len()).zip(buf.iter_mut()) {
    ///     *slot = *b;
    /// }
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
    fn choose_multiple<R>(&self, rng: &mut R, amount: usize) -> SliceChooseIter<Self, Self::Output>
    where
        Self::Output: Sized,
        R: Rng + ?Sized,
    {
        let amount = ::core::cmp::min(amount, self.len());
        SliceChooseIter {
            slice: self,
            _phantom: Default::default(),
            indices: index::sample(rng, self.len(), amount).into_iter(),
        }
    }

    /// Biased sampling for one element
    ///
    /// Returns a reference to one element of the slice, sampled according
    /// to the provided weights. Returns `None` only if the slice is empty.
    ///
    /// The specified function `weight` maps each item `x` to a relative
    /// likelihood `weight(x)`. The probability of each item being selected is
    /// therefore `weight(x) / s`, where `s` is the sum of all `weight(x)`.
    ///
    /// For slices of length `n`, complexity is `O(n)`.
    /// For more information about the underlying algorithm,
    /// see [`distributions::WeightedIndex`].
    ///
    /// See also [`choose_weighted_mut`].
    ///
    /// # Example
    ///
    /// ```
    /// use rand::prelude::*;
    ///
    /// let choices = [('a', 2), ('b', 1), ('c', 1), ('d', 0)];
    /// let mut rng = thread_rng();
    /// // 50% chance to print 'a', 25% chance to print 'b', 25% chance to print 'c',
    /// // and 'd' will never be printed
    /// println!("{:?}", choices.choose_weighted(&mut rng, |item| item.1).unwrap().0);
    /// ```
    /// [`choose`]: IndexedRandom::choose
    /// [`choose_weighted_mut`]: IndexedMutRandom::choose_weighted_mut
    /// [`distributions::WeightedIndex`]: crate::distributions::WeightedIndex
    #[cfg(feature = "alloc")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
    fn choose_weighted<R, F, B, X>(
        &self, rng: &mut R, weight: F,
    ) -> Result<&Self::Output, WeightError>
    where
        R: Rng + ?Sized,
        F: Fn(&Self::Output) -> B,
        B: SampleBorrow<X>,
        X: SampleUniform + Weight + ::core::cmp::PartialOrd<X>,
    {
        use crate::distributions::{Distribution, WeightedIndex};
        let distr = WeightedIndex::new((0..self.len()).map(|idx| weight(&self[idx])))?;
        Ok(&self[distr.sample(rng)])
    }

    /// Biased sampling of `amount` distinct elements
    ///
    /// Similar to [`choose_multiple`], but where the likelihood of each element's
    /// inclusion in the output may be specified. The elements are returned in an
    /// arbitrary, unspecified order.
    ///
    /// The specified function `weight` maps each item `x` to a relative
    /// likelihood `weight(x)`. The probability of each item being selected is
    /// therefore `weight(x) / s`, where `s` is the sum of all `weight(x)`.
    ///
    /// If all of the weights are equal, even if they are all zero, each element has
    /// an equal likelihood of being selected.
    ///
    /// This implementation uses `O(length + amount)` space and `O(length)` time
    /// if the "nightly" feature is enabled, or `O(length)` space and
    /// `O(length + amount * log length)` time otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::prelude::*;
    ///
    /// let choices = [('a', 2), ('b', 1), ('c', 1)];
    /// let mut rng = thread_rng();
    /// // First Draw * Second Draw = total odds
    /// // -----------------------
    /// // (50% * 50%) + (25% * 67%) = 41.7% chance that the output is `['a', 'b']` in some order.
    /// // (50% * 50%) + (25% * 67%) = 41.7% chance that the output is `['a', 'c']` in some order.
    /// // (25% * 33%) + (25% * 33%) = 16.6% chance that the output is `['b', 'c']` in some order.
    /// println!("{:?}", choices.choose_multiple_weighted(&mut rng, 2, |item| item.1).unwrap().collect::<Vec<_>>());
    /// ```
    /// [`choose_multiple`]: IndexedRandom::choose_multiple
    //
    // Note: this is feature-gated on std due to usage of f64::powf.
    // If necessary, we may use alloc+libm as an alternative (see PR #1089).
    #[cfg(feature = "std")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
    fn choose_multiple_weighted<R, F, X>(
        &self, rng: &mut R, amount: usize, weight: F,
    ) -> Result<SliceChooseIter<Self, Self::Output>, WeightError>
    where
        Self::Output: Sized,
        R: Rng + ?Sized,
        F: Fn(&Self::Output) -> X,
        X: Into<f64>,
    {
        let amount = ::core::cmp::min(amount, self.len());
        Ok(SliceChooseIter {
            slice: self,
            _phantom: Default::default(),
            indices: index::sample_weighted(
                rng,
                self.len(),
                |idx| weight(&self[idx]).into(),
                amount,
            )?
            .into_iter(),
        })
    }
}

/// Extension trait on indexable lists, providing random sampling methods.
///
/// This trait is implemented automatically for every type implementing
/// [`IndexedRandom`] and [`std::ops::IndexMut<usize>`].
pub trait IndexedMutRandom: IndexedRandom + IndexMut<usize> {
    /// Uniformly sample one element (mut)
    ///
    /// Returns a mutable reference to one uniformly-sampled random element of
    /// the slice, or `None` if the slice is empty.
    ///
    /// For slices, complexity is `O(1)`.
    fn choose_mut<R>(&mut self, rng: &mut R) -> Option<&mut Self::Output>
    where
        R: Rng + ?Sized,
    {
        if self.is_empty() {
            None
        } else {
            let len = self.len();
            Some(&mut self[gen_index(rng, len)])
        }
    }

    /// Biased sampling for one element (mut)
    ///
    /// Returns a mutable reference to one element of the slice, sampled according
    /// to the provided weights. Returns `None` only if the slice is empty.
    ///
    /// The specified function `weight` maps each item `x` to a relative
    /// likelihood `weight(x)`. The probability of each item being selected is
    /// therefore `weight(x) / s`, where `s` is the sum of all `weight(x)`.
    ///
    /// For slices of length `n`, complexity is `O(n)`.
    /// For more information about the underlying algorithm,
    /// see [`distributions::WeightedIndex`].
    ///
    /// See also [`choose_weighted`].
    ///
    /// [`choose_mut`]: IndexedMutRandom::choose_mut
    /// [`choose_weighted`]: IndexedRandom::choose_weighted
    /// [`distributions::WeightedIndex`]: crate::distributions::WeightedIndex
    #[cfg(feature = "alloc")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
    fn choose_weighted_mut<R, F, B, X>(
        &mut self, rng: &mut R, weight: F,
    ) -> Result<&mut Self::Output, WeightError>
    where
        R: Rng + ?Sized,
        F: Fn(&Self::Output) -> B,
        B: SampleBorrow<X>,
        X: SampleUniform + Weight + ::core::cmp::PartialOrd<X>,
    {
        use crate::distributions::{Distribution, WeightedIndex};
        let distr = WeightedIndex::new((0..self.len()).map(|idx| weight(&self[idx])))?;
        let index = distr.sample(rng);
        Ok(&mut self[index])
    }
}

/// Extension trait on slices, providing shuffling methods.
///
/// This trait is implemented on all `[T]` slice types, providing several
/// methods for choosing and shuffling elements. You must `use` this trait:
///
/// ```
/// use rand::seq::SliceRandom;
///
/// let mut rng = rand::thread_rng();
/// let mut bytes = "Hello, random!".to_string().into_bytes();
/// bytes.shuffle(&mut rng);
/// let str = String::from_utf8(bytes).unwrap();
/// println!("{}", str);
/// ```
/// Example output (non-deterministic):
/// ```none
/// l,nmroHado !le
/// ```
pub trait SliceRandom: IndexedMutRandom {
    /// Shuffle a mutable slice in place.
    ///
    /// For slices of length `n`, complexity is `O(n)`.
    /// The resulting permutation is picked uniformly from the set of all possible permutations.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::seq::SliceRandom;
    /// use rand::thread_rng;
    ///
    /// let mut rng = thread_rng();
    /// let mut y = [1, 2, 3, 4, 5];
    /// println!("Unshuffled: {:?}", y);
    /// y.shuffle(&mut rng);
    /// println!("Shuffled:   {:?}", y);
    /// ```
    fn shuffle<R>(&mut self, rng: &mut R)
    where
        R: Rng + ?Sized;

    /// Shuffle a slice in place, but exit early.
    ///
    /// Returns two mutable slices from the source slice. The first contains
    /// `amount` elements randomly permuted. The second has the remaining
    /// elements that are not fully shuffled.
    ///
    /// This is an efficient method to select `amount` elements at random from
    /// the slice, provided the slice may be mutated.
    ///
    /// If you only need to choose elements randomly and `amount > self.len()/2`
    /// then you may improve performance by taking
    /// `amount = self.len() - amount` and using only the second slice.
    ///
    /// If `amount` is greater than the number of elements in the slice, this
    /// will perform a full shuffle.
    ///
    /// For slices, complexity is `O(m)` where `m = amount`.
    fn partial_shuffle<R>(
        &mut self, rng: &mut R, amount: usize,
    ) -> (&mut [Self::Output], &mut [Self::Output])
    where
        Self::Output: Sized,
        R: Rng + ?Sized;
}

/// Extension trait on iterators, providing random sampling methods.
///
/// This trait is implemented on all iterators `I` where `I: Iterator + Sized`
/// and provides methods for
/// choosing one or more elements. You must `use` this trait:
///
/// ```
/// use rand::seq::IteratorRandom;
///
/// let mut rng = rand::thread_rng();
///
/// let faces = "😀😎😐😕😠😢";
/// println!("I am {}!", faces.chars().choose(&mut rng).unwrap());
/// ```
/// Example output (non-deterministic):
/// ```none
/// I am 😀!
/// ```
pub trait IteratorRandom: Iterator + Sized {
    /// Uniformly sample one element
    ///
    /// Assuming that the [`Iterator::size_hint`] is correct, this method
    /// returns one uniformly-sampled random element of the slice, or `None`
    /// only if the slice is empty. Incorrect bounds on the `size_hint` may
    /// cause this method to incorrectly return `None` if fewer elements than
    /// the advertised `lower` bound are present and may prevent sampling of
    /// elements beyond an advertised `upper` bound (i.e. incorrect `size_hint`
    /// is memory-safe, but may result in unexpected `None` result and
    /// non-uniform distribution).
    ///
    /// With an accurate [`Iterator::size_hint`] and where [`Iterator::nth`] is
    /// a constant-time operation, this method can offer `O(1)` performance.
    /// Where no size hint is
    /// available, complexity is `O(n)` where `n` is the iterator length.
    /// Partial hints (where `lower > 0`) also improve performance.
    ///
    /// Note further that [`Iterator::size_hint`] may affect the number of RNG
    /// samples used as well as the result (while remaining uniform sampling).
    /// Consider instead using [`IteratorRandom::choose_stable`] to avoid
    /// [`Iterator`] combinators which only change size hints from affecting the
    /// results.
    fn choose<R>(mut self, rng: &mut R) -> Option<Self::Item>
    where
        R: Rng + ?Sized,
    {
        let (mut lower, mut upper) = self.size_hint();
        let mut result = None;

        // Handling for this condition outside the loop allows the optimizer to eliminate the loop
        // when the Iterator is an ExactSizeIterator. This has a large performance impact on e.g.
        // seq_iter_choose_from_1000.
        if upper == Some(lower) {
            return match lower {
                0 => None,
                1 => self.next(),
                _ => self.nth(gen_index(rng, lower)),
            };
        }

        let mut coin_flipper = coin_flipper::CoinFlipper::new(rng);
        let mut consumed = 0;

        // Continue until the iterator is exhausted
        loop {
            if lower > 1 {
                let ix = gen_index(coin_flipper.rng, lower + consumed);
                let skip = if ix < lower {
                    result = self.nth(ix);
                    lower - (ix + 1)
                } else {
                    lower
                };
                if upper == Some(lower) {
                    return result;
                }
                consumed += lower;
                if skip > 0 {
                    self.nth(skip - 1);
                }
            } else {
                let elem = self.next();
                if elem.is_none() {
                    return result;
                }
                consumed += 1;
                if coin_flipper.gen_ratio_one_over(consumed) {
                    result = elem;
                }
            }

            let hint = self.size_hint();
            lower = hint.0;
            upper = hint.1;
        }
    }

    /// Uniformly sample one element (stable)
    ///
    /// This method is very similar to [`choose`] except that the result
    /// only depends on the length of the iterator and the values produced by
    /// `rng`. Notably for any iterator of a given length this will make the
    /// same requests to `rng` and if the same sequence of values are produced
    /// the same index will be selected from `self`. This may be useful if you
    /// need consistent results no matter what type of iterator you are working
    /// with. If you do not need this stability prefer [`choose`].
    ///
    /// Note that this method still uses [`Iterator::size_hint`] to skip
    /// constructing elements where possible, however the selection and `rng`
    /// calls are the same in the face of this optimization. If you want to
    /// force every element to be created regardless call `.inspect(|e| ())`.
    ///
    /// [`choose`]: IteratorRandom::choose
    fn choose_stable<R>(mut self, rng: &mut R) -> Option<Self::Item>
    where
        R: Rng + ?Sized,
    {
        let mut consumed = 0;
        let mut result = None;
        let mut coin_flipper = CoinFlipper::new(rng);

        loop {
            // Currently the only way to skip elements is `nth()`. So we need to
            // store what index to access next here.
            // This should be replaced by `advance_by()` once it is stable:
            // https://github.com/rust-lang/rust/issues/77404
            let mut next = 0;

            let (lower, _) = self.size_hint();
            if lower >= 2 {
                let highest_selected = (0..lower)
                    .filter(|ix| coin_flipper.gen_ratio_one_over(consumed + ix + 1))
                    .last();

                consumed += lower;
                next = lower;

                if let Some(ix) = highest_selected {
                    result = self.nth(ix);
                    next -= ix + 1;
                    debug_assert!(result.is_some(), "iterator shorter than size_hint().0");
                }
            }

            let elem = self.nth(next);
            if elem.is_none() {
                return result;
            }

            if coin_flipper.gen_ratio_one_over(consumed + 1) {
                result = elem;
            }
            consumed += 1;
        }
    }

    /// Uniformly sample `amount` distinct elements into a buffer
    ///
    /// Collects values at random from the iterator into a supplied buffer
    /// until that buffer is filled.
    ///
    /// Although the elements are selected randomly, the order of elements in
    /// the buffer is neither stable nor fully random. If random ordering is
    /// desired, shuffle the result.
    ///
    /// Returns the number of elements added to the buffer. This equals the length
    /// of the buffer unless the iterator contains insufficient elements, in which
    /// case this equals the number of elements available.
    ///
    /// Complexity is `O(n)` where `n` is the length of the iterator.
    /// For slices, prefer [`IndexedRandom::choose_multiple`].
    fn choose_multiple_fill<R>(mut self, rng: &mut R, buf: &mut [Self::Item]) -> usize
    where
        R: Rng + ?Sized,
    {
        let amount = buf.len();
        let mut len = 0;
        while len < amount {
            if let Some(elem) = self.next() {
                buf[len] = elem;
                len += 1;
            } else {
                // Iterator exhausted; stop early
                return len;
            }
        }

        // Continue, since the iterator was not exhausted
        for (i, elem) in self.enumerate() {
            let k = gen_index(rng, i + 1 + amount);
            if let Some(slot) = buf.get_mut(k) {
                *slot = elem;
            }
        }
        len
    }

    /// Uniformly sample `amount` distinct elements into a [`Vec`]
    ///
    /// This is equivalent to `choose_multiple_fill` except for the result type.
    ///
    /// Although the elements are selected randomly, the order of elements in
    /// the buffer is neither stable nor fully random. If random ordering is
    /// desired, shuffle the result.
    ///
    /// The length of the returned vector equals `amount` unless the iterator
    /// contains insufficient elements, in which case it equals the number of
    /// elements available.
    ///
    /// Complexity is `O(n)` where `n` is the length of the iterator.
    /// For slices, prefer [`IndexedRandom::choose_multiple`].
    #[cfg(feature = "alloc")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
    fn choose_multiple<R>(mut self, rng: &mut R, amount: usize) -> Vec<Self::Item>
    where
        R: Rng + ?Sized,
    {
        let mut reservoir = Vec::with_capacity(amount);
        reservoir.extend(self.by_ref().take(amount));

        // Continue unless the iterator was exhausted
        //
        // note: this prevents iterators that "restart" from causing problems.
        // If the iterator stops once, then so do we.
        if reservoir.len() == amount {
            for (i, elem) in self.enumerate() {
                let k = gen_index(rng, i + 1 + amount);
                if let Some(slot) = reservoir.get_mut(k) {
                    *slot = elem;
                }
            }
        } else {
            // Don't hang onto extra memory. There is a corner case where
            // `amount` was much less than `self.len()`.
            reservoir.shrink_to_fit();
        }
        reservoir
    }
}

impl<T> IndexedRandom for [T] {
    fn len(&self) -> usize {
        self.len()
    }
}

impl<IR: IndexedRandom + IndexMut<usize> + ?Sized> IndexedMutRandom for IR {}

impl<T> SliceRandom for [T] {
    fn shuffle<R>(&mut self, rng: &mut R)
    where
        R: Rng + ?Sized,
    {
        if self.len() <= 1 {
            // There is no need to shuffle an empty or single element slice
            return;
        }
        self.partial_shuffle(rng, self.len());
    }

    fn partial_shuffle<R>(
        &mut self, rng: &mut R, amount: usize,
    ) -> (&mut [T], &mut [T])
    where
        R: Rng + ?Sized,
    {
        let m = self.len().saturating_sub(amount);

        // The algorithm below is based on Durstenfeld's algorithm for the
        // [Fisher–Yates shuffle](https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle#The_modern_algorithm)
        // for an unbiased permutation.
        // It ensures that the last `amount` elements of the slice
        // are randomly selected from the whole slice.

        // `IncreasingUniform::next_index()` is faster than `gen_index`
        // but only works for 32 bit integers
        // So we must use the slow method if the slice is longer than that.
        if self.len() < (u32::MAX as usize) {
            let mut chooser = IncreasingUniform::new(rng, m as u32);
            for i in m..self.len() {
                let index = chooser.next_index();
                self.swap(i, index);
            }
        } else {
            for i in m..self.len() {
                let index = gen_index(rng, i + 1);
                self.swap(i, index);
            }
        }
        let r = self.split_at_mut(m);
        (r.1, r.0)
    }
}

impl<I> IteratorRandom for I where I: Iterator + Sized {}

/// An iterator over multiple slice elements.
///
/// This struct is created by
/// [`IndexedRandom::choose_multiple`](trait.IndexedRandom.html#tymethod.choose_multiple).
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[derive(Debug)]
pub struct SliceChooseIter<'a, S: ?Sized + 'a, T: 'a> {
    slice: &'a S,
    _phantom: ::core::marker::PhantomData<T>,
    indices: index::IndexVecIntoIter,
}

#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
impl<'a, S: Index<usize, Output = T> + ?Sized + 'a, T: 'a> Iterator for SliceChooseIter<'a, S, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO: investigate using SliceIndex::get_unchecked when stable
        self.indices.next().map(|i| &self.slice[i])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.indices.len(), Some(self.indices.len()))
    }
}

#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
impl<'a, S: Index<usize, Output = T> + ?Sized + 'a, T: 'a> ExactSizeIterator
    for SliceChooseIter<'a, S, T>
{
    fn len(&self) -> usize {
        self.indices.len()
    }
}

// Sample a number uniformly between 0 and `ubound`. Uses 32-bit sampling where
// possible, primarily in order to produce the same output on 32-bit and 64-bit
// platforms.
#[inline]
fn gen_index<R: Rng + ?Sized>(rng: &mut R, ubound: usize) -> usize {
    if ubound <= (core::u32::MAX as usize) {
        rng.gen_range(0..ubound as u32) as usize
    } else {
        rng.gen_range(0..ubound)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[cfg(all(feature = "alloc", not(feature = "std")))]
    use alloc::vec::Vec;

    #[test]
    fn test_slice_choose() {
        let mut r = crate::test::rng(107);
        let chars = [
            'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n',
        ];
        let mut chosen = [0i32; 14];
        // The below all use a binomial distribution with n=1000, p=1/14.
        // binocdf(40, 1000, 1/14) ~= 2e-5; 1-binocdf(106, ..) ~= 2e-5
        for _ in 0..1000 {
            let picked = *chars.choose(&mut r).unwrap();
            chosen[(picked as usize) - ('a' as usize)] += 1;
        }
        for count in chosen.iter() {
            assert!(40 < *count && *count < 106);
        }

        chosen.iter_mut().for_each(|x| *x = 0);
        for _ in 0..1000 {
            *chosen.choose_mut(&mut r).unwrap() += 1;
        }
        for count in chosen.iter() {
            assert!(40 < *count && *count < 106);
        }

        let mut v: [isize; 0] = [];
        assert_eq!(v.choose(&mut r), None);
        assert_eq!(v.choose_mut(&mut r), None);
    }

    #[test]
    fn value_stability_slice() {
        let mut r = crate::test::rng(413);
        let chars = [
            'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n',
        ];
        let mut nums = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

        assert_eq!(chars.choose(&mut r), Some(&'l'));
        assert_eq!(nums.choose_mut(&mut r), Some(&mut 3));

        #[cfg(feature = "alloc")]
        assert_eq!(
            &chars
                .choose_multiple(&mut r, 8)
                .cloned()
                .collect::<Vec<char>>(),
            &['f', 'i', 'd', 'b', 'c', 'm', 'j', 'k']
        );

        #[cfg(feature = "alloc")]
        assert_eq!(chars.choose_weighted(&mut r, |_| 1), Ok(&'l'));
        #[cfg(feature = "alloc")]
        assert_eq!(nums.choose_weighted_mut(&mut r, |_| 1), Ok(&mut 8));

        let mut r = crate::test::rng(414);
        nums.shuffle(&mut r);
        assert_eq!(nums, [5, 11, 0, 8, 7, 12, 6, 4, 9, 3, 1, 2, 10]);
        nums = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let res = nums.partial_shuffle(&mut r, 6);
        assert_eq!(res.0, &mut [7, 12, 6, 8, 1, 9]);
        assert_eq!(res.1, &mut [0, 11, 2, 3, 4, 5, 10]);
    }

    #[derive(Clone)]
    struct UnhintedIterator<I: Iterator + Clone> {
        iter: I,
    }
    impl<I: Iterator + Clone> Iterator for UnhintedIterator<I> {
        type Item = I::Item;

        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next()
        }
    }

    #[derive(Clone)]
    struct ChunkHintedIterator<I: ExactSizeIterator + Iterator + Clone> {
        iter: I,
        chunk_remaining: usize,
        chunk_size: usize,
        hint_total_size: bool,
    }
    impl<I: ExactSizeIterator + Iterator + Clone> Iterator for ChunkHintedIterator<I> {
        type Item = I::Item;

        fn next(&mut self) -> Option<Self::Item> {
            if self.chunk_remaining == 0 {
                self.chunk_remaining = ::core::cmp::min(self.chunk_size, self.iter.len());
            }
            self.chunk_remaining = self.chunk_remaining.saturating_sub(1);

            self.iter.next()
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (
                self.chunk_remaining,
                if self.hint_total_size {
                    Some(self.iter.len())
                } else {
                    None
                },
            )
        }
    }

    #[derive(Clone)]
    struct WindowHintedIterator<I: ExactSizeIterator + Iterator + Clone> {
        iter: I,
        window_size: usize,
        hint_total_size: bool,
    }
    impl<I: ExactSizeIterator + Iterator + Clone> Iterator for WindowHintedIterator<I> {
        type Item = I::Item;

        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next()
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            (
                ::core::cmp::min(self.iter.len(), self.window_size),
                if self.hint_total_size {
                    Some(self.iter.len())
                } else {
                    None
                },
            )
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_iterator_choose() {
        let r = &mut crate::test::rng(109);
        fn test_iter<R: Rng + ?Sized, Iter: Iterator<Item = usize> + Clone>(r: &mut R, iter: Iter) {
            let mut chosen = [0i32; 9];
            for _ in 0..1000 {
                let picked = iter.clone().choose(r).unwrap();
                chosen[picked] += 1;
            }
            for count in chosen.iter() {
                // Samples should follow Binomial(1000, 1/9)
                // Octave: binopdf(x, 1000, 1/9) gives the prob of *count == x
                // Note: have seen 153, which is unlikely but not impossible.
                assert!(
                    72 < *count && *count < 154,
                    "count not close to 1000/9: {}",
                    count
                );
            }
        }

        test_iter(r, 0..9);
        test_iter(r, [0, 1, 2, 3, 4, 5, 6, 7, 8].iter().cloned());
        #[cfg(feature = "alloc")]
        test_iter(r, (0..9).collect::<Vec<_>>().into_iter());
        test_iter(r, UnhintedIterator { iter: 0..9 });
        test_iter(
            r,
            ChunkHintedIterator {
                iter: 0..9,
                chunk_size: 4,
                chunk_remaining: 4,
                hint_total_size: false,
            },
        );
        test_iter(
            r,
            ChunkHintedIterator {
                iter: 0..9,
                chunk_size: 4,
                chunk_remaining: 4,
                hint_total_size: true,
            },
        );
        test_iter(
            r,
            WindowHintedIterator {
                iter: 0..9,
                window_size: 2,
                hint_total_size: false,
            },
        );
        test_iter(
            r,
            WindowHintedIterator {
                iter: 0..9,
                window_size: 2,
                hint_total_size: true,
            },
        );

        assert_eq!((0..0).choose(r), None);
        assert_eq!(UnhintedIterator { iter: 0..0 }.choose(r), None);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_iterator_choose_stable() {
        let r = &mut crate::test::rng(109);
        fn test_iter<R: Rng + ?Sized, Iter: Iterator<Item = usize> + Clone>(r: &mut R, iter: Iter) {
            let mut chosen = [0i32; 9];
            for _ in 0..1000 {
                let picked = iter.clone().choose_stable(r).unwrap();
                chosen[picked] += 1;
            }
            for count in chosen.iter() {
                // Samples should follow Binomial(1000, 1/9)
                // Octave: binopdf(x, 1000, 1/9) gives the prob of *count == x
                // Note: have seen 153, which is unlikely but not impossible.
                assert!(
                    72 < *count && *count < 154,
                    "count not close to 1000/9: {}",
                    count
                );
            }
        }

        test_iter(r, 0..9);
        test_iter(r, [0, 1, 2, 3, 4, 5, 6, 7, 8].iter().cloned());
        #[cfg(feature = "alloc")]
        test_iter(r, (0..9).collect::<Vec<_>>().into_iter());
        test_iter(r, UnhintedIterator { iter: 0..9 });
        test_iter(
            r,
            ChunkHintedIterator {
                iter: 0..9,
                chunk_size: 4,
                chunk_remaining: 4,
                hint_total_size: false,
            },
        );
        test_iter(
            r,
            ChunkHintedIterator {
                iter: 0..9,
                chunk_size: 4,
                chunk_remaining: 4,
                hint_total_size: true,
            },
        );
        test_iter(
            r,
            WindowHintedIterator {
                iter: 0..9,
                window_size: 2,
                hint_total_size: false,
            },
        );
        test_iter(
            r,
            WindowHintedIterator {
                iter: 0..9,
                window_size: 2,
                hint_total_size: true,
            },
        );

        assert_eq!((0..0).choose(r), None);
        assert_eq!(UnhintedIterator { iter: 0..0 }.choose(r), None);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_iterator_choose_stable_stability() {
        fn test_iter(iter: impl Iterator<Item = usize> + Clone) -> [i32; 9] {
            let r = &mut crate::test::rng(109);
            let mut chosen = [0i32; 9];
            for _ in 0..1000 {
                let picked = iter.clone().choose_stable(r).unwrap();
                chosen[picked] += 1;
            }
            chosen
        }

        let reference = test_iter(0..9);
        assert_eq!(
            test_iter([0, 1, 2, 3, 4, 5, 6, 7, 8].iter().cloned()),
            reference
        );

        #[cfg(feature = "alloc")]
        assert_eq!(test_iter((0..9).collect::<Vec<_>>().into_iter()), reference);
        assert_eq!(test_iter(UnhintedIterator { iter: 0..9 }), reference);
        assert_eq!(
            test_iter(ChunkHintedIterator {
                iter: 0..9,
                chunk_size: 4,
                chunk_remaining: 4,
                hint_total_size: false,
            }),
            reference
        );
        assert_eq!(
            test_iter(ChunkHintedIterator {
                iter: 0..9,
                chunk_size: 4,
                chunk_remaining: 4,
                hint_total_size: true,
            }),
            reference
        );
        assert_eq!(
            test_iter(WindowHintedIterator {
                iter: 0..9,
                window_size: 2,
                hint_total_size: false,
            }),
            reference
        );
        assert_eq!(
            test_iter(WindowHintedIterator {
                iter: 0..9,
                window_size: 2,
                hint_total_size: true,
            }),
            reference
        );
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_shuffle() {
        let mut r = crate::test::rng(108);
        let empty: &mut [isize] = &mut [];
        empty.shuffle(&mut r);
        let mut one = [1];
        one.shuffle(&mut r);
        let b: &[_] = &[1];
        assert_eq!(one, b);

        let mut two = [1, 2];
        two.shuffle(&mut r);
        assert!(two == [1, 2] || two == [2, 1]);

        fn move_last(slice: &mut [usize], pos: usize) {
            // use slice[pos..].rotate_left(1); once we can use that
            let last_val = slice[pos];
            for i in pos..slice.len() - 1 {
                slice[i] = slice[i + 1];
            }
            *slice.last_mut().unwrap() = last_val;
        }
        let mut counts = [0i32; 24];
        for _ in 0..10000 {
            let mut arr: [usize; 4] = [0, 1, 2, 3];
            arr.shuffle(&mut r);
            let mut permutation = 0usize;
            let mut pos_value = counts.len();
            for i in 0..4 {
                pos_value /= 4 - i;
                let pos = arr.iter().position(|&x| x == i).unwrap();
                assert!(pos < (4 - i));
                permutation += pos * pos_value;
                move_last(&mut arr, pos);
                assert_eq!(arr[3], i);
            }
            for (i, &a) in arr.iter().enumerate() {
                assert_eq!(a, i);
            }
            counts[permutation] += 1;
        }
        for count in counts.iter() {
            // Binomial(10000, 1/24) with average 416.667
            // Octave: binocdf(n, 10000, 1/24)
            // 99.9% chance samples lie within this range:
            assert!(352 <= *count && *count <= 483, "count: {}", count);
        }
    }

    #[test]
    fn test_partial_shuffle() {
        let mut r = crate::test::rng(118);

        let mut empty: [u32; 0] = [];
        let res = empty.partial_shuffle(&mut r, 10);
        assert_eq!((res.0.len(), res.1.len()), (0, 0));

        let mut v = [1, 2, 3, 4, 5];
        let res = v.partial_shuffle(&mut r, 2);
        assert_eq!((res.0.len(), res.1.len()), (2, 3));
        assert!(res.0[0] != res.0[1]);
        // First elements are only modified if selected, so at least one isn't modified:
        assert!(res.1[0] == 1 || res.1[1] == 2 || res.1[2] == 3);
    }

    #[test]
    #[cfg(feature = "alloc")]
    fn test_sample_iter() {
        let min_val = 1;
        let max_val = 100;

        let mut r = crate::test::rng(401);
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample = vals.iter().choose_multiple(&mut r, 5);
        let large_sample = vals.iter().choose_multiple(&mut r, vals.len() + 5);

        assert_eq!(small_sample.len(), 5);
        assert_eq!(large_sample.len(), vals.len());
        // no randomization happens when amount >= len
        assert_eq!(large_sample, vals.iter().collect::<Vec<_>>());

        assert!(small_sample
            .iter()
            .all(|e| { **e >= min_val && **e <= max_val }));
    }

    #[test]
    #[cfg(feature = "alloc")]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_weighted() {
        let mut r = crate::test::rng(406);
        const N_REPS: u32 = 3000;
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

        // choose_weighted
        fn get_weight<T>(item: &(u32, T)) -> u32 {
            item.0
        }
        let mut chosen = [0i32; 14];
        let mut items = [(0u32, 0usize); 14]; // (weight, index)
        for (i, item) in items.iter_mut().enumerate() {
            *item = (weights[i], i);
        }
        for _ in 0..N_REPS {
            let item = items.choose_weighted(&mut r, get_weight).unwrap();
            chosen[item.1] += 1;
        }
        verify(chosen);

        // choose_weighted_mut
        let mut items = [(0u32, 0i32); 14]; // (weight, count)
        for (i, item) in items.iter_mut().enumerate() {
            *item = (weights[i], 0);
        }
        for _ in 0..N_REPS {
            items.choose_weighted_mut(&mut r, get_weight).unwrap().1 += 1;
        }
        for (ch, item) in chosen.iter_mut().zip(items.iter()) {
            *ch = item.1;
        }
        verify(chosen);

        // Check error cases
        let empty_slice = &mut [10][0..0];
        assert_eq!(
            empty_slice.choose_weighted(&mut r, |_| 1),
            Err(WeightError::InvalidInput)
        );
        assert_eq!(
            empty_slice.choose_weighted_mut(&mut r, |_| 1),
            Err(WeightError::InvalidInput)
        );
        assert_eq!(
            ['x'].choose_weighted_mut(&mut r, |_| 0),
            Err(WeightError::InsufficientNonZero)
        );
        assert_eq!(
            [0, -1].choose_weighted_mut(&mut r, |x| *x),
            Err(WeightError::InvalidWeight)
        );
        assert_eq!(
            [-1, 0].choose_weighted_mut(&mut r, |x| *x),
            Err(WeightError::InvalidWeight)
        );
    }

    #[test]
    fn value_stability_choose() {
        fn choose<I: Iterator<Item = u32>>(iter: I) -> Option<u32> {
            let mut rng = crate::test::rng(411);
            iter.choose(&mut rng)
        }

        assert_eq!(choose([].iter().cloned()), None);
        assert_eq!(choose(0..100), Some(33));
        assert_eq!(choose(UnhintedIterator { iter: 0..100 }), Some(27));
        assert_eq!(
            choose(ChunkHintedIterator {
                iter: 0..100,
                chunk_size: 32,
                chunk_remaining: 32,
                hint_total_size: false,
            }),
            Some(91)
        );
        assert_eq!(
            choose(ChunkHintedIterator {
                iter: 0..100,
                chunk_size: 32,
                chunk_remaining: 32,
                hint_total_size: true,
            }),
            Some(91)
        );
        assert_eq!(
            choose(WindowHintedIterator {
                iter: 0..100,
                window_size: 32,
                hint_total_size: false,
            }),
            Some(34)
        );
        assert_eq!(
            choose(WindowHintedIterator {
                iter: 0..100,
                window_size: 32,
                hint_total_size: true,
            }),
            Some(34)
        );
    }

    #[test]
    fn value_stability_choose_stable() {
        fn choose<I: Iterator<Item = u32>>(iter: I) -> Option<u32> {
            let mut rng = crate::test::rng(411);
            iter.choose_stable(&mut rng)
        }

        assert_eq!(choose([].iter().cloned()), None);
        assert_eq!(choose(0..100), Some(27));
        assert_eq!(choose(UnhintedIterator { iter: 0..100 }), Some(27));
        assert_eq!(
            choose(ChunkHintedIterator {
                iter: 0..100,
                chunk_size: 32,
                chunk_remaining: 32,
                hint_total_size: false,
            }),
            Some(27)
        );
        assert_eq!(
            choose(ChunkHintedIterator {
                iter: 0..100,
                chunk_size: 32,
                chunk_remaining: 32,
                hint_total_size: true,
            }),
            Some(27)
        );
        assert_eq!(
            choose(WindowHintedIterator {
                iter: 0..100,
                window_size: 32,
                hint_total_size: false,
            }),
            Some(27)
        );
        assert_eq!(
            choose(WindowHintedIterator {
                iter: 0..100,
                window_size: 32,
                hint_total_size: true,
            }),
            Some(27)
        );
    }

    #[test]
    fn value_stability_choose_multiple() {
        fn do_test<I: Clone + Iterator<Item = u32>>(iter: I, v: &[u32]) {
            let mut rng = crate::test::rng(412);
            let mut buf = [0u32; 8];
            assert_eq!(iter.clone().choose_multiple_fill(&mut rng, &mut buf), v.len());
            assert_eq!(&buf[0..v.len()], v);

            #[cfg(feature = "alloc")]
            {
                let mut rng = crate::test::rng(412);
                assert_eq!(iter.choose_multiple(&mut rng, v.len()), v);
            }
        }

        do_test(0..4, &[0, 1, 2, 3]);
        do_test(0..8, &[0, 1, 2, 3, 4, 5, 6, 7]);
        do_test(0..100, &[77, 95, 38, 23, 25, 8, 58, 40]);
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_multiple_weighted_edge_cases() {
        use super::*;

        let mut rng = crate::test::rng(413);

        // Case 1: One of the weights is 0
        let choices = [('a', 2), ('b', 1), ('c', 0)];
        for _ in 0..100 {
            let result = choices
                .choose_multiple_weighted(&mut rng, 2, |item| item.1)
                .unwrap()
                .collect::<Vec<_>>();

            assert_eq!(result.len(), 2);
            assert!(!result.iter().any(|val| val.0 == 'c'));
        }

        // Case 2: All of the weights are 0
        let choices = [('a', 0), ('b', 0), ('c', 0)];
        let r = choices.choose_multiple_weighted(&mut rng, 2, |item| item.1);
        assert_eq!(r.unwrap_err(), WeightError::InsufficientNonZero);

        // Case 3: Negative weights
        let choices = [('a', -1), ('b', 1), ('c', 1)];
        let r = choices.choose_multiple_weighted(&mut rng, 2, |item| item.1);
        assert_eq!(r.unwrap_err(), WeightError::InvalidWeight);

        // Case 4: Empty list
        let choices = [];
        let r = choices.choose_multiple_weighted(&mut rng, 0, |_: &()| 0);
        assert_eq!(r.unwrap().count(), 0);

        // Case 5: NaN weights
        let choices = [('a', core::f64::NAN), ('b', 1.0), ('c', 1.0)];
        let r = choices.choose_multiple_weighted(&mut rng, 2, |item| item.1);
        assert_eq!(r.unwrap_err(), WeightError::InvalidWeight);

        // Case 6: +infinity weights
        let choices = [('a', core::f64::INFINITY), ('b', 1.0), ('c', 1.0)];
        for _ in 0..100 {
            let result = choices
                .choose_multiple_weighted(&mut rng, 2, |item| item.1)
                .unwrap()
                .collect::<Vec<_>>();
            assert_eq!(result.len(), 2);
            assert!(result.iter().any(|val| val.0 == 'a'));
        }

        // Case 7: -infinity weights
        let choices = [('a', core::f64::NEG_INFINITY), ('b', 1.0), ('c', 1.0)];
        let r = choices.choose_multiple_weighted(&mut rng, 2, |item| item.1);
        assert_eq!(r.unwrap_err(), WeightError::InvalidWeight);

        // Case 8: -0 weights
        let choices = [('a', -0.0), ('b', 1.0), ('c', 1.0)];
        let r = choices.choose_multiple_weighted(&mut rng, 2, |item| item.1);
        assert!(r.is_ok());
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_multiple_weighted_distributions() {
        use super::*;

        // The theoretical probabilities of the different outcomes are:
        // AB: 0.5  * 0.5  = 0.250
        // AC: 0.5  * 0.5  = 0.250
        // BA: 0.25 * 0.67 = 0.167
        // BC: 0.25 * 0.33 = 0.082
        // CA: 0.25 * 0.67 = 0.167
        // CB: 0.25 * 0.33 = 0.082
        let choices = [('a', 2), ('b', 1), ('c', 1)];
        let mut rng = crate::test::rng(414);

        let mut results = [0i32; 3];
        let expected_results = [4167, 4167, 1666];
        for _ in 0..10000 {
            let result = choices
                .choose_multiple_weighted(&mut rng, 2, |item| item.1)
                .unwrap()
                .collect::<Vec<_>>();

            assert_eq!(result.len(), 2);

            match (result[0].0, result[1].0) {
                ('a', 'b') | ('b', 'a') => {
                    results[0] += 1;
                }
                ('a', 'c') | ('c', 'a') => {
                    results[1] += 1;
                }
                ('b', 'c') | ('c', 'b') => {
                    results[2] += 1;
                }
                (_, _) => panic!("unexpected result"),
            }
        }

        let mut diffs = results
            .iter()
            .zip(&expected_results)
            .map(|(a, b)| (a - b).abs());
        assert!(!diffs.any(|deviation| deviation > 100));
    }
}
