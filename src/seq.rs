// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functions for randomly accessing and sampling sequences.
//! 
//! TODO: module doc

#[cfg(feature="alloc")] use core::ops::Index;

#[cfg(feature="std")] use std::vec;
#[cfg(all(feature="alloc", not(feature="std")))] use alloc::{vec, Vec};

// BTreeMap is not as fast in tests, but better than nothing.
#[cfg(feature="std")] use std::collections::HashMap;
#[cfg(all(feature="alloc", not(feature="std")))] use alloc::btree_map::BTreeMap;

use super::Rng;
use distributions::uniform::SampleUniform;

/// Extension trait on slices, providing random mutation and sampling methods.
/// 
/// An implementation is provided for slices. This may also be implementable for
/// other types.
pub trait SliceRandom {
    /// The element type.
    type Item;

    /// Returns a reference to one random element of the slice, or `None` if the
    /// slice is empty.
    /// 
    /// Depending on the implementation, complexity is expected to be `O(1)`.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::thread_rng;
    /// use rand::seq::SliceRandom;
    ///
    /// let choices = [1, 2, 4, 8, 16, 32];
    /// let mut rng = thread_rng();
    /// println!("{:?}", choices.choose(&mut rng));
    /// assert_eq!(choices[..0].choose(&mut rng), None);
    /// ```
    fn choose<R>(&self, rng: &mut R) -> Option<&Self::Item>
        where R: Rng + ?Sized;

    /// Returns a mutable reference to one random element of the slice, or
    /// `None` if the slice is empty.
    /// 
    /// Depending on the implementation, complexity is expected to be `O(1)`.
    fn choose_mut<R>(&mut self, rng: &mut R) -> Option<&mut Self::Item>
        where R: Rng + ?Sized;

    /// Produces an iterator that chooses `amount` elements from the slice at
    /// random without repeating any.
    ///
    /// In case this API is not sufficiently flexible, use `sample_indices` then
    /// apply the indices to the slice.
    /// 
    /// Although the elements are selected randomly, the order of returned
    /// elements is neither stable nor fully random. If random ordering is
    /// desired, either use `partial_shuffle` or use this method and shuffle
    /// the result. If stable order is desired, use `sample_indices`, sort the
    /// result, then apply to the slice.
    /// 
    /// Complexity is expected to be the same as `sample_indices`.
    /// 
    /// # Example
    /// ```
    /// use rand::seq::SliceRandom;
    /// 
    /// let mut rng = &mut rand::thread_rng();
    /// let sequence = "Hello, audience!".as_bytes();
    /// 
    /// // collect the results into a vector:
    /// let v: Vec<u8> = sequence.sample(&mut rng, 3).cloned().collect();
    /// 
    /// // store in a buffer:
    /// let mut buf = [0u8; 5];
    /// for (b, slot) in sequence.sample(&mut rng, buf.len()).zip(buf.iter_mut()) {
    ///     *slot = *b;
    /// }
    /// ```
    #[cfg(feature = "alloc")]
    fn sample<R>(&self, rng: &mut R, amount: usize) -> SliceChooseIter<Self, Self::Item>
        where R: Rng + ?Sized;

    /// Shuffle a mutable slice in place.
    /// 
    /// Depending on the implementation, complexity is expected to be `O(1)`.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::thread_rng;
    /// use rand::seq::SliceRandom;
    ///
    /// let mut rng = thread_rng();
    /// let mut y = [1, 2, 3, 4, 5];
    /// println!("Unshuffled: {:?}", y);
    /// y.shuffle(&mut rng);
    /// println!("Shuffled:   {:?}", y);
    /// ```
    fn shuffle<R>(&mut self, rng: &mut R) where R: Rng + ?Sized;

    /// Shuffle a slice in place, but exit early.
    ///
    /// Returns two mutable slices from the source slice. The first contains
    /// `amount` elements randomly permuted. The second has the remaining
    /// elements that are not fully shuffled.
    ///
    /// This is an efficient method to select `amount` elements at random from
    /// the slice, provided the slice may be mutated.
    ///
    /// If you only need to chose elements randomly and `amount > self.len()/2`
    /// then you may improve performance by taking
    /// `amount = values.len() - amount` and using only the second slice.
    ///
    /// If `amount` is greater than the number of elements in the slice, this
    /// will perform a full shuffle.
    ///
    /// Depending on the implementation, complexity is expected to be `O(m)`,
    /// where `m = amount`.
    fn partial_shuffle<R>(&mut self, rng: &mut R, amount: usize)
        -> (&mut [Self::Item], &mut [Self::Item]) where R: Rng + ?Sized;
}

/// Extension trait on iterators, providing random sampling methods.
pub trait IteratorRandom: Iterator + Sized {
    /// Choose one element at random from the iterator.
    ///
    /// Returns `None` if and only if the iterator is empty.
    /// 
    /// Complexity is `O(n)`, where `n` is the length of the iterator.
    /// This likely consumes multiple random numbers, but the exact number
    /// is unspecified.
    fn choose<R>(mut self, rng: &mut R) -> Option<Self::Item>
        where R: Rng + ?Sized
    {
        if let Some(elem) = self.next() {
            let mut result = elem;
            
            // Continue until the iterator is exhausted
            for (i, elem) in self.enumerate() {
                let denom = (i + 2) as u32;
                assert_eq!(denom as usize, i + 2);  // check against overflow
                if rng.gen_ratio(1, denom) {
                    result = elem;
                }
            }
            
            Some(result)
        } else {
            None
        }
    }

    /// Collects `amount` values at random from the iterator into a supplied
    /// buffer.
    /// 
    /// Although the elements are selected randomly, the order of elements in
    /// the buffer is neither stable nor fully random. If random ordering is
    /// desired, shuffle the result.
    /// 
    /// Returns the number of elements added to the buffer. This equals `amount`
    /// unless the iterator contains insufficient elements, in which case this
    /// equals the number of elements available.
    /// 
    /// Complexity is `O(n)` where `n` is the length of the iterator.
    fn sample_fill<R>(mut self, rng: &mut R, buf: &mut [Self::Item])
        -> usize where R: Rng + ?Sized
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
            let k = rng.gen_range(0, i + 1 + amount);
            if k < amount {
                buf[k] = elem;
            }
        }
        len
    }

    /// Collects `amount` values at random from the iterator into a vector.
    ///
    /// This is equivalent to `sample_fill` except for the result type.
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
    #[cfg(feature = "alloc")]
    fn sample<R>(mut self, rng: &mut R, amount: usize) -> Vec<Self::Item>
        where R: Rng + ?Sized
    {
        let mut reservoir = Vec::with_capacity(amount);
        reservoir.extend(self.by_ref().take(amount));

        // Continue unless the iterator was exhausted
        //
        // note: this prevents iterators that "restart" from causing problems.
        // If the iterator stops once, then so do we.
        if reservoir.len() == amount {
            for (i, elem) in self.enumerate() {
                let k = rng.gen_range(0, i + 1 + amount);
                if let Some(spot) = reservoir.get_mut(k) {
                    *spot = elem;
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


impl<T> SliceRandom for [T] {
    type Item = T;

    fn choose<R>(&self, rng: &mut R) -> Option<&Self::Item>
        where R: Rng + ?Sized
    {
        if self.is_empty() {
            None
        } else {
            Some(&self[rng.gen_range(0, self.len())])
        }
    }

    fn choose_mut<R>(&mut self, rng: &mut R) -> Option<&mut Self::Item>
        where R: Rng + ?Sized
    {
        if self.is_empty() {
            None
        } else {
            let len = self.len();
            Some(&mut self[rng.gen_range(0, len)])
        }
    }

    #[cfg(feature = "alloc")]
    fn sample<R>(&self, rng: &mut R, amount: usize) -> SliceChooseIter<Self, Self::Item>
        where R: Rng + ?Sized
    {
        let amount = ::core::cmp::min(amount, self.len());
        SliceChooseIter {
            slice: self,
            _phantom: Default::default(),
            indices: sample_indices(rng, self.len(), amount).into_iter(),
        }
    }

    fn shuffle<R>(&mut self, rng: &mut R) where R: Rng + ?Sized
    {
        for i in (1..self.len()).rev() {
            // invariant: elements with index > i have been locked in place.
            self.swap(i, rng.gen_range(0, i + 1));
        }
    }

    fn partial_shuffle<R>(&mut self, rng: &mut R, amount: usize)
        -> (&mut [Self::Item], &mut [Self::Item]) where R: Rng + ?Sized
    {
        // This applies Durstenfeld's algorithm for the
        // [Fisher–Yates shuffle](https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle#The_modern_algorithm)
        // for an unbiased permutation, but exits early after choosing `amount`
        // elements.
        
        let len = self.len();
        let end = if amount >= len { 0 } else { len - amount };
        
        for i in (end..len).rev() {
            // invariant: elements with index > i have been locked in place.
            self.swap(i, rng.gen_range(0, i + 1));
        }
        let r = self.split_at_mut(end);
        (r.1, r.0)
    }
}

impl<I> IteratorRandom for I where I: Iterator + Sized {}


/// Iterator over multiple choices, as returned by [`SliceRandom::sample](
/// trait.SliceRandom.html#method.sample).
#[cfg(feature = "alloc")]
#[derive(Debug)]
pub struct SliceChooseIter<'a, S: ?Sized + 'a, T: 'a> {
    slice: &'a S,
    _phantom: ::core::marker::PhantomData<T>,
    indices: vec::IntoIter<usize>,
}

#[cfg(feature = "alloc")]
impl<'a, S: Index<usize, Output = T> + ?Sized + 'a, T: 'a> Iterator for SliceChooseIter<'a, S, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO: get_unchecked?
        self.indices.next().map(|i| &(*self.slice)[i])
    }
    
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.indices.len(), Some(self.indices.len()))
    }
}

#[cfg(feature = "alloc")]
impl<'a, S: Index<usize, Output = T> + ?Sized + 'a, T: 'a> ExactSizeIterator
    for SliceChooseIter<'a, S, T>
{
    fn len(&self) -> usize {
        self.indices.len()
    }
}


// ———
// TODO: also revise signature of `sample_indices`?
// ———

/// Randomly sample `amount` elements from a finite iterator.
///
/// Deprecated: use [`IteratorRandom::sample`] instead.
/// 
/// [`IteratorRandom::sample`]: trait.IteratorRandom.html#method.sample
#[cfg(feature = "alloc")]
#[deprecated(since="0.6.0", note="use IteratorRandom::sample instead")]
pub fn sample_iter<T, I, R>(rng: &mut R, iterable: I, amount: usize) -> Result<Vec<T>, Vec<T>>
    where I: IntoIterator<Item=T>,
          R: Rng + ?Sized,
{
    use seq::IteratorRandom;
    let iter = iterable.into_iter();
    let result = iter.sample(rng, amount);
    if result.len() == amount {
        Ok(result)
    } else {
        Err(result)
    }
}

/// Randomly sample exactly `amount` values from `slice`.
///
/// The values are non-repeating and in random order.
///
/// This implementation uses `O(amount)` time and memory.
///
/// Panics if `amount > slice.len()`
///
/// Deprecated: use [`SliceRandom::sample`] instead.
/// 
/// [`SliceRandom::sample`]: trait.SliceRandom.html#method.sample
#[cfg(feature = "alloc")]
#[deprecated(since="0.6.0", note="use SliceRandom::sample instead")]
pub fn sample_slice<R, T>(rng: &mut R, slice: &[T], amount: usize) -> Vec<T>
    where R: Rng + ?Sized,
          T: Clone
{
    let indices = sample_indices(rng, slice.len(), amount);

    let mut out = Vec::with_capacity(amount);
    out.extend(indices.iter().map(|i| slice[*i].clone()));
    out
}

/// Randomly sample exactly `amount` references from `slice`.
///
/// The references are non-repeating and in random order.
///
/// This implementation uses `O(amount)` time and memory.
///
/// Panics if `amount > slice.len()`
///
/// Deprecated: use [`SliceRandom::sample`] instead.
/// 
/// [`SliceRandom::sample`]: trait.SliceRandom.html#method.sample
#[cfg(feature = "alloc")]
#[deprecated(since="0.6.0", note="use SliceRandom::sample instead")]
pub fn sample_slice_ref<'a, R, T>(rng: &mut R, slice: &'a [T], amount: usize) -> Vec<&'a T>
    where R: Rng + ?Sized
{
    let indices = sample_indices(rng, slice.len(), amount);

    let mut out = Vec::with_capacity(amount);
    out.extend(indices.iter().map(|i| &slice[*i]));
    out
}

/// Randomly sample exactly `amount` indices from `0..length`.
///
/// The values are non-repeating and in random order.
///
/// This implementation uses `O(amount)` time and memory.
///
/// This method is used internally by the slice sampling methods, but it can sometimes be useful to
/// have the indices themselves so this is provided as an alternative.
///
/// Panics if `amount > length`
#[cfg(feature = "alloc")]
pub fn sample_indices<R>(rng: &mut R, length: usize, amount: usize) -> Vec<usize>
    where R: Rng + ?Sized,
{
    if amount > length {
        panic!("`amount` must be less than or equal to `slice.len()`");
    }

    // We are going to have to allocate at least `amount` for the output no matter what. However,
    // if we use the `cached` version we will have to allocate `amount` as a HashMap as well since
    // it inserts an element for every loop.
    //
    // Therefore, if `amount >= length / 2` then inplace will be both faster and use less memory.
    // In fact, benchmarks show the inplace version is faster for length up to about 20 times
    // faster than amount.
    //
    // TODO: there is probably even more fine-tuning that can be done here since
    // `HashMap::with_capacity(amount)` probably allocates more than `amount` in practice,
    // and a trade off could probably be made between memory/cpu, since hashmap operations
    // are slower than array index swapping.
    if amount >= length / 20 {
        sample_indices_inplace(rng, length, amount)
    } else {
        sample_indices_cache(rng, length, amount)
    }
}

/// Sample an amount of indices using an inplace partial fisher yates method.
///
/// This allocates the entire `length` of indices and randomizes only the first `amount`.
/// It then truncates to `amount` and returns.
///
/// This is better than using a `HashMap` "cache" when `amount >= length / 2`
/// since it does not require allocating an extra cache and is much faster.
#[cfg(feature = "alloc")]
fn sample_indices_inplace<R>(rng: &mut R, length: usize, amount: usize) -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    let mut indices: Vec<usize> = Vec::with_capacity(length);
    indices.extend(0..length);
    for i in 0..amount {
        let j: usize = rng.gen_range(i, length);
        indices.swap(i, j);
    }
    indices.truncate(amount);
    debug_assert_eq!(indices.len(), amount);
    indices
}


/// This method performs a partial fisher-yates on a range of indices using a
/// `HashMap` as a cache to record potential collisions.
///
/// The cache avoids allocating the entire `length` of values. This is especially useful when
/// `amount <<< length`, i.e. select 3 non-repeating from `1_000_000`
#[cfg(feature = "alloc")]
fn sample_indices_cache<R>(
    rng: &mut R,
    length: usize,
    amount: usize,
) -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    #[cfg(feature="std")] let mut cache = HashMap::with_capacity(amount);
    #[cfg(not(feature="std"))] let mut cache = BTreeMap::new();
    let mut out = Vec::with_capacity(amount);
    for i in 0..amount {
        let j: usize = rng.gen_range(i, length);

        // equiv: let tmp = slice[i];
        let tmp = match cache.get(&i) {
            Some(e) => *e,
            None => i,
        };

        // equiv: slice[i] = slice[j];
        let x = match cache.get(&j) {
            Some(x) => *x,
            None => j,
        };

        // equiv: slice[j] = tmp;
        cache.insert(j, tmp);

        // note that in the inplace version, slice[i] is automatically "returned" value
        out.push(x);
    }
    debug_assert_eq!(out.len(), amount);
    out
}

/// Return a random element from `items` where the chance of a given item
/// being picked is proportional to the corresponding value in `weights`.
/// `weights` and `items` must return exactly the same number of values.
///
/// All values returned by `weights` must be `>= 0`.
///
/// This function iterates over `weights` twice. Once to get the total
/// weight, and once while choosing the random value. If you know the total
/// weight, or plan to call this function multiple times, you should
/// consider using [`choose_weighted_with_total`] instead.
///
/// Return `None` if `items` and `weights` is empty.
///
/// # Panics
///
/// If a value in `weights < 0`.
/// If `weights` and `items` return different number of items.
///
/// # Example
///
/// ```
/// use rand::thread_rng;
/// use rand::seq::choose_weighted;
///
/// let choices = ['a', 'b', 'c'];
/// let weights = [2,   1,   1];
/// let mut rng = thread_rng();
/// // 50% chance to print 'a', 25% chance to print 'b', 25% chance to print 'c'
/// println!("{}", choose_weighted(&mut rng, choices.iter(), weights.iter().cloned()).unwrap());
/// ```
/// [`choose_weighted_with_total`]: seq/fn.choose_weighted_with_total.html
pub fn choose_weighted<R, IterItems, IterWeights>(rng: &mut R,
                                                  items: IterItems,
                                                  weights: IterWeights) -> Option<IterItems::Item>
    where R: Rng + ?Sized,
          IterItems: Iterator,
          IterWeights: Iterator + Clone,
          IterWeights::Item: SampleUniform +
                             Default +
                             ::core::ops::Add<IterWeights::Item, Output=IterWeights::Item> +
                             ::core::cmp::PartialOrd<IterWeights::Item> +
                             Clone { // Clone is only needed for debug assertions
    let total_weight: IterWeights::Item =
        weights.clone().fold(Default::default(), |acc, w| {
            assert!(w >= Default::default(), "Weight must be larger than zero");
            acc + w
        });
    choose_weighted_with_total(rng, items, weights, total_weight)
}

/// Return a random element from `items` where. The chance of a given item
/// being picked, is proportional to the corresponding value in `weights`.
/// `weights` and `items` must return exactly the same number of values.
///
/// All values returned by `weights` must be `>= 0`.
///
/// `total_weight` must be exactly the sum of all values returned by
/// `weights`. Builds with debug_assertions turned on will assert that this
/// equality holds. Simply storing the result of `weights.sum()` and using
/// that as `total_weight` should work.
///
/// Return `None` if `items` and `weights` is empty.
///
/// # Example
///
/// ```
/// use rand::thread_rng;
/// use rand::seq::choose_weighted_with_total;
///
/// let choices = ['a', 'b', 'c'];
/// let weights = [2,   1,   1];
/// let mut rng = thread_rng();
/// // 50% chance to print 'a', 25% chance to print 'b', 25% chance to print 'c'
/// println!("{}", choose_weighted_with_total(&mut rng, choices.iter(), weights.iter().cloned(), 4).unwrap());
/// ```
pub fn choose_weighted_with_total<R, IterItems, IterWeights>(rng: &mut R,
                                                             mut items: IterItems,
                                                             mut weights: IterWeights,
                                                             total_weight: IterWeights::Item) -> Option<IterItems::Item>
    where R: Rng + ?Sized,
          IterItems: Iterator,
          IterWeights: Iterator,
          IterWeights::Item: SampleUniform +
                             Default +
                             ::core::ops::Add<IterWeights::Item, Output=IterWeights::Item> +
                             ::core::cmp::PartialOrd<IterWeights::Item> +
                             Clone { // Clone is only needed for debug assertions

    if total_weight == Default::default() {
        debug_assert!(items.next().is_none());
        return None;
    }

    // Only used when debug_assertions are turned on
    let mut debug_result = None;
    let debug_total_weight = if cfg!(debug_assertions) { Some(total_weight.clone()) } else { None };

    let chosen_weight = rng.gen_range(Default::default(), total_weight);
    let mut cumulative_weight: IterWeights::Item = Default::default();

    for item in items {
        let weight_opt = weights.next();
        assert!(weight_opt.is_some(), "`weights` returned fewer items than `items` did");
        let weight = weight_opt.unwrap();
        assert!(weight >= Default::default(), "Weight must be larger than zero");

        cumulative_weight = cumulative_weight + weight;

        if cumulative_weight > chosen_weight {
            if !cfg!(debug_assertions) {
                return Some(item);
            }
            if debug_result.is_none() {
                debug_result = Some(item);
            }
        }
    }

    assert!(weights.next().is_none(), "`weights` returned more items than `items` did");
    debug_assert!(debug_total_weight.unwrap() == cumulative_weight);
    if cfg!(debug_assertions) && debug_result.is_some() {
      return debug_result;
    }

    panic!("total_weight did not match up with sum of weights");
}

#[cfg(test)]
mod test {
    use super::*;
    use super::IteratorRandom;
    #[cfg(feature = "alloc")]
    use {XorShiftRng, Rng, SeedableRng};
    #[cfg(all(feature="alloc", not(feature="std")))]
    use alloc::Vec;
    #[cfg(feature="std")]
    use core::panic::catch_unwind;

    #[test]
    fn test_choose() {
        let mut r = ::test::rng(107);
        assert_eq!([1, 1, 1].choose(&mut r), Some(&1));
        
        let mut v = [2];
        v.choose_mut(&mut r).map(|x| *x = 5);
        assert_eq!(v[0], 5);

        let v = [3, 3, 3, 3];
        assert_eq!(v.iter().choose(&mut r), Some(&3));

        let v: &[isize] = &[];
        assert_eq!(v.choose(&mut r), None);
    }

    #[test]
    fn test_shuffle() {
        let mut r = ::test::rng(108);
        let empty: &mut [isize] = &mut [];
        empty.shuffle(&mut r);
        let mut one = [1];
        one.shuffle(&mut r);
        let b: &[_] = &[1];
        assert_eq!(one, b);

        let mut two = [1, 2];
        two.shuffle(&mut r);
        assert!(two == [1, 2] || two == [2, 1]);

        let mut x = [1, 1, 1];
        x.shuffle(&mut r);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(x, b);
    }
    
    #[test]
    fn test_partial_shuffle() {
        let mut r = ::test::rng(118);
        
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

        let mut r = ::test::rng(401);
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample = vals.iter().sample(&mut r, 5);
        let large_sample = vals.iter().sample(&mut r, vals.len() + 5);

        assert_eq!(small_sample.len(), 5);
        assert_eq!(large_sample.len(), vals.len());
        // no randomization happens when amount >= len
        assert_eq!(large_sample, vals.iter().collect::<Vec<_>>());

        assert!(small_sample.iter().all(|e| {
            **e >= min_val && **e <= max_val
        }));
    }
    #[test]
    #[cfg(feature = "alloc")]
    #[allow(deprecated)]
    fn test_sample_slice_boundaries() {
        let empty: &[u8] = &[];

        let mut r = ::test::rng(402);

        // sample 0 items
        assert_eq!(&sample_slice(&mut r, empty, 0)[..], [0u8; 0]);
        assert_eq!(&sample_slice(&mut r, &[42, 2, 42], 0)[..], [0u8; 0]);

        // sample 1 item
        assert_eq!(&sample_slice(&mut r, &[42], 1)[..], [42]);
        let v = sample_slice(&mut r, &[1, 42], 1)[0];
        assert!(v == 1 || v == 42);

        // sample "all" the items
        let v = sample_slice(&mut r, &[42, 133], 2);
        assert!(&v[..] == [42, 133] || v[..] == [133, 42]);

        assert_eq!(&sample_indices_inplace(&mut r, 0, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_inplace(&mut r, 1, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_inplace(&mut r, 1, 1)[..], [0]);

        assert_eq!(&sample_indices_cache(&mut r, 0, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_cache(&mut r, 1, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_cache(&mut r, 1, 1)[..], [0]);

        // Make sure lucky 777's aren't lucky
        let slice = &[42, 777];
        let mut num_42 = 0;
        let total = 1000;
        for _ in 0..total {
            let v = sample_slice(&mut r, slice, 1);
            assert_eq!(v.len(), 1);
            let v = v[0];
            assert!(v == 42 || v == 777);
            if v == 42 {
                num_42 += 1;
            }
        }
        let ratio_42 = num_42 as f64 / 1000 as f64;
        assert!(0.4 <= ratio_42 || ratio_42 <= 0.6, "{}", ratio_42);
    }

    #[test]
    #[cfg(feature = "alloc")]
    #[allow(deprecated)]
    fn test_sample_slice() {
        let xor_rng = XorShiftRng::from_seed;

        let max_range = 100;
        let mut r = ::test::rng(403);

        for length in 1usize..max_range {
            let amount = r.gen_range(0, length);
            let mut seed = [0u8; 16];
            r.fill(&mut seed);

            // assert that the two index methods give exactly the same result
            let inplace = sample_indices_inplace(
                &mut xor_rng(seed), length, amount);
            let cache = sample_indices_cache(
                &mut xor_rng(seed), length, amount);
            assert_eq!(inplace, cache);

            // assert the basics work
            let regular = sample_indices(
                &mut xor_rng(seed), length, amount);
            assert_eq!(regular.len(), amount);
            assert!(regular.iter().all(|e| *e < length));
            assert_eq!(regular, inplace);

            // also test that sampling the slice works
            let vec: Vec<usize> = (0..length).collect();
            {
                let result = sample_slice(&mut xor_rng(seed), &vec, amount);
                assert_eq!(result, regular);
            }

            {
                let result = sample_slice_ref(&mut xor_rng(seed), &vec, amount);
                let expected = regular.iter().map(|v| v).collect::<Vec<_>>();
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_choose_weighted() {
        let mut r = ::test::rng(406);
        let chars = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n'];
        let weights = [1u32, 2, 3, 0, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7];
        let total_weight = weights.iter().sum();
        assert_eq!(chars.len(), weights.len());

        let mut chosen = [0i32; 14];
        for _ in 0..1000 {
            let picked = *choose_weighted(&mut r,
                                          chars.iter(),
                                          weights.iter().cloned()).unwrap();
            chosen[(picked as usize) - ('a' as usize)] += 1;
        }
        for (i, count) in chosen.iter().enumerate() {
            let err = *count - ((weights[i] * 1000 / total_weight) as i32);
            assert!(-25 <= err && err <= 25);
        }

        // Mutable items
        chosen.iter_mut().for_each(|x| *x = 0);
        for _ in 0..1000 {
            *choose_weighted(&mut r,
                             chosen.iter_mut(),
                             weights.iter().cloned()).unwrap() += 1;
        }
        for (i, count) in chosen.iter().enumerate() {
            let err = *count - ((weights[i] * 1000 / total_weight) as i32);
            assert!(-25 <= err && err <= 25);
        }

        // choose_weighted_with_total
        chosen.iter_mut().for_each(|x| *x = 0);
        for _ in 0..1000 {
            let picked = *choose_weighted_with_total(&mut r,
                                                     chars.iter(),
                                                     weights.iter().cloned(),
                                                     total_weight).unwrap();
            chosen[(picked as usize) - ('a' as usize)] += 1;
        }
        for (i, count) in chosen.iter().enumerate() {
            let err = *count - ((weights[i] * 1000 / total_weight) as i32);
            assert!(-25 <= err && err <= 25);
        }
    }

    #[test]
    #[cfg(all(feature="std",
              not(target_arch = "wasm32"),
              not(target_arch = "asmjs")))]
    fn test_choose_weighted_assertions() {
        fn inner_delta(delta: i32) {
            let items = vec![1, 2, 3];
            let mut r = ::test::rng(407);
            if cfg!(debug_assertions) || delta == 0 {
                choose_weighted_with_total(&mut r,
                                           items.iter(),
                                           items.iter().cloned(),
                                           6+delta);
            } else {
                loop {
                    choose_weighted_with_total(&mut r,
                                               items.iter(),
                                               items.iter().cloned(),
                                               6+delta);
                }
            }
        }

        assert!(catch_unwind(|| inner_delta(0)).is_ok());
        assert!(catch_unwind(|| inner_delta(1)).is_err());
        assert!(catch_unwind(|| inner_delta(1000)).is_err());
        if cfg!(debug_assertions) {
            // The non-debug-assertions code can't detect too small total_weight
            assert!(catch_unwind(|| inner_delta(-1)).is_err());
            assert!(catch_unwind(|| inner_delta(-1000)).is_err());
        }

        fn inner_size(items: usize, weights: usize, with_total: bool) {
            let mut r = ::test::rng(408);
            if with_total {
                choose_weighted_with_total(&mut r,
                                           ::core::iter::repeat(1usize).take(items),
                                           ::core::iter::repeat(1usize).take(weights),
                                           weights);
            } else {
                choose_weighted(&mut r,
                                ::core::iter::repeat(1usize).take(items),
                                ::core::iter::repeat(1usize).take(weights));
            }
        }

        assert!(catch_unwind(|| inner_size(2, 2, true)).is_ok());
        assert!(catch_unwind(|| inner_size(2, 2, false)).is_ok());
        assert!(catch_unwind(|| inner_size(2, 1, true)).is_err());
        assert!(catch_unwind(|| inner_size(2, 1, false)).is_err());
        if cfg!(debug_assertions) {
            // The non-debug-assertions code can't detect too many weights
            assert!(catch_unwind(|| inner_size(2, 3, true)).is_err());
            assert!(catch_unwind(|| inner_size(2, 3, false)).is_err());
        }
    }
}
