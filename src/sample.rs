// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functions for sampling data

use super::Rng;
use std::collections::hash_map::HashMap;

/// The `Sample` trait provides the `sample` method.
///
/// This is intended to be implemented for containers that:
/// - Can be sampled in `O(amount)` time.
/// - Whos items can be `cloned`.
///
/// If cloning is impossible or expensive, use `sample_ref` instead.
pub trait Sample {
    /// The returned sampled data. Typically the either a `Vec<T>` or a new instance of the
    /// container's own type.
    type Sampled;

    /// Return exactly `amount` randomly sampled values.
    ///
    /// Any type which implements `sample` should guarantee that:
    /// - Both the order and values of `Sampled` is random.
    /// - The implementation uses `O(amount)` speed and memory
    /// - The returned values are not references (if so, implement `SampleRef` instead).
    ///
    /// Panics if `amount > self.len()`
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Sample};
    ///
    /// let mut rng = thread_rng();
    /// let values = vec![5, 6, 1, 3, 4, 6, 7];
    /// println!("{:?}", values.sample(&mut rng, 3))
    /// ```
    fn sample<R: Rng>(&self, rng: &mut R, amount: usize) -> Self::Sampled;
}

/// The `SampleRef` trait provides the `sample_ref` method.
///
/// This is intended to be implemented for containers that which can be sampled in `O(amount)` time
/// and want a fast way to give references to a sample of their items.
pub trait SampleRef {
    /// The returned sampled data. Typically the either a `Vec<&T>` or a new instance of the
    /// container's own type containing references to the underlying data.
    type SampledRef;

    /// Return exactly `amount` references to randomly sampled values.
    ///
    /// Any type which implements `sample_ref` should guarantee that:
    /// - Both the order and values of `SampledRef` is random.
    /// - The implementation uses `O(amount)` speed and memory.
    /// - The returned values are not copies/clones (if so, implement `Sample` instead).
    ///
    /// Panics if `amount > self.len()`
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, SampleRef};
    ///
    /// let mut rng = thread_rng();
    /// let values = vec![5, 6, 1, 3, 4, 6, 7];
    /// println!("{:?}", values.as_slice().sample_ref(&mut rng, 3))
    /// ```
    fn sample_ref<R: Rng>(&self, rng: &mut R, amount: usize) -> Self::SampledRef;
}

/// Randomly sample *up to* `amount` elements from a finite iterator using a reservoir.
///
/// The order of elements in the sample is not random. In fact, if `len(iterable) <= amount` then
/// the output will be in the exact order they were collected.
///
/// The reservoir method used allocates only an `Vec` of size `amount`. The size of the iterable
/// does not affect the amount of memory used.
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, sample_reservoir};
///
/// let mut rng = thread_rng();
/// let sample = sample_reservoir(&mut rng, 1..100, 5);
/// println!("{:?}", sample);
/// ```
pub fn sample_reservoir<T, I, R>(rng: &mut R, iterable: I, amount: usize) -> Vec<T>
    where I: IntoIterator<Item=T>,
          R: Rng,
{
    let mut iter = iterable.into_iter();
    let mut reservoir = Vec::with_capacity(amount);
    reservoir.extend(iter.by_ref().take(amount));

    // continue unless the iterator was exhausted
    if reservoir.len() == amount {
        for (i, elem) in iter.enumerate() {
            let k = rng.gen_range(0, i + 1 + amount);
            if let Some(spot) = reservoir.get_mut(k) {
                *spot = elem;
            }
        }
    }
    reservoir
}

/// Sample (non-repeating) exactly `amount` of indices from a sequence of the given `length`.
///
/// The returned elements and their order are random.
///
/// Panics if `amount > length`
///
/// TODO: IMO this should be made public since it can be generally useful, although
/// there might be a way to make the output type more generic/compact.
fn sample_indices<R>(rng: &mut R, length: usize, amount: usize) -> Vec<usize>
    where R: Rng,
{
    if amount > length {
        panic!("`amount` must be less than or equal to `slice.len()`");
    }

    // We are going to have to allocate at least `amount` for the output no matter what. However,
    // if we use the `cached` version we will have to allocate `amount` as a HashMap as well since
    // it inserts an element for every loop.
    //
    // Therefore, if amount >= length / 2, inplace will be both faster and use less memory.
    //
    // TODO: there is probably even more fine-tuning that can be done here since
    // `HashMap::with_capacity(amount)` probably allocates more than `amount` in practice,
    // and a trade off could probably be made between memory/cpu, since hashmap operations
    // are slower than array index swapping.
    if amount >= length / 2 {
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
/// This is better than using a HashMap "cache" when `amount >= length / 2` since it does not
/// require allocating an extra cache and is much faster.
fn sample_indices_inplace<R>(rng: &mut R, length: usize, amount: usize) -> Vec<usize>
    where R: Rng,
{
    debug_assert!(amount <= length);
    let amount = if amount == length {
        // It isn't necessary to shuffle the final element if we are shuffling
        // the whole array... it would just be shuffled with itself
        amount - 1
    } else {
        amount
    };

    let mut indices: Vec<usize> = Vec::with_capacity(length);
    indices.extend(0..length);
    for i in 0..amount {
        let j: usize = rng.gen_range(i, length);
        let tmp = indices[i];
        indices[i] = indices[j];
        indices[j] = tmp;
    }
    indices.truncate(amount);
    indices
}


/// This method performs a partial fisher-yates on a range of indices using a HashMap
/// as a cache to record potential collisions.
///
/// The cache avoids allocating the entire `length` of values. This is especially useful when
/// `amount <<< length`, i.e. select 3 non-repeating from 1_000_000
fn sample_indices_cache<R>(
    rng: &mut R,
    length: usize,
    amount: usize,
) -> Vec<usize>
    where R: Rng,
{
    debug_assert!(amount <= length);
    let mut cache = HashMap::with_capacity(amount);
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
    out
}

impl<'a, T: Clone> Sample for &'a [T] {
    type Sampled = Vec<T>;

    fn sample<R: Rng>(&self, rng: &mut R, amount: usize) -> Vec<T> {
        let indices = sample_indices(rng, self.len(), amount);

        let mut out = Vec::with_capacity(amount);
        out.extend(indices.iter().map(|i| self[*i].clone()));
        out
    }
}

impl<'a, T: Clone> Sample for Vec<T> {
    type Sampled = Vec<T>;

    fn sample<R: Rng>(&self, rng: &mut R, amount: usize) -> Vec<T> {
        self.as_slice().sample(rng, amount)
    }
}

impl<'a, T> SampleRef for &'a [T] {
    type SampledRef = Vec<&'a T>;

    fn sample_ref<R: Rng>(&self, rng: &mut R, amount: usize) -> Vec<&'a T> {
        let indices = sample_indices(rng, self.len(), amount);

        let mut out = Vec::with_capacity(amount);
        out.extend(indices.iter().map(|i| &self[*i]));
        out
    }
}

// TODO: It looks like implementing this depends on RFC 1598 being implemented.
// See this: https://github.com/rust-lang/rfcs/issues/1965
//
// impl<'a, T> SampleRef for Vec<&'a T>{
//     type SampledRef = Vec<&'a T>;
//
//     fn sample_ref<R: Rng>(&'a self, rng: &mut R, amount: usize) -> Vec<&'a T> {
//        self.as_slice().sample_ref(rng, amount)
//     }
// }

#[cfg(test)]
mod test {
    use super::*;
    use {thread_rng, XorShiftRng, SeedableRng};

    #[test]
    fn test_sample_reservoir() {
        let min_val = 1;
        let max_val = 100;

        let mut r = thread_rng();
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample = sample_reservoir(&mut r, vals.iter(), 5);
        let large_sample = sample_reservoir(&mut r, vals.iter(), vals.len() + 5);

        assert_eq!(small_sample.len(), 5);
        assert_eq!(large_sample.len(), vals.len());

        assert!(small_sample.iter().all(|e| {
            **e >= min_val && **e <= max_val
        }));
    }

    #[test]
    /// This test mainly works by asserting that the two cases are equivalent,
    /// as well as equivalent to the exported function.
    fn test_sample_indices() {
        let xor_rng = XorShiftRng::from_seed;

        let max_range = 100;
        let mut r = thread_rng();

        for length in 1usize..max_range {
            let amount = r.gen_range(0, length);
            let seed: [u32; 4] = [
                r.next_u32(), r.next_u32(), r.next_u32(), r.next_u32()
            ];

            println!("Selecting indices: len={}, amount={}, seed={:?}", length, amount, seed);

            // assert that the two methods give exactly the same result
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

            // just for fun, also test sampling from a vector
            let vec: Vec<usize> = (0..length).collect();
            {
                let result = vec.sample(&mut xor_rng(seed), amount);
                assert_eq!(result, regular);
            }

            {
                let result = vec.as_slice().sample_ref(&mut xor_rng(seed), amount);
                let expected = regular.iter().map(|v| v).collect::<Vec<_>>();
                assert_eq!(result, expected);
            }
        }
    }
}
