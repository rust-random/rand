// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functions for randomly accessing and sampling sequences.

use super::Rng;
use std::collections::hash_map::HashMap;

/// Randomly sample *up to* `amount` elements from a finite iterator.
///
/// The values are non-repeating but the order of elements returned is *not* random.
///
/// This implementation uses `O(len(iterable))` time and `O(amount)` memory.
///
/// > If `len(iterable) <= amount` then the values will be in sequential order. In all other
/// > cases the order of the elements is neither random nor guaranteed.
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let sample = seq::sample_iter(&mut rng, 1..100, 5);
/// println!("{:?}", sample);
/// ```
pub fn sample_iter<T, I, R>(rng: &mut R, iterable: I, amount: usize) -> Vec<T>
    where I: IntoIterator<Item=T>,
          R: Rng,
{
    let mut iter = iterable.into_iter();
    let mut reservoir = Vec::with_capacity(amount);
    reservoir.extend(iter.by_ref().take(amount));

    // continue unless the iterator was exhausted
    //
    // note: this prevents iterators that "restart" from causing problems.
    // If the iterator stops once, then so do we.
    if reservoir.len() == amount {
        for (i, elem) in iter.enumerate() {
            let k = rng.gen_range(0, i + 1 + amount);
            if let Some(spot) = reservoir.get_mut(k) {
                *spot = elem;
            }
        }
    } else {
        // Don't hang onto extra memory. There is a corner case where
        // `amount <<< len(iterable)` that we want to avoid.
        reservoir.shrink_to_fit();
    }
    reservoir
}

/// Randomly sample exactly `amount` values from `slice`.
///
/// The values are non-repeating and in random order.
///
/// This implementation uses `O(amount)` time and memory.
///
/// Panics if `amount > self.len()`
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let values = vec![5, 6, 1, 3, 4, 6, 7];
/// println!("{:?}", seq::sample_slice(&mut rng, &values, 3));
/// ```
pub fn sample_slice<R, T>(rng: &mut R, slice: &[T], amount: usize) -> Vec<T>
    where R: Rng,
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
/// Panics if `amount > self.len()`
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let values = vec![5, 6, 1, 3, 4, 6, 7];
/// println!("{:?}", seq::sample_slice_ref(&mut rng, &values, 3));
/// ```
pub fn sample_slice_ref<'a, R, T>(rng: &mut R, slice: &'a [T], amount: usize) -> Vec<&'a T>
    where R: Rng
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
/// Panics if `amount > self.len()`
pub fn sample_indices<R>(rng: &mut R, length: usize, amount: usize) -> Vec<usize>
    where R: Rng,
{
    if amount > length {
        panic!("`amount` must be less than or equal to `slice.len()`");
    }

    // We are going to have to allocate at least `amount` for the output no matter what. However,
    // if we use the `cached` version we will have to allocate `amount` as a HashMap as well since
    // it inserts an element for every loop.
    //
    // Therefore, if `amount >= length / 2` then inplace will be both faster and use less memory.
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
    let mut indices: Vec<usize> = Vec::with_capacity(length);
    indices.extend(0..length);
    let end_i = if length != 0 && amount == length {
        // It isn't necessary to shuffle the final element if we are shuffling
        // the whole array... it would just be shuffled with itself
        //
        // Also, `rng.gen_range(i, i)` panics.
        amount - 1
    } else {
        amount
    };
    for i in 0..end_i {
        let j: usize = rng.gen_range(i, length);
        let tmp = indices[i];
        indices[i] = indices[j];
        indices[j] = tmp;
    }
    indices.truncate(amount);
    debug_assert_eq!(indices.len(), amount);
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
    debug_assert_eq!(out.len(), amount);
    out
}

#[cfg(test)]
mod test {
    use super::*;
    use {thread_rng, XorShiftRng, SeedableRng};

    #[test]
    fn test_sample_iter() {
        let min_val = 1;
        let max_val = 100;

        let mut r = thread_rng();
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample = sample_iter(&mut r, vals.iter(), 5);
        let large_sample = sample_iter(&mut r, vals.iter(), vals.len() + 5);

        assert_eq!(small_sample.len(), 5);
        assert_eq!(large_sample.len(), vals.len());

        assert!(small_sample.iter().all(|e| {
            **e >= min_val && **e <= max_val
        }));
    }
    #[test]
    fn test_sample_slice_boundaries() {
        let empty: &[u8] = &[];

        let mut r = thread_rng();

        // sample 0 items
        assert_eq!(sample_slice(&mut r, empty, 0), vec![]);
        assert_eq!(sample_slice(&mut r, &[42, 2, 42], 0), vec![]);

        // sample 1 item
        assert_eq!(sample_slice(&mut r, &[42], 1), vec![42]);
        let v = sample_slice(&mut r, &[1, 42], 1)[0];
        assert!(v == 1 || v == 42);

        // sample "all" the items
        let v = sample_slice(&mut r, &[42, 133], 2);
        assert!(v == vec![42, 133] || v == vec![133, 42]);
    }

    #[test]
    fn test_sample_slice() {
        let xor_rng = XorShiftRng::from_seed;

        let max_range = 100;
        let mut r = thread_rng();

        for length in 1usize..max_range {
            let amount = r.gen_range(0, length);
            let seed: [u32; 4] = [
                r.next_u32(), r.next_u32(), r.next_u32(), r.next_u32()
            ];

            println!("Selecting indices: len={}, amount={}, seed={:?}", length, amount, seed);

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
}
