// Copyright 2024 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module contains an implementation of a tree structure for sampling random
//! indices with probabilities proportional to a collection of weights.

use core::ops::SubAssign;

use super::WeightError;
use crate::Distribution;
use alloc::vec::Vec;
use rand::distributions::uniform::{SampleBorrow, SampleUniform};
use rand::distributions::Weight;
use rand::Rng;
#[cfg(feature = "serde1")]
use serde::{Deserialize, Serialize};

/// A distribution using weighted sampling to pick a discretely selected item.
///
/// Sampling a [`WeightedTreeIndex<W>`] distribution returns the index of a randomly
/// selected element from the vector used to create the [`WeightedTreeIndex<W>`].
/// The chance of a given element being picked is proportional to the value of
/// the element. The weights can have any type `W` for which an implementation of
/// [`Weight`] exists.
///
/// # Key differences
///
/// The main distinction between [`WeightedTreeIndex<W>`] and [`rand::distributions::WeightedIndex<W>`]
/// lies in the internal representation of weights. In [`WeightedTreeIndex<W>`],
/// weights are structured as a tree, which is optimized for frequent updates of the weights.
///
/// # Caution: Floating point types
///
/// When utilizing [`WeightedTreeIndex<W>`] with floating point types (such as f32 or f64),
/// exercise caution due to the inherent nature of floating point arithmetic. Floating point types
/// are susceptible to numerical rounding errors. Since operations on floating point weights are
/// repeated numerous times, rounding errors can accumulate, potentially leading to noticeable
/// deviations from the expected behavior.
///
/// Ideally, use fixed point or integer types whenever possible.
///
/// # Performance
///
/// A [`WeightedTreeIndex<W>`] with `n` elements requires `O(n)` memory.
///
/// Time complexity for the operations of a [`WeightedTreeIndex<W>`] are:
/// * Constructing: Building the initial tree from an iterator of weights takes `O(n)` time.
/// * Sampling: Choosing an index (traversing down the tree) requires `O(log n)` time.
/// * Weight Update: Modifying a weight (traversing up the tree), requires `O(log n)` time.
/// * Weight Addition (Pushing): Adding a new weight (traversing up the tree), requires `O(log n)` time.
/// * Weight Removal (Popping): Removing a weight (traversing up the tree), requires `O(log n)` time.
///
/// # Example
///
/// ```
/// use rand_distr::WeightedTreeIndex;
/// use rand::prelude::*;
///
/// let choices = vec!['a', 'b', 'c'];
/// let weights = vec![2, 0];
/// let mut dist = WeightedTreeIndex::new(&weights).unwrap();
/// dist.push(1).unwrap();
/// dist.update(1, 1).unwrap();
/// let mut rng = thread_rng();
/// let mut samples = [0; 3];
/// for _ in 0..100 {
///     // 50% chance to print 'a', 25% chance to print 'b', 25% chance to print 'c'
///     let i = dist.sample(&mut rng);
///     samples[i] += 1;
/// }
/// println!("Results: {:?}", choices.iter().zip(samples.iter()).collect::<Vec<_>>());
/// ```
///
/// [`WeightedTreeIndex<W>`]: WeightedTreeIndex
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
#[cfg_attr(
    feature = "serde1",
    serde(bound(serialize = "W: Serialize, W::Sampler: Serialize"))
)]
#[cfg_attr(
    feature = "serde1 ",
    serde(bound(deserialize = "W: Deserialize<'de>, W::Sampler: Deserialize<'de>"))
)]
#[derive(Clone, Default, Debug, PartialEq)]
pub struct WeightedTreeIndex<
    W: Clone + PartialEq + PartialOrd + SampleUniform + SubAssign<W> + Weight,
> {
    subtotals: Vec<W>,
}

impl<W: Clone + PartialEq + PartialOrd + SampleUniform + SubAssign<W> + Weight>
    WeightedTreeIndex<W>
{
    /// Creates a new [`WeightedTreeIndex`] from a slice of weights.
    ///
    /// Error cases:
    /// -   [`WeightError::InvalidWeight`] when a weight is not-a-number or negative.
    /// -   [`WeightError::Overflow`] when the sum of all weights overflows.
    pub fn new<I>(weights: I) -> Result<Self, WeightError>
    where
        I: IntoIterator,
        I::Item: SampleBorrow<W>,
    {
        let mut subtotals: Vec<W> = weights.into_iter().map(|x| x.borrow().clone()).collect();
        for weight in subtotals.iter() {
            if !(*weight >= W::ZERO) {
                return Err(WeightError::InvalidWeight);
            }
        }
        let n = subtotals.len();
        for i in (1..n).rev() {
            let w = subtotals[i].clone();
            let parent = (i - 1) / 2;
            subtotals[parent]
                .checked_add_assign(&w)
                .map_err(|()| WeightError::Overflow)?;
        }
        Ok(Self { subtotals })
    }

    /// Returns `true` if the tree contains no weights.
    pub fn is_empty(&self) -> bool {
        self.subtotals.is_empty()
    }

    /// Returns the number of weights.
    pub fn len(&self) -> usize {
        self.subtotals.len()
    }

    /// Returns `true` if we can sample.
    ///
    /// This is the case if the total weight of the tree is greater than zero.
    pub fn is_valid(&self) -> bool {
        if let Some(weight) = self.subtotals.first() {
            *weight > W::ZERO
        } else {
            false
        }
    }

    /// Gets the weight at an index.
    pub fn get(&self, index: usize) -> W {
        let left_index = 2 * index + 1;
        let right_index = 2 * index + 2;
        let mut w = self.subtotals[index].clone();
        w -= self.subtotal(left_index);
        w -= self.subtotal(right_index);
        w
    }

    /// Removes the last weight and returns it, or [`None`] if it is empty.
    pub fn pop(&mut self) -> Option<W> {
        self.subtotals.pop().map(|weight| {
            let mut index = self.len();
            while index != 0 {
                index = (index - 1) / 2;
                self.subtotals[index] -= weight.clone();
            }
            weight
        })
    }

    /// Appends a new weight at the end.
    ///
    /// Error cases:
    /// -   [`WeightError::InvalidWeight`] when a weight is not-a-number or negative.
    /// -   [`WeightError::Overflow`] when the sum of all weights overflows.
    pub fn push(&mut self, weight: W) -> Result<(), WeightError> {
        if !(weight >= W::ZERO) {
            return Err(WeightError::InvalidWeight);
        }
        if let Some(total) = self.subtotals.first() {
            let mut total = total.clone();
            if total.checked_add_assign(&weight).is_err() {
                return Err(WeightError::Overflow);
            }
        }
        let mut index = self.len();
        self.subtotals.push(weight.clone());
        while index != 0 {
            index = (index - 1) / 2;
            self.subtotals[index].checked_add_assign(&weight).unwrap();
        }
        Ok(())
    }

    /// Updates the weight at an index.
    ///
    /// Error cases:
    /// -   [`WeightError::InvalidWeight`] when a weight is not-a-number or negative.
    /// -   [`WeightError::Overflow`] when the sum of all weights overflows.
    pub fn update(&mut self, mut index: usize, weight: W) -> Result<(), WeightError> {
        if !(weight >= W::ZERO) {
            return Err(WeightError::InvalidWeight);
        }
        let old_weight = self.get(index);
        if weight > old_weight {
            let mut difference = weight;
            difference -= old_weight;
            if let Some(total) = self.subtotals.first() {
                let mut total = total.clone();
                if total.checked_add_assign(&difference).is_err() {
                    return Err(WeightError::Overflow);
                }
            }
            self.subtotals[index]
                .checked_add_assign(&difference)
                .unwrap();
            while index != 0 {
                index = (index - 1) / 2;
                self.subtotals[index]
                    .checked_add_assign(&difference)
                    .unwrap();
            }
        } else if weight < old_weight {
            let mut difference = old_weight;
            difference -= weight;
            self.subtotals[index] -= difference.clone();
            while index != 0 {
                index = (index - 1) / 2;
                self.subtotals[index] -= difference.clone();
            }
        }
        Ok(())
    }

    fn subtotal(&self, index: usize) -> W {
        if index < self.subtotals.len() {
            self.subtotals[index].clone()
        } else {
            W::ZERO
        }
    }
}

impl<W: Clone + PartialEq + PartialOrd + SampleUniform + SubAssign<W> + Weight>
    WeightedTreeIndex<W>
{
    /// Samples a randomly selected index from the weighted distribution.
    ///
    /// Returns an error if there are no elements or all weights are zero. This
    /// is unlike [`Distribution::sample`], which panics in those cases.
    pub fn try_sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Result<usize, WeightError> {
        let total_weight = self.subtotals.first().cloned().unwrap_or(W::ZERO);
        if total_weight == W::ZERO {
            return Err(WeightError::InsufficientNonZero);
        }
        let mut target_weight = rng.gen_range(W::ZERO..total_weight);
        let mut index = 0;
        loop {
            // Maybe descend into the left sub tree.
            let left_index = 2 * index + 1;
            let left_subtotal = self.subtotal(left_index);
            if target_weight < left_subtotal {
                index = left_index;
                continue;
            }
            target_weight -= left_subtotal;

            // Maybe descend into the right sub tree.
            let right_index = 2 * index + 2;
            let right_subtotal = self.subtotal(right_index);
            if target_weight < right_subtotal {
                index = right_index;
                continue;
            }
            target_weight -= right_subtotal;

            // Otherwise we found the index with the target weight.
            break;
        }
        assert!(target_weight >= W::ZERO);
        assert!(target_weight < self.get(index));
        Ok(index)
    }
}

/// Samples a randomly selected index from the weighted distribution.
///
/// Caution: This method panics if there are no elements or all weights are zero. However,
/// it is guaranteed that this method will not panic if a call to [`WeightedTreeIndex::is_valid`]
/// returns `true`.
impl<W: Clone + PartialEq + PartialOrd + SampleUniform + SubAssign<W> + Weight> Distribution<usize>
    for WeightedTreeIndex<W>
{
    #[track_caller]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        self.try_sample(rng).unwrap()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_no_item_error() {
        let mut rng = crate::test::rng(0x9c9fa0b0580a7031);
        let tree = WeightedTreeIndex::<f64>::new(&[]).unwrap();
        assert_eq!(
            tree.try_sample(&mut rng).unwrap_err(),
            WeightError::InsufficientNonZero
        );
    }

    #[test]
    fn test_overflow_error() {
        assert_eq!(
            WeightedTreeIndex::new(&[i32::MAX, 2]),
            Err(WeightError::Overflow)
        );
        let mut tree = WeightedTreeIndex::new(&[i32::MAX - 2, 1]).unwrap();
        assert_eq!(tree.push(3), Err(WeightError::Overflow));
        assert_eq!(tree.update(1, 4), Err(WeightError::Overflow));
        tree.update(1, 2).unwrap();
    }

    #[test]
    fn test_all_weights_zero_error() {
        let tree = WeightedTreeIndex::<f64>::new(&[0.0, 0.0]).unwrap();
        let mut rng = crate::test::rng(0x9c9fa0b0580a7031);
        assert_eq!(
            tree.try_sample(&mut rng).unwrap_err(),
            WeightError::InsufficientNonZero
        );
    }

    #[test]
    fn test_invalid_weight_error() {
        assert_eq!(
            WeightedTreeIndex::<i32>::new(&[1, -1]).unwrap_err(),
            WeightError::InvalidWeight
        );
        let mut tree = WeightedTreeIndex::<i32>::new(&[]).unwrap();
        assert_eq!(tree.push(-1).unwrap_err(), WeightError::InvalidWeight);
        tree.push(1).unwrap();
        assert_eq!(
            tree.update(0, -1).unwrap_err(),
            WeightError::InvalidWeight
        );
    }

    #[test]
    fn test_tree_modifications() {
        let mut tree = WeightedTreeIndex::new(&[9, 1, 2]).unwrap();
        tree.push(3).unwrap();
        tree.push(5).unwrap();
        tree.update(0, 0).unwrap();
        assert_eq!(tree.pop(), Some(5));
        let expected = WeightedTreeIndex::new(&[0, 1, 2, 3]).unwrap();
        assert_eq!(tree, expected);
    }

    #[test]
    fn test_sample_counts_match_probabilities() {
        let start = 1;
        let end = 3;
        let samples = 20;
        let mut rng = crate::test::rng(0x9c9fa0b0580a7031);
        let weights: Vec<_> = (0..end).map(|_| rng.gen()).collect();
        let mut tree = WeightedTreeIndex::new(&weights).unwrap();
        let mut total_weight = 0.0;
        let mut weights = alloc::vec![0.0; end];
        for i in 0..end {
            tree.update(i, i as f64).unwrap();
            weights[i] = i as f64;
            total_weight += i as f64;
        }
        for i in 0..start {
            tree.update(i, 0.0).unwrap();
            weights[i] = 0.0;
            total_weight -= i as f64;
        }
        let mut counts = alloc::vec![0_usize; end];
        for _ in 0..samples {
            let i = tree.sample(&mut rng);
            counts[i] += 1;
        }
        for i in 0..start {
            assert_eq!(counts[i], 0);
        }
        for i in start..end {
            let diff = counts[i] as f64 / samples as f64 - weights[i] / total_weight;
            assert!(diff.abs() < 0.05);
        }
    }
}
