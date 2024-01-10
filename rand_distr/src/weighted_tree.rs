// Copyright 2024 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module contains an implementation of a tree sttructure for sampling random
//! indices with probabilities proportional to a collection of weights.

use core::ops::{Add, AddAssign, Sub, SubAssign};

use super::WeightedError;
use crate::Distribution;
use alloc::{vec, vec::Vec};
use num_traits::Zero;
use rand::{distributions::uniform::SampleUniform, Rng};
#[cfg(feature = "serde1")]
use serde::{Deserialize, Serialize};

/// A distribution using weighted sampling to pick a discretely selected item.
///
/// Sampling a [`WeightedTreeIndex<W>`] distribution returns the index of a randomly
/// selected element from the vector used to create the [`WeightedTreeIndex<W>`].
/// The chance of a given element being picked is proportional to the value of
/// the element. The weights can have any type `W` for which a implementation of
/// [`Weight`] exists.
///
/// # Key differences
///
/// The main distinction between [`WeightedTreeIndex<W>`] and [`rand::distributions::WeightedIndex<W>`]
/// lies in the internal representation of weights. In [`WeightedTreeIndex<W>`],
/// weights are structured as a tree, which is optimized for frequent updates of the weights.
///
/// # Performance
///
/// A [`WeightedTreeIndex<W>`] with `n` elements requires `O(n)` memory.
///
/// Time complexity for the operations of a [`WeightedTreeIndex<W>`] are:
/// * Constructing: Building the initial tree from a slice of weights takes `O(n)` time.
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
/// let weights = vec![2, 1, 1];
/// let dist = WeightedTreeIndex::new(&weights).unwrap();
/// let mut rng = thread_rng();
/// for _ in 0..100 {
///     // 50% chance to print 'a', 25% chance to print 'b', 25% chance to print 'c'
///     let i = dist.sample(&mut rng).unwrap();
///     println!("{}", choices[i]);
/// }
/// ```
///
/// [`WeightedTreeIndex<W>`]: WeightedTreeIndex
/// [`Uniform<W>::sample`]: Distribution::sample
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
pub struct WeightedTreeIndex<W: Weight> {
    subtotals: Vec<W>,
}

impl<W: Weight> WeightedTreeIndex<W> {
    /// Creates a new [`WeightedTreeIndex`] from a slice of weights.
    pub fn new(weights: &[W]) -> Result<Self, WeightedError> {
        for &weight in weights {
            if weight < W::zero() {
                return Err(WeightedError::InvalidWeight);
            }
        }
        let n = weights.len();
        let mut subtotals = vec![W::zero(); n];
        for i in (0..n).rev() {
            let left_index = 2 * i + 1;
            let left_subtotal = if left_index < n {
                subtotals[left_index]
            } else {
                W::zero()
            };
            let right_index = 2 * i + 2;
            let right_subtotal = if right_index < n {
                subtotals[right_index]
            } else {
                W::zero()
            };
            subtotals[i] = weights[i] + left_subtotal + right_subtotal;
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
    pub fn can_sample(&self) -> bool {
        self.subtotals.first().is_some_and(|x| *x > W::zero())
    }

    /// Gets the weight at an index.
    pub fn get(&self, index: usize) -> W {
        let left_index = 2 * index + 1;
        let right_index = 2 * index + 2;
        self.subtotals[index] - self.subtotal(left_index) - self.subtotal(right_index)
    }

    /// Removes the last weight and returns it, or [`None`] if it is empty.
    pub fn pop(&mut self) -> Option<W> {
        self.subtotals.pop().map(|weight| {
            let mut index = self.len();
            while index != 0 {
                index = (index - 1) / 2;
                self.subtotals[index] -= weight;
            }
            weight
        })
    }

    /// Appends a new weight at the end.
    pub fn push(&mut self, weight: W) -> Result<(), WeightedError> {
        if weight < W::zero() {
            return Err(WeightedError::InvalidWeight);
        }
        let mut index = self.len();
        self.subtotals.push(weight);
        while index != 0 {
            index = (index - 1) / 2;
            self.subtotals[index] += weight;
        }
        Ok(())
    }

    /// Updates the weight at an index.
    pub fn update(&mut self, mut index: usize, weight: W) -> Result<(), WeightedError> {
        if weight < W::zero() {
            return Err(WeightedError::InvalidWeight);
        }
        let difference = weight - self.get(index);
        if difference == W::zero() {
            return Ok(());
        }
        self.subtotals[index] += difference;
        while index != 0 {
            index = (index - 1) / 2;
            self.subtotals[index] += difference;
        }
        Ok(())
    }

    fn subtotal(&self, index: usize) -> W {
        if index < self.subtotals.len() {
            self.subtotals[index]
        } else {
            W::zero()
        }
    }
}

impl<W: Weight> Distribution<Result<usize, WeightedError>> for WeightedTreeIndex<W> {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Result<usize, WeightedError> {
        if self.subtotals.is_empty() {
            return Err(WeightedError::NoItem);
        }
        let total_weight = self.subtotals[0];
        if total_weight == W::zero() {
            return Err(WeightedError::AllWeightsZero);
        }
        let mut target_weight = rng.gen_range(W::zero()..total_weight);
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
        Ok(index)
    }
}

/// Trait that must be implemented for weights, that are used with
/// [`WeightedTreeIndex`]. Currently no guarantees on the correctness of
/// [`WeightedTreeIndex`] are given for custom implementations of this trait.
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
pub trait Weight:
    Sized
    + Copy
    + SampleUniform
    + PartialOrd
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Zero
{
}

impl<T> Weight for T where
    T: Sized
        + Copy
        + SampleUniform
        + PartialOrd
        + Add<Output = Self>
        + AddAssign
        + Sub<Output = Self>
        + SubAssign
        + Zero
{
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_no_item_error() {
        let mut rng = crate::test::rng(0x9c9fa0b0580a7031);
        let mut tree = WeightedTreeIndex::<f64>::new(&[]).unwrap();
        assert_eq!(tree.sample(&mut rng).unwrap_err(), WeightedError::NoItem);
    }

    #[test]
    fn test_all_weights_zero_error() {
        let tree = WeightedTreeIndex::<f64>::new(&[0.0, 0.0]).unwrap();
        let mut rng = crate::test::rng(0x9c9fa0b0580a7031);
        assert_eq!(
            tree.sample(&mut rng).unwrap_err(),
            WeightedError::AllWeightsZero
        );
    }

    #[test]
    fn test_invalid_weight_error() {
        assert_eq!(
            WeightedTreeIndex::<i32>::new(&[1, -1]).unwrap_err(),
            WeightedError::InvalidWeight
        );
        let mut tree = WeightedTreeIndex::<i32>::new(&[]).unwrap();
        assert_eq!(tree.push(-1).unwrap_err(), WeightedError::InvalidWeight);
        tree.push(1).unwrap();
        assert_eq!(
            tree.update(0, -1).unwrap_err(),
            WeightedError::InvalidWeight
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
        let mut weights = vec![0.0; end];
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
        let mut counts = vec![0_usize; end];
        for _ in 0..samples {
            let i = tree.sample(&mut rng).unwrap();
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
