// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
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
use ::{Error, ErrorKind};

// Note that this whole module is only imported if feature="alloc" is enabled.
#[cfg(not(feature="std"))] use alloc::vec::Vec;

/// A distribution using weighted sampling to pick a discretely selected item.
///
/// Sampling a `WeightedIndex` distribution returns the index of a randomly
/// selected element from the iterator used when the `WeightedIndex` was
/// created. The chance of a given element being picked is proportional to the
/// value of the element. The weights can use any type `X` for which an
/// implementation of [`Uniform<X>`] exists.
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
    /// [`Distribution`]: trait.Distribution.html
    /// [`Uniform<X>`]: struct.Uniform.html
    pub fn new<I>(weights: I) -> Result<WeightedIndex<X>, Error>
        where I: IntoIterator,
              I::Item: SampleBorrow<X>,
              X: for<'a> ::core::ops::AddAssign<&'a X> +
                 Clone +
                 Default {
        let mut iter = weights.into_iter();
        let mut total_weight: X = iter.next()
                                      .ok_or(Error::new(ErrorKind::Unexpected, "Empty iterator in WeightedIndex::new"))?
                                      .borrow()
                                      .clone();

        let zero = <X as Default>::default();
        if total_weight < zero {
            return Err(Error::new(ErrorKind::Unexpected, "Negative weight in WeightedIndex::new"));
        }

        let mut weights = Vec::<X>::with_capacity(iter.size_hint().0);
        for w in iter {
            if *w.borrow() < zero {
                return Err(Error::new(ErrorKind::Unexpected, "Negative weight in WeightedIndex::new"));
            }
            weights.push(total_weight.clone());
            total_weight += w.borrow();
        }

        if total_weight == zero {
            return Err(Error::new(ErrorKind::Unexpected, "Total weight is zero in WeightedIndex::new"));
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

        assert!(WeightedIndex::new(&[10][0..0]).is_err());
        assert!(WeightedIndex::new(&[0]).is_err());
        assert!(WeightedIndex::new(&[10, 20, -1, 30]).is_err());
        assert!(WeightedIndex::new(&[-10, 20, 1, 30]).is_err());
        assert!(WeightedIndex::new(&[-10]).is_err());
    }
}
