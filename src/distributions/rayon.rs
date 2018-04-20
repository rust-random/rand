// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Parallel iterator to sample from distributions.

use {Rng, SeedableRng};
use distributions::Distribution;

use rayon::iter::plumbing::{Consumer, Producer, ProducerCallback, UnindexedConsumer, bridge};
use rayon::iter::{ParallelIterator, IndexedParallelIterator};


/// An iterator that generates random values of `T` with distribution `D`,
/// using `R` as the source of randomness.
///
/// This `struct` is created by the [`par_sample_iter`] method on
/// [`Distribution`]. See its documentation for more.
///
/// [`Distribution`]: trait.Distribution.html
/// [`sample_iter`]: trait.Distribution.html#method.sample_iter
#[cfg(feature = "rayon")]
#[derive(Debug)]
pub struct ParallelDistIter<'a, D: 'a, R, T> {
    distr: &'a D,
    rng: R,
    amount: usize,
    phantom: ::core::marker::PhantomData<T>,
}

impl<'a, D, R, T> ParallelDistIter<'a, D, R, T> {
    pub fn new(distr: &'a D, rng: &mut R, amount: usize)
        -> ParallelDistIter<'a, D, R, T>
        where D: Distribution<T>,
              R: Rng + SeedableRng,
    {
        ParallelDistIter {
            distr,
            rng: R::from_rng(rng).unwrap(),
            amount,
            phantom: ::core::marker::PhantomData,
        }
    }
}

#[cfg(feature = "rayon")]
impl<'a, D, R, T> ParallelIterator for ParallelDistIter<'a, D, R, T>
    where D: Distribution<T> + Send + Sync,
          R: Rng + SeedableRng + Send,
          T: Send,
{
    type Item = T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
        where C: UnindexedConsumer<Self::Item>
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.amount)
    }
}

#[cfg(feature = "rayon")]
impl<'a, D, R, T> IndexedParallelIterator for ParallelDistIter<'a, D, R, T>
    where D: Distribution<T> + Send + Sync,
          R: Rng + SeedableRng + Send,
          T: Send,
{
    fn drive<C>(self, consumer: C) -> C::Result
        where C: Consumer<Self::Item>
    {
        bridge(self, consumer)
    }

    fn len(&self) -> usize {
        self.amount
    }

    fn with_producer<CB>(self, callback: CB) -> CB::Output
        where CB: ProducerCallback<Self::Item>
    {
        callback.callback(
            DistProducer {
                distr: self.distr.clone(),
                amount: self.amount,
                rng: self.rng,
                phantom: ::core::marker::PhantomData,
            }
        )
    }
}

/// FIXME
#[cfg(feature = "rayon")]
#[derive(Debug)]
pub struct DistProducer<'a, D: 'a, R, T> {
    distr: &'a D,
    rng: R,
    amount: usize,
    phantom: ::core::marker::PhantomData<T>,
}

/// This method is intented to be used by fast and relatively simple PRNGs used
/// for simulations etc. While it will also work with cryptographic RNGs, that
/// is not optimal.
///
/// Every time `rayon` splits the work in two to create parallel tasks, one new
/// PRNG is created. The original PRNG is used to seed the new one using
/// `SeedableRng::from_rng`. **Important**: Not all RNG algorithms support this!
/// Notably the low-quality plain Xorshift, the current default for `SmallRng`,
/// will simply clone itself using this method instead of seeding the split off
/// RNG well. Consider using something like PCG or Xoroshiro128+.
///
/// It is hard to predict what will happen to the statistical quality of PRNGs
/// when they are split off many times, and only very short runs are used. We
/// limit the minimum number of items that should be used of the PRNG to at
/// least 100 to hopefully keep similar statistical properties as one PRNG used
/// continuously.
#[cfg(feature = "rayon")]
impl<'a, D, R, T> Producer for DistProducer<'a, D, R, T>
    where D: Distribution<T> + Send + Sync,
          R: Rng + SeedableRng + Send,
          T: Send,
{
    type Item = T;
    type IntoIter = BoundedDistIter<'a, D, R, T>;
    fn into_iter(self) -> Self::IntoIter {
        BoundedDistIter {
            distr: self.distr,
            amount: self.amount,
            rng: self.rng,
            phantom: ::core::marker::PhantomData,
        }
    }

    fn split_at(mut self, index: usize) -> (Self, Self) {
        assert!(index <= self.amount);
        // Create a new PRNG of the same type, by seeding it with this PRNG.
        // `from_rng` should never fail.
        let new = DistProducer {
            distr: self.distr,
            amount: self.amount - index,
            rng: R::from_rng(&mut self.rng).unwrap(),
            phantom: ::core::marker::PhantomData,
        };
        self.amount = index;
        (self, new)
    }

    fn min_len(&self) -> usize {
        100
    }
}

/// FIXME
#[cfg(feature = "rayon")]
#[derive(Debug)]
pub struct BoundedDistIter<'a, D: 'a, R, T> {
    distr: &'a D,
    rng: R,
    amount: usize,
    phantom: ::core::marker::PhantomData<T>,
}

#[cfg(feature = "rayon")]
impl<'a, D, R, T> Iterator for BoundedDistIter<'a, D, R, T>
    where D: Distribution<T>, R: Rng
{
    type Item = T;

    #[inline(always)]
    fn next(&mut self) -> Option<T> {
        if self.amount > 0 {
            self.amount -= 1;
            Some(self.distr.sample(&mut self.rng))
        } else {
            None
        }
    }
}

#[cfg(feature = "rayon")]
impl<'a, D, R, T> DoubleEndedIterator for BoundedDistIter<'a, D, R, T>
    where D: Distribution<T>, R: Rng
{
    #[inline(always)]
    fn next_back(&mut self) -> Option<T> {
        if self.amount > 0 {
            self.amount -= 1;
            Some(self.distr.sample(&mut self.rng))
        } else {
            None
        }
    }
}

#[cfg(feature = "rayon")]
impl<'a, D, R, T> ExactSizeIterator for BoundedDistIter<'a, D, R, T>
    where D: Distribution<T>, R: Rng
{
    fn len(&self) -> usize {
        self.amount
    }
}
