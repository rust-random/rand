// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Random operations on sequences

use Rng;
use distributions::range;

#[cfg(feature="std")]
pub use self::weighted::{Weighted, WeightedChoice};

#[cfg(feature="std")]
mod weighted;

/// This trait implements a `choose` operations on slices and sequences.
pub trait Choose<T> {
    /// Return one element from a sequence.
    /// 
    /// Returns `None` only if the sequence is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::thread_rng;
    /// use rand::sequences::Choose;
    ///
    /// let choices = [1, 2, 4, 8, 16, 32];
    /// let mut rng = thread_rng();
    /// println!("{:?}", choices[..].choose(&mut rng));
    /// assert_eq!(choices[..0].choose(&mut rng), None);
    /// ```
    fn choose<R: Rng+?Sized>(self, rng: &mut R) -> Option<T>;
}

impl<'a, T> Choose<&'a T> for &'a [T] {
    fn choose<R: Rng+?Sized>(self, rng: &mut R) -> Option<&'a T> {
        if self.is_empty() {
            None
        } else {
            Some(&self[range(0, self.len(), rng)])
        }
    }
}

impl<'a, T> Choose<&'a mut T> for &'a mut [T] {
    fn choose<R: Rng+?Sized>(self, rng: &mut R) -> Option<&'a mut T> {
        if self.is_empty() {
            None
        } else {
            let len = self.len();
            Some(&mut self[range(0, len, rng)])
        }
    }
}

#[cfg(feature="std")]
impl<T> Choose<T> for Vec<T> {
    fn choose<R: Rng+?Sized>(mut self, rng: &mut R) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            let index = range(0, self.len(), rng);
            self.drain(index..).next()
        }
    }
}

/// Randomly sample up to `amount` elements from a finite iterator.
/// The order of elements in the sample is not random.
///
/// # Example
///
/// ```rust
/// use rand::thread_rng;
/// use rand::sequences::sample;
///
/// let mut rng = thread_rng();
/// let sample = sample(&mut rng, 1..100, 5);
/// println!("{:?}", sample);
/// ```
#[cfg(feature="std")]
pub fn sample<T, I, R>(rng: &mut R, iterable: I, amount: usize) -> Vec<T>
    where I: IntoIterator<Item=T>,
          R: Rng,
{
    let mut iter = iterable.into_iter();
    let mut reservoir: Vec<T> = iter.by_ref().take(amount).collect();
    // continue unless the iterator was exhausted
    if reservoir.len() == amount {
        for (i, elem) in iter.enumerate() {
            let k = range(0, i + 1 + amount, rng);
            if let Some(spot) = reservoir.get_mut(k) {
                *spot = elem;
            }
        }
    }
    reservoir
}

/// This trait introduces a `shuffle` operations on slices.
pub trait Shuffle {
    /// Shuffle a mutable sequence in place.
    ///
    /// This applies Durstenfeld's algorithm for the [Fisher–Yates shuffle](https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle#The_modern_algorithm)
    /// which produces an unbiased permutation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::thread_rng;
    /// use rand::sequences::Shuffle;
    ///
    /// let mut rng = thread_rng();
    /// let mut y = [1, 2, 3];
    /// y[..].shuffle(&mut rng);
    /// println!("{:?}", y);
    /// y[..].shuffle(&mut rng);
    /// println!("{:?}", y);
    /// ```
    fn shuffle<R: Rng+?Sized>(self, rng: &mut R);
}

impl<'a, T> Shuffle for &'a mut [T] {
    fn shuffle<R: Rng+?Sized>(self, rng: &mut R) {
        let mut i = self.len();
        while i >= 2 {
            // invariant: elements with index >= i have been locked in place.
            i -= 1;
            // lock element i in place.
            self.swap(i, range(0, i + 1, rng));
        }
    }
}

#[cfg(feature="std")]
impl<'a, T> Shuffle for &'a mut Vec<T> {
    fn shuffle<R: Rng+?Sized>(self, rng: &mut R) {
        (self[..]).shuffle(rng)
    }
}

#[cfg(test)]
mod test {
    use {Rng, thread_rng};
    use super::{Choose, sample, Shuffle};
    
    #[test]
    fn test_choose() {
        let mut r = thread_rng();
        assert_eq!([1, 1, 1][..].choose(&mut r).map(|&x|x), Some(1));

        let v: &[isize] = &[];
        assert_eq!(v.choose(&mut r), None);
    }

    #[test]
    fn test_sample() {
        let min_val = 1;
        let max_val = 100;

        let mut r = thread_rng();
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample = sample(&mut r, vals.iter(), 5);
        let large_sample = sample(&mut r, vals.iter(), vals.len() + 5);

        assert_eq!(small_sample.len(), 5);
        assert_eq!(large_sample.len(), vals.len());

        assert!(small_sample.iter().all(|e| {
            **e >= min_val && **e <= max_val
        }));
    }

    #[test]
    fn test_shuffle() {
        let mut r = thread_rng();
        let empty: &mut [isize] = &mut [];
        empty.shuffle(&mut r);
        let mut one = [1];
        one[..].shuffle(&mut r);
        let b: &[_] = &[1];
        assert_eq!(one, b);

        let mut two = [1, 2];
        two[..].shuffle(&mut r);
        assert!(two == [1, 2] || two == [2, 1]);

        let mut x = [1, 1, 1];
        x[..].shuffle(&mut r);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(x, b);
    }
    
    #[test]
    fn dyn_dispatch() {
        let mut r: &mut Rng = &mut thread_rng();
        
        assert_eq!([7, 7][..].choose(r), Some(&7));
        
        let mut x = [6, 2];
        x[..].shuffle(r);
        assert!(x == [6, 2] || x == [2, 6]);
    }
}
