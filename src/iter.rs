// Copyright 2017-2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Iterators over `RngCore`

use core::cmp::min;
use core::usize;

use RngCore;

// TODO: in the future (see https://github.com/rust-lang/rfcs/issues/1403)
// it may be possible to allow reborrows in user code; this would let us
// replace `rng: &'a mut R` with `rng: R` in `Iter`, without having to create a
// redundant reference when calling `Map::next`. In this case `Rng::iter` would
// return `Iter<&mut Self>` and a separate constructor would be needed for
// reference/copy types not needing an extra reference.

/// An "iterator" over a random number generator; created by [`Rng::iter`].
/// 
/// This does not implement `std::iter::Iterator` since we cannot support
/// `next()`: it makes no sense to return a copy of an RNG, and though in
/// theory it should be possible to return `&mut RngCore`, `Iterator` does not
/// allow the lifetime of the item returned by `next` to be linked to the
/// iterator (or enclosed RNG). Instead, we support other selected operations
/// such as `map` and `take` directly.
/// 
/// [`Rng::iter`]: ../trait.Rng.html#method.iter
#[derive(Debug)]
pub struct Iter<'a, R: RngCore + ?Sized + 'a> {
    pub(crate) rng: &'a mut R,
    pub(crate) len: Option<usize>,
}

impl<'a, R: RngCore + ?Sized + 'a> Iter<'a, R> {
    pub(crate) fn new(rng: &'a mut R) -> Iter<'a, R> {
        Iter { rng, len: None }
    }
}

impl<'a, R: RngCore + ?Sized + 'a> Iter<'a, R> {
    /// Restricts the number of generated items to at most `len`.
    pub fn take(self, len: usize) -> Self {
        Iter {
            rng: self.rng,
            len: Some(self.len.map_or(len, |old| min(old, len))),
        }
    }
    
    /// Takes a closure and creates an iterator which calls that closure on
    /// each element.
    /// 
    /// ### Example
    /// 
    /// ```rust
    /// use rand::{thread_rng, Rng};
    /// use rand::distributions::Range;
    /// 
    /// let die_range = Range::new(1, 7);
    /// let mut rng = thread_rng();
    /// let mut die = rng.iter().map(|rng| rng.sample(die_range));
    /// for _ in 0..3 {
    ///     println!("Die roll: {}", die.next().unwrap());
    /// }
    /// ```
    pub fn map<B, F>(self, f: F) -> Map<'a, R, B, F>
        where F: FnMut(&mut R) -> B
    {
        Map {
            rng: self.rng,
            len: self.len,
            f: f,
        }
    }
    
    /// Creates an iterator that works like map, but flattens nested structure.
    /// 
    /// The [`map`] adapter is very useful, but only when the closure argument
    /// produces values. If it produces an iterator instead, there's an extra
    /// layer of indirection. `flat_map()` will remove this extra layer on its
    /// own.
    /// 
    /// ### Example
    /// 
    /// ```rust
    /// use rand::{thread_rng, Rng};
    /// use rand::distributions::Range;
    /// 
    /// let len_range = Range::new(1, 10);
    /// let mut rng = thread_rng();
    /// 
    /// // Count from 1 to a number between 1 and 9 several times:
    /// let mut iter = rng.iter().flat_map(|rng| 1..rng.sample(len_range)).take(20);
    /// while let Some(n) = iter.next() {
    ///     println!("{}", n);
    /// }
    /// ```
    /// 
    /// [`map`]: struct.Iter.html#method.map
    pub fn flat_map<U, F>(self, f: F) -> FlatMap<'a, R, U, F>
        where F: FnMut(&mut R) -> U, U: IntoIterator
    {
        FlatMap {
            rng: self.rng,
            len: self.len,
            f: f,
            frontiter: None,
        }
    }
}

/// Type created by [`Iter::map`](struct.Iter.html#method.map)
#[derive(Debug)]
pub struct Map<'a, R:?Sized+'a, B, F> where F: FnMut(&mut R) -> B {
    rng: &'a mut R,
    len: Option<usize>,
    f: F,
}
impl<'a, R:?Sized+'a, B, F> Iterator for Map<'a, R, B, F>
    where F: FnMut(&mut R) -> B
{
    type Item = B;
    
    fn next(&mut self) -> Option<B> {
        match self.len {
            Some(0) => return None,
            Some(ref mut n) => { *n -= 1; }
            None => {}
        }
        
        Some((self.f)(self.rng))
    }
    
    fn size_hint(&self) -> (usize, Option<usize>) {
        // If len == None we have an infinite iterator; usize::MAX is nearest
        // available lower bound. Probably this suffices to make the following equal:
        // rng.iter().take(n).map(f).size_hint() == rng.iter().map(f).take(n).size_hint()
        self.len.map_or((usize::MAX, None), |len| (len, Some(len)))
    }
}

/// Type created by [`Iter::flat_map`](struct.Iter.html#method.flat_map)
#[derive(Debug)]
pub struct FlatMap<'a, R:?Sized+'a, U, F>
    where F: FnMut(&mut R) -> U, U: IntoIterator
{
    rng: &'a mut R,
    len: Option<usize>,
    f: F,
    frontiter: Option<U::IntoIter>,
}
impl<'a, R:?Sized+'a, U, F> Iterator for FlatMap<'a, R, U, F>
    where F: FnMut(&mut R) -> U, U: IntoIterator
{
    type Item = <U as IntoIterator>::Item;
    
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ref mut inner) = self.frontiter {
                if let Some(x) = inner.by_ref().next() {
                    return Some(x)
                }
            }
            
            match self.len {
                Some(0) => return None,
                Some(ref mut n) => { *n -= 1; }
                None => {}
            }
            
            self.frontiter = Some(IntoIterator::into_iter((self.f)(self.rng)));
        }
    }
    
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.len == Some(0) {
            // No new iters, so we have frontiter or nothing
            self.frontiter.as_ref().map_or((0, Some(0)), |it| it.size_hint())
        } else {
            // Can't compute an actual bound without producing the sub-iters,
            // which we don't want to do. But we may have a lower bound.
            let lb = self.frontiter.as_ref().map_or(0, |it| it.size_hint().0);
            (lb, None)
        }
    }
}

#[cfg(test)]
mod tests {
    use {Rng, RngCore};
    use distributions::{Uniform};
    #[cfg(all(not(feature="std"), feature="alloc"))] use alloc::{Vec, String};

    #[test]
    #[cfg(any(feature="std", feature="alloc"))]
    fn test_iter() {
        let mut rng = ::test::rng(160);
        
        let x: Vec<()> = rng.iter().take(10).map(|_| ()).collect();
        assert_eq!(x.len(), 10);
        let y: Vec<u32> = rng.iter().take(10).map(|rng| rng.sample(Uniform)).collect();
        assert_eq!(y.len(), 10);
        let z: Vec<u32> = rng.iter().take(10).flat_map(|rng|
                vec![rng.sample(Uniform), rng.sample(Uniform)].into_iter()).collect();
        assert_eq!(z.len(), 20);
        let w: Vec<String> = rng.iter().take(10).flat_map(|_| vec![].into_iter()).collect();
        assert_eq!(w.len(), 0);
    }
    
    #[test]
    fn test_dyn_dispatch() {
        let mut rng = ::test::rng(161);
        let mut r: &mut RngCore = &mut rng;
        
        let mut x = 0;
        for n in r.iter().map(|rng| rng.next_u32()).take(2) {
            x ^= n;
        }
        assert!(x != 0);
    }
}
