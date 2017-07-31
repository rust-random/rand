// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Iterators attached to an `Rng`
//! 
//! Lifetime restrictions prevent an `Rng` iterator from simply implementing
//! `std::iter::Iterator`. Instead, you get the simplified iterators below,
//! providing only a subset of functionality.

use std::cmp::min;

use Rng;

/// Pseudo-iterator encapsulating a random number generator.
/// See [`Rng::iter`](trait.Rng.html#method.iter).
#[derive(Debug)]
pub struct Iter<'a, R: Rng+?Sized+'a> {
    pub(crate) rng: &'a mut R,
    pub(crate) len: Option<usize>,
}

impl<'a, R: Rng+?Sized+'a> Iter<'a, R> {
    /// Create an instance. Same as `Rng::iter()` but supports dynamic dispatch.
    // TODO: remove `Rng::iter()`?
    pub fn new(rng: &'a mut R) -> Self {
        Iter { rng, len: None }
    }
    
    /// Restrict number of generated items to at most `len`
    pub fn take(self, len: usize) -> Self {
        Iter {
            rng: self.rng,
            len: Some(self.len.map_or(len, |old| min(old, len))),
        }
    }
    
    /// Produce an iterator returning a mapped value
    pub fn map<B, F>(self, f: F) -> Map<'a, R, B, F>
        where F: FnMut(&mut R) -> B
    {
        Map {
            rng: self.rng,
            len: self.len,
            f: f,
        }
    }
    
    /// Produce an iterator returning a flat-mapped value
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
}

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
}

#[cfg(test)]
mod tests {
    use {Rng, thread_rng};
    use dist::{uniform, ascii_word_char};
    use iter::Iter;
    
    #[test]
    fn test_iter() {
        let mut rng = thread_rng();
        
        let x: Vec<()> = rng.iter().take(10).map(|_| ()).collect();
        assert_eq!(x.len(), 10);
        let y: Vec<u32> = rng.iter().take(10).map(|rng| uniform(rng)).collect();
        assert_eq!(y.len(), 10);
        let z: Vec<u32> = rng.iter().take(10).flat_map(|rng|
                vec![uniform(rng), uniform(rng)].into_iter()).collect();
        assert_eq!(z.len(), 20);
        let w: Vec<String> = rng.iter().take(10).flat_map(|_| vec![].into_iter()).collect();
        assert_eq!(w.len(), 0);
    }
    
    #[test]
    fn test_dyn_dispatch() {
        let mut r: &mut Rng = &mut thread_rng();
        
        let x: String = Iter::new(r).take(10).map(|rng| ascii_word_char(rng)).collect();
        assert_eq!(x.len(), 10);
    }
}
