// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(test)]

extern crate test;

use rand::distributions::WeightedIndex;
use rand::Rng;
use test::Bencher;

#[bench]
fn weighted_index_assignment(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let weights = &[1u32, 2, 3, 0, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7][..];
    let mut distr = WeightedIndex::new(weights).unwrap();
    b.iter(|| {
        distr.assign_new_weights(weights).unwrap();
        rng.sample(&distr)
    })
}

#[bench]
fn weighted_index_assignment_large(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let weights: Vec<u64> = (0u64..1000).collect();
    let mut distr = WeightedIndex::new(&weights).unwrap();
    b.iter(|| {
        distr.assign_new_weights(&weights).unwrap();
        rng.sample(&distr)
    })
}

#[bench]
fn weighted_index_creation(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let weights = &[1u32, 2, 4, 0, 5, 1, 7, 1, 2, 3, 4, 5, 6, 7][..];
    b.iter(|| {
        let distr = WeightedIndex::new(weights).unwrap();
        rng.sample(distr)
    })
}

#[bench]
fn weighted_index_creation_large(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let weights: Vec<u64> = (0u64..1000).collect();
    b.iter(|| {
        let distr = WeightedIndex::new(&weights).unwrap();
        rng.sample(&distr)
    })
}

#[bench]
fn weighted_index_modification(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let weights = &[1u32, 2, 3, 0, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7][..];
    let mut distr = WeightedIndex::new(weights).unwrap();
    b.iter(|| {
        distr.update_weights(&[(2, &4), (5, &1)]).unwrap();
        rng.sample(&distr)
    })
}
