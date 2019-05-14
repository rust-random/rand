// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use average::Histogram;
use rand::prelude::*;

const N_BINS: usize = 100;
const N_SAMPLES: u32 = 1_000_000;
const TOL: f64 = 1e-3;
average::define_histogram!(hist, 100);
use hist::Histogram as Histogram100;

#[test]
fn unit_sphere() {
    const N_DIM: usize = 3;
    let h = Histogram100::with_const_width(-1., 1.);
    let mut histograms = [h.clone(), h.clone(), h];
    let dist = rand_distr::UnitSphere;
    let mut rng = rand_pcg::Pcg32::from_entropy();
    for _ in 0..N_SAMPLES {
        let v: [f64; 3] = dist.sample(&mut rng);
        for i in 0..N_DIM {
            histograms[i].add(v[i]).map_err(
                |e| { println!("v: {}", v[i]); e }
            ).unwrap();
        }
    }
    for h in &histograms {
        let sum: u64 = h.bins().iter().sum();
        println!("{:?}", h);
        for &b in h.bins() {
            let p = (b as f64) / (sum as f64);
            assert!((p - 1.0 / (N_BINS as f64)).abs() < TOL, "{}", p);
        }
    }
}

#[test]
fn unit_circle() {
    use std::f64::consts::PI;
    let mut h = Histogram100::with_const_width(-PI, PI);
    let dist = rand_distr::UnitCircle;
    let mut rng = rand_pcg::Pcg32::from_entropy();
    for _ in 0..N_SAMPLES {
        let v: [f64; 2] = dist.sample(&mut rng);
        h.add(v[0].atan2(v[1])).unwrap();
    }
    let sum: u64 = h.bins().iter().sum();
    println!("{:?}", h);
    for &b in h.bins() {
        let p = (b as f64) / (sum as f64);
        assert!((p - 1.0 / (N_BINS as f64)).abs() < TOL, "{}", p);
    }
}
