// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rand::SeedableRng;
use rand_distr::{Distribution, Normal};
use statrs::distribution::ContinuousCDF;
use statrs::distribution::DiscreteCDF;

/// Empirical Cumulative Distribution Function (ECDF)
struct Ecdf {
    sorted_samples: Vec<f64>,
}

impl Ecdf {
    fn new(mut samples: Vec<f64>) -> Self {
        samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
        Self {
            sorted_samples: samples,
        }
    }

    /// Returns the step points of the ECDF
    /// The ECDF is a step function that increases by 1/n at each sample point
    /// The function is continoius from the right, so we give the bigger value at the step points
    /// First point is (-inf, 0.0), last point is (max(samples), 1.0)
    fn step_points(&self) -> Vec<(f64, f64)> {
        let mut points = Vec::with_capacity(self.sorted_samples.len() + 1);
        let mut last = f64::NEG_INFINITY;
        let mut count = 0;
        let n = self.sorted_samples.len() as f64;
        for &x in &self.sorted_samples {
            if x != last {
                points.push((last, count as f64 / n));
                last = x;
            }
            count += 1;
        }
        points.push((last, count as f64 / n));
        points
    }
}

fn kolmo_smirnov_statistic_continuous(ecdf: Ecdf, cdf: impl Fn(f64) -> f64) -> f64 {
    let mut max_diff = 0.;
    // The maximum will always be at a step point, because the cdf is continious monotonic increasing
    let step_points = ecdf.step_points();
    for i in 0..step_points.len() - 1 {
        // This shift is because we want the value of the ecdf at (x_{i + 1} - epsilon) = ecdf(x_i) and comare it to cdf(x_{i + 1})
        // cdf(x_{i + 1} - epsilon) = cdf(x_{i+1}) because cdf is continious
        let x = step_points[i + 1].0;
        let diff = (step_points[i].1 - cdf(x)).abs();

        if diff > max_diff {
            max_diff = diff;
        }
    }
    max_diff
}

fn kolmo_smirnov_statistic_discrete(ecdf: Ecdf, cdf: impl Fn(i64) -> f64) -> f64 {
    let mut max_diff = 0.;

    // The maximum will always be at a step point, but we have to be careful because the cdf is not continious
    // It is actually easier because both are right continious step functions
    let step_points = ecdf.step_points();
    for (x, y) in step_points[1..].iter() {
        let diff = (*y - cdf(*x as i64)).abs();
        if diff > max_diff {
            max_diff = diff;
        }
    }
    max_diff
}

#[cfg(test)]
fn test_continious(dist: impl Distribution<f64>, cdf: impl Fn(f64) -> f64) {
    const N_SAMPLES: u64 = 1_000_000;
    let mut rng = rand::rngs::SmallRng::seed_from_u64(1);
    let samples = (0..N_SAMPLES).map(|_| dist.sample(&mut rng)).collect();
    let ecdf = Ecdf::new(samples);

    let ks_statistic = kolmo_smirnov_statistic_continuous(ecdf, cdf);

    // It is a heuristic value, we want to prove that the distributions match, so p values don't help us
    let critical_value = 1.36 / (N_SAMPLES as f64).sqrt();

    println!("KS statistic: {}", ks_statistic);
    println!("Critical value: {}", critical_value);
    assert!(ks_statistic < critical_value);
}

#[cfg(test)]
fn test_discrete<I: TryInto<i64>>(dist: impl Distribution<I>, cdf: impl Fn(i64) -> f64)
where
    <I as TryInto<i64>>::Error: std::fmt::Debug,
{
    const N_SAMPLES: u64 = 1_000_000;
    let mut rng = rand::rngs::SmallRng::seed_from_u64(1);
    let samples = (0..N_SAMPLES)
        .map(|_| dist.sample(&mut rng).try_into().unwrap() as f64)
        .collect();
    let ecdf = Ecdf::new(samples);

    let ks_statistic = kolmo_smirnov_statistic_discrete(ecdf, cdf);

    let critical_value = 1.36 / (N_SAMPLES as f64).sqrt();

    println!("KS statistic: {}", ks_statistic);
    println!("Critical value: {}", critical_value);
    assert!(ks_statistic < critical_value);
}

#[test]
fn normal() {
    test_continious(Normal::new(0.0, 1.0).unwrap(), |x| {
        statrs::distribution::Normal::new(0.0, 1.0).unwrap().cdf(x)
    });
}

#[test]
fn binomial() {
    test_discrete(rand_distr::Binomial::new(10, 0.5).unwrap(), |x| {
        statrs::distribution::Binomial::new(0.5, 10)
            .unwrap()
            .cdf(x as u64)
    });
}
