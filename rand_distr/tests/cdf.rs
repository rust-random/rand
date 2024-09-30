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

// [1] Nonparametric Goodness-of-Fit Tests for Discrete Null Distributions
//     by Taylor B. Arnold and John W. Emerson
//     http://www.stat.yale.edu/~jay/EmersonMaterials/DiscreteGOF.pdf

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
    /// The function is continuous from the right, so we give the bigger value at the step points
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

fn kolmogorov_smirnov_statistic_continuous(ecdf: Ecdf, cdf: impl Fn(f64) -> f64) -> f64 {
    // We implement equation (3) from [1]

    let mut max_diff: f64 = 0.;

    let step_points = ecdf.step_points(); // x_i in the paper
    for i in 1..step_points.len() {
        let (x_i, f_i) = step_points[i];
        let (_, f_i_1) = step_points[i - 1];
        let max_1 = (cdf(x_i) - f_i).abs();
        let max_2 = (cdf(x_i) - f_i_1).abs();

        max_diff = max_diff.max(max_1).max(max_2);
    }
    max_diff
}

fn kolmogorov_smirnov_statistic_discrete(ecdf: Ecdf, cdf: impl Fn(i64) -> f64) -> f64 {
    // We implement equation (4) from [1]
    
    let mut max_diff: f64 = 0.;

    let step_points = ecdf.step_points(); // x_i in the paper
    for i in 1..step_points.len() {
        let (x_i, f_i) = step_points[i];
        let (_, f_i_1) = step_points[i - 1];
        let max_1 = (cdf(x_i as i64) - f_i).abs();
        let max_2 = (cdf(x_i as i64 - 1) - f_i_1).abs(); // -1 is the same as -epsilon, because we have integer support

        max_diff = max_diff.max(max_1).max(max_2);
    }
    max_diff
}

#[cfg(test)]
fn test_continuous(seed: u64, dist: impl Distribution<f64>, cdf: impl Fn(f64) -> f64) {
    const N_SAMPLES: u64 = 1_000_000;
    let mut rng = rand::rngs::SmallRng::seed_from_u64(seed);
    let samples = (0..N_SAMPLES).map(|_| dist.sample(&mut rng)).collect();
    let ecdf = Ecdf::new(samples);

    let ks_statistic = kolmogorov_smirnov_statistic_continuous(ecdf, cdf);

    // If the sampler is correct, we expect less than 0.001 false positives (alpha = 0.001).
    // Passing this does not prove that the sampler is correct but is a good indication.
    let critical_value = 1.95 / (N_SAMPLES as f64).sqrt();

    println!("KS statistic: {}", ks_statistic);
    println!("Critical value: {}", critical_value);
    assert!(ks_statistic < critical_value);
}

#[cfg(test)]
fn test_discrete<I: TryInto<i64>>(seed: u64, dist: impl Distribution<I>, cdf: impl Fn(i64) -> f64)
where
    <I as TryInto<i64>>::Error: std::fmt::Debug,
{
    const N_SAMPLES: u64 = 1_000_000;
    let mut rng = rand::rngs::SmallRng::seed_from_u64(seed);
    let samples = (0..N_SAMPLES)
        .map(|_| dist.sample(&mut rng).try_into().unwrap() as f64)
        .collect();
    let ecdf = Ecdf::new(samples);

    let ks_statistic = kolmogorov_smirnov_statistic_discrete(ecdf, cdf);

    // If the sampler is correct, we expect less than 0.001 false positives (alpha = 0.001). Passing this does not prove that the sampler is correct but is a good indication.
    let critical_value = 1.95 / (N_SAMPLES as f64).sqrt();

    println!("KS statistic: {}", ks_statistic);
    println!("Critical value: {}", critical_value);
    assert!(ks_statistic < critical_value);
}

#[test]
fn normal() {
    for seed in 1..20 {
        test_continuous(seed, Normal::new(0.0, 1.0).unwrap(), |x| {
            statrs::distribution::Normal::new(0.0, 1.0).unwrap().cdf(x)
        });
    }
}

#[test]
fn binomial() {
    for seed in 1..20 {
        test_discrete(seed, rand_distr::Binomial::new(10, 0.5).unwrap(), |x| {
            statrs::distribution::Binomial::new(0.5, 10)
                .unwrap()
                .cdf(x as u64)
        });
    }
}
