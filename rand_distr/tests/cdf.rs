// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use num_traits::AsPrimitive;
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

const SAMPLE_SIZE: u64 = 1_000_000;

fn critical_value() -> f64 {
    // If the sampler is correct, we expect less than 0.001 false positives (alpha = 0.001).
    // Passing this does not prove that the sampler is correct but is a good indication.
    1.95 / (SAMPLE_SIZE as f64).sqrt()
}

fn sample_ecdf<T>(seed: u64, dist: impl Distribution<T>) -> Ecdf
where
    T: AsPrimitive<f64>,
{
    let mut rng = rand::rngs::SmallRng::seed_from_u64(seed);
    let samples = (0..SAMPLE_SIZE)
        .map(|_| dist.sample(&mut rng).as_())
        .collect();
    Ecdf::new(samples)
}

fn test_continuous(seed: u64, dist: impl Distribution<f64>, cdf: impl Fn(f64) -> f64) {
    let ecdf = sample_ecdf(seed, dist);
    let ks_statistic = kolmogorov_smirnov_statistic_continuous(ecdf, cdf);

    let critical_value = critical_value();

    println!("KS statistic: {}", ks_statistic);
    println!("Critical value: {}", critical_value);
    assert!(ks_statistic < critical_value);
}

fn test_discrete<I: AsPrimitive<f64>>(
    seed: u64,
    dist: impl Distribution<I>,
    cdf: impl Fn(i64) -> f64,
) {
    let ecdf = sample_ecdf(seed, dist);
    let ks_statistic = kolmogorov_smirnov_statistic_discrete(ecdf, cdf);

    // This critical value is bigger than it could be for discrete distributions, but because of large sample sizes this should not matter too much
    let critical_value = critical_value();

    println!("KS statistic: {}", ks_statistic);
    println!("Critical value: {}", critical_value);
    assert!(ks_statistic < critical_value);
}

#[test]
fn normal() {
    let parameters = [
        (0.0, 1.0),
        (0.0, 0.1),
        (1.0, 10.0),
        (1.0, 100.0),
        (-1.0, 0.00001),
        (-1.0, 0.0000001),
    ];

    for (seed, (mean, std_dev)) in parameters.into_iter().enumerate() {
        test_continuous(seed as u64, Normal::new(mean, std_dev).unwrap(), |x| {
            statrs::distribution::Normal::new(mean, std_dev)
                .unwrap()
                .cdf(x)
        });
    }
}

#[test]
fn binomial() {
    let parameters = [
        (0.5, 10),
        (0.5, 100),
        (0.1, 10),
        (0.0000001, 1000000),
        (0.0000001, 10),
        (0.9999, 2),
    ];

    for (seed, (p, n)) in parameters.into_iter().enumerate() {
        test_discrete(seed as u64, rand_distr::Binomial::new(n, p).unwrap(), |x| {
            if x < 0 {
                0.0
            } else {
                statrs::distribution::Binomial::new(p, n)
                    .unwrap()
                    .cdf(x as u64)
            }
        });
    }
}
