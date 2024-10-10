// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::f64;

use num_traits::AsPrimitive;
use rand::SeedableRng;
use rand_distr::{Distribution, Normal};
use special::{Beta, Gamma, Primitive};

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
        let cdf_i = cdf(x_i);
        let max_1 = (cdf_i - f_i).abs();
        let max_2 = (cdf_i - f_i_1).abs();

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

/// Tests a distribution against an analytical CDF.
/// The CDF has to be continuous.
pub fn test_continuous(seed: u64, dist: impl Distribution<f64>, cdf: impl Fn(f64) -> f64) {
    let ecdf = sample_ecdf(seed, dist);
    let ks_statistic = kolmogorov_smirnov_statistic_continuous(ecdf, cdf);

    let critical_value = critical_value();

    println!("KS statistic: {}", ks_statistic);
    println!("Critical value: {}", critical_value);
    assert!(ks_statistic < critical_value);
}

/// Tests a distribution over integers against an analytical CDF.
/// The analytical CDF must not have jump points which are not integers.
pub fn test_discrete<I: AsPrimitive<f64>>(
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

fn normal_cdf(x: f64, mean: f64, std_dev: f64) -> f64 {
    0.5 * ((mean - x) / (std_dev * f64::consts::SQRT_2)).erfc()
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
            normal_cdf(x, mean, std_dev)
        });
    }
}

#[test]
fn cauchy() {
    fn cdf(x: f64, median: f64, scale: f64) -> f64 {
        (1.0 / f64::consts::PI) * ((x - median) / scale).atan() + 0.5
    }

    let parameters = [
        (0.0, 1.0),
        (0.0, 0.1),
        (1.0, 10.0),
        (1.0, 100.0),
        (-1.0, 0.00001),
        (-1.0, 0.0000001),
    ];

    for (seed, (median, scale)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Cauchy::new(median, scale).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, median, scale));
    }
}

#[test]
fn uniform() {
    fn cdf(x: f64, a: f64, b: f64) -> f64 {
        if x < a {
            0.0
        } else if x < b {
            (x - a) / (b - a)
        } else {
            1.0
        }
    }

    let parameters = [(0.0, 1.0), (-1.0, 1.0), (0.0, 100.0), (-100.0, 100.0)];

    for (seed, (a, b)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Uniform::new(a, b).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, a, b));
    }
}

#[test]
fn log_normal() {
    fn cdf(x: f64, mean: f64, std_dev: f64) -> f64 {
        if x <= 0.0 {
            0.0
        } else if x.is_infinite() {
            1.0
        } else {
            0.5 * ((mean - x.ln()) / (std_dev * f64::consts::SQRT_2)).erfc()
        }
    }

    let parameters = [
        (0.0, 1.0),
        (0.0, 0.1),
        (0.5, 0.7),
        (1.0, 10.0),
        (1.0, 100.0),
    ];

    println!("{}", cdf(5.0, 2.0, 1.5));

    for (seed, (mean, std_dev)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::LogNormal::new(mean, std_dev).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, mean, std_dev));
    }
}

#[test]
fn pareto() {
    fn cdf(x: f64, scale: f64, alpha: f64) -> f64 {
        if x <= scale {
            0.0
        } else {
            1.0 - (scale / x).powf(alpha)
        }
    }

    let parameters = [
        (1.0, 1.0),
        (1.0, 0.1),
        (1.0, 10.0),
        (1.0, 100.0),
        (0.1, 1.0),
        (10.0, 1.0),
        (100.0, 1.0),
    ];

    for (seed, (scale, alpha)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Pareto::new(scale, alpha).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, scale, alpha));
    }
}

#[test]
fn exp() {
    fn cdf(x: f64, lambda: f64) -> f64 {
        1.0 - (-lambda * x).exp()
    }

    let parameters = [0.5, 1.0, 7.5, 32.0, 100.0];

    for (seed, lambda) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Exp::new(lambda).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, lambda));
    }
}

#[test]
fn weibull() {
    fn cdf(x: f64, lambda: f64, k: f64) -> f64 {
        if x < 0.0 {
            return 0.0;
        }

        1.0 - (-(x / lambda).powf(k)).exp()
    }

    let parameters = [
        (0.5, 1.0),
        (1.0, 1.0),
        (10.0, 0.1),
        (0.1, 10.0),
        (15.0, 20.0),
        // (1000.0, 0.001), // Fail case
    ];

    for (seed, (lambda, k)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Weibull::new(lambda, k).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, lambda, k));
    }
}

#[test]
fn gumbel() {
    fn cdf(x: f64, mu: f64, beta: f64) -> f64 {
        (-(-(x - mu) / beta).exp()).exp()
    }

    let parameters = [
        (0.0, 1.0),
        (1.0, 2.0),
        (-1.0, 0.5),
        (10.0, 0.1),
        (100.0, 0.0001),
    ];

    for (seed, (mu, beta)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Gumbel::new(mu, beta).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, mu, beta));
    }
}

#[test]
fn frechet() {
    fn cdf(x: f64, alpha: f64, s: f64, m: f64) -> f64 {
        if x < m {
            return 0.0;
        }

        (-((x - m) / s).powf(-alpha)).exp()
    }

    let parameters = [
        (0.5, 2.0, 1.0),
        (1.0, 1.0, 1.0),
        (10.0, 0.1, 1.0),
        (100.0, 0.0001, 1.0),
        (0.9999, 2.0, 1.0),
    ];

    for (seed, (alpha, s, m)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Frechet::new(m, s, alpha).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, alpha, s, m));
    }
}

#[test]
fn gamma() {
    fn cdf(x: f64, shape: f64, scale: f64) -> f64 {
        if x < 0.0 {
            return 0.0;
        }

        (x / scale).inc_gamma(shape)
    }

    let parameters = [
        (0.5, 2.0),
        (1.0, 1.0),
        (10.0, 0.1),
        (100.0, 0.0001),
        (0.9999, 2.0),
    ];

    for (seed, (shape, scale)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Gamma::new(shape, scale).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, shape, scale));
    }
}

#[test]
fn chi_squared() {
    fn cdf(x: f64, k: f64) -> f64 {
        if x < 0.0 {
            return 0.0;
        }

        (x / 2.0).inc_gamma(k / 2.0)
    }

    let parameters = [
        // 0.01, // Fail case
        0.1, 1.0, 2.0, 10.0, 100.0, 1000.0,
    ];

    for (seed, k) in parameters.into_iter().enumerate() {
        let dist = rand_distr::ChiSquared::new(k).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, k));
    }
}
#[test]
fn studend_t() {
    fn cdf(x: f64, df: f64) -> f64 {
        let h = df / (df + x.powi(2));
        let ib = 0.5 * h.inc_beta(df / 2.0, 0.5, 0.5.ln_beta(df / 2.0));
        if x < 0.0 {
            ib
        } else {
            1.0 - ib
        }
    }

    let parameters = [1.0, 10.0, 50.0];

    for (seed, df) in parameters.into_iter().enumerate() {
        let dist = rand_distr::StudentT::new(df).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, df));
    }
}

#[test]
fn fisher_f() {
    fn cdf(x: f64, m: f64, n: f64) -> f64 {
        if m == 1.0 && x <= 0.0 {
            return 0.0;
        } else if x < 0.0 {
            return 0.0;
        } else {
            let k = m * x / (m * x + n);
            let d1 = m / 2.0;
            let d2 = n / 2.0;
            k.inc_beta(d1, d2, d1.ln_beta(d2))
        }
    }

    let parameters = [(1.0, 1.0), (1.0, 2.0), (2.0, 1.0), (50.0, 1.0)];

    for (seed, (m, n)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::FisherF::new(m, n).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, m, n));
    }
}

#[test]
fn beta() {
    fn cdf(x: f64, alpha: f64, beta: f64) -> f64 {
        if x < 0.0 {
            return 0.0;
        }
        if x > 1.0 {
            return 1.0;
        }
        let ln_beta_ab = alpha.ln_beta(beta);
        x.inc_beta(alpha, beta, ln_beta_ab)
    }

    let parameters = [
        (0.5, 0.5),
        (2.0, 3.5),
        (10.0, 1.0),
        (100.0, 50.0),
        // (10.0, 0.1), // Fail case
    ];

    for (seed, (alpha, beta)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Beta::new(alpha, beta).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, alpha, beta));
    }
}

#[test]
fn triangular() {
    fn cdf(x: f64, a: f64, b: f64, c: f64) -> f64 {
        if x <= a {
            0.0
        } else if a < x && x <= c {
            (x - a).powi(2) / ((b - a) * (c - a))
        } else if c < x && x < b {
            1.0 - (b - x).powi(2) / ((b - a) * (b - c))
        } else {
            1.0
        }
    }

    let parameters = [
        (0.0, 1.0, 0.0001),
        (0.0, 1.0, 0.9999),
        (0.0, 1.0, 0.5),
        (0.0, 100.0, 50.0),
        (-100.0, 100.0, 0.0),
    ];

    for (seed, (a, b, c)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Triangular::new(a, b, c).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, a, b, c));
    }
}

fn binomial_cdf(k: i64, p: f64, n: u64) -> f64 {
    if k < 0 {
        return 0.0;
    }
    let k = k as u64;
    if k >= n {
        return 1.0;
    }

    let a = (n - k) as f64;
    let b = k as f64 + 1.0;

    let q = 1.0 - p;

    let ln_beta_ab = a.ln_beta(b);

    q.inc_beta(a, b, ln_beta_ab)
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
        test_discrete(seed as u64, rand_distr::Binomial::new(n, p).unwrap(), |k| {
            binomial_cdf(k, p, n)
        });
    }
}

#[test]
fn geometric() {
    fn cdf(k: i64, p: f64) -> f64 {
        if k < 0 {
            0.0
        } else {
            1.0 - (1.0 - p).powi(1 + k as i32)
        }
    }

    let parameters = [0.3, 0.5, 0.7, 0.0000001, 0.9999];

    for (seed, p) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Geometric::new(p).unwrap();
        test_discrete(seed as u64, dist, |k| cdf(k, p));
    }
}

#[test]
fn hypergeometric() {
    fn cdf(x: i64, n: u64, k: u64, n_: u64) -> f64 {
        let min = if n_ + k > n { n_ + k - n } else { 0 };
        let max = k.min(n_);
        if x < min as i64 {
            return 0.0;
        } else if x >= max as i64 {
            return 1.0;
        }

        (min..x as u64 + 1).fold(0.0, |acc, k_| {
            acc + (ln_binomial(k, k_) + ln_binomial(n - k, n_ - k_) - ln_binomial(n, n_)).exp()
        })
    }

    let parameters = [
        (15, 13, 10),
        (25, 15, 5),
        (60, 10, 7),
        (70, 20, 50),
        (100, 50, 10),
        // (100, 50, 49), // Fail case
    ];

    for (seed, (n, k, n_)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Hypergeometric::new(n, k, n_).unwrap();
        test_discrete(seed as u64, dist, |x| cdf(x, n, k, n_));
    }
}

#[test]
fn poisson() {
    fn cdf(k: i64, lambda: f64) -> f64 {
        if k < 0 || lambda <= 0.0 {
            return 0.0;
        }

        1.0 - gamma_lr(k as f64 + 1.0, lambda)
    }
    let parameters = [
        0.1_f32, 1.0, 7.5, 2e4,
        // 1e9,
        // 1.844E+19,  // fail case
    ];

    for (seed, lambda) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Poisson::new(lambda).unwrap();
        test_discrete(seed as u64, dist, |k| cdf(k, lambda as f64));
    }
}

fn ln_factorial(n: u64) -> f64 {
    (n as f64 + 1.0).lgamma().0
}

fn ln_binomial(n: u64, k: u64) -> f64 {
    ln_factorial(n) - ln_factorial(k) - ln_factorial(n - k)
}

/// https://docs.rs/statrs/latest/src/statrs/function/gamma.rs.html#260-347
fn gamma_lr(a: f64, x: f64) -> f64 {
    let eps = 0.000000000000001;
    let big = 4503599627370496.0;
    let big_inv = 2.22044604925031308085e-16;

    let ax = a * x.ln() - x - a.lgamma().0;
    if ax < -709.78271289338399 {
        if a < x {
            return 1.0;
        }
        return 0.0;
    }
    if x <= 1.0 || x <= a {
        let mut r2 = a;
        let mut c2 = 1.0;
        let mut ans2 = 1.0;
        loop {
            r2 += 1.0;
            c2 *= x / r2;
            ans2 += c2;

            if c2 / ans2 <= eps {
                break;
            }
        }
        return ax.exp() * ans2 / a;
    }

    let mut y = 1.0 - a;
    let mut z = x + y + 1.0;
    let mut c = 0;

    let mut p3 = 1.0;
    let mut q3 = x;
    let mut p2 = x + 1.0;
    let mut q2 = z * x;
    let mut ans = p2 / q2;

    loop {
        y += 1.0;
        z += 2.0;
        c += 1;
        let yc = y * f64::from(c);

        let p = p2 * z - p3 * yc;
        let q = q2 * z - q3 * yc;

        p3 = p2;
        p2 = p;
        q3 = q2;
        q2 = q;

        if p.abs() > big {
            p3 *= big_inv;
            p2 *= big_inv;
            q3 *= big_inv;
            q2 *= big_inv;
        }

        if q != 0.0 {
            let nextans = p / q;
            let error = ((ans - nextans) / nextans).abs();
            ans = nextans;

            if error <= eps {
                break;
            }
        }
    }
    1.0 - ax.exp() * ans
}
