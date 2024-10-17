// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

mod common;
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
pub fn test_discrete<I, D, F>(seed: u64, dist: D, cdf: F)
where
    I: AsPrimitive<f64>,
    D: Distribution<I>,
    F: Fn(i64) -> f64,
{
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
fn skew_normal() {
    fn cdf(x: f64, location: f64, scale: f64, shape: f64) -> f64 {
        let norm = (x - location) / scale;
        phi(norm) - 2.0 * owen_t(norm, shape)
    }

    let parameters = [(0.0, 1.0, 5.0), (1.0, 10.0, -5.0), (-1.0, 0.00001, 0.0)];

    for (seed, (location, scale, shape)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::SkewNormal::new(location, scale, shape).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, location, scale, shape));
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
        (1000.0, 0.01),
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
fn zeta() {
    fn cdf(k: i64, s: f64) -> f64 {
        use common::spec_func::zeta_func;
        if k < 1 {
            return 0.0;
        }

        gen_harmonic(k as u64, s) / zeta_func(s)
    }

    let parameters = [2.0, 3.7, 5.0, 100.0];

    for (seed, s) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Zeta::new(s).unwrap();
        test_discrete(seed as u64, dist, |k| cdf(k, s));
    }
}

#[test]
fn zipf() {
    fn cdf(k: i64, n: u64, s: f64) -> f64 {
        if k < 1 {
            return 0.0;
        }
        if k > n as i64 {
            return 1.0;
        }
        gen_harmonic(k as u64, s) / gen_harmonic(n, s)
    }

    let parameters = [(1000, 1.0), (500, 2.0), (1000, 0.5)];

    for (seed, (n, x)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Zipf::new(n, x).unwrap();
        test_discrete(seed as u64, dist, |k| cdf(k, n, x));
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

    let parameters = [0.1, 1.0, 2.0, 10.0, 100.0, 1000.0];

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
        if (m == 1.0 && x <= 0.0) || x < 0.0 {
            0.0
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

    let parameters = [(0.5, 0.5), (2.0, 3.5), (10.0, 1.0), (100.0, 50.0)];

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
    use rand_distr::Poisson;
    fn cdf(k: i64, lambda: f64) -> f64 {
        use common::spec_func::gamma_lr;

        if k < 0 || lambda <= 0.0 {
            return 0.0;
        }

        1.0 - gamma_lr(k as f64 + 1.0, lambda)
    }
    let parameters = [
        0.1, 1.0, 7.5,
        // 1e9, passed case but too slow
        // 1.844E+19,  // fail case
    ];

    for (seed, lambda) in parameters.into_iter().enumerate() {
        let dist = Poisson::new(lambda).unwrap();
        test_discrete::<f64, Poisson<f64>, _>(seed as u64, dist, |k| cdf(k, lambda));
    }
}

fn ln_factorial(n: u64) -> f64 {
    (n as f64 + 1.0).lgamma().0
}

fn ln_binomial(n: u64, k: u64) -> f64 {
    ln_factorial(n) - ln_factorial(k) - ln_factorial(n - k)
}

fn gen_harmonic(n: u64, m: f64) -> f64 {
    match n {
        0 => 1.0,
        _ => (0..n).fold(0.0, |acc, x| acc + (x as f64 + 1.0).powf(-m)),
    }
}

/// [1] Patefield, M. (2000). Fast and Accurate Calculation of Owen’s T Function.
///     Journal of Statistical Software, 5(5), 1–25.
///     https://doi.org/10.18637/jss.v005.i05
///
/// This function is ported to Rust from the Fortran code provided in the paper
fn owen_t(h: f64, a: f64) -> f64 {
    let absh = h.abs();
    let absa = a.abs();
    let ah = absa * absh;

    let mut t;
    if absa <= 1.0 {
        t = tf(absh, absa, ah);
    } else if absh <= 0.67 {
        t = 0.25 - znorm1(absh) * znorm1(ah) - tf(ah, 1.0 / absa, absh);
    } else {
        let normh = znorm2(absh);
        let normah = znorm2(ah);
        t = 0.5 * (normh + normah) - normh * normah - tf(ah, 1.0 / absa, absh);
    }

    if a < 0.0 {
        t = -t;
    }

    fn tf(h: f64, a: f64, ah: f64) -> f64 {
        let rtwopi = 0.159_154_943_091_895_35;
        let rrtpi = 0.398_942_280_401_432_7;

        let c2 = [
            0.999_999_999_999_999_9,
            -0.999_999_999_999_888,
            0.999_999_999_982_907_5,
            -0.999_999_998_962_825,
            0.999_999_966_604_593_7,
            -0.999_999_339_862_724_7,
            0.999_991_256_111_369_6,
            -0.999_917_776_244_633_8,
            0.999_428_355_558_701_4,
            -0.996_973_117_207_23,
            0.987_514_480_372_753,
            -0.959_158_579_805_728_8,
            0.892_463_055_110_067_1,
            -0.768_934_259_904_64,
            0.588_935_284_684_846_9,
            -0.383_803_451_604_402_55,
            0.203_176_017_010_453,
            -8.281_363_160_700_499e-2,
            2.416_798_473_575_957_8e-2,
            -4.467_656_666_397_183e-3,
            3.914_116_940_237_383_6e-4,
        ];

        let pts = [
            3.508_203_967_645_171_6e-3,
            3.127_904_233_803_075_6e-2,
            8.526_682_628_321_945e-2,
            0.162_450_717_308_122_77,
            0.258_511_960_491_254_36,
            0.368_075_538_406_975_3,
            0.485_010_929_056_047,
            0.602_775_141_526_185_7,
            0.714_778_842_177_532_3,
            0.814_755_109_887_601,
            0.897_110_297_559_489_7,
            0.957_238_080_859_442_6,
            0.991_788_329_746_297,
        ];

        let wts = [
            1.883_143_811_532_350_3e-2,
            1.856_708_624_397_765e-2,
            1.804_209_346_122_338_5e-2,
            1.726_382_960_639_875_2e-2,
            1.624_321_997_598_985_8e-2,
            1.499_459_203_411_670_5e-2,
            1.353_547_446_966_209e-2,
            1.188_635_160_582_016_5e-2,
            1.007_037_724_277_743_2e-2,
            8.113_054_574_229_958e-3,
            6.041_900_952_847_024e-3,
            3.886_221_701_074_205_7e-3,
            1.679_303_108_454_609e-3,
        ];

        let hrange = [
            0.02, 0.06, 0.09, 0.125, 0.26, 0.4, 0.6, 1.6, 1.7, 2.33, 2.4, 3.36, 3.4, 4.8,
        ];
        let arange = [0.025, 0.09, 0.15, 0.36, 0.5, 0.9, 0.99999];

        let select = [
            [1, 1, 2, 13, 13, 13, 13, 13, 13, 13, 13, 16, 16, 16, 9],
            [1, 2, 2, 3, 3, 5, 5, 14, 14, 15, 15, 16, 16, 16, 9],
            [2, 2, 3, 3, 3, 5, 5, 15, 15, 15, 15, 16, 16, 16, 10],
            [2, 2, 3, 5, 5, 5, 5, 7, 7, 16, 16, 16, 16, 16, 10],
            [2, 3, 3, 5, 5, 6, 6, 8, 8, 17, 17, 17, 12, 12, 11],
            [2, 3, 5, 5, 5, 6, 6, 8, 8, 17, 17, 17, 12, 12, 12],
            [2, 3, 4, 4, 6, 6, 8, 8, 17, 17, 17, 17, 17, 12, 12],
            [2, 3, 4, 4, 6, 6, 18, 18, 18, 18, 17, 17, 17, 12, 12],
        ];

        let ihint = hrange.iter().position(|&r| h < r).unwrap_or(14);

        let iaint = arange.iter().position(|&r| a < r).unwrap_or(7);

        let icode = select[iaint][ihint];
        let m = [
            2, 3, 4, 5, 7, 10, 12, 18, 10, 20, 30, 20, 4, 7, 8, 20, 13, 0,
        ][icode - 1];
        let method = [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4, 4, 4, 5, 6][icode - 1];

        match method {
            1 => {
                let hs = -0.5 * h * h;
                let dhs = hs.exp();
                let as_ = a * a;
                let mut j = 1;
                let mut jj = 1;
                let mut aj = rtwopi * a;
                let mut tf = rtwopi * a.atan();
                let mut dj = dhs - 1.0;
                let mut gj = hs * dhs;
                loop {
                    tf += dj * aj / (jj as f64);
                    if j >= m {
                        return tf;
                    }
                    j += 1;
                    jj += 2;
                    aj *= as_;
                    dj = gj - dj;
                    gj *= hs / (j as f64);
                }
            }
            2 => {
                let maxii = m + m + 1;
                let mut ii = 1;
                let mut tf = 0.0;
                let hs = h * h;
                let as_ = -a * a;
                let mut vi = rrtpi * a * (-0.5 * ah * ah).exp();
                let mut z = znorm1(ah) / h;
                let y = 1.0 / hs;
                loop {
                    tf += z;
                    if ii >= maxii {
                        tf *= rrtpi * (-0.5 * hs).exp();
                        return tf;
                    }
                    z = y * (vi - (ii as f64) * z);
                    vi *= as_;
                    ii += 2;
                }
            }
            3 => {
                let mut i = 1;
                let mut ii = 1;
                let mut tf = 0.0;
                let hs = h * h;
                let as_ = a * a;
                let mut vi = rrtpi * a * (-0.5 * ah * ah).exp();
                let mut zi = znorm1(ah) / h;
                let y = 1.0 / hs;
                loop {
                    tf += zi * c2[i - 1];
                    if i > m {
                        tf *= rrtpi * (-0.5 * hs).exp();
                        return tf;
                    }
                    zi = y * ((ii as f64) * zi - vi);
                    vi *= as_;
                    i += 1;
                    ii += 2;
                }
            }
            4 => {
                let maxii = m + m + 1;
                let mut ii = 1;
                let mut tf = 0.0;
                let hs = h * h;
                let as_ = -a * a;
                let mut ai = rtwopi * a * (-0.5 * hs * (1.0 - as_)).exp();
                let mut yi = 1.0;
                loop {
                    tf += ai * yi;
                    if ii >= maxii {
                        return tf;
                    }
                    ii += 2;
                    yi = (1.0 - hs * yi) / (ii as f64);
                    ai *= as_;
                }
            }
            5 => {
                let mut tf = 0.0;
                let as_ = a * a;
                let hs = -0.5 * h * h;
                for i in 0..m {
                    let r = 1.0 + as_ * pts[i];
                    tf += wts[i] * (hs * r).exp() / r;
                }
                tf *= a;
                tf
            }
            6 => {
                let normh = znorm2(h);
                let mut tf = 0.5 * normh * (1.0 - normh);
                let y = 1.0 - a;
                let r = (y / (1.0 + a)).atan();
                if r != 0.0 {
                    tf -= rtwopi * r * (-0.5 * y * h * h / r).exp();
                }
                tf
            }
            _ => 0.0,
        }
    }

    // P(0 ≤ Z ≤ x)
    fn znorm1(x: f64) -> f64 {
        phi(x) - 0.5
    }

    // P(x ≤ Z < ∞)
    fn znorm2(x: f64) -> f64 {
        1.0 - phi(x)
    }

    t
}

/// standard normal cdf
fn phi(x: f64) -> f64 {
    normal_cdf(x, 0.0, 1.0)
}
