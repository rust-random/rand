// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::f64;

use special::{Beta, Gamma, Primitive};
use statrs::distribution::ContinuousCDF;
use statrs::distribution::DiscreteCDF;

mod ks;
use ks::test_continuous;
use ks::test_discrete;

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
        test_continuous(seed as u64, rand_distr::Normal::new(mean, std_dev).unwrap(), |x| {
            statrs::distribution::Normal::new(mean, std_dev)
                .unwrap()
                .cdf(x)
        });
    }
}


#[test]
fn cauchy() {
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
        test_continuous(seed as u64, dist, |x| {
            statrs::distribution::Cauchy::new(median, scale)
                .unwrap()
                .cdf(x)
        });
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
    let parameters = [
        (0.0, 1.0),
        (0.0, 0.1),
        (0.5, 0.7),
        (1.0, 10.0),
        (1.0, 100.0),
    ];

    for (seed, (mean, std_dev)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::LogNormal::new(mean, std_dev).unwrap();
        test_continuous(seed as u64, dist, |x| {
            statrs::distribution::LogNormal::new(mean, std_dev)
                .unwrap()
                .cdf(x)
        });
    }
}

#[test]
fn pareto() {
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
        test_continuous(seed as u64, dist, |x| {
            statrs::distribution::Pareto::new(scale, alpha)
                .unwrap()
                .cdf(x)
        });
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
        use spfunc::zeta::zeta as zeta_func;
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
        let dist = rand_distr::Zipf::new(n as f64, x).unwrap();
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
        (100, 50, 49),
    ];

    for (seed, (n, k, n_)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::Hypergeometric::new(n, k, n_).unwrap();
        test_discrete(seed as u64, dist, |x| cdf(x, n, k, n_));
    }
}

#[test]
fn poisson() {
    use rand_distr::Poisson;
    let parameters = [
        0.1, 1.0, 7.5, 45.0
        // 1e9, passed case but too slow
        // 1.844E+19,  // fail case
    ];

    for (seed, lambda) in parameters.into_iter().enumerate() {
        let dist = Poisson::new(lambda).unwrap();
        let analytic = statrs::distribution::Poisson::new(lambda).unwrap();
        test_discrete::<f64, Poisson<f64>, _>(seed as u64, dist, |k| {
            if k < 0 {
                0.0
            } else {
                analytic.cdf(k as u64)
            }
        });
    }
}

fn ln_factorial(n: u64) -> f64 {
    (n as f64 + 1.0).lgamma().0
}

fn ln_binomial(n: u64, k: u64) -> f64 {
    ln_factorial(n) - ln_factorial(k) - ln_factorial(n - k)
}


