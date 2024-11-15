// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


mod ks;
use ks::test_discrete;

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
        let dist = rand_distr::Zipf::new(n, x).unwrap();
        test_discrete(seed as u64, dist, |k| cdf(k, n, x));
    }
}

fn gen_harmonic(n: u64, m: f64) -> f64 {
    match n {
        0 => 1.0,
        _ => (0..n).fold(0.0, |acc, x| acc + (x as f64 + 1.0).powf(-m)),
    }
}