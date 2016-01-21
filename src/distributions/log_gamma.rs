// Copyright 2016-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Calculates ln(gamma(x)) (natural logarithm of the gamma
/// function) using the Lanczos approximation with g=5
pub fn log_gamma(x: f64) -> f64 {
    // precalculated 6 coefficients for the first 6 terms of the series
    let coefficients: [f64; 6] = [
        76.18009172947146,
        -86.50532032941677,
        24.01409824083091,
        -1.231739572450155,
        0.1208650973866179e-2,
        -0.5395239384953e-5,
    ];

    // ln((x+g+0.5)^(x+0.5)*exp(-(x+g+0.5)))
    let tmp = x + 5.5;
    let log = (x + 0.5) * tmp.ln() - tmp;

    // the first few terms of the series
    let mut a = 1.000000000190015;
    let mut denom = x;
    for j in 0..6 {
        denom += 1.0;
        a += coefficients[j] / denom;
    }

    // get everything together
    // division by x is because the series is actually for gamma(x+1) = x*gamma(x)
    return log + (2.5066282746310005 * a / x).ln();
}
