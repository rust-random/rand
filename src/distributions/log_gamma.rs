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
/// function) using the Lanczos approximation.
///
/// The approximation expresses the gamma function as:
/// `gamma(z+1) = sqrt(2*pi)*(z+g+0.5)^(z+0.5)*exp(-z-g-0.5)*Ag(z)`
/// `g` is an arbitrary constant; we use the approximation with `g=5`.
///
/// Noting that `gamma(z+1) = z*gamma(z)` and applying `ln` to both sides:
/// `ln(gamma(z)) = (z+0.5)*ln(z+g+0.5)-(z+g+0.5) + ln(sqrt(2*pi)*Ag(z)/z)`
///
/// `Ag(z)` is an infinite series with coefficients that can be calculated
/// ahead of time - we use just the first 6 terms, which is good enough
/// for most purposes.
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

    // (x+0.5)*ln(x+g+0.5)-(x+g+0.5)
    let tmp = x + 5.5;
    let log = (x + 0.5) * tmp.ln() - tmp;

    // the first few terms of the series for Ag(x)
    let mut a = 1.000000000190015;
    let mut denom = x;
    for coeff in &coefficients {
        denom += 1.0;
        a += coeff / denom;
    }

    // get everything together
    // a is Ag(x)
    // 2.5066... is sqrt(2pi)
    log + (2.5066282746310005 * a / x).ln()
}
