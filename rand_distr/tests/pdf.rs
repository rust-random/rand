// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(clippy::float_cmp)]

use average::Histogram;
use rand::{Rng, SeedableRng};
use rand_distr::{Normal, SkewNormal};

const HIST_LEN: usize = 100;
average::define_histogram!(hist, crate::HIST_LEN);
use hist::Histogram as Histogram100;

mod sparkline;

#[test]
fn normal() {
    const N_SAMPLES: u64 = 1_000_000;
    const MEAN: f64 = 2.;
    const STD_DEV: f64 = 0.5;
    const MIN_X: f64 = -1.;
    const MAX_X: f64 = 5.;

    let dist = Normal::new(MEAN, STD_DEV).unwrap();
    let mut hist = Histogram100::with_const_width(MIN_X, MAX_X);
    let mut rng = rand::rngs::SmallRng::seed_from_u64(1);

    for _ in 0..N_SAMPLES {
        let _ = hist.add(rng.sample(dist)); // Ignore out-of-range values
    }

    println!(
        "Sampled normal distribution:\n{}",
        sparkline::render_u64_as_string(hist.bins())
    );

    fn pdf(x: f64) -> f64 {
        (-0.5 * ((x - MEAN) / STD_DEV).powi(2)).exp()
            / (STD_DEV * (2. * core::f64::consts::PI).sqrt())
    }

    let mut bin_centers = hist.centers();
    let mut expected = [0.; HIST_LEN];
    for e in &mut expected[..] {
        *e = pdf(bin_centers.next().unwrap());
    }

    println!(
        "Expected normal distribution:\n{}",
        sparkline::render_u64_as_string(hist.bins())
    );

    let mut diff = [0.; HIST_LEN];
    for (i, n) in hist.normalized_bins().enumerate() {
        let bin = (n as f64) / (N_SAMPLES as f64);
        diff[i] = (bin - expected[i]).abs();
    }

    println!(
        "Difference:\n{}",
        sparkline::render_f64_as_string(&diff[..])
    );
    println!(
        "max diff: {:?}",
        diff.iter().fold(core::f64::NEG_INFINITY, |a, &b| a.max(b))
    );

    // Check that the differences are significantly smaller than the expected error.
    let mut expected_error = [0.; HIST_LEN];
    // Calculate error from histogram
    for (err, var) in expected_error.iter_mut().zip(hist.variances()) {
        *err = var.sqrt() / (N_SAMPLES as f64);
    }
    // Normalize error by bin width
    for (err, width) in expected_error.iter_mut().zip(hist.widths()) {
        *err /= width;
    }
    // TODO: Calculate error from distribution cutoff / normalization

    println!(
        "max expected_error: {:?}",
        expected_error
            .iter()
            .fold(core::f64::NEG_INFINITY, |a, &b| a.max(b))
    );
    for (&d, &e) in diff.iter().zip(expected_error.iter()) {
        // Difference larger than 3 standard deviations or cutoff
        let tol = (3. * e).max(1e-4);
        assert!(d <= tol, "Difference = {} * tol", d / tol);
    }
}

#[test]
fn skew_normal() {
    const N_SAMPLES: u64 = 1_000_000;
    const LOCATION: f64 = 2.;
    const SCALE: f64 = 0.5;
    const SHAPE: f64 = -3.0;
    const MIN_X: f64 = -1.;
    const MAX_X: f64 = 4.;

    let dist = SkewNormal::new(LOCATION, SCALE, SHAPE).unwrap();
    let mut hist = Histogram100::with_const_width(MIN_X, MAX_X);
    let mut rng = rand::rngs::SmallRng::seed_from_u64(1);

    for _ in 0..N_SAMPLES {
        let _ = hist.add(rng.sample(dist)); // Ignore out-of-range values
    }

    println!(
        "Sampled skew normal distribution:\n{}",
        sparkline::render_u64_as_string(hist.bins())
    );

    use special::Error;
    fn pdf(x: f64) -> f64 {
        let x_normalized = (x - LOCATION) / SCALE;
        let normal_density_x =
            (-0.5 * (x_normalized).powi(2)).exp() / (2. * core::f64::consts::PI).sqrt();
        let normal_distribution_x =
            0.5 * (1.0 + (SHAPE * x_normalized / core::f64::consts::SQRT_2).error());
        2.0 / SCALE * normal_density_x * normal_distribution_x
    }

    let mut bin_centers = hist.centers();
    let mut expected = [0.; HIST_LEN];
    for e in &mut expected[..] {
        *e = pdf(bin_centers.next().unwrap());
    }

    println!(
        "Expected skew normal distribution:\n{}",
        sparkline::render_u64_as_string(hist.bins())
    );

    let mut diff = [0.; HIST_LEN];
    for (i, n) in hist.normalized_bins().enumerate() {
        let bin = (n as f64) / (N_SAMPLES as f64);
        diff[i] = (bin - expected[i]).abs();
    }

    println!(
        "Difference:\n{}",
        sparkline::render_f64_as_string(&diff[..])
    );
    println!(
        "max diff: {:?}",
        diff.iter().fold(core::f64::NEG_INFINITY, |a, &b| a.max(b))
    );

    // Check that the differences are significantly smaller than the expected error.
    let mut expected_error = [0.; HIST_LEN];
    // Calculate error from histogram
    for (err, var) in expected_error.iter_mut().zip(hist.variances()) {
        *err = var.sqrt() / (N_SAMPLES as f64);
    }
    // Normalize error by bin width
    for (err, width) in expected_error.iter_mut().zip(hist.widths()) {
        *err /= width;
    }
    // TODO: Calculate error from distribution cutoff / normalization

    println!(
        "max expected_error: {:?}",
        expected_error
            .iter()
            .fold(core::f64::NEG_INFINITY, |a, &b| a.max(b))
    );
    for (&d, &e) in diff.iter().zip(expected_error.iter()) {
        // Difference larger than 3 standard deviations or cutoff
        let tol = (3. * e).max(1e-4);
        assert!(d <= tol, "Difference = {} * tol", d / tol);
    }
}
