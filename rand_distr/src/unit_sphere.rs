// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rand::Rng;
use crate::{Distribution, Uniform, uniform::SampleUniform};
use crate::utils::Float;

/// Samples uniformly from the surface of the unit sphere in three dimensions.
///
/// Implemented via a method by Marsaglia[^1].
///
///
/// # Example
///
/// ```
/// use rand_distr::{UnitSphereSurface, Distribution};
///
/// let v: [f64; 3] = UnitSphereSurface.sample(&mut rand::thread_rng());
/// println!("{:?} is from the unit sphere surface.", v)
/// ```
///
/// [^1]: Marsaglia, George (1972). [*Choosing a Point from the Surface of a
///       Sphere.*](https://doi.org/10.1214/aoms/1177692644)
///       Ann. Math. Statist. 43, no. 2, 645--646.
#[derive(Clone, Copy, Debug)]
pub struct UnitSphereSurface;

impl<N: Float + SampleUniform> Distribution<[N; 3]> for UnitSphereSurface {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [N; 3] {
        let uniform = Uniform::new(N::from(-1.), N::from(1.));
        loop {
            let (x1, x2) = (uniform.sample(rng), uniform.sample(rng));
            let sum = x1*x1 + x2*x2;
            if sum >= N::from(1.) {
                continue;
            }
            let factor = N::from(2.) * (N::from(1.0) - sum).sqrt();
            return [x1 * factor, x2 * factor, N::from(1.) - N::from(2.)*sum];
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Distribution;
    use super::UnitSphereSurface;

    /// Assert that two numbers are almost equal to each other.
    ///
    /// On panic, this macro will print the values of the expressions with their
    /// debug representations.
    macro_rules! assert_almost_eq {
        ($a:expr, $b:expr, $prec:expr) => (
            let diff = ($a - $b).abs();
            if diff > $prec {
                panic!(format!(
                    "assertion failed: `abs(left - right) = {:.1e} < {:e}`, \
                     (left: `{}`, right: `{}`)",
                    diff, $prec, $a, $b));
            }
        );
    }

    #[test]
    fn norm() {
        let mut rng = crate::test::rng(1);
        for _ in 0..1000 {
            let x: [f64; 3] = UnitSphereSurface.sample(&mut rng);
            assert_almost_eq!(x[0]*x[0] + x[1]*x[1] + x[2]*x[2], 1., 1e-15);
        }
    }

    #[test]
    fn value_stability() {
        let mut rng = crate::test::rng(2);
        let expected = [
                [-0.24950027180862533, -0.7552572587896719, 0.6060825747478084],
                [0.47604534507233487, -0.797200864987207, -0.3712837328763685],
                [0.9795722330927367, 0.18692349236651176, 0.07414747571708524],
            ];
        let samples: [[f64; 3]; 3] = [
                UnitSphereSurface.sample(&mut rng),
                UnitSphereSurface.sample(&mut rng),
                UnitSphereSurface.sample(&mut rng),
            ];
        assert_eq!(samples, expected);
    }
}
