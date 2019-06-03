// Copyright 2018-2019 Developers of the Rand project.
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
/// use rand_distr::{UnitSphere, Distribution};
///
/// let v: [f64; 3] = UnitSphere.sample(&mut rand::thread_rng());
/// println!("{:?} is from the unit sphere surface.", v)
/// ```
///
/// [^1]: Marsaglia, George (1972). [*Choosing a Point from the Surface of a
///       Sphere.*](https://doi.org/10.1214/aoms/1177692644)
///       Ann. Math. Statist. 43, no. 2, 645--646.
#[derive(Clone, Copy, Debug)]
pub struct UnitSphere;

impl<N: Float + SampleUniform> Distribution<[N; 3]> for UnitSphere {
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
    use super::UnitSphere;

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
            let x: [f64; 3] = UnitSphere.sample(&mut rng);
            assert_almost_eq!(x[0]*x[0] + x[1]*x[1] + x[2]*x[2], 1., 1e-15);
        }
    }

    #[test]
    fn value_stability() {
        let mut rng = crate::test::rng(2);
        let expected = [
                [0.03247542860231647, -0.7830477442152738, 0.6211131755296027],
                [-0.09978440840914075, 0.9706650829833128, -0.21875184231323952],
                [0.2735582468624679, 0.9435374242279655, -0.1868234852870203],
            ];
        let samples: [[f64; 3]; 3] = [
                UnitSphere.sample(&mut rng),
                UnitSphere.sample(&mut rng),
                UnitSphere.sample(&mut rng),
            ];
        assert_eq!(samples, expected);
    }
}
