// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rand::Rng;
use crate::{Distribution, Uniform, uniform::SampleUniform};
use crate::utils::Float;

/// Samples uniformly from the unit ball (surface and interior) in three
/// dimensions.
///
/// Implemented via rejection sampling.
///
///
/// # Example
///
/// ```
/// use rand_distr::{UnitBall, Distribution};
///
/// let v: [f64; 3] = UnitBall.sample(&mut rand::thread_rng());
/// println!("{:?} is from the unit ball.", v)
/// ```
#[derive(Clone, Copy, Debug)]
pub struct UnitBall;

impl<N: Float + SampleUniform> Distribution<[N; 3]> for UnitBall {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [N; 3] {
        let uniform = Uniform::new(N::from(-1.), N::from(1.));
        let mut x1;
        let mut x2;
        let mut x3;
        loop {
            x1 = uniform.sample(rng);
            x2 = uniform.sample(rng);
            x3 = uniform.sample(rng);
            if x1*x1 + x2*x2 + x3*x3 <= N::from(1.) {
                break;
            }
        }
        [x1, x2, x3]
    }
}

#[cfg(test)]
mod tests {
    use crate::Distribution;
    use super::UnitBall;

    #[test]
    fn value_stability() {
        let mut rng = crate::test::rng(2);
        let expected = [
                [0.018035709265959987, -0.4348771383120438, -0.07982762085055706],
                [0.10588569388223945, -0.4734350111375454, -0.7392104908825501],
                [0.11060237642041049, -0.16065642822852677, -0.8444043930440075]
            ];
        let samples: [[f64; 3]; 3] = [
                UnitBall.sample(&mut rng),
                UnitBall.sample(&mut rng),
                UnitBall.sample(&mut rng),
            ];
        assert_eq!(samples, expected);
    }
}
