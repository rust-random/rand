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

/// Samples uniformly from the unit disc in two dimensions.
///
/// Implemented via rejection sampling.
///
///
/// # Example
///
/// ```
/// use rand_distr::{UnitDisc, Distribution};
///
/// let v: [f64; 2] = UnitDisc.sample(&mut rand::thread_rng());
/// println!("{:?} is from the unit Disc.", v)
/// ```
#[derive(Clone, Copy, Debug)]
pub struct UnitDisc;

impl<N: Float + SampleUniform> Distribution<[N; 2]> for UnitDisc {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [N; 2] {
        let uniform = Uniform::new(N::from(-1.), N::from(1.));
        let mut x1;
        let mut x2;
        loop {
            x1 = uniform.sample(rng);
            x2 = uniform.sample(rng);
            if x1*x1 + x2*x2 <= N::from(1.) {
                break;
            }
        }
        [x1, x2]
    }
}

#[cfg(test)]
mod tests {
    use crate::Distribution;
    use super::UnitDisc;

    #[test]
    fn value_stability() {
        let mut rng = crate::test::rng(2);
        let expected = [
            [-0.13921053103419823, -0.42140140089381806],
            [0.4245276448803281, -0.7109276652167549],
            [0.6683277779168173, 0.12753134283863998],
        ];
        let samples: [[f64; 2]; 3] = [
                UnitDisc.sample(&mut rng),
                UnitDisc.sample(&mut rng),
                UnitDisc.sample(&mut rng),
            ];
        assert_eq!(samples, expected);
    }
}
