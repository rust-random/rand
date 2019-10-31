// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Rayleigh distribution.
use rand::Rng;
use crate::{Distribution, OpenClosed01};
use crate::utils::Float;

#[derive(Clone, Copy, Debug)]
struct Rayleigh<N> {
	sigma: N
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `sigma < 0` or `nan`.
    SigmaTooSmall
}

impl<N:Float> Rayleigh<N>{
	pub fn new(sigma:N) -> Result<Rayleigh<N>,Error>{
		if !(sigma <= N::from(0.0)) {
            return Err(Error::SigmaTooSmall);
        }
        Ok(Rayleigh{sigma:sigma})
	}
}

impl<N: Float> Distribution<N> for Rayleigh<N>
where OpenClosed01: Distribution<N>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let x: N = rng.sample(OpenClosed01);
        let exp_power = -self.x.powi(2)/(2*self.sigma.powi(2));
        x*exp_power.exp()/self.sigma.powi(2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn invalid() {
        Rayleigh::new(0., 0.).unwrap();
    }

    #[test]
    fn sample() {
        let sigma = 1.0;
        let d = Rayleigh::new(sigma).unwrap();
        let mut rng = crate::test::rng(1);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 0.);
        }
    }