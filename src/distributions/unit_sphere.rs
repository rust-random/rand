use Rng;
use distributions::{Distribution, Uniform};

/// Samples uniformly from the surface of the unit sphere in three dimensions.
///
/// Implemented via a method by Marsaglia[^1].
///
///
/// # Example
///
/// ```
/// use rand::distributions::{UnitSphereSurface, Distribution};
///
/// let sphere = UnitSphereSurface::new();
/// let v = sphere.sample(&mut rand::thread_rng());
/// println!("{:?} is from the unit sphere surface.", v)
/// ```
///
/// [^1]: Marsaglia, George (1972). [*Choosing a Point from the Surface of a
///       Sphere.*](https://doi.org/10.1214/aoms/1177692644)
///       Ann. Math. Statist. 43 (1972), no. 2, 645--646.
#[derive(Clone, Copy, Debug)]
pub struct UnitSphereSurface {
    uniform: Uniform<f64>,
}

impl UnitSphereSurface {
    /// Construct a new `UnitSphereSurface` distribution.
    #[inline]
    pub fn new() -> UnitSphereSurface {
        UnitSphereSurface { uniform: Uniform::new(-1., 1.) }
    }
}

impl Distribution<[f64; 3]> for UnitSphereSurface {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [f64; 3] {
        loop {
            let (x1, x2) = (self.uniform.sample(rng), self.uniform.sample(rng));
            let sum = x1*x1 + x2*x2;
            if sum >= 1. {
                continue;
            }
            let factor = 2. * (1.0_f64 - sum).sqrt();
            return [x1 * factor, x2 * factor, 1. - 2.*sum];
        }
    }
}

#[cfg(test)]
mod tests {
    use distributions::Distribution;
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
        let mut rng = ::test::rng(1);
        let dist = UnitSphereSurface::new();
        for _ in 0..1000 {
            let x = dist.sample(&mut rng);
            assert_almost_eq!(x[0]*x[0] + x[1]*x[1] + x[2]*x[2], 1., 1e-15);
        }
    }

    #[test]
    fn value_stability() {
        let mut rng = ::test::rng(2);
        let dist = UnitSphereSurface::new();
        assert_eq!(dist.sample(&mut rng),
                   [0.1660727273690104, 0.5202698793511903, 0.8376986939610902]);
        assert_eq!(dist.sample(&mut rng),
                   [0.40052443371799834, 0.4237054996596154, -0.812436968356975]);
        assert_eq!(dist.sample(&mut rng),
                   [0.9209910250970449, -0.32692477745072107, 0.21188610520628948]);
    }
}
