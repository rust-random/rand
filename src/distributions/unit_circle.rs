use Rng;
use distributions::{Distribution, Uniform};

/// Samples uniformly from the edge of the unit circle in two dimensions.
///
/// Implemented via a method by von Neumann[^1].
///
///
/// # Example
///
/// ```
/// use rand::distributions::{UnitCircle, Distribution};
///
/// let circle = UnitCircle::new();
/// let v = circle.sample(&mut rand::thread_rng());
/// println!("{:?} is from the unit circle.", v)
/// ```
///
/// [^1]: von Neumann, J. (1951) [*Various Techniques Used in Connection with
///       Random Digits.*](https://mcnp.lanl.gov/pdf_files/nbs_vonneumann.pdf)
///       NBS Appl. Math. Ser., No. 12. Washington, DC: U.S. Government Printing
///       Office, pp. 36-38.
#[derive(Clone, Copy, Debug)]
pub struct UnitCircle {
    uniform: Uniform<f64>,
}

impl UnitCircle {
    /// Construct a new `UnitCircle` distribution.
    #[inline]
    pub fn new() -> UnitCircle {
        UnitCircle { uniform: Uniform::new(-1., 1.) }
    }
}

impl Distribution<[f64; 2]> for UnitCircle {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [f64; 2] {
        let mut x1;
        let mut x2;
        let mut sum;
        loop {
            x1 = self.uniform.sample(rng);
            x2 = self.uniform.sample(rng);
            sum = x1*x1 + x2*x2;
            if sum < 1. {
                break;
            }
        }
        let diff = x1*x1 - x2*x2;
        [diff / sum, 2.*x1*x2 / sum]
    }
}

#[cfg(test)]
mod tests {
    use distributions::Distribution;
    use super::UnitCircle;

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
        let dist = UnitCircle::new();
        for _ in 0..1000 {
            let x = dist.sample(&mut rng);
            assert_almost_eq!(x[0]*x[0] + x[1]*x[1], 1., 1e-15);
        }
    }

    #[test]
    fn value_stability() {
        let mut rng = ::test::rng(2);
        let dist = UnitCircle::new();
        assert_eq!(dist.sample(&mut rng), [-0.8150602311723979, 0.5793762331690843]);
        assert_eq!(dist.sample(&mut rng), [-0.056204569973983196, 0.998419273809375]);
        assert_eq!(dist.sample(&mut rng), [0.7761923749562624, -0.630496151502733]);
    }
}
