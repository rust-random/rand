//! The Bernoulli distribution.

use Rng;
use distributions::Distribution;

/// The Bernoulli distribution.
///
/// This is a special case of the Binomial distribution where `n = 1`.
///
/// # Example
///
/// ```rust
/// use rand::distributions::{Bernoulli, Distribution};
///
/// let d = Bernoulli::new(0.3);
/// let v: u64 = d.sample(&mut rand::thread_rng());
/// println!("{} is from a Bernoulli distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Bernoulli {
    /// Probability of success.
    p: f64,
}

impl Bernoulli {
    /// Construct a new `Bernoulli` with the given probability of success `p`.
    ///
    /// # Panics
    ///
    /// If `p < 0` or `p > 1`.
    #[inline]
    pub fn new(p: f64) -> Bernoulli {
        assert!(p >= 0.0, "Bernoulli::new called with p < 0");
        assert!(p <= 1.0, "Bernoulli::new called with p > 1");
        Bernoulli { p }
    }
}

impl Distribution<bool> for Bernoulli {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> bool {
        rng.gen_bool(self.p)
    }
}

macro_rules! impl_bernoulli_int {
    ($($t: ty), *) => {
        $(
            impl Distribution<$t> for Bernoulli {
                #[inline]
                fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $t {
                    rng.gen_bool(self.p) as $t
                }
            }
        )*
    }
}

impl_bernoulli_int!(u8, u16, u32, u64, i8, i16, i32, i64);

macro_rules! impl_bernoulli_float {
    ($($t: ty), *) => {
        $(
            impl Distribution<$t> for Bernoulli {
                #[inline]
                fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $t {
                    rng.gen_bool(self.p) as u8 as $t
                }
            }
        )*
    }
}

impl_bernoulli_float!(f32, f64);

#[cfg(test)]
mod test {
    use {Rng, SmallRng, FromEntropy};
    use distributions::Distribution;
    use super::Bernoulli;

    #[test]
    fn test_trivial() {
        let mut r = SmallRng::from_entropy();
        let always_false = Bernoulli::new(0.0);
        let always_true = Bernoulli::new(1.0);
        for _ in 0..5 {
            assert_eq!(r.sample::<bool, _>(&always_false), false);
            assert_eq!(r.sample::<bool, _>(&always_true), true);
            assert_eq!(Distribution::<bool>::sample(&always_false, &mut r), false);
            assert_eq!(Distribution::<bool>::sample(&always_true, &mut r), true);
        }
    }

    #[test]
    fn test_average() {
        const P: f64 = 0.3;
        let d = Bernoulli::new(P);
        const N: u32 = 10_000_000;

        let mut sum: u32 = 0;
        let mut rng = SmallRng::from_entropy();
        for _ in 0..N {
            if d.sample(&mut rng) {
                sum += 1;
            }
        }
        let avg = (sum as f64) / (N as f64);

        assert!((avg - P).abs() < 1e-3);
    }

    #[test]
    fn test_nonbool() {

        macro_rules! assert_nonbool {
            ($($t: ty), *) => {
                let d = Bernoulli::new(0.3);
                let r = SmallRng::from_entropy();
                $(
                    assert_eq!(r.clone().sample::<$t, _>(&d) as f64 != 0.,
                               r.clone().sample::<bool, _>(&d));
                )*
            }
        }

        assert_nonbool!(u8, u16, u32, u64, i8, i16, i32, i64, f32, f64);
    }
}
