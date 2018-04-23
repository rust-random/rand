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
/// let v = d.sample(&mut rand::thread_rng());
/// println!("{} is from a Bernoulli distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Bernoulli {
    /// Probability of success, relative to the maximal integer.
    p_int: u64,
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
        let p_int = if p != 1.0 {
            (p * (::core::u64::MAX as f64)) as u64
        } else {
            ::core::u64::MAX
        };
        Bernoulli { p_int }
    }
}

impl Distribution<bool> for Bernoulli {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> bool {
        let r: u64 = rng.gen();
        r <= self.p_int
    }
}

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
}
