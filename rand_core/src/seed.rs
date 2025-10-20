/// Trait implemented by types used for seeding PRNG.
///
/// This crate provides implementations for `[u8; N]`, `u32`, `u64`, and `u128`.
pub trait Seed: Sized {
    /// Create seed from a fallible closure which fills the provided buffer.
    fn try_from_bytes<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E>;

    /// Create seed from an infallible closure which fills the provided buffer.
    fn from_bytes(fill: impl FnOnce(&mut [u8])) -> Self {
        let Ok(seed) = Self::try_from_bytes::<core::convert::Infallible>(|buf| {
            fill(buf);
            Ok(())
        });
        seed
    }
}

impl<const N: usize> Seed for [u8; N] {
    fn try_from_bytes<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E> {
        let mut buf = [0u8; N];
        fill(&mut buf)?;
        Ok(buf)
    }
}

impl Seed for u32 {
    fn try_from_bytes<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E> {
        let mut buf = [0u8; 4];
        fill(&mut buf)?;
        Ok(u32::from_le_bytes(buf))
    }
}

impl Seed for u64 {
    fn try_from_bytes<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E> {
        let mut buf = [0u8; 8];
        fill(&mut buf)?;
        Ok(u64::from_le_bytes(buf))
    }
}

impl Seed for u128 {
    fn try_from_bytes<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E> {
        let mut buf = [0u8; 16];
        fill(&mut buf)?;
        Ok(u128::from_le_bytes(buf))
    }
}
