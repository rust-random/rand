/// Trait implemented by types used for seeding PRNG.
///
/// This crate provides implementations for `[u8; N]`, `u32`, `u64`, and `u128`.
pub trait Seed: Sized {
    /// Create seed from a fallible closure which fills the provided buffer.
    fn try_from_fill<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E>;

    /// Create seed from an infallible closure which fills the provided buffer.
    fn from_fill(fill: impl FnOnce(&mut [u8])) -> Self {
        let Ok(seed) = Self::try_from_fill::<core::convert::Infallible>(|buf| {
            fill(buf);
            Ok(())
        });
        seed
    }
}

impl<const N: usize> Seed for [u8; N] {
    fn try_from_fill<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E> {
        let mut buf = [0u8; N];
        fill(&mut buf)?;
        Ok(buf)
    }
}

macro_rules! impl_un {
    ($($t:ty)*) => {
        $(
            impl Seed for $t {
                fn try_from_fill<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E> {
                    let mut buf = [0u8; size_of::<$t>()];
                    fill(&mut buf)?;
                    Ok(<$t>::from_le_bytes(buf))
                }
            }
        )*
    };
}

impl_un!(u8 u16 u32 u64 u128);

macro_rules! impl_array_un {
    ($($t:ty)*) => {
        $(
            impl<const N: usize> Seed for [$t; N] {
                fn try_from_fill<E>(fill: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<Self, E> {
                    let mut buf: [$t; N] = [0; N];

                    {
                        let byte_size = size_of_val(&buf);
                        // SAFETY: it's safe to case `&mut [uM; N]` to `&mut [u8]`
                        // with size equal to `size_of_val`
                        let bytes_buf: &mut [u8] = unsafe {
                            core::slice::from_raw_parts_mut(
                                buf.as_mut_ptr().cast(),
                                byte_size,
                            )
                        };
                        fill(bytes_buf)?;
                    }

                    for val in &mut buf {
                        *val = val.to_le();
                    }

                    Ok(buf)
                }
            }
        )*
    };
}

impl_array_un!(u16 u32 u64 u128);
