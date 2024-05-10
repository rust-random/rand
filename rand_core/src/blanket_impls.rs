#[cfg(feature = "alloc")]
use alloc::boxed::Box;

use crate::{CryptoRng, RngCore, TryCryptoRng, TryRngCore};

impl<'a, R: RngCore + ?Sized> RngCore for &'a mut R {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        R::next_u32(self)
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        R::next_u64(self)
    }

    #[inline(always)]
    fn fill_bytes(&mut self, dst: &mut [u8]) {
        R::fill_bytes(self, dst)
    }
}

impl<'a, R: CryptoRng + ?Sized> CryptoRng for &'a mut R {}

impl<'a, R: TryRngCore + ?Sized> TryRngCore for &'a mut R {
    type Error = R::Error;

    #[inline(always)]
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        R::try_next_u32(self)
    }

    #[inline(always)]
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        R::try_next_u64(self)
    }

    #[inline(always)]
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        R::try_fill_bytes(self, dst)
    }
}

impl<'a, R: TryCryptoRng + ?Sized> TryCryptoRng for &'a mut R {}

#[cfg(feature = "alloc")]
impl<R: RngCore + ?Sized> RngCore for Box<R> {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        R::next_u32(self)
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        R::next_u64(self)
    }

    #[inline(always)]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        R::fill_bytes(self, dest)
    }
}

#[cfg(feature = "alloc")]
impl<R: CryptoRng + ?Sized> CryptoRng for Box<R> {}

#[cfg(feature = "alloc")]
impl<R: TryRngCore + ?Sized> TryRngCore for Box<R> {
    type Error = R::Error;

    #[inline(always)]
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        R::try_next_u32(self)
    }

    #[inline(always)]
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        R::try_next_u64(self)
    }

    #[inline(always)]
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        R::try_fill_bytes(self, dst)
    }
}

#[cfg(feature = "alloc")]
impl<R: TryCryptoRng + ?Sized> TryCryptoRng for Box<R> {}
