// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The implementations of `Rand` for the built-in types.

use std::borrow::Cow;
use std::cell::{Cell, RefCell};
use std::char;
use std::cmp::Ordering;
use std::marker::PhantomData;
use std::mem;
use std::net::{Ipv4Addr, Ipv6Addr};

use std::num::Wrapping;
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::rc::Rc;
use std::sync::Arc;

#[cfg(feature = "duration")]
use std::time::Duration;
#[cfg(feature = "ip_addr")]
use std::net::IpAddr;
#[cfg(feature = "bound")]
use std::collections::Bound;

use {Rand,Rng};

impl Rand for isize {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> isize {
        if mem::size_of::<isize>() == 4 {
            rng.gen::<i32>() as isize
        } else {
            rng.gen::<i64>() as isize
        }
    }
}

impl Rand for i8 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> i8 {
        rng.next_u32() as i8
    }
}

impl Rand for i16 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> i16 {
        rng.next_u32() as i16
    }
}

impl Rand for i32 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> i32 {
        rng.next_u32() as i32
    }
}

impl Rand for i64 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> i64 {
        rng.next_u64() as i64
    }
}

#[cfg(feature = "i128_support")]
impl Rand for i128 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> i128 {
        rng.gen::<u128>() as i128
    }
}

impl Rand for usize {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> usize {
        if mem::size_of::<usize>() == 4 {
            rng.gen::<u32>() as usize
        } else {
            rng.gen::<u64>() as usize
        }
    }
}

impl Rand for u8 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> u8 {
        rng.next_u32() as u8
    }
}

impl Rand for u16 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> u16 {
        rng.next_u32() as u16
    }
}

impl Rand for u32 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> u32 {
        rng.next_u32()
    }
}

impl Rand for u64 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> u64 {
        rng.next_u64()
    }
}

#[cfg(feature = "i128_support")]
impl Rand for u128 {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> u128 {
        ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128)
    }
}

impl<T: Rand> Rand for Wrapping<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Wrapping<T> {
        Wrapping(rng.gen())
    }
}


macro_rules! float_impls {
    ($mod_name:ident, $ty:ty, $mantissa_bits:expr, $method_name:ident) => {
        mod $mod_name {
            use {Rand, Rng, Open01, Closed01};

            const SCALE: $ty = (1u64 << $mantissa_bits) as $ty;

            impl Rand for $ty {
                /// Generate a floating point number in the half-open
                /// interval `[0,1)`.
                ///
                /// See `Closed01` for the closed interval `[0,1]`,
                /// and `Open01` for the open interval `(0,1)`.
                #[inline]
                fn rand<R: Rng>(rng: &mut R) -> $ty {
                    rng.$method_name()
                }
            }
            impl Rand for Open01<$ty> {
                #[inline]
                fn rand<R: Rng>(rng: &mut R) -> Open01<$ty> {
                    // add a small amount (specifically 2 bits below
                    // the precision of f64/f32 at 1.0), so that small
                    // numbers are larger than 0, but large numbers
                    // aren't pushed to/above 1.
                    Open01(rng.$method_name() + 0.25 / SCALE)
                }
            }
            impl Rand for Closed01<$ty> {
                #[inline]
                fn rand<R: Rng>(rng: &mut R) -> Closed01<$ty> {
                    // rescale so that 1.0 - epsilon becomes 1.0
                    // precisely.
                    Closed01(rng.$method_name() * SCALE / (SCALE - 1.0))
                }
            }
        }
    }
}
float_impls! { f64_rand_impls, f64, 53, next_f64 }
float_impls! { f32_rand_impls, f32, 24, next_f32 }

impl<T: ?Sized> Rand for PhantomData<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> PhantomData<T> {
        PhantomData
    }
}

impl Rand for char {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> char {
        // a char is 21 bits
        const CHAR_MASK: u32 = 0x001f_ffff;
        loop {
            // Rejection sampling. About 0.2% of numbers with at most
            // 21-bits are invalid codepoints (surrogates), so this
            // will succeed first go almost every time.
            match char::from_u32(rng.next_u32() & CHAR_MASK) {
                Some(c) => return c,
                None => {}
            }
        }
    }
}

impl Rand for bool {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> bool {
        rng.gen::<u8>() & 1 == 1
    }
}

impl Rand for Ordering {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Ordering {
        match rng.gen_range(0, 3) {
            0 => Ordering::Less,
            1 => Ordering::Equal,
            2 => Ordering::Greater,
            _ => unreachable!(),
        }
    }
}

#[cfg(feature = "duration")]
impl Rand for Duration {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Duration {
        Duration::new(rng.gen(), rng.gen_range(0, 1_000_000_000))
    }
}

impl Rand for RangeFull {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> RangeFull {
        ..
    }
}

impl<T: Rand + PartialOrd> Rand for Range<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Range<T> {
        Range { start: rng.gen(), end: rng.gen() }
    }
}

impl<T: Rand> Rand for RangeFrom<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> RangeFrom<T> {
        RangeFrom { start: rng.gen() }
    }
}

impl<T: Rand> Rand for RangeTo<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> RangeTo<T> {
        RangeTo { end: rng.gen() }
    }
}

#[cfg(feature = "bound")]
impl<T: Rand> Rand for Bound<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Bound<T> {
        match rng.gen_range(0, 3) {
            0 => Bound::Included(rng.gen()),
            1 => Bound::Excluded(rng.gen()),
            2 => Bound::Unbounded,
            _ => unreachable!(),
        }
    }
}

impl Rand for Ipv4Addr {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Ipv4Addr {
        Ipv4Addr::new(rng.gen(), rng.gen(), rng.gen(), rng.gen())
    }
}

impl Rand for Ipv6Addr {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Ipv6Addr {
        Ipv6Addr::new(rng.gen(), rng.gen(), rng.gen(), rng.gen(),
                      rng.gen(), rng.gen(), rng.gen(), rng.gen())
    }
}

#[cfg(feature = "ip_addr")]
impl Rand for IpAddr {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> IpAddr {
        if rng.gen() {
            IpAddr::V4(rng.gen())
        } else {
            IpAddr::V6(rng.gen())
        }
    }
}

macro_rules! tuple_impl {
    // use variables to indicate the arity of the tuple
    ($($tyvar:ident),* ) => {
        // the trailing commas are for the 1 tuple
        impl<
            $( $tyvar : Rand ),*
            > Rand for ( $( $tyvar ),* , ) {

            #[inline]
            fn rand<R: Rng>(_rng: &mut R) -> ( $( $tyvar ),* , ) {
                (
                    // use the $tyvar's to get the appropriate number of
                    // repeats (they're not actually needed)
                    $(
                        _rng.gen::<$tyvar>()
                    ),*
                    ,
                )
            }
        }
    }
}

impl Rand for () {
    #[inline]
    fn rand<R: Rng>(_: &mut R) -> () { () }
}
tuple_impl!{A}
tuple_impl!{A, B}
tuple_impl!{A, B, C}
tuple_impl!{A, B, C, D}
tuple_impl!{A, B, C, D, E}
tuple_impl!{A, B, C, D, E, F}
tuple_impl!{A, B, C, D, E, F, G}
tuple_impl!{A, B, C, D, E, F, G, H}
tuple_impl!{A, B, C, D, E, F, G, H, I}
tuple_impl!{A, B, C, D, E, F, G, H, I, J}
tuple_impl!{A, B, C, D, E, F, G, H, I, J, K}
tuple_impl!{A, B, C, D, E, F, G, H, I, J, K, L}

macro_rules! array_impl {
    {$n:expr, $t:ident, $($ts:ident,)*} => {
        array_impl!{($n - 1), $($ts,)*}

        impl<T> Rand for [T; $n] where T: Rand {
            #[inline]
            fn rand<R: Rng>(_rng: &mut R) -> [T; $n] {
                [_rng.gen::<$t>(), $(_rng.gen::<$ts>()),*]
            }
        }
    };
    {$n:expr,} => {
        impl<T> Rand for [T; $n] {
            fn rand<R: Rng>(_rng: &mut R) -> [T; $n] { [] }
        }
    };
}

array_impl!{32, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T,}

impl<T: Rand> Rand for Option<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Option<T> {
        if rng.gen() {
            Some(rng.gen())
        } else {
            None
        }
    }
}

impl<T: Rand, E: Rand> Rand for Result<T, E> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Result<T, E> {
        if rng.gen() {
            Ok(rng.gen())
        } else {
            Err(rng.gen())
        }
    }
}

impl<T: Rand> Rand for Box<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Box<T> {
        Box::new(rng.gen())
    }
}

impl<T: Rand> Rand for Rc<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Rc<T> {
        Rc::new(rng.gen())
    }
}

impl<T: Rand> Rand for Arc<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Arc<T> {
        Arc::new(rng.gen())
    }
}

// TODO: remove Copy
impl<T: Copy + Rand> Rand for Cell<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Cell<T> {
        Cell::new(rng.gen())
    }
}

impl<T: Rand> Rand for RefCell<T> {
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> RefCell<T> {
        RefCell::new(rng.gen())
    }
}

impl<'a, T: ToOwned> Rand for Cow<'a, T>
where
    <T as ToOwned>::Owned: Rand
{
    #[inline]
    fn rand<R: Rng>(rng: &mut R) -> Cow<'a, T> {
        Cow::Owned(rng.gen())
    }
}


#[cfg(test)]
mod tests {
    use {Rng, thread_rng, Open01, Closed01};

    struct ConstantRng(u64);
    impl Rng for ConstantRng {
        fn next_u32(&mut self) -> u32 {
            let ConstantRng(v) = *self;
            v as u32
        }
        fn next_u64(&mut self) -> u64 {
            let ConstantRng(v) = *self;
            v
        }
    }

    #[test]
    fn floating_point_edge_cases() {
        // the test for exact equality is correct here.
        assert!(ConstantRng(0xffff_ffff).gen::<f32>() != 1.0);
        assert!(ConstantRng(0xffff_ffff_ffff_ffff).gen::<f64>() != 1.0);
    }

    #[test]
    fn rand_open() {
        // this is unlikely to catch an incorrect implementation that
        // generates exactly 0 or 1, but it keeps it sane.
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let Open01(f) = rng.gen::<Open01<f64>>();
            assert!(0.0 < f && f < 1.0);

            let Open01(f) = rng.gen::<Open01<f32>>();
            assert!(0.0 < f && f < 1.0);
        }
    }

    #[test]
    fn rand_closed() {
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let Closed01(f) = rng.gen::<Closed01<f64>>();
            assert!(0.0 <= f && f <= 1.0);

            let Closed01(f) = rng.gen::<Closed01<f32>>();
            assert!(0.0 <= f && f <= 1.0);
        }
    }
}
