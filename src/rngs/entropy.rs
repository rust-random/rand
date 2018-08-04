// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Entropy generator, or wrapper around external generators

use core::fmt;
use std::sync::{Once, Mutex, MutexGuard, ONCE_INIT};
use std::marker::PhantomData;

use rand_core::{RngCore, CryptoRng, Error, ErrorKind, impls};
#[allow(unused)]
use rngs;

/// An interface returning random data from external source(s), provided
/// specifically for securely seeding algorithmic generators (PRNGs).
///
/// Where possible, `EntropyRng` retrieves random data from the operating
/// system's interface for random numbers ([`OsRng`]); if that fails it will
/// fall back to the [`JitterRng`] entropy collector. In the latter case it will
/// still try to use [`OsRng`] on the next usage.
///
/// If no secure source of entropy is available `EntropyRng` will panic on use;
/// i.e. it should never output predictable data.
///
/// This is either a little slow ([`OsRng`] requires a system call) or extremely
/// slow ([`JitterRng`] must use significant CPU time to generate sufficient
/// jitter); for better performance it is common to seed a local PRNG from
/// external entropy then primarily use the local PRNG ([`thread_rng`] is
/// provided as a convenient, local, automatically-seeded CSPRNG).
/// 
/// `EntropyRng` instances are explicitly not `Send` or `Sync`.
///
/// # Panics
///
/// On most systems, like Windows, Linux, macOS and *BSD on common hardware, it
/// is highly unlikely for both [`OsRng`] and [`JitterRng`] to fail. But on
/// combinations like webassembly without Emscripten or stdweb both sources are
/// unavailable. If both sources fail, only [`try_fill_bytes`] is able to
/// report the error, and only the one from `OsRng`. The other [`RngCore`]
/// methods will panic in case of an error.
///
/// [`OsRng`]: struct.OsRng.html
/// [`JitterRng`]: jitter/struct.JitterRng.html
/// [`thread_rng`]: ../fn.thread_rng.html
/// [`RngCore`]: ../trait.RngCore.html
/// [`try_fill_bytes`]: ../trait.RngCore.html#method.tymethod.try_fill_bytes
#[derive(Debug)]
pub struct EntropyRng {
    source: Source,
    _not_send: PhantomData<*mut ()>,    // enforce !Send
}

#[derive(Debug)]
enum Source {
    Os(Os),
    Custom(Custom),
    Jitter(Jitter),
    None,
}

impl EntropyRng {
    /// Create a new `EntropyRng`.
    ///
    /// This method will do no system calls or other initialization routines,
    /// those are done on first use. This is done to make `new` infallible,
    /// and `try_fill_bytes` the only place to report errors.
    pub fn new() -> Self {
        EntropyRng { source: Source::None, _not_send: Default::default() }
    }
}

impl Default for EntropyRng {
    fn default() -> Self {
        EntropyRng::new()
    }
}

impl RngCore for EntropyRng {
    fn next_u32(&mut self) -> u32 {
        impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.try_fill_bytes(dest).unwrap_or_else(|err|
                panic!("all entropy sources failed; first error: {}", err))
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        let mut reported_error = None;
        
        macro_rules! try_source {
            ($source:ident) => {
                if let Source::$source(ref mut inner) = self.source {
                    match inner.fill(dest) {
                        Ok(()) => return Ok(()),
                        Err(err) => {
                            warn!("EntropyRng: source {} failed: {}", $source::name(), err);
                            reported_error = Some(err);
                        },
                    }
                } else if $source::is_available() {
                    match $source::new().and_then(|mut inner|
                        inner.fill(dest).and(Ok(inner)))
                    {
                        Ok(inner) => {
                            debug!("EntropyRng: using source {}", $source::name());
                            self.source = Source::$source(inner);
                            return Ok(());
                        },
                        Err(err) => {
                            reported_error = reported_error.or(Some(err));
                        },
                    }
                }
            }
        }

        try_source!(Os);
        try_source!(Custom);
        try_source!(Jitter);

        if let Some(err) = reported_error {
            Err(Error::with_cause(ErrorKind::Unavailable,
                                  "All entropy sources failed",
                                  err))
        } else {
            Err(Error::new(ErrorKind::Unavailable,
                           "No entropy sources available"))
        }
    }
}

impl CryptoRng for EntropyRng {}



trait EntropySource {
    /// Name of this source
    fn name() -> &'static str;
    
    /// Is this source available?
    fn is_available() -> bool;
    
    /// Create an instance
    fn new() -> Result<Self, Error> where Self: Sized;

    /// Fill `dest` with random data from the entropy source
    fn fill(&mut self, dest: &mut [u8]) -> Result<(), Error>;
}

#[allow(unused)]
#[derive(Clone, Debug)]
struct NoSource;

#[allow(unused)]
impl EntropySource for NoSource {
    fn name() -> &'static str { unreachable!() }
    fn is_available() -> bool { false }
    
    fn new() -> Result<Self, Error> {
        Err(Error::new(ErrorKind::Unavailable, "Source not supported"))
    }

    fn fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        unreachable!()
    }
}


#[cfg(all(feature="std",
          any(target_os = "linux", target_os = "android",
              target_os = "netbsd",
              target_os = "dragonfly",
              target_os = "haiku",
              target_os = "emscripten",
              target_os = "solaris",
              target_os = "cloudabi",
              target_os = "macos", target_os = "ios",
              target_os = "freebsd",
              target_os = "openbsd", target_os = "bitrig",
              target_os = "redox",
              target_os = "fuchsia",
              windows,
              all(target_arch = "wasm32", feature = "stdweb"),
              all(target_arch = "wasm32", feature = "wasm-bindgen"),
)))]
#[derive(Clone, Debug)]
pub struct Os(rngs::OsRng);

#[cfg(all(feature="std",
          any(target_os = "linux", target_os = "android",
              target_os = "netbsd",
              target_os = "dragonfly",
              target_os = "haiku",
              target_os = "emscripten",
              target_os = "solaris",
              target_os = "cloudabi",
              target_os = "macos", target_os = "ios",
              target_os = "freebsd",
              target_os = "openbsd", target_os = "bitrig",
              target_os = "redox",
              target_os = "fuchsia",
              windows,
              all(target_arch = "wasm32", feature = "stdweb"),
              all(target_arch = "wasm32", feature = "wasm-bindgen"),
)))]
impl EntropySource for Os {
    fn name() -> &'static str { "OsRng" }
    
    fn is_available() -> bool { true }

    fn new() -> Result<Self, Error> {
        Ok(Os(rngs::OsRng::new()?))
    }

    fn fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

#[cfg(not(all(feature="std",
              any(target_os = "linux", target_os = "android",
                  target_os = "netbsd",
                  target_os = "dragonfly",
                  target_os = "haiku",
                  target_os = "emscripten",
                  target_os = "solaris",
                  target_os = "cloudabi",
                  target_os = "macos", target_os = "ios",
                  target_os = "freebsd",
                  target_os = "openbsd", target_os = "bitrig",
                  target_os = "redox",
                  target_os = "fuchsia",
                  windows,
                  all(target_arch = "wasm32", feature = "stdweb"),
                  all(target_arch = "wasm32", feature = "wasm-bindgen"),
))))]
type Os = NoSource;

#[derive(Clone)]
struct Custom {
    source: &'static CustomEntropySource,
    param: u64,
    _not_send: PhantomData<*mut ()>,    // enforce !Send
}

impl fmt::Debug for Custom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Custom {{ ... }}")
    }
}

#[test]
fn test_size() {
    use core::mem::size_of;
    println!("Size of Custom: {}", size_of::<Custom>());
    assert!(size_of::<Custom>() <= size_of::<rngs::JitterRng>());
}

/// Properties of a custom entropy source.
pub trait CustomEntropySource {
    /// Name of this source
    fn name(&self) -> &'static str;
    
    /// Is this source available?
    /// 
    /// The default implementation returns `true`.
    fn is_available(&self) -> bool { true }
    
    /// Prepare the entropy source for use.
    /// 
    /// This is always called before `fill` on each thread. This may be called
    /// multiple times.
    /// 
    /// A `u64` parameter may be returned, which is passed to `fill` when
    /// called, and is considered `!Send` (i.e. is never passed to a different
    /// thread).
    fn init(&self) -> Result<u64, Error>;

    /// Fill `dest` with random data from the entropy source.
    /// 
    /// The `u64` parameter from `init` is passed.
    fn fill(&self, param: &mut u64, dest: &mut [u8]) -> Result<(), Error>;
}

struct CustomNoSource;
impl CustomEntropySource for CustomNoSource {
    fn name(&self) -> &'static str {
        "no source"
    }
    
    fn is_available(&self) -> bool { false }
    
    fn init(&self) -> Result<u64, Error> {
        unreachable!()
    }

    fn fill(&self, _: &mut u64, _: &mut [u8]) -> Result<(), Error> {
        unreachable!()
    }
}

// TODO: remove outer Option when `Mutex::new(&...)` is a constant expression
static mut CUSTOM_SOURCE: Option<Mutex<&CustomEntropySource>> = None;
static CUSTOM_SOURCE_ONCE: Once = ONCE_INIT;

fn access_custom_entropy() -> MutexGuard<'static, &'static CustomEntropySource> {
    CUSTOM_SOURCE_ONCE.call_once(|| {
        unsafe { CUSTOM_SOURCE = Some(Mutex::new(&CustomNoSource)) }
    });
    let mutex = unsafe { CUSTOM_SOURCE.as_ref().unwrap() };
    mutex.lock().unwrap()
}

fn get_custom_entropy() -> &'static CustomEntropySource {
    *access_custom_entropy()
}

/// Specify a custom entropy source.
/// 
/// This must be a static reference to an object implementing the
/// `CustomEntropySource` trait.
pub fn set_custom_entropy(source: &'static CustomEntropySource) {
    let mut guard = access_custom_entropy();
    *guard = source;
}

impl EntropySource for Custom {
    fn name() -> &'static str {
        get_custom_entropy().name()
    }
    
    /// Is this source available?
    /// 
    /// The default implementation returns `true`.
    fn is_available() -> bool {
        get_custom_entropy().is_available()
    }
    
    /// Create an instance
    fn new() -> Result<Self, Error> where Self: Sized {
        let source = get_custom_entropy();
        let param = source.init()?;
        Ok(Custom {
            source,
            param,
            _not_send: Default::default(),
        })
    }

    /// Fill `dest` with random data from the entropy source
    fn fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.source.fill(&mut self.param, dest)
    }
}


#[cfg(not(target_arch = "wasm32"))]
#[derive(Clone, Debug)]
pub struct Jitter(rngs::JitterRng);

#[cfg(not(target_arch = "wasm32"))]
impl EntropySource for Jitter {
    fn name() -> &'static str { "JitterRng" }
    
    fn is_available() -> bool { true }

    fn new() -> Result<Self, Error> {
        Ok(Jitter(rngs::JitterRng::new()?))
    }

    fn fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

#[cfg(target_arch = "wasm32")]
type Jitter = NoSource;


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_entropy() {
        let mut rng = EntropyRng::new();
        let n = (rng.next_u32() ^ rng.next_u32()).count_ones();
        assert!(n >= 2);    // p(failure) approx 1e-7
    }
    
    #[test]
    fn test_custom_entropy() {
        struct FakeEntropy;
        impl CustomEntropySource for FakeEntropy {
            fn name(&self) -> &'static str { "fake entropy" }
            fn init(&self) -> Result<u64, Error> { Ok(0) }
            fn fill(&self, _: &mut u64, dest: &mut [u8]) -> Result<(), Error> {
                for x in dest { *x = 0 }
                Ok(())
            }
        }
        set_custom_entropy(&FakeEntropy);
        let mut entropy = EntropyRng::new();
        // we can't properly test this because we can't disable `OsRng`
        assert!(entropy.next_u64() != 1);
    }
}
