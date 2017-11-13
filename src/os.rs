// Copyright 2013-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interfaces to the operating system provided random number
//! generators.

use std::fmt;
use std::io::Read;

use {Rng, Error, ErrorKind};
// TODO: replace many of the panics below with Result error handling

/// A random number generator that retrieves randomness straight from
/// the operating system.
///
/// Platform sources:
///
/// - Unix-like systems (Linux, Android, Mac OSX): read directly from
///   `/dev/urandom`, or from `getrandom(2)` system call if available.
/// - OpenBSD: calls `getentropy(2)`
/// - FreeBSD: uses the `kern.arandom` `sysctl(2)` mib
/// - Windows: calls `RtlGenRandom`, exported from `advapi32.dll` as
///   `SystemFunction036`.
/// - iOS: calls SecRandomCopyBytes as /dev/(u)random is sandboxed.
///
/// This usually does not block. On some systems (e.g. FreeBSD, OpenBSD,
/// Max OS X, and modern Linux) this may block very early in the init
/// process, if the CSPRNG has not been seeded yet.[1]
///
/// [1] See <https://www.python.org/dev/peps/pep-0524/> for a more
///     in-depth discussion.
#[allow(unused)]    // not used by all targets
pub struct OsRng(imp::OsRng);

impl fmt::Debug for OsRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl OsRng {
    /// Create a new `OsRng`.
    pub fn new() -> Result<OsRng, Error> {
        imp::OsRng::new().map(OsRng)
    }
}

impl Rng for OsRng {
    fn next_u32(&mut self) -> u32 {
        // note: `next_u32_via_fill` does a byte-swap on big-endian
        // architectures, which is not really needed here
        ::rand_core::impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        ::rand_core::impls::next_u64_via_fill(self)
    }

    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        ::rand_core::impls::fill_via_try_fill(self, dest)
    }

    fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill(v)
    }
}

// Specialisation of `ReadRng` for our purposes
#[derive(Debug)]
struct ReadRng<R> (R);

impl<R: Read> ReadRng<R> {
    #[allow(unused)]    // not used by all targets
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        if dest.len() == 0 { return Ok(()); }
        // Use `std::io::read_exact`, which retries on `ErrorKind::Interrupted`.
        self.0.read_exact(dest).map_err(|err| {
            Error::new_with_cause(ErrorKind::Unavailable, "error reading random device", err)
        })
    }
}

#[cfg(all(unix, not(target_os = "ios"),
          not(target_os = "nacl"),
          not(target_os = "freebsd"),
          not(target_os = "fuchsia"),
          not(target_os = "openbsd"),
          not(target_os = "redox")))]
mod imp {
    extern crate libc;

    use self::OsRngInner::*;
    use super::ReadRng;
    use {Error, ErrorKind};

    use std::io;
    use std::fs::File;

    #[cfg(all(target_os = "linux",
              any(target_arch = "x86_64",
                  target_arch = "x86",
                  target_arch = "arm",
                  target_arch = "aarch64",
                  target_arch = "powerpc")))]
    fn getrandom(buf: &mut [u8]) -> libc::c_long {
        extern "C" {
            fn syscall(number: libc::c_long, ...) -> libc::c_long;
        }

        #[cfg(target_arch = "x86_64")]
        const NR_GETRANDOM: libc::c_long = 318;
        #[cfg(target_arch = "x86")]
        const NR_GETRANDOM: libc::c_long = 355;
        #[cfg(target_arch = "arm")]
        const NR_GETRANDOM: libc::c_long = 384;
        #[cfg(target_arch = "aarch64")]
        const NR_GETRANDOM: libc::c_long = 278;
        #[cfg(target_arch = "powerpc")]
        const NR_GETRANDOM: libc::c_long = 384;
        
        const GRND_NONBLOCK: libc::c_uint = 0x0001;

        unsafe {
            syscall(NR_GETRANDOM, buf.as_mut_ptr(), buf.len(), GRND_NONBLOCK)
        }
    }

    #[cfg(not(all(target_os = "linux",
                  any(target_arch = "x86_64",
                      target_arch = "x86",
                      target_arch = "arm",
                      target_arch = "aarch64",
                      target_arch = "powerpc"))))]
    fn getrandom(_buf: &mut [u8]) -> libc::c_long { -1 }

    fn getrandom_try_fill(v: &mut [u8]) -> Result<(), Error> {
        let mut read = 0;
        let len = v.len();
        while read < len {
            let result = getrandom(&mut v[read..]);
            if result == -1 {
                let err = io::Error::last_os_error();
                let kind = err.kind();
                if kind == io::ErrorKind::Interrupted {
                    continue;
                } else if kind == io::ErrorKind::WouldBlock {
                    // Potentially this would waste bytes, but since we use
                    // /dev/urandom blocking only happens if not initialised.
                    // Also, wasting the bytes in v doesn't matter very much.
                    return Err(Error::new(ErrorKind::NotReady, "getrandom not ready"));
                } else {
                    return Err(Error::new_with_cause(
                        ErrorKind::Unavailable,
                        "unexpected getrandom error",
                        err,
                    ));
                }
            } else {
                read += result as usize;
            }
        }
        Ok(())
    }

    #[cfg(all(target_os = "linux",
              any(target_arch = "x86_64",
                  target_arch = "x86",
                  target_arch = "arm",
                  target_arch = "aarch64",
                  target_arch = "powerpc")))]
    fn is_getrandom_available() -> bool {
        use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};
        use std::sync::{Once, ONCE_INIT};

        static CHECKER: Once = ONCE_INIT;
        static AVAILABLE: AtomicBool = ATOMIC_BOOL_INIT;

        CHECKER.call_once(|| {
            let mut buf: [u8; 0] = [];
            let result = getrandom(&mut buf);
            let available = if result == -1 {
                let err = io::Error::last_os_error().raw_os_error();
                err != Some(libc::ENOSYS)
            } else {
                true
            };
            AVAILABLE.store(available, Ordering::Relaxed);
        });

        AVAILABLE.load(Ordering::Relaxed)
    }

    #[cfg(not(all(target_os = "linux",
                  any(target_arch = "x86_64",
                      target_arch = "x86",
                      target_arch = "arm",
                      target_arch = "aarch64",
                      target_arch = "powerpc"))))]
    fn is_getrandom_available() -> bool { false }

    #[derive(Debug)]
    pub struct OsRng {
        inner: OsRngInner,
    }

    #[derive(Debug)]
    enum OsRngInner {
        OsGetrandomRng,
        OsReadRng(ReadRng<File>),
    }

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            if is_getrandom_available() {
                return Ok(OsRng { inner: OsGetrandomRng });
            }

            let reader = File::open("/dev/urandom").map_err(|err| {
                Error::new_with_cause(ErrorKind::Unavailable, "error opening random device", err)
            })?;
            let reader_rng = ReadRng(reader);

            Ok(OsRng { inner: OsReadRng(reader_rng) })
        }
        
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            match self.inner {
                OsGetrandomRng => getrandom_try_fill(v),
                OsReadRng(ref mut rng) => rng.try_fill(v)
            }
        }
    }
}

#[cfg(target_os = "ios")]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    
    use std::io;
    use self::libc::{c_int, size_t};

    #[derive(Debug)]
    pub struct OsRng;

    enum SecRandom {}

    #[allow(non_upper_case_globals)]
    const kSecRandomDefault: *const SecRandom = 0 as *const SecRandom;

    #[link(name = "Security", kind = "framework")]
    extern {
        fn SecRandomCopyBytes(rnd: *const SecRandom,
                              count: size_t, bytes: *mut u8) -> c_int;
    }

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            let ret = unsafe {
                SecRandomCopyBytes(kSecRandomDefault, v.len() as size_t, v.as_mut_ptr())
            };
            if ret == -1 {
                Err(Error::new_with_cause(
                    ErrorKind::Unavailable,
                    "couldn't generate random bytes",
                    io::Error::last_os_error()))
            } else {
                Ok(())
            }
        }
    }
}

#[cfg(target_os = "freebsd")]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    
    use std::{io, ptr};

    #[derive(Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            let mib = [libc::CTL_KERN, libc::KERN_ARND];
            // kern.arandom permits a maximum buffer size of 256 bytes
            for s in v.chunks_mut(256) {
                let mut s_len = s.len();
                let ret = unsafe {
                    libc::sysctl(mib.as_ptr(), mib.len() as libc::c_uint,
                                 s.as_mut_ptr() as *mut _, &mut s_len,
                                 ptr::null(), 0)
                };
                if ret == -1 || s_len != s.len() {
                    // Old format string:
                    // "kern.arandom sysctl failed! (returned {}, s.len() {}, oldlenp {})"
                    return Err(Error::new(
                        ErrorKind::Unavailable,
                        "kern.arandom sysctl failed"));
                }
            }
            Ok(())
        }
    }
}

#[cfg(target_os = "openbsd")]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    
    use std::io;

    #[derive(Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            // getentropy(2) permits a maximum buffer size of 256 bytes
            for s in v.chunks_mut(256) {
                let ret = unsafe {
                    libc::getentropy(s.as_mut_ptr() as *mut libc::c_void, s.len())
                };
                if ret == -1 {
                    return Err(Error::new_with_cause(
                        ErrorKind::Unavailable,
                        "getentropy failed",
                        io::Error::last_os_error()));
                }
            }
            Ok(())
        }
    }
}

#[cfg(target_os = "redox")]
mod imp {
    use {Error, ErrorKind};
    
    use std::io;
    use std::fs::File;
    use super::ReadRng;

    #[derive(Debug)]
    pub struct OsRng {
        inner: ReadRng<File>,
    }

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            let reader = File::open("rand:").map_err(|err| {
                Error::new_with_cause(ErrorKind::Unavailable, "error opening random device", err)
            })?;
            let reader_rng = ReadRng(reader);

            Ok(OsRng { inner: reader_rng })
        }
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            self.inner.try_fill(v)
        }
    }
}

#[cfg(target_os = "fuchsia")]
mod imp {
    extern crate fuchsia_zircon;

    use {Error, ErrorKind};
    
    use std::io;

    #[derive(Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            for s in v.chunks_mut(fuchsia_zircon::ZX_CPRNG_DRAW_MAX_LEN) {
                let mut filled = 0;
                while filled < s.len() {
                    match fuchsia_zircon::cprng_draw(&mut s[filled..]) {
                        Ok(actual) => filled += actual,
                        Err(e) => {
                            return Err(Error::new_with_cause(
                                ErrorKind::Unavailable,
                                "cprng_draw failed",
                                e));
                        }
                    };
                }
            }
            Ok(())
        }
    }
}

#[cfg(windows)]
mod imp {
    use {Error, ErrorKind};
    
    use std::io;

    type BOOLEAN = u8;
    type ULONG = u32;

    #[link(name = "advapi32")]
    extern "system" {
        // This function's real name is `RtlGenRandom`.
        fn SystemFunction036(RandomBuffer: *mut u8, RandomBufferLength: ULONG) -> BOOLEAN;
    }

    #[derive(Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            // RtlGenRandom takes an ULONG (u32) for the length so we need to
            // split up the buffer.
            for slice in v.chunks_mut(<ULONG>::max_value() as usize) {
                let ret = unsafe {
                    SystemFunction036(slice.as_mut_ptr(), slice.len() as ULONG)
                };
                if ret == 0 {
                    return Err(Error::new_with_cause(
                        ErrorKind::Unavailable,
                        "couldn't generate random bytes",
                        io::Error::last_os_error()));
                }
            }
            Ok(())
        }
    }
}


#[cfg(test)]
mod test {
    use std::sync::mpsc::channel;
    use Rng;
    use OsRng;
    use std::thread;

    #[test]
    fn test_os_rng() {
        let mut r = OsRng::new().unwrap();

        r.next_u32();
        r.next_u64();

        let mut v = [0u8; 1000];
        r.try_fill(&mut v).unwrap();
    }

    #[test]
    fn test_os_rng_tasks() {

        let mut txs = vec!();
        for _ in 0..20 {
            let (tx, rx) = channel();
            txs.push(tx);

            thread::spawn(move|| {
                // wait until all the tasks are ready to go.
                rx.recv().unwrap();

                // deschedule to attempt to interleave things as much
                // as possible (XXX: is this a good test?)
                let mut r = OsRng::new().unwrap();
                thread::yield_now();
                let mut v = [0u8; 1000];

                for _ in 0..100 {
                    r.next_u32();
                    thread::yield_now();
                    r.next_u64();
                    thread::yield_now();
                    r.try_fill(&mut v).unwrap();
                    thread::yield_now();
                }
            });
        }

        // start all the tasks
        for tx in txs.iter() {
            tx.send(()).unwrap();
        }
    }
}
