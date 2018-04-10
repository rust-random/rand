// Copyright 2013-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interfaces to the operating system provided random number
//! generators.

use std::fmt;
use rand_core::{RngCore, Error, impls};

/// A random number generator that retrieves randomness straight from the
/// operating system.
///
/// This is the preferred external source of entropy for most
/// applications. Commonly it is used to initialize a user-space RNG, which can
/// then be used to generate random values with much less overhead than `OsRng`.
///
/// You may prefer to use [`EntropyRng`] instead of `OsRng`. Is is unlikely, but
/// not entirely theoretical, for `OsRng` to fail. In such cases `EntropyRng`
/// falls back on a good alternative entropy source.
///
/// `OsRng` usually does not block. On some systems, and notably virtual
/// machines, it may block very early in the init process, when the OS CSPRNG
/// has not yet been seeded.
///
/// `OsRng::new()` is guaranteed to be very cheap (after the first successful
/// call), and will never consume more than one file handle per process.
///
/// ## Platform sources:
///
/// - Linux, Android: reads from the `getrandom(2)` system call if available,
///   otherwise from `/dev/urandom`.
/// - macOS, iOS: calls `SecRandomCopyBytes`.
/// - Windows: calls `RtlGenRandom`.
/// - WASM: calls `window.crypto.getRandomValues` in browsers,
///   and in Node.js `require("crypto").randomBytes`.
/// - OpenBSD: calls `getentropy(2)`.
/// - FreeBSD: uses the `kern.arandom` `sysctl(2)` mib.
/// - Fuchsia: calls `cprng_draw`.
/// - Redox: reads from `rand:` device.
/// - CloudABI: calls `random_get`.
/// - Other Unix-like systems: reads directly from `/dev/urandom`.
///   Note: many Unix systems provide `/dev/random` as well as `/dev/urandom`.
///   On all modern systems these two interfaces offer identical quality, with
///   the difference that on some systems `/dev/random` may block. This is a
///   dated design, and `/dev/urandom` is preferred by cryptography experts. [1]
///
/// [1] See [Myths about urandom](https://www.2uo.de/myths-about-urandom/).
///
/// [`EntropyRng`]: struct.EntropyRng.html

#[allow(unused)]    // not used by all targets
#[derive(Clone)]
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

impl RngCore for OsRng {
    fn next_u32(&mut self) -> u32 {
        impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        use std::{time, thread};

        // We cannot return Err(..), so we try to handle before panicking.
        const MAX_RETRY_PERIOD: u32 = 10; // max 10s
        const WAIT_DUR_MS: u32 = 100; // retry every 100ms
        let wait_dur = time::Duration::from_millis(WAIT_DUR_MS as u64);
        const RETRY_LIMIT: u32 = (MAX_RETRY_PERIOD * 1000) / WAIT_DUR_MS;
        const TRANSIENT_RETRIES: u32 = 8;
        let mut err_count = 0;
        let mut error_logged = false;

        loop {
            if let Err(e) = self.try_fill_bytes(dest) {
                if err_count >= RETRY_LIMIT {
                    error!("OsRng failed too many times; last error: {}", e);
                    panic!("OsRng failed too many times; last error: {}", e);
                }

                if e.kind.should_wait() {
                    if !error_logged {
                        warn!("OsRng failed; waiting up to {}s and retrying. Error: {}",
                                MAX_RETRY_PERIOD, e);
                        error_logged = true;
                    }
                    err_count += 1;
                    thread::sleep(wait_dur);
                    continue;
                } else if e.kind.should_retry() {
                    if !error_logged {
                        warn!("OsRng failed; retrying up to {} times. Error: {}",
                                TRANSIENT_RETRIES, e);
                        error_logged = true;
                    }
                    err_count += (RETRY_LIMIT + TRANSIENT_RETRIES - 1)
                            / TRANSIENT_RETRIES;    // round up
                    continue;
                } else {
                    error!("OsRng failed: {}", e);
                    panic!("OsRng fatal error: {}", e);
                }
            }

            break;
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

#[cfg(all(unix,
          not(target_os = "cloudabi"),
          not(target_os = "freebsd"),
          not(target_os = "fuchsia"),
          not(target_os = "ios"),
          not(target_os = "macos"),
          not(target_os = "openbsd"),
          not(target_os = "redox")))]
mod imp {
    extern crate libc;
    use {Error, ErrorKind};
    use std::fs::{OpenOptions, File};
    use std::os::unix::fs::OpenOptionsExt;
    use std::io;
    use std::io::Read;
    use std::sync::{Once, Mutex, ONCE_INIT};

    #[derive(Clone, Debug)]
    pub struct OsRng(OsRngMethod);

    #[derive(Clone, Debug)]
    enum OsRngMethod {
        GetRandom,
        RandomDevice,
    }

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            if is_getrandom_available() {
                return Ok(OsRng(OsRngMethod::GetRandom));
            }

            open_dev_random()?;
            Ok(OsRng(OsRngMethod::RandomDevice))
        }

        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            match self.0 {
                OsRngMethod::GetRandom => getrandom_try_fill(dest),
                OsRngMethod::RandomDevice => dev_random_try_fill(dest),
            }
        }
    }

    #[cfg(all(any(target_os = "linux", target_os = "android"),
              any(target_arch = "x86_64", target_arch = "x86",
                  target_arch = "arm", target_arch = "aarch64",
                  target_arch = "s390x", target_arch = "powerpc",
                  target_arch = "mips", target_arch = "mips64")))]
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
         #[cfg(target_arch = "s390x")]
        const NR_GETRANDOM: libc::c_long = 349;
        #[cfg(target_arch = "powerpc")]
        const NR_GETRANDOM: libc::c_long = 359;
        #[cfg(target_arch = "mips")] // old ABI
        const NR_GETRANDOM: libc::c_long = 4353;
        #[cfg(target_arch = "mips64")]
        const NR_GETRANDOM: libc::c_long = 5313;

        const GRND_NONBLOCK: libc::c_uint = 0x0001;

        unsafe {
            syscall(NR_GETRANDOM, buf.as_mut_ptr(), buf.len(), GRND_NONBLOCK)
        }
    }

    #[cfg(not(all(any(target_os = "linux", target_os = "android"),
                  any(target_arch = "x86_64", target_arch = "x86",
                      target_arch = "arm", target_arch = "aarch64",
                      target_arch = "s390x", target_arch = "powerpc",
                      target_arch = "mips", target_arch = "mips64"))))]
    fn getrandom(_buf: &mut [u8]) -> libc::c_long { -1 }

    fn getrandom_try_fill(dest: &mut [u8]) -> Result<(), Error> {
        trace!("OsRng: reading {} bytes via getrandom", dest.len());
        let mut read = 0;
        let len = dest.len();
        while read < len {
            let result = getrandom(&mut dest[read..]);
            if result == -1 {
                let err = io::Error::last_os_error();
                let kind = err.kind();
                if kind == io::ErrorKind::Interrupted {
                    continue;
                } else if kind == io::ErrorKind::WouldBlock {
                    // Potentially this would waste bytes, but since we use
                    // /dev/urandom blocking only happens if not initialised.
                    // Also, wasting the bytes in dest doesn't matter very much.
                    return Err(Error::with_cause(
                        ErrorKind::NotReady,
                        "getrandom not ready",
                        err,
                    ));
                } else {
                    return Err(Error::with_cause(
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

    #[cfg(all(any(target_os = "linux", target_os = "android"),
              any(target_arch = "x86_64", target_arch = "x86",
                  target_arch = "arm", target_arch = "aarch64",
                  target_arch = "s390x", target_arch = "powerpc",
                  target_arch = "mips", target_arch = "mips64")))]
    fn is_getrandom_available() -> bool {
        use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};
        use std::sync::{Once, ONCE_INIT};

        static CHECKER: Once = ONCE_INIT;
        static AVAILABLE: AtomicBool = ATOMIC_BOOL_INIT;

        CHECKER.call_once(|| {
            debug!("OsRng: testing getrandom");
            let mut buf: [u8; 0] = [];
            let result = getrandom(&mut buf);
            let available = if result == -1 {
                let err = io::Error::last_os_error().raw_os_error();
                err != Some(libc::ENOSYS)
            } else {
                true
            };
            AVAILABLE.store(available, Ordering::Relaxed);
            info!("OsRng: using {}", if available { "getrandom" } else { "/dev/urandom" });
        });

        AVAILABLE.load(Ordering::Relaxed)
    }

    #[cfg(not(all(any(target_os = "linux", target_os = "android"),
                  any(target_arch = "x86_64", target_arch = "x86",
                      target_arch = "arm", target_arch = "aarch64",
                      target_arch = "s390x", target_arch = "powerpc",
                      target_arch = "mips", target_arch = "mips64"))))]
    fn is_getrandom_available() -> bool { false }

    // TODO: remove outer Option when `Mutex::new(None)` is a constant expression
    static mut READ_RNG_FILE: Option<Mutex<Option<File>>> = None;
    static READ_RNG_ONCE: Once = ONCE_INIT;

    // Note: all instances use a single internal file handle, to prevent
    // possible exhaustion of file descriptors.
    //
    // On some systems reading from `/dev/urandom` "may return data prior to the
    // to the entropy pool being initialized". I.e., early in the boot process,
    // and especially on virtual machines, `/dev/urandom` may return data that
    // is less random.
    //
    // As a countermeasure we try to do a single read from `/dev/random` in
    // non-blocking mode. If the OS RNG is not yet properly seeded, we will get
    // an error. Because we keep `/dev/urandom` open when succesful, this is
    // only a small one-time cost.
    fn open_dev_random() -> Result<(), Error> {
        fn map_err(err: io::Error) -> Error {
            match err.kind() {
                io::ErrorKind::Interrupted =>
                        Error::new(ErrorKind::Transient, "interrupted"),
                io::ErrorKind::WouldBlock =>
                        Error::with_cause(ErrorKind::NotReady,
                        "OS RNG not yet seeded", err),
                _ => Error::with_cause(ErrorKind::Unavailable,
                        "error while opening random device", err)
            }
        }

        READ_RNG_ONCE.call_once(|| {
            unsafe { READ_RNG_FILE = Some(Mutex::new(None)) }
        });

        // We try opening the file outside the `call_once` fn because we cannot
        // clone the error, thus we must retry on failure.

        let mutex = unsafe { READ_RNG_FILE.as_ref().unwrap() };
        let mut guard = mutex.lock().unwrap();
        if (*guard).is_none() {
            {
                info!("OsRng: opening random device /dev/random");
                let mut file = OpenOptions::new()
                    .read(true)
                    .custom_flags(libc::O_NONBLOCK)
                    .open("/dev/random")
                    .map_err(map_err)?;
                let mut buf = [0u8; 1];
                file.read_exact(&mut buf).map_err(map_err)?;
            }

            info!("OsRng: opening random device /dev/urandom");
            let file = File::open("/dev/urandom").map_err(map_err)?;
            *guard = Some(file);
        };
        Ok(())
    }

    fn dev_random_try_fill(dest: &mut [u8]) -> Result<(), Error> {
        if dest.len() == 0 { return Ok(()); }
        trace!("OsRng: reading {} bytes from random device", dest.len());

        // We expect this function only to be used after `open_dev_random` was
        // succesful. Therefore we can assume that our memory was set with a
        // valid object.
        let mutex = unsafe { READ_RNG_FILE.as_ref().unwrap() };
        let mut guard = mutex.lock().unwrap();
        let file = (*guard).as_mut().unwrap();
        // Use `std::io::read_exact`, which retries on `ErrorKind::Interrupted`.
        file.read_exact(dest).map_err(|err| {
            match err.kind() {
                ::std::io::ErrorKind::WouldBlock => Error::with_cause(
                    ErrorKind::NotReady,
                    "reading from random device would block", err),
                _ => Error::with_cause(ErrorKind::Unavailable,
                    "error reading random device", err)
            }
        })
    }
}

#[cfg(target_os = "cloudabi")]
mod imp {
    extern crate cloudabi;

    use {Error, ErrorKind};

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }

        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            trace!("OsRng: reading {} bytes via cloadabi::random_get", dest.len());
            let errno = unsafe { cloudabi::random_get(dest) };
            if errno == cloudabi::errno::SUCCESS {
                Ok(())
            } else {
                // Cloudlibc provides its own `strerror` implementation so we
                // can use `from_raw_os_error` here.
                Err(Error::with_cause(
                    ErrorKind::Unavailable,
                    "random_get() system call failed",
                    io::Error::from_raw_os_error(errno),
                ))
            }
        }
    }
}

#[cfg(any(target_os = "macos", target_os = "ios"))]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    
    use std::io;
    use self::libc::{c_int, size_t};

    #[derive(Clone, Debug)]
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
        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            trace!("OsRng: reading {} bytes via SecRandomCopyBytes", dest.len());
            let ret = unsafe {
                SecRandomCopyBytes(kSecRandomDefault, dest.len() as size_t, dest.as_mut_ptr())
            };
            if ret == -1 {
                Err(Error::with_cause(
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
    
    use std::ptr;
    use std::io;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            let mib = [libc::CTL_KERN, libc::KERN_ARND];
            trace!("OsRng: reading {} bytes via kern.arandom", dest.len());
            // kern.arandom permits a maximum buffer size of 256 bytes
            for s in dest.chunks_mut(256) {
                let mut s_len = s.len();
                let ret = unsafe {
                    libc::sysctl(mib.as_ptr(), mib.len() as libc::c_uint,
                                 s.as_mut_ptr() as *mut _, &mut s_len,
                                 ptr::null(), 0)
                };
                if ret == -1 || s_len != s.len() {
                    return Err(Error::with_cause(
                        ErrorKind::Unavailable,
                        "kern.arandom sysctl failed",
                        io::Error::last_os_error()));
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

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            // getentropy(2) permits a maximum buffer size of 256 bytes
            for s in dest.chunks_mut(256) {
                trace!("OsRng: reading {} bytes via getentropy", s.len());
                let ret = unsafe {
                    libc::getentropy(s.as_mut_ptr() as *mut libc::c_void, s.len())
                };
                if ret == -1 {
                    return Err(Error::with_cause(
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
    use std::fs::File;
    use std::io::Read;
    use std::io::ErrorKind::*;
    use std::sync::{Once, Mutex, ONCE_INIT};

    #[derive(Clone, Debug)]
    pub struct OsRng();

    // TODO: remove outer Option when `Mutex::new(None)` is a constant expression
    static mut READ_RNG_FILE: Option<Mutex<Option<File>>> = None;
    static READ_RNG_ONCE: Once = ONCE_INIT;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            READ_RNG_ONCE.call_once(|| {
                unsafe { READ_RNG_FILE = Some(Mutex::new(None)) }
            });

            // We try opening the file outside the `call_once` fn because we cannot
            // clone the error, thus we must retry on failure.

            let mutex = unsafe { READ_RNG_FILE.as_ref().unwrap() };
            let mut guard = mutex.lock().unwrap();
            if (*guard).is_none() {
                info!("OsRng: opening random device 'rand:'");
                let file = File::open("rand:").map_err(|err| {
                    match err.kind() {
                        Interrupted => Error::new(ErrorKind::Transient, "interrupted"),
                        WouldBlock => Error::with_cause(ErrorKind::NotReady,
                                "opening random device would block", err),
                        _ => Error::with_cause(ErrorKind::Unavailable,
                                "error while opening random device", err)
                    }
                })?;
                *guard = Some(file);
            };
            Ok(OsRng())
        }

        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            if dest.len() == 0 { return Ok(()); }
            trace!("OsRng: reading {} bytes from random device", dest.len());

            // Since we have an instance of Self, we can assume that our memory was
            // set with a valid object.
            let mutex = unsafe { READ_RNG_FILE.as_ref().unwrap() };
            let mut guard = mutex.lock().unwrap();
            let file = (*guard).as_mut().unwrap();
            // Use `std::io::read_exact`, which retries on `ErrorKind::Interrupted`.
            file.read_exact(dest).map_err(|err| {
                Error::with_cause(ErrorKind::Unavailable,
                                  "error reading random device", err)
            })
        }
    }
}

#[cfg(target_os = "fuchsia")]
mod imp {
    extern crate fuchsia_zircon;

    use {Error, ErrorKind};
    
    use std::io;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            for s in dest.chunks_mut(fuchsia_zircon::sys::ZX_CPRNG_DRAW_MAX_LEN) {
                trace!("OsRng: reading {} bytes via cprng_draw", s.len());
                let mut filled = 0;
                while filled < s.len() {
                    match fuchsia_zircon::cprng_draw(&mut s[filled..]) {
                        Ok(actual) => filled += actual,
                        Err(e) => {
                            return Err(Error::with_cause(
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
    extern crate winapi;
    
    use {Error, ErrorKind};
    
    use std::io;

    use self::winapi::shared::minwindef::ULONG;
    use self::winapi::um::ntsecapi::RtlGenRandom;
    use self::winapi::um::winnt::PVOID;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Ok(OsRng)
        }
        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            // RtlGenRandom takes an ULONG (u32) for the length so we need to
            // split up the buffer.
            for slice in dest.chunks_mut(<ULONG>::max_value() as usize) {
                trace!("OsRng: reading {} bytes via RtlGenRandom", slice.len());
                let ret = unsafe {
                    RtlGenRandom(slice.as_mut_ptr() as PVOID, slice.len() as ULONG)
                };
                if ret == 0 {
                    return Err(Error::with_cause(
                        ErrorKind::Unavailable,
                        "couldn't generate random bytes",
                        io::Error::last_os_error()));
                }
            }
            Ok(())
        }
    }
}

#[cfg(all(target_arch = "wasm32",
          not(target_os = "emscripten"),
          not(feature = "stdweb")))]
mod imp {
    use {Error, ErrorKind};

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            Err(Error::new(ErrorKind::Unavailable,
                           "not supported on WASM without stdweb"))
        }

        pub fn try_fill_bytes(&mut self, _v: &mut [u8]) -> Result<(), Error> {
            Err(Error::new(ErrorKind::Unavailable,
                           "not supported on WASM without stdweb"))
        }
    }
}

#[cfg(all(target_arch = "wasm32",
          not(target_os = "emscripten"),
          feature = "stdweb"))]
mod imp {
    use std::mem;
    use stdweb::unstable::TryInto;
    use stdweb::web::error::Error as WebError;
    use {Error, ErrorKind};

    #[derive(Clone, Debug)]
    enum OsRngInner {
        Browser,
        Node
    }

    #[derive(Clone, Debug)]
    pub struct OsRng(OsRngInner);

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            let result = js! {
                try {
                    if (
                        typeof window === "object" &&
                        typeof window.crypto === "object" &&
                        typeof window.crypto.getRandomValues === "function"
                    ) {
                        return { success: true, ty: 1 };
                    }

                    if (typeof require("crypto").randomBytes === "function") {
                        return { success: true, ty: 2 };
                    }

                    return { success: false, error: new Error("not supported") };
                } catch(err) {
                    return { success: false, error: err };
                }
            };

            if js!{ return @{ result.as_ref() }.success } == true {
                let ty = js!{ return @{ result }.ty };

                if ty == 1 { Ok(OsRng(OsRngInner::Browser)) }
                else if ty == 2 { Ok(OsRng(OsRngInner::Node)) }
                else { unreachable!() }
            } else {
                let err: WebError = js!{ return @{ result }.error }.try_into().unwrap();
                Err(Error::with_cause(ErrorKind::Unavailable, "WASM Error", err))
            }
        }

        pub fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            assert_eq!(mem::size_of::<usize>(), 4);

            let len = dest.len() as u32;
            let ptr = dest.as_mut_ptr() as i32;

            let result = match self.0 {
                OsRngInner::Browser => js! {
                    try {
                        let array = new Uint8Array(@{ len });
                        window.crypto.getRandomValues(array);
                        HEAPU8.set(array, @{ ptr });

                        return { success: true };
                    } catch(err) {
                        return { success: false, error: err };
                    }
                },
                OsRngInner::Node => js! {
                    try {
                        let bytes = require("crypto").randomBytes(@{ len });
                        HEAPU8.set(new Uint8Array(bytes), @{ ptr });

                        return { success: true };
                    } catch(err) {
                        return { success: false, error: err };
                    }
                }
            };

            if js!{ return @{ result.as_ref() }.success } == true {
                Ok(())
            } else {
                let err: WebError = js!{ return @{ result }.error }.try_into().unwrap();
                Err(Error::with_cause(ErrorKind::Unexpected, "WASM Error", err))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use RngCore;
    use OsRng;

    #[test]
    fn test_os_rng() {
        let mut r = OsRng::new().unwrap();

        r.next_u32();
        r.next_u64();

        let mut v1 = [0u8; 1000];
        r.fill_bytes(&mut v1);

        let mut v2 = [0u8; 1000];
        r.fill_bytes(&mut v2);

        let mut n_diff_bits = 0;
        for i in 0..v1.len() {
            n_diff_bits += (v1[i] ^ v2[i]).count_ones();
        }

        // Check at least 1 bit per byte differs. p(failure) < 1e-1000 with random input.
        assert!(n_diff_bits >= v1.len() as u32);
    }

    #[cfg(not(any(target_arch = "wasm32", target_arch = "asmjs")))]
    #[test]
    fn test_os_rng_tasks() {
        use std::sync::mpsc::channel;
        use std::thread;

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
                    r.fill_bytes(&mut v);
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
