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

use std::{mem, fmt};
use std::io::Read;

use {Rng, Error};
// TODO: replace many of the panics below with Result error handling

/// A random number generator that retrieves randomness straight from
/// the operating system. Platform sources:
///
/// - Unix-like systems (Linux, Android, Mac OSX): read directly from
///   `/dev/urandom`, or from `getrandom(2)` system call if available.
/// - OpenBSD: calls `getentropy(2)`
/// - FreeBSD: uses the `kern.arandom` `sysctl(2)` mib
/// - Windows: calls `RtlGenRandom`, exported from `advapi32.dll` as
///   `SystemFunction036`.
/// - iOS: calls SecRandomCopyBytes as /dev/(u)random is sandboxed.
/// - PNaCl: calls into the `nacl-irt-random-0.1` IRT interface.
///
/// This usually does not block. On some systems (e.g. FreeBSD, OpenBSD,
/// Max OS X, and modern Linux) this may block very early in the init
/// process, if the CSPRNG has not been seeded yet.[1]
///
/// [1] See <https://www.python.org/dev/peps/pep-0524/> for a more
///     in-depth discussion.
pub struct OsRng(imp::OsRng);

impl OsRng {
    /// Create a new `OsRng`.
    pub fn new() -> Result<OsRng, Error> {
        imp::OsRng::new().map(OsRng)
    }
}

impl Rng for OsRng {
    fn next_u32(&mut self) -> u32 {
        let mut buf: [u8; 4] = [0; 4];
        self.try_fill(&mut buf).unwrap_or_else(|e| panic!("try_fill failed: {:?}", e));
        unsafe{ *(buf.as_ptr() as *const u32) }
    }
    fn next_u64(&mut self) -> u64 {
        let mut buf: [u8; 8] = [0; 8];
        self.try_fill(&mut buf).unwrap_or_else(|e| panic!("try_fill failed: {:?}", e));
        unsafe{ *(buf.as_ptr() as *const u64) }
    }
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        let mut buf: [u8; 16] = [0; 16];
        self.try_fill(&mut buf).unwrap_or_else(|e| panic!("try_fill failed: {:?}", e));
        unsafe{ *(buf.as_ptr() as *const u128) }
    }
    fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill(v)
    }
}

impl fmt::Debug for OsRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "OsRng {{}}")
    }
}

// Specialisation of `ReadRng` for our purposes
#[derive(Debug)]
struct ReadRng<R> (R);

impl<R: Read> ReadRng<R> {
    fn try_fill(&mut self, mut buf: &mut [u8]) -> Result<(), Error> {
        while buf.len() > 0 {
            match self.0.read(buf).unwrap_or_else(|e| panic!("Read error: {}", e)) {
                0 => panic!("OsRng: no bytes available"),
                n => buf = &mut mem::replace(&mut buf, &mut [])[n..],
            }
        }
        Ok(())
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
    use Error;

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

        unsafe {
            syscall(NR_GETRANDOM, buf.as_mut_ptr(), buf.len(), 0)
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
                if err.kind() == io::ErrorKind::Interrupted {
                    continue
                } else {
                    panic!("unexpected getrandom error: {}", err);
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

            let reader = File::open("/dev/urandom").unwrap();
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
                panic!("couldn't generate random bytes: {}", io::Error::last_os_error());
            }
            Ok(())
        }
    }
}

#[cfg(target_os = "freebsd")]
mod imp {
    extern crate libc;

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
                    panic!("kern.arandom sysctl failed! (returned {}, s.len() {}, oldlenp {})",
                           ret, s.len(), s_len);
                }
            }
            Ok(())
        }
    }
}

#[cfg(target_os = "openbsd")]
mod imp {
    extern crate libc;

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
                    let err = io::Error::last_os_error();
                    panic!("getentropy failed: {}", err);
                }
            }
            Ok(())
        }
    }
}

#[cfg(target_os = "redox")]
mod imp {
    use std::io;
    use std::fs::File;
    use super::ReadRng;

    #[derive(Debug)]
    pub struct OsRng {
        inner: ReadRng<File>,
    }

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            let reader = File::open("rand:").unwrap();
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
                        Err(e) => panic!("cprng_draw failed: {:?}", e),
                    };
                }
            }
            Ok(())
        }
    }
}

#[cfg(windows)]
mod imp {
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
                    panic!("couldn't generate random bytes: {}",
                           io::Error::last_os_error());
                }
            }
            Ok(())
        }
    }
}

#[cfg(target_os = "nacl")]
mod imp {
    extern crate libc;

    use std::io;
    use std::mem;

    #[derive(Debug)]
    pub struct OsRng(extern fn(dest: *mut libc::c_void,
                               bytes: libc::size_t,
                               read: *mut libc::size_t) -> libc::c_int);

    extern {
        fn nacl_interface_query(name: *const libc::c_char,
                                table: *mut libc::c_void,
                                table_size: libc::size_t) -> libc::size_t;
    }

    const INTERFACE: &'static [u8] = b"nacl-irt-random-0.1\0";

    #[repr(C)]
    struct NaClIRTRandom {
        get_random_bytes: Option<extern fn(dest: *mut libc::c_void,
                                           bytes: libc::size_t,
                                           read: *mut libc::size_t) -> libc::c_int>,
    }

    impl OsRng {
        pub fn new() -> Result<OsRng, Error> {
            let mut iface = NaClIRTRandom {
                get_random_bytes: None,
            };
            let result = unsafe {
                nacl_interface_query(INTERFACE.as_ptr() as *const _,
                                     mem::transmute(&mut iface),
                                     mem::size_of::<NaClIRTRandom>() as libc::size_t)
            };
            if result != 0 {
                assert!(iface.get_random_bytes.is_some());
                let result = OsRng(iface.get_random_bytes.take().unwrap());
                Ok(result)
            } else {
                // let error = io::ErrorKind::NotFound;
                // let error = io::Error::new(error, "IRT random interface missing");
                Err(Result)
            }
        }
        pub fn try_fill(&mut self, v: &mut [u8]) -> Result<(), Error> {
            let mut read = 0;
            loop {
                let mut r: libc::size_t = 0;
                let len = v.len();
                let error = (self.0)(v[read..].as_mut_ptr() as *mut _,
                                     (len - read) as libc::size_t,
                                     &mut r as *mut _);
                assert!(error == 0, "`get_random_bytes` failed!");
                read += r as usize;

                if read >= v.len() { break; }
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
