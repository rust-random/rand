// Copyright 2013-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interface to the random number generator of the operating system.

use std::fmt;
use rand_core::{CryptoRng, RngCore, Error, impls};

/// A random number generator that retrieves randomness straight from the
/// operating system.
///
/// This is the preferred external source of entropy for most applications.
/// Commonly it is used to initialize a user-space RNG, which can then be used
/// to generate random values with much less overhead than `OsRng`.
///
/// You may prefer to use [`EntropyRng`] instead of `OsRng`. It is unlikely, but
/// not entirely theoretical, for `OsRng` to fail. In such cases [`EntropyRng`]
/// falls back on a good alternative entropy source.
///
/// `OsRng::new()` is guaranteed to be very cheap (after the first successful
/// call), and will never consume more than one file handle per process.
///
/// # Platform sources
///
/// | OS               | interface
/// |------------------|---------------------------------------------------------
/// | Linux, Android   | [`getrandom`][1] system call if available, otherwise [`/dev/urandom`][2] after reading from `/dev/random` once
/// | Windows          | [`RtlGenRandom`][3]
/// | macOS, iOS       | [`SecRandomCopyBytes`][4]
/// | FreeBSD          | [`kern.arandom`][5]
/// | OpenBSD, Bitrig  | [`getentropy`][6]
/// | NetBSD           | [`/dev/urandom`][7] after reading from `/dev/random` once
/// | Dragonfly BSD    | [`/dev/random`][8]
/// | Solaris, illumos | [`getrandom`][9] system call if available, otherwise [`/dev/random`][10]
/// | Fuchsia OS       | [`cprng_draw`][11]
/// | Redox            | [`rand:`][12]
/// | CloudABI         | [`random_get`][13]
/// | Haiku            | `/dev/random` (identical to `/dev/urandom`)
/// | Web browsers     | [`Crypto.getRandomValues`][14] (see [Support for WebAssembly and ams.js][14])
/// | Node.js          | [`crypto.randomBytes`][15] (see [Support for WebAssembly and ams.js][16])
///
/// Rand doesn't have a blanket implementation for all Unix-like operating
/// systems that reads from `/dev/urandom`. This ensures all supported operating
/// systems are using the recommended interface and respect maximum buffer
/// sizes.
///
/// ## Support for WebAssembly and ams.js
///
/// The three Emscripten targets `asmjs-unknown-emscripten`,
/// `wasm32-unknown-emscripten` and `wasm32-experimental-emscripten` use
/// Emscripten's emulation of `/dev/random` on web browsers and Node.js.
/// Unfortunately it falls back to the insecure `Math.random()` if a browser
/// doesn't support [`Crypto.getRandomValues`][12].
///
/// The bare Wasm target `wasm32-unknown-unknown` tries to call the javascript
/// methods directly, using `stdweb` in combination with `cargo-web`.
/// `wasm-bindgen` is not yet supported.
///
/// ## Early boot
///
/// It is possible that early in the boot process the OS hasn't had enough time
/// yet to collect entropy to securely seed its RNG, especially on virtual
/// machines.
///
/// Some operating systems always block the thread until the RNG is securely
/// seeded. This can take anywhere from a few seconds to more than a minute.
/// Others make a best effort to use a seed from before the shutdown and don't
/// document much.
///
/// A few, Linux, NetBSD and Solaris, offer a choice between blocking, and
/// getting an error. With `try_fill_bytes` we choose to get the error
/// ([`ErrorKind::NotReady`]), while the other methods use a blocking interface.
///
/// On Linux (when the `genrandom` system call is not available) and on NetBSD
/// reading from `/dev/urandom` never blocks, even when the OS hasn't collected
/// enough entropy yet. As a countermeasure we try to do a single read from
/// `/dev/random` until we know the OS RNG is initialized (and store this in a
/// global static).
///
/// # Panics
///
/// `OsRng` is extremely unlikely to fail if `OsRng::new()`, and one read from
/// it, where succesfull. But in case it does fail, only [`try_fill_bytes`] is
/// able to report the cause. Depending on the error the other [`RngCore`]
/// methods will retry several times, and panic in case the error remains.
///
/// [`EntropyRng`]: struct.EntropyRng.html
/// [`RngCore`]: ../trait.RngCore.html
/// [`try_fill_bytes`]: ../trait.RngCore.html#method.tymethod.try_fill_bytes
/// [`ErrorKind::NotReady`]: ../enum.ErrorKind.html#variant.NotReady
///
/// [1]: http://man7.org/linux/man-pages/man2/getrandom.2.html
/// [2]: http://man7.org/linux/man-pages/man4/urandom.4.html
/// [3]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa387694.aspx
/// [4]: https://developer.apple.com/documentation/security/1399291-secrandomcopybytes?language=objc
/// [5]: https://www.freebsd.org/cgi/man.cgi?query=random&sektion=4
/// [6]: https://man.openbsd.org/getentropy.2
/// [7]: http://netbsd.gw.com/cgi-bin/man-cgi?random+4+NetBSD-current
/// [8]: https://leaf.dragonflybsd.org/cgi/web-man?command=random&section=4
/// [9]: https://docs.oracle.com/cd/E88353_01/html/E37841/getrandom-2.html
/// [10]: https://docs.oracle.com/cd/E86824_01/html/E54777/random-7d.html
/// [11]: https://fuchsia.googlesource.com/zircon/+/HEAD/docs/syscalls/cprng_draw.md
/// [12]: https://github.com/redox-os/randd/blob/master/src/main.rs
/// [13]: https://github.com/NuxiNL/cloudabi/blob/v0.20/cloudabi.txt#L1826
/// [14]: https://www.w3.org/TR/WebCryptoAPI/#Crypto-method-getRandomValues
/// [15]: https://nodejs.org/api/crypto.html#crypto_crypto_randombytes_size_callback
/// [16]: #support-for-webassembly-and-amsjs


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

impl CryptoRng for OsRng {}

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

        // Maybe block until the OS RNG is initialized
        let mut read = 0;
        if let Ok(n) = self.0.test_initialized(dest, true) { read = n };
        let dest = &mut dest[read..];

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
        // Some systems do not support reading 0 random bytes.
        // (And why waste a system call?)
        if dest.len() == 0 { return Ok(()); }

        let read = self.0.test_initialized(dest, false)?;
        let dest = &mut dest[read..];

        let max = self.0.max_chunk_size();
        if dest.len() <= max {
            trace!("OsRng: reading {} bytes via {}",
                   dest.len(), self.0.method_str());
        } else {
            trace!("OsRng: reading {} bytes via {} in {} chunks of {} bytes",
                   dest.len(), self.0.method_str(), (dest.len() + max) / max, max);
        }
        for slice in dest.chunks_mut(max) {
            self.0.fill_chunk(slice)?;
        }
        Ok(())
    }
}

trait OsRngImpl where Self: Sized {
    // Create a new `OsRng` platform interface.
    fn new() -> Result<Self, Error>;

    // Fill a chunk with random bytes.
    fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error>;

    // Test whether the OS RNG is initialized. This method may not be possible
    // to support cheaply (or at all) on all operating systems.
    //
    // If `blocking` is set, this will cause the OS the block execution until
    // its RNG is initialized.
    //
    // Random values that are read while this are stored in `dest`, the amount
    // of read bytes is returned.
    fn test_initialized(&mut self, _dest: &mut [u8], _blocking: bool)
        -> Result<usize, Error> { Ok(0) }

    // Maximum chunk size supported.
    fn max_chunk_size(&self) -> usize { ::core::usize::MAX }

    // Name of the OS interface (used for logging).
    fn method_str(&self) -> &'static str;
}




// Helper functions to read from a random device such as `/dev/urandom`.
//
// All instances use a single internal file handle, to prevent possible
// exhaustion of file descriptors.
#[cfg(any(target_os = "linux", target_os = "android",
          target_os = "netbsd", target_os = "dragonfly",
          target_os = "solaris", target_os = "redox",
          target_os = "haiku", target_os = "emscripten"))]
mod random_device {
    use {Error, ErrorKind};
    use std::fs::File;
    use std::io;
    use std::io::Read;
    use std::sync::{Once, Mutex, ONCE_INIT};

    // TODO: remove outer Option when `Mutex::new(None)` is a constant expression
    static mut READ_RNG_FILE: Option<Mutex<Option<File>>> = None;
    static READ_RNG_ONCE: Once = ONCE_INIT;

    #[allow(unused)]
    pub fn open<F>(path: &'static str, open_fn: F) -> Result<(), Error>
        where F: Fn(&'static str) -> Result<File, io::Error>
    {
        READ_RNG_ONCE.call_once(|| {
            unsafe { READ_RNG_FILE = Some(Mutex::new(None)) }
        });

        // We try opening the file outside the `call_once` fn because we cannot
        // clone the error, thus we must retry on failure.

        let mutex = unsafe { READ_RNG_FILE.as_ref().unwrap() };
        let mut guard = mutex.lock().unwrap();
        if (*guard).is_none() {
            info!("OsRng: opening random device {}", path);
            let file = open_fn(path).map_err(map_err)?;
            *guard = Some(file);
        };
        Ok(())
    }

    pub fn read(dest: &mut [u8]) -> Result<(), Error> {
        // We expect this function only to be used after `random_device::open`
        // was succesful. Therefore we can assume that our memory was set with a
        // valid object.
        let mutex = unsafe { READ_RNG_FILE.as_ref().unwrap() };
        let mut guard = mutex.lock().unwrap();
        let file = (*guard).as_mut().unwrap();

        // Use `std::io::read_exact`, which retries on `ErrorKind::Interrupted`.
        file.read_exact(dest).map_err(|err| {
            Error::with_cause(ErrorKind::Unavailable,
                              "error reading random device", err)
        })

    }

    pub fn map_err(err: io::Error) -> Error {
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
}


#[cfg(any(target_os = "linux", target_os = "android"))]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    use super::random_device;
    use super::OsRngImpl;

    use std::io;
    use std::io::Read;
    use std::fs::{File, OpenOptions};
    use std::os::unix::fs::OpenOptionsExt;
    use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};
    use std::sync::{Once, ONCE_INIT};

    #[derive(Clone, Debug)]
    pub struct OsRng {
        method: OsRngMethod,
        initialized: bool,
    }

    #[derive(Clone, Debug)]
    enum OsRngMethod {
        GetRandom,
        RandomDevice,
    }

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> {
            if is_getrandom_available() {
                return Ok(OsRng { method: OsRngMethod::GetRandom,
                                  initialized: false });
            }
            random_device::open("/dev/urandom", &|p| File::open(p))?;
            Ok(OsRng { method: OsRngMethod::RandomDevice, initialized: false })
        }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            match self.method {
                OsRngMethod::GetRandom => getrandom_try_fill(dest, false),
                OsRngMethod::RandomDevice => random_device::read(dest),
            }
        }

        fn test_initialized(&mut self, dest: &mut [u8], blocking: bool)
            -> Result<usize, Error>
        {
            static OS_RNG_INITIALIZED: AtomicBool = ATOMIC_BOOL_INIT;
            if !self.initialized {
                self.initialized = OS_RNG_INITIALIZED.load(Ordering::Relaxed);
            }
            if self.initialized { return Ok(0); }

            let result = match self.method {
                OsRngMethod::GetRandom => {
                    getrandom_try_fill(dest, blocking)?;
                    Ok(dest.len())
                }
                OsRngMethod::RandomDevice => {
                    info!("OsRng: testing random device /dev/random");
                    let mut file = OpenOptions::new()
                        .read(true)
                        .custom_flags(if blocking { 0 } else { libc::O_NONBLOCK })
                        .open("/dev/random")
                        .map_err(random_device::map_err)?;
                    file.read(&mut dest[..1]).map_err(random_device::map_err)?;
                    Ok(1)
                }
            };
            OS_RNG_INITIALIZED.store(true, Ordering::Relaxed);
            self.initialized = true;
            result
        }

        fn method_str(&self) -> &'static str {
            match self.method {
                OsRngMethod::GetRandom => "getrandom",
                OsRngMethod::RandomDevice => "/dev/urandom",
            }
        }
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
    #[cfg(not(any(target_arch = "x86_64", target_arch = "x86",
                  target_arch = "arm", target_arch = "aarch64",
                  target_arch = "s390x", target_arch = "powerpc",
                  target_arch = "mips", target_arch = "mips64")))]
    const NR_GETRANDOM: libc::c_long = 0;

    fn getrandom(buf: &mut [u8], blocking: bool) -> libc::c_long {
        extern "C" {
            fn syscall(number: libc::c_long, ...) -> libc::c_long;
        }
        const GRND_NONBLOCK: libc::c_uint = 0x0001;

        if NR_GETRANDOM == 0 { return -1 };

        unsafe {
            syscall(NR_GETRANDOM, buf.as_mut_ptr(), buf.len(),
                    if blocking { 0 } else { GRND_NONBLOCK })
        }
    }

    fn getrandom_try_fill(dest: &mut [u8], blocking: bool) -> Result<(), Error> {
        let mut read = 0;
        while read < dest.len() {
            let result = getrandom(&mut dest[read..], blocking);
            if result == -1 {
                let err = io::Error::last_os_error();
                let kind = err.kind();
                if kind == io::ErrorKind::Interrupted {
                    continue;
                } else if kind == io::ErrorKind::WouldBlock {
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

    fn is_getrandom_available() -> bool {
        static CHECKER: Once = ONCE_INIT;
        static AVAILABLE: AtomicBool = ATOMIC_BOOL_INIT;

        if NR_GETRANDOM == 0 { return false };

        CHECKER.call_once(|| {
            debug!("OsRng: testing getrandom");
            let mut buf: [u8; 0] = [];
            let result = getrandom(&mut buf, false);
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
}


#[cfg(target_os = "netbsd")]
mod imp {
    use Error;
    use super::random_device;
    use super::OsRngImpl;

    use std::fs::File;
    use std::io::Read;
    use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};

    #[derive(Clone, Debug)]
    pub struct OsRng { initialized: bool }

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> {
            random_device::open("/dev/urandom", &|p| File::open(p))?;
            Ok(OsRng { initialized: false })
        }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            random_device::read(dest)
        }

        // Read a single byte from `/dev/random` to determine if the OS RNG is
        // already seeded. NetBSD always blocks if not yet ready.
        fn test_initialized(&mut self, dest: &mut [u8], _blocking: bool)
            -> Result<usize, Error>
        {
            static OS_RNG_INITIALIZED: AtomicBool = ATOMIC_BOOL_INIT;
            if !self.initialized {
                self.initialized = OS_RNG_INITIALIZED.load(Ordering::Relaxed);
            }
            if self.initialized { return Ok(0); }

            info!("OsRng: testing random device /dev/random");
            let mut file =
                File::open("/dev/random").map_err(random_device::map_err)?;
            file.read(&mut dest[..1]).map_err(random_device::map_err)?;

            OS_RNG_INITIALIZED.store(true, Ordering::Relaxed);
            self.initialized = true;
            Ok(1)
        }

        fn method_str(&self) -> &'static str { "/dev/urandom" }
    }
}


#[cfg(any(target_os = "dragonfly",
          target_os = "haiku",
          target_os = "emscripten"))]
mod imp {
    use Error;
    use super::random_device;
    use super::OsRngImpl;
    use std::fs::File;

    #[derive(Clone, Debug)]
    pub struct OsRng();

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> {
            random_device::open("/dev/random", &|p| File::open(p))?;
            Ok(OsRng())
        }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            random_device::read(dest)
        }

        #[cfg(target_os = "emscripten")]
        fn max_chunk_size(&self) -> usize {
            // `Crypto.getRandomValues` documents `dest` should be at most 65536
            // bytes. `crypto.randomBytes` documents: "To minimize threadpool
            // task length variation, partition large randomBytes requests when
            // doing so as part of fulfilling a client request.
            65536
        }

        fn method_str(&self) -> &'static str { "/dev/random" }
    }
}


// Read from `/dev/random`, with chunks of limited size (1040 bytes).
// `/dev/random` uses the Hash_DRBG with SHA512 algorithm from NIST SP 800-90A.
// `/dev/urandom` uses the FIPS 186-2 algorithm, which is considered less
// secure. We choose to read from `/dev/random`.
//
// Since Solaris 11.3 the `getrandom` syscall is available. To make sure we can
// compile on both Solaris and on OpenSolaris derivatives, that do not have the
// function, we do a direct syscall instead of calling a library function.
//
// We have no way to differentiate between Solaris, illumos, SmartOS, etc.
#[cfg(target_os = "solaris")]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    use super::random_device;
    use super::OsRngImpl;

    use std::io;
    use std::io::Read;
    use std::fs::{File, OpenOptions};
    use std::os::unix::fs::OpenOptionsExt;
    use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};

    #[derive(Clone, Debug)]
    pub struct OsRng {
        method: OsRngMethod,
        initialized: bool,
    }

    #[derive(Clone, Debug)]
    enum OsRngMethod {
        GetRandom,
        RandomDevice,
    }

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> {
            if is_getrandom_available() {
                return Ok(OsRng { method: OsRngMethod::GetRandom,
                                  initialized: false });
            }
            let open = |p| OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NONBLOCK)
                .open(p);
            random_device::open("/dev/random", &open)?;
            Ok(OsRng { method: OsRngMethod::RandomDevice, initialized: false })
        }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            match self.method {
                OsRngMethod::GetRandom => getrandom_try_fill(dest, false),
                OsRngMethod::RandomDevice => random_device::read(dest),
            }
        }

        fn test_initialized(&mut self, dest: &mut [u8], blocking: bool)
            -> Result<usize, Error>
        {
            static OS_RNG_INITIALIZED: AtomicBool = ATOMIC_BOOL_INIT;
            if !self.initialized {
                self.initialized = OS_RNG_INITIALIZED.load(Ordering::Relaxed);
            }
            if self.initialized { return Ok(0); }

            let chunk_len = ::core::cmp::min(1024, dest.len());
            let dest = &mut dest[..chunk_len];

            match self.method {
                OsRngMethod::GetRandom => getrandom_try_fill(dest, blocking)?,
                OsRngMethod::RandomDevice => {
                    if blocking {
                        info!("OsRng: testing random device /dev/random");
                        // We already have a non-blocking handle, but now need a
                        // blocking one. Not much choice except opening it twice
                        let mut file = File::open("/dev/random")
                            .map_err(random_device::map_err)?;
                        file.read(dest).map_err(random_device::map_err)?;
                    } else {
                        self.fill_chunk(dest)?;
                    }
                }
            };
            OS_RNG_INITIALIZED.store(true, Ordering::Relaxed);
            self.initialized = true;
            Ok(chunk_len)
        }

        fn max_chunk_size(&self) -> usize {
            // The documentation says 1024 is the maximum for getrandom, but
            // 1040 for /dev/random.
            1024
        }

        fn method_str(&self) -> &'static str {
            match self.method {
                OsRngMethod::GetRandom => "getrandom",
                OsRngMethod::RandomDevice => "/dev/random",
            }
        }
    }

    fn getrandom(buf: &mut [u8], blocking: bool) -> libc::c_long {
        extern "C" {
            fn syscall(number: libc::c_long, ...) -> libc::c_long;
        }

        const SYS_GETRANDOM: libc::c_long = 143;
        const GRND_NONBLOCK: libc::c_uint = 0x0001;
        const GRND_RANDOM: libc::c_uint = 0x0002;

        unsafe {
            syscall(SYS_GETRANDOM, buf.as_mut_ptr(), buf.len(),
                    if blocking { 0 } else { GRND_NONBLOCK } | GRND_RANDOM)
        }
    }

    fn getrandom_try_fill(dest: &mut [u8], blocking: bool) -> Result<(), Error> {
        let result = getrandom(dest, blocking);
        if result == -1 || result == 0 {
            let err = io::Error::last_os_error();
            let kind = err.kind();
            if kind == io::ErrorKind::WouldBlock {
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
        } else if result != dest.len() as i64 {
            return Err(Error::new(ErrorKind::Unavailable,
                                  "unexpected getrandom error"));
        }
        Ok(())
    }

    fn is_getrandom_available() -> bool {
        use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};
        use std::sync::{Once, ONCE_INIT};

        static CHECKER: Once = ONCE_INIT;
        static AVAILABLE: AtomicBool = ATOMIC_BOOL_INIT;

        CHECKER.call_once(|| {
            debug!("OsRng: testing getrandom");
            let mut buf: [u8; 0] = [];
            let result = getrandom(&mut buf, false);
            let available = if result == -1 {
                let err = io::Error::last_os_error().raw_os_error();
                err != Some(libc::ENOSYS)
            } else {
                true
            };
            AVAILABLE.store(available, Ordering::Relaxed);
            info!("OsRng: using {}", if available { "getrandom" } else { "/dev/random" });
        });

        AVAILABLE.load(Ordering::Relaxed)
    }
}


#[cfg(target_os = "cloudabi")]
mod imp {
    extern crate cloudabi;

    use std::io;
    use {Error, ErrorKind};
    use super::OsRngImpl;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> { Ok(OsRng) }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            let errno = unsafe { cloudabi::random_get(dest) };
            if errno == cloudabi::errno::SUCCESS {
                Ok(())
            } else {
                // Cloudlibc provides its own `strerror` implementation so we
                // can use `from_raw_os_error` here.
                Err(Error::with_cause(
                    ErrorKind::Unavailable,
                    "random_get() system call failed",
                    io::Error::from_raw_os_error(errno as i32),
                ))
            }
        }

        fn method_str(&self) -> &'static str { "cloudabi::random_get" }
    }
}


#[cfg(any(target_os = "macos", target_os = "ios"))]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    use super::OsRngImpl;

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

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> { Ok(OsRng) }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            let ret = unsafe {
                SecRandomCopyBytes(kSecRandomDefault,
                                   dest.len() as size_t,
                                   dest.as_mut_ptr())
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

        fn method_str(&self) -> &'static str { "SecRandomCopyBytes" }
    }
}


#[cfg(target_os = "freebsd")]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    use super::OsRngImpl;

    use std::ptr;
    use std::io;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> { Ok(OsRng) }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            let mib = [libc::CTL_KERN, libc::KERN_ARND];
            let mut len = dest.len();
            let ret = unsafe {
                libc::sysctl(mib.as_ptr(), mib.len() as libc::c_uint,
                             dest.as_mut_ptr() as *mut _, &mut len,
                             ptr::null(), 0)
            };
            if ret == -1 || len != dest.len() {
                return Err(Error::with_cause(
                    ErrorKind::Unavailable,
                    "kern.arandom sysctl failed",
                    io::Error::last_os_error()));
            }
            Ok(())
        }

        fn max_chunk_size(&self) -> usize { 256 }

        fn method_str(&self) -> &'static str { "kern.arandom" }
    }
}


#[cfg(any(target_os = "openbsd", target_os = "bitrig"))]
mod imp {
    extern crate libc;

    use {Error, ErrorKind};
    use super::OsRngImpl;

    use std::io;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> { Ok(OsRng) }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            let ret = unsafe {
                libc::getentropy(dest.as_mut_ptr() as *mut libc::c_void, dest.len())
            };
            if ret == -1 {
                return Err(Error::with_cause(
                    ErrorKind::Unavailable,
                    "getentropy failed",
                    io::Error::last_os_error()));
            }
            Ok(())
        }

        fn max_chunk_size(&self) -> usize { 256 }

        fn method_str(&self) -> &'static str { "getentropy" }
    }
}


#[cfg(target_os = "redox")]
mod imp {
    use Error;
    use super::random_device;
    use super::OsRngImpl;
    use std::fs::File;

    #[derive(Clone, Debug)]
    pub struct OsRng();

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> {
            random_device::open("rand:", &|p| File::open(p))?;
            Ok(OsRng())
        }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            random_device::read(dest)
        }

        fn method_str(&self) -> &'static str { "'rand:'" }
    }
}


#[cfg(target_os = "fuchsia")]
mod imp {
    extern crate fuchsia_cprng;

    use Error;
    use super::OsRngImpl;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> { Ok(OsRng) }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            fuchsia_cprng::cprng_draw(dest);
            Ok(())
        }

        fn method_str(&self) -> &'static str { "cprng_draw" }
    }
}


#[cfg(windows)]
mod imp {
    extern crate winapi;
    
    use {Error, ErrorKind};
    use super::OsRngImpl;

    use std::io;

    use self::winapi::shared::minwindef::ULONG;
    use self::winapi::um::ntsecapi::RtlGenRandom;
    use self::winapi::um::winnt::PVOID;

    #[derive(Clone, Debug)]
    pub struct OsRng;

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> { Ok(OsRng) }

        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            let ret = unsafe {
                RtlGenRandom(dest.as_mut_ptr() as PVOID, dest.len() as ULONG)
            };
            if ret == 0 {
                return Err(Error::with_cause(
                    ErrorKind::Unavailable,
                    "couldn't generate random bytes",
                    io::Error::last_os_error()));
            }
            Ok(())
        }

        fn max_chunk_size(&self) -> usize { <ULONG>::max_value() as usize }

        fn method_str(&self) -> &'static str { "RtlGenRandom" }
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
    use super::OsRngImpl;

    #[derive(Clone, Debug)]
    enum OsRngMethod {
        Browser,
        Node
    }

    #[derive(Clone, Debug)]
    pub struct OsRng(OsRngMethod);

    impl OsRngImpl for OsRng {
        fn new() -> Result<OsRng, Error> {
            let result = js! {
                try {
                    if (
                        typeof self === "object" &&
                        typeof self.crypto === "object" &&
                        typeof self.crypto.getRandomValues === "function"
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

                if ty == 1 { Ok(OsRng(OsRngMethod::Browser)) }
                else if ty == 2 { Ok(OsRng(OsRngMethod::Node)) }
                else { unreachable!() }
            } else {
                let err: WebError = js!{ return @{ result }.error }.try_into().unwrap();
                Err(Error::with_cause(ErrorKind::Unavailable, "WASM Error", err))
            }
        }


        fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            assert_eq!(mem::size_of::<usize>(), 4);

            let len = dest.len() as u32;
            let ptr = dest.as_mut_ptr() as i32;

            let result = match self.0 {
                OsRngMethod::Browser => js! {
                    try {
                        let array = new Uint8Array(@{ len });
                        self.crypto.getRandomValues(array);
                        HEAPU8.set(array, @{ ptr });

                        return { success: true };
                    } catch(err) {
                        return { success: false, error: err };
                    }
                },
                OsRngMethod::Node => js! {
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

        fn max_chunk_size(&self) -> usize { 65536 }

        fn method_str(&self) -> &'static str {
            match self.0 {
                OsRngMethod::Browser => "Crypto.getRandomValues",
                OsRngMethod::Node => "crypto.randomBytes",
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

    #[test]
    fn test_os_rng_empty() {
        let mut r = OsRng::new().unwrap();

        let mut empty = [0u8; 0];
        r.fill_bytes(&mut empty);
    }

    #[test]
    fn test_os_rng_huge() {
        let mut r = OsRng::new().unwrap();

        let mut huge = [0u8; 100_000];
        r.fill_bytes(&mut huge);
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
