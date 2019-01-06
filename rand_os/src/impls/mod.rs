use std::fmt;
use rand_core::{CryptoRng, RngCore, Error, impls};

#[cfg(not(feature = "log"))]
#[macro_use]
mod dummy_log;

/// A random number generator that retrieves randomness straight from the
/// operating system.
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
    fn max_chunk_size(&self) -> usize { ::std::usize::MAX }

    // Name of the OS interface (used for logging).
    fn method_str(&self) -> &'static str;
}

#[cfg(any(target_os = "linux", target_os = "android",
          target_os = "netbsd", target_os = "dragonfly",
          target_os = "solaris", target_os = "redox",
          target_os = "haiku", target_os = "emscripten"))]
mod random_device;

macro_rules! mod_use {
    ($cond:meta, $module:ident) => {
        #[$cond]
        mod $module;
        #[$cond]
        use self::$module as imp;
    }
}

mod_use!(cfg(target_os = "android"), linux_android);
mod_use!(cfg(target_os = "bitrig"), openbsd_bitrig);
mod_use!(cfg(target_os = "cloudabi"), cloudabi);
mod_use!(cfg(target_os = "dragonfly"), dragonfly_haiku_emscripten);
mod_use!(cfg(target_os = "emscripten"), dragonfly_haiku_emscripten);
mod_use!(cfg(target_os = "freebsd"), freebsd);
mod_use!(cfg(target_os = "fuchsia"), fuchsia);
mod_use!(cfg(target_os = "haiku"), dragonfly_haiku_emscripten);
mod_use!(cfg(target_os = "ios"), macos);
mod_use!(cfg(target_os = "linux"), linux_android);
mod_use!(cfg(target_os = "macos"), macos);
mod_use!(cfg(target_os = "netbsd"), netbsd);
mod_use!(cfg(target_os = "openbsd"), openbsd_bitrig);
mod_use!(cfg(target_os = "redox"), redox);
mod_use!(cfg(target_os = "solaris"), solaris);
mod_use!(cfg(windows), windows);

mod_use!(
    cfg(all(
        target_arch = "wasm32",
        not(target_os = "emscripten"),
        not(feature = "stdweb"),
        feature = "wasm-bindgen"
    )),
    wasm32_bindgen
);

mod_use!(
    cfg(all(
        target_arch = "wasm32",
        not(target_os = "emscripten"),
        not(feature = "wasm-bindgen"),
        feature = "stdweb",
    )),
    wasm32_stdweb
);

