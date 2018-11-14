// Copyright 2018 Developers of the Rand project.
// Copyright 2013-2015 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interface to the random number generator of the operating system.
//!
//! See `OsRng` documentation for more details.
#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand_os/0.1.0")]

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]
pub extern crate rand_core;
#[cfg(feature = "log")]
#[macro_use] extern crate log;

#[cfg(not(feature = "log"))]
#[macro_use]
mod dummy_log;

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
///
/// The bare Wasm target `wasm32-unknown-unknown` tries to call the javascript
/// methods directly, using either `stdweb` in combination with `cargo-web` or
/// `wasm-bindgen` depending on what features are activated for this crate.
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
    fn max_chunk_size(&self) -> usize { ::std::usize::MAX }

    // Name of the OS interface (used for logging).
    fn method_str(&self) -> &'static str;
}

#[cfg(any(target_os = "linux", target_os = "android",
          target_os = "netbsd", target_os = "dragonfly",
          target_os = "solaris", target_os = "redox",
          target_os = "haiku", target_os = "emscripten"))]
mod random_device;

#[cfg(any(target_os = "linux", target_os = "android"))]
mod linux_android;
#[cfg(any(target_os = "linux", target_os = "android"))]
use linux_android as imp;

#[cfg(target_os = "netbsd")] mod netbsd;
#[cfg(target_os = "netbsd")] use netbsd as imp;

#[cfg(any(target_os = "dragonfly", target_os = "haiku", target_os = "emscripten"))]
mod dragonfly_haiku_emscripten;
#[cfg(any(target_os = "dragonfly", target_os = "haiku", target_os = "emscripten"))]
use dragonfly_haiku_emscripten as imp;

#[cfg(target_os = "solaris")] mod solaris;
#[cfg(target_os = "solaris")] use solaris as imp;

#[cfg(target_os = "cloudabi")] mod cloudabi;
#[cfg(target_os = "cloudabi")] use cloudabi as imp;

#[cfg(any(target_os = "macos", target_os = "ios"))] mod macos;
#[cfg(any(target_os = "macos", target_os = "ios"))] use macos as imp;

#[cfg(target_os = "freebsd")] mod freebsd;
#[cfg(target_os = "freebsd")] use freebsd as imp;

#[cfg(any(target_os = "openbsd", target_os = "bitrig"))]
mod openbsd_bitrig;
#[cfg(any(target_os = "openbsd", target_os = "bitrig"))]
use openbsd_bitrig as imp;

#[cfg(target_os = "redox")] mod redox;
#[cfg(target_os = "redox")] use redox as imp;

#[cfg(target_os = "fuchsia")] mod fuchsia;
#[cfg(target_os = "fuchsia")] use fuchsia as imp;

#[cfg(windows)] mod windows;
#[cfg(windows)] use windows as imp;

#[cfg(all(target_arch = "wasm32",
          not(target_os = "emscripten"),
          feature = "stdweb"))]
mod wasm32_stdweb;
#[cfg(all(target_arch = "wasm32",
          not(target_os = "emscripten"),
          feature = "stdweb"))]
use wasm32_stdweb as imp;

#[cfg(all(target_arch = "wasm32",
          not(target_os = "emscripten"),
          not(feature = "stdweb"),
          feature = "wasm-bindgen"))]
mod wasm32_bindgen;
#[cfg(all(target_arch = "wasm32",
          not(target_os = "emscripten"),
          not(feature = "stdweb"),
          feature = "wasm-bindgen"))]
use wasm32_bindgen as imp;

#[cfg(not(any(
    target_os = "linux", target_os = "android",
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
compile_error!("OS RNG support is not added for this platform");
