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
//! `OsRng` is the preferred external source of entropy for most applications.
//! Commonly it is used to initialize a user-space RNG, which can then be used
//! to generate random values with much less overhead than `OsRng`.
//!
//! You may prefer to use [`EntropyRng`] instead of `OsRng`. It is unlikely, but
//! not entirely theoretical, for `OsRng` to fail. In such cases [`EntropyRng`]
//! falls back on a good alternative entropy source.
//!
//! `OsRng::new()` is guaranteed to be very cheap (after the first successful
//! call), and will never consume more than one file handle per process.
//!
//! # Usage example
//! ```
//! use rand_os::OsRng;
//! use rand_os::rand_core::RngCore;
//!
//! let mut os_rng = OsRng::new().unwrap();
//! let mut key = [0u8; 16];
//! os_rng.fill_bytes(&mut key);
//! let random_u64 = os_rng.next_u64();
//! ```
//!
//! # Platform sources
//!
//! | OS               | interface
//! |------------------|---------------------------------------------------------
//! | Linux, Android   | [`getrandom`][1] system call if available, otherwise [`/dev/urandom`][2] after reading from `/dev/random` once
//! | Windows          | [`RtlGenRandom`][3]
//! | macOS, iOS       | [`SecRandomCopyBytes`][4]
//! | FreeBSD          | [`kern.arandom`][5]
//! | OpenBSD, Bitrig  | [`getentropy`][6]
//! | NetBSD           | [`/dev/urandom`][7] after reading from `/dev/random` once
//! | Dragonfly BSD    | [`/dev/random`][8]
//! | Solaris, illumos | [`getrandom`][9] system call if available, otherwise [`/dev/random`][10]
//! | Fuchsia OS       | [`cprng_draw`][11]
//! | Redox            | [`rand:`][12]
//! | CloudABI         | [`random_get`][13]
//! | Haiku            | `/dev/random` (identical to `/dev/urandom`)
//! | Web browsers     | [`Crypto.getRandomValues`][14] (see [Support for WebAssembly and ams.js][14])
//! | Node.js          | [`crypto.randomBytes`][15] (see [Support for WebAssembly and ams.js][16])
//!
//! Rand doesn't have a blanket implementation for all Unix-like operating
//! systems that reads from `/dev/urandom`. This ensures all supported operating
//! systems are using the recommended interface and respect maximum buffer
//! sizes.
//!
//! ## Support for WebAssembly and ams.js
//!
//! The three Emscripten targets `asmjs-unknown-emscripten`,
//! `wasm32-unknown-emscripten` and `wasm32-experimental-emscripten` use
//! Emscripten's emulation of `/dev/random` on web browsers and Node.js.
//!
//! The bare WASM target `wasm32-unknown-unknown` tries to call the javascript
//! methods directly, using either `stdweb` or `wasm-bindgen` depending on what
//! features are activated for this crate. Note that if both features are
//! enabled `wasm-bindgen` will be used.
//!
//! ## Early boot
//!
//! It is possible that early in the boot process the OS hasn't had enough time
//! yet to collect entropy to securely seed its RNG, especially on virtual
//! machines.
//!
//! Some operating systems always block the thread until the RNG is securely
//! seeded. This can take anywhere from a few seconds to more than a minute.
//! Others make a best effort to use a seed from before the shutdown and don't
//! document much.
//!
//! A few, Linux, NetBSD and Solaris, offer a choice between blocking, and
//! getting an error. With `try_fill_bytes` we choose to get the error
//! ([`ErrorKind::NotReady`]), while the other methods use a blocking interface.
//!
//! On Linux (when the `genrandom` system call is not available) and on NetBSD
//! reading from `/dev/urandom` never blocks, even when the OS hasn't collected
//! enough entropy yet. As a countermeasure we try to do a single read from
//! `/dev/random` until we know the OS RNG is initialized (and store this in a
//! global static).
//!
//! # Panics and error handling
//!
//! We cannot guarantee that `OsRng` will fail, but if it does, it will likely
//! be either when `OsRng::new()` is first called or when data is first read.
//! If you wish to catch errors early, then test reading of at least one byte
//! from `OsRng` via [`try_fill_bytes`]. If this succeeds, it is extremely
//! unlikely that any further errors will occur.
//! 
//! Only [`try_fill_bytes`] is able to report the cause of an error; the other
//! [`RngCore`] methods may (depending on the error kind) retry several times,
//! but must eventually panic if the error persists.
//!
//! [`EntropyRng`]: ../rand/rngs/struct.EntropyRng.html
//! [`RngCore`]: ../rand_core/trait.RngCore.html
//! [`try_fill_bytes`]: ../rand_core/trait.RngCore.html#method.tymethod.try_fill_bytes
//! [`ErrorKind::NotReady`]: ../rand_core/enum.ErrorKind.html#variant.NotReady
//!
//! [1]: http://man7.org/linux/man-pages/man2/getrandom.2.html
//! [2]: http://man7.org/linux/man-pages/man4/urandom.4.html
//! [3]: https://msdn.microsoft.com/en-us/library/windows/desktop/aa387694.aspx
//! [4]: https://developer.apple.com/documentation/security/1399291-secrandomcopybytes?language=objc
//! [5]: https://www.freebsd.org/cgi/man.cgi?query=random&sektion=4
//! [6]: https://man.openbsd.org/getentropy.2
//! [7]: http://netbsd.gw.com/cgi-bin/man-cgi?random+4+NetBSD-current
//! [8]: https://leaf.dragonflybsd.org/cgi/web-man?command=random&section=4
//! [9]: https://docs.oracle.com/cd/E88353_01/html/E37841/getrandom-2.html
//! [10]: https://docs.oracle.com/cd/E86824_01/html/E54777/random-7d.html
//! [11]: https://fuchsia.googlesource.com/zircon/+/HEAD/docs/syscalls/cprng_draw.md
//! [12]: https://github.com/redox-os/randd/blob/master/src/main.rs
//! [13]: https://github.com/NuxiNL/cloudabi/blob/v0.20/cloudabi.txt#L1826
//! [14]: https://www.w3.org/TR/WebCryptoAPI/#Crypto-method-getRandomValues
//! [15]: https://nodejs.org/api/crypto.html#crypto_crypto_randombytes_size_callback
//! [16]: #support-for-webassembly-and-amsjs
#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://rust-random.github.io/rand/")]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]
// for stdweb
#![recursion_limit="128"]

pub extern crate rand_core;
#[cfg(feature = "log")]
#[macro_use] extern crate log;

// We have to do it here because we load macros
#[cfg(all(target_arch = "wasm32", not(target_os = "emscripten"),
          feature = "wasm-bindgen"))]
extern crate wasm_bindgen;
#[cfg(all(target_arch = "wasm32", not(target_os = "emscripten"),
          not(feature = "wasm-bindgen"),
          feature = "stdweb"))]
#[macro_use] extern crate stdweb;

#[cfg(any(
    target_os = "android",
    target_os = "bitrig",
    target_os = "cloudabi",
    target_os = "dragonfly",
    target_os = "emscripten",
    target_os = "freebsd",
    target_os = "fuchsia",
    target_os = "haiku",
    target_os = "ios",
    target_os = "linux",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "redox",
    target_os = "solaris",
    windows,
    all(target_arch = "wasm32", any(feature = "wasm-bindgen", feature = "stdweb"))
))]
mod impls;

#[cfg(any(
    target_os = "android",
    target_os = "bitrig",
    target_os = "cloudabi",
    target_os = "dragonfly",
    target_os = "emscripten",
    target_os = "freebsd",
    target_os = "fuchsia",
    target_os = "haiku",
    target_os = "ios",
    target_os = "linux",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "redox",
    target_os = "solaris",
    windows,
    all(target_arch = "wasm32", any(feature = "wasm-bindgen", feature = "stdweb"))
))]
pub use impls::OsRng;

// compile-time errors are temporarily disabled, see https://github.com/rust-random/rand/issues/681 
/*
#[cfg(all(
    target_arch = "wasm32",
    not(target_os = "emscripten"),
    not(feature = "wasm-bindgen"),
    not(feature = "stdweb"),
))]
compile_error!("enable either wasm_bindgen or stdweb feature");

#[cfg(all(
    target_arch = "wasm32",
    not(target_os = "emscripten"),
    feature = "wasm-bindgen",
    feature = "stdweb",
))]
compile_error!("wasm_bindgen and stdweb features should not be enabled together");

#[cfg(not(any(
    target_os = "android",
    target_os = "bitrig",
    target_os = "cloudabi",
    target_os = "dragonfly",
    target_os = "emscripten",
    target_os = "freebsd",
    target_os = "fuchsia",
    target_os = "haiku",
    target_os = "ios",
    target_os = "linux",
    target_os = "macos",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "redox",
    target_os = "solaris",
    windows,
    target_arch = "wasm32",
)))]
compile_error!("OS RNG support is not available for this platform");
*/
