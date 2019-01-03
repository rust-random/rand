// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implementation for the Solaris family
//!
//! Read from `/dev/random`, with chunks of limited size (1040 bytes).
//! `/dev/random` uses the Hash_DRBG with SHA512 algorithm from NIST SP 800-90A.
//! `/dev/urandom` uses the FIPS 186-2 algorithm, which is considered less
//! secure. We choose to read from `/dev/random`.
//!
//! Since Solaris 11.3 the `getrandom` syscall is available. To make sure we can
//! compile on both Solaris and on OpenSolaris derivatives, that do not have the
//! function, we do a direct syscall instead of calling a library function.
//!
//! We have no way to differentiate between Solaris, illumos, SmartOS, etc.
extern crate libc;

use rand_core::{Error, ErrorKind};
use super::random_device;
use super::OsRngImpl;

use std::io;
use std::io::Read;
use std::fs::{File, OpenOptions};
use std::os::unix::fs::OpenOptionsExt;
use std::sync::atomic::{AtomicBool, ATOMIC_BOOL_INIT, Ordering};
use std::cmp;

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

        let chunk_len = cmp::min(1024, dest.len());
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
