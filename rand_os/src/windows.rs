extern crate winapi;

use rand_core::{Error, ErrorKind};
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
