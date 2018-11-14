use rand_core::Error;
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
