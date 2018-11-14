use rand_core::Error;
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
