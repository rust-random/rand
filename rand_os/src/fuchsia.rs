extern crate fuchsia_zircon;

use rand_core::{Error, ErrorKind};
use super::OsRngImpl;

#[derive(Clone, Debug)]
pub struct OsRng;

impl OsRngImpl for OsRng {
    fn new() -> Result<OsRng, Error> { Ok(OsRng) }

    fn fill_chunk(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        let mut read = 0;
        while read < dest.len() {
            match fuchsia_zircon::cprng_draw(&mut dest[read..]) {
                Ok(actual) => read += actual,
                Err(e) => {
                    return Err(Error::with_cause(
                        ErrorKind::Unavailable,
                        "cprng_draw failed",
                        e.into_io_error()));
                }
            };
        }
        Ok(())
    }

    fn max_chunk_size(&self) -> usize {
        fuchsia_zircon::sys::ZX_CPRNG_DRAW_MAX_LEN
    }

    fn method_str(&self) -> &'static str { "cprng_draw" }
}
