// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error types

use core::fmt;
use core::num::NonZeroU32;

/// TODO
#[derive(Debug, Copy, Clone)]
struct ErrorCode(NonZeroU32);

/// TODO
#[derive(Debug)]
pub struct Error {
    #[cfg(not(feature="std"))]
    code: ErrorCode,
    #[cfg(feature="std")]
    cause: Box<dyn std::error::Error + Send + Sync>,
}

impl Error {
    /// TODO
    pub fn from_code(code: NonZeroU32) -> Self {
        let code = ErrorCode(code);
        #[cfg(not(feature="std"))] {
            Self { code }
        }
        #[cfg(feature="std")] {
            Self { cause: Box::new(code) }
        }
    }

    /// TODO
    pub fn code(&self) -> Option<NonZeroU32> {
        #[cfg(not(feature="std"))] {
            Some(self.code.0)
        }
        #[cfg(feature="std")] {
            self.cause.downcast_ref().map(|r: &ErrorCode| r.0)
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO
        Ok(())
    }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO
        Ok(())
    }
}

#[cfg(feature="std")]
mod std_impls {
    use std::error::Error as StdError;
    use std::io;
    use super::{Error, ErrorCode};

    impl Error {
        /// TODO
        pub fn from_cause<E>(cause: E) -> Self
            where E: Into<Box<dyn StdError + Send + Sync>>
        {
            Self { cause: cause.into() }
        }

        /// TODO
        pub fn cause(self) -> Box<dyn StdError + Send + Sync> {
            self.cause
        }
    }

    impl StdError for ErrorCode { }
    impl StdError for Error { }

    impl From<Error> for io::Error {
        fn from(error: Error) -> Self {
            io::Error::new(io::ErrorKind::Other, error)
        }
    }
}
