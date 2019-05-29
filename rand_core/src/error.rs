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


/// Error type of random number generators
///
/// In order to be compatible with `std` and `no_std`, this type has two
/// possible implementations: with `std` a boxed `Error` trait object is stored,
/// while with `no_std` we merely store an error code.
#[derive(Debug)]
pub struct Error {
    #[cfg(feature="std")]
    inner: Box<dyn std::error::Error + Send + Sync + 'static>,
    #[cfg(not(feature="std"))]
    code: NonZeroU32,
}

impl Error {
    /// Construct from any type supporting `std::error::Error`
    /// 
    /// Available only when configured with `std`.
    /// 
    /// See also `From<NonZeroU32>`, which is available with and without `std`.
    #[cfg(feature="std")]
    pub fn new<E>(err: E) -> Self
    where E: Into<Box<dyn std::error::Error + Send + Sync + 'static>>
    {
        Error { inner: err.into() }
    }
    
    /// Reference the inner error (`std` only)
    /// 
    /// When configured with `std`, this is a trivial operation and never
    /// panics. Without `std`, this method is simply unavailable.
    #[cfg(feature="std")]
    pub fn inner(&self) -> &(dyn std::error::Error + Send + Sync + 'static) {
        &*self.inner
    }
    
    /// Unwrap the inner error (`std` only)
    /// 
    /// When configured with `std`, this is a trivial operation and never
    /// panics. Without `std`, this method is simply unavailable.
    #[cfg(feature="std")]
    pub fn take_inner(self) -> Box<dyn std::error::Error + Send + Sync + 'static> {
        self.inner
    }
    
    /// Retrieve the error code, if any.
    /// 
    /// If this `Error` was constructed via `From<NonZeroU32>`, then this method
    /// will return this `NonZeroU32` code (for `no_std` this is always the
    /// case). Otherwise, this method will return `None`.
    pub fn code(&self) -> Option<NonZeroU32> {
        #[cfg(feature="std")] {
            self.inner.downcast_ref::<ErrorCode>().map(|c| c.0)
        }
        #[cfg(not(feature="std"))] {
            Some(self.code)
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[cfg(feature="std")] {
            write!(f, "{}", self.inner)
        }
        #[cfg(not(feature="std"))] {
            write!(f, "error code {}", self.code)
        }
    }
}

impl From<NonZeroU32> for Error {
    fn from(code: NonZeroU32) -> Self {
        #[cfg(feature="std")] {
            Error { inner: Box::new(ErrorCode(code)) }
        }
        #[cfg(not(feature="std"))] {
            Error { code }
        }
    }
}

#[cfg(feature="getrandom")]
impl From<getrandom::Error> for Error {
    fn from(error: getrandom::Error) -> Self {
        #[cfg(feature="std")] {
            Error { inner: Box::new(error) }
        }
        #[cfg(not(feature="std"))] {
            Error { code: error.code() }
        }
    }
}

#[cfg(feature="std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.inner.source()
    }
}

#[cfg(feature="std")]
impl From<Error> for std::io::Error {
    fn from(error: Error) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, error)
    }
}

#[cfg(feature="std")]
#[derive(Debug, Copy, Clone)]
struct ErrorCode(NonZeroU32);

#[cfg(feature="std")]
impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "error code {}", self.0)
    }
}

#[cfg(feature="std")]
impl std::error::Error for ErrorCode {}
