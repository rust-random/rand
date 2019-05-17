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


// A randomly-chosen 24-bit prefix for our codes.
#[cfg(not(feature="std"))]
pub(crate) const CODE_PREFIX: u32 = 0x517e8100;

/// Error type of random number generators
/// 
/// This is a relatively simple error type, designed for compatibility with and
/// without the Rust `std` library. It embeds a message (static
/// string only), and an optional chained cause (`std` only). The
/// `msg` field can be accessed directly; cause can be accessed via
/// `std::error::Error::cause` or `Error::take_cause`. Construction can only be
/// done via `Error::new` or `Error::with_cause`.
#[derive(Debug)]
pub struct Error {
    msg: &'static str,
    #[cfg(feature="std")]
    cause: Option<Box<std::error::Error + Send + Sync>>,
    #[cfg(not(feature="std"))]
    code: NonZeroU32,
}

impl Error {
    /// Create a new instance, with a message.
    pub fn new(msg: &'static str) -> Self {
        #[cfg(feature="std")] {
            Error { msg, cause: None }
        }
        #[cfg(not(feature="std"))] {
            Error {  msg, code: NonZeroU32::new(CODE_PREFIX).unwrap() }
        }
    }
    
    /// Create a new instance, with a message and a chained cause.
    ///
    /// This function is only available with the `std` feature.
    // NOTE: with specialisation we could support both.
    #[cfg(feature="std")]
    pub fn with_cause<E>(msg: &'static str, cause: E) -> Self
        where E: Into<Box<std::error::Error + Send + Sync>>
    {
        Error { msg, cause: Some(cause.into()) }
    }
    
    /// Create a new instance, with a message and an error code.
    pub fn with_code(msg: &'static str, code: NonZeroU32) -> Self {
        #[cfg(feature="std")] {
            Error { msg, cause: Some(Box::new(ErrorCode(code))) }
        }
        #[cfg(not(feature="std"))] {
            Error { msg, code }
        }
    }

    /// Retrieve the error message.
    pub fn msg(&self) -> &str {
        self.msg
    }
    
    /// Take the cause, if any. This allows the embedded cause to be extracted.
    /// This uses `Option::take`, leaving `self` with no cause.
    ///
    /// This function is only available with the `std` feature.
    #[cfg(feature="std")]
    pub fn take_cause(&mut self) -> Option<Box<std::error::Error + Send + Sync>> {
        self.cause.take()
    }
    
    /// Retrieve the error code, if any.
    #[cfg(not(feature="std"))]
    pub fn code(&self) -> Option<NonZeroU32> {
        #[cfg(feature="std")] {
            self.cause.as_ref().and_then(|b| b.downcast_ref::<ErrorCode>()).map(|c| c.0)
        }
        #[cfg(not(feature="std"))] {
            Some(self.code)
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

#[cfg(feature="getrandom")]
impl From<getrandom::Error> for Error {
    fn from(error: getrandom::Error) -> Self {
        let msg = "getrandom error";
        #[cfg(feature="std")] {
            Error { msg, cause: Some(Box::new(error)) }
        }
        #[cfg(not(feature="std"))] {
            Error { msg, code: error.code() }
        }
    }
}

#[cfg(feature="std")]
impl std::error::Error for Error {
    fn description(&self) -> &str {
        self.msg
    }

    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.cause.as_ref().map(|e| e.as_ref() as &std::error::Error)
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
        write!(f, "ErrorCode({})", self.0)
    }
}

#[cfg(feature="std")]
impl std::error::Error for ErrorCode {}
