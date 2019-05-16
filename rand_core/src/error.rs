// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error types

use core::fmt;

#[cfg(feature="std")]
use std::error::Error as stdError;
#[cfg(feature="std")]
use std::io;



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
    /// The error message
    pub msg: &'static str,
    #[cfg(feature="std")]
    cause: Option<Box<stdError + Send + Sync>>,
}

impl Error {
    /// Create a new instance, with a message.
    pub fn new(msg: &'static str) -> Self {
        #[cfg(feature="std")] {
            Error { msg, cause: None }
        }
        #[cfg(not(feature="std"))] {
            Error {  msg }
        }
    }
    
    /// Create a new instance, with a message and a chained cause.
    /// 
    /// Note: `stdError` is an alias for `std::error::Error`.
    /// 
    /// If not targetting `std` (i.e. `no_std`), this function is replaced by
    /// another with the same prototype, except that there are no bounds on the
    /// type `E` (because both `Box` and `stdError` are unavailable), and the
    /// `cause` is ignored.
    #[cfg(feature="std")]
    pub fn with_cause<E>(msg: &'static str, cause: E) -> Self
        where E: Into<Box<stdError + Send + Sync>>
    {
        Error { msg, cause: Some(cause.into()) }
    }
    
    /// Create a new instance, with a message and a chained cause.
    /// 
    /// In `no_std` mode the *cause* is ignored.
    #[cfg(not(feature="std"))]
    pub fn with_cause<E>(msg: &'static str, _cause: E) -> Self {
        Error { msg }
    }
    
    /// Take the cause, if any. This allows the embedded cause to be extracted.
    /// This uses `Option::take`, leaving `self` with no cause.
    #[cfg(feature="std")]
    pub fn take_cause(&mut self) -> Option<Box<stdError + Send + Sync>> {
        self.cause.take()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[cfg(feature="std")] {
            if let Some(ref cause) = self.cause {
                return write!(f, "{}; cause: {}",
                        self.msg, cause);
            }
        }
        write!(f, "{}", self.msg)
    }
}

#[cfg(feature="std")]
impl stdError for Error {
    fn description(&self) -> &str {
        self.msg
    }

    fn cause(&self) -> Option<&stdError> {
        self.cause.as_ref().map(|e| e.as_ref() as &stdError)
    }
}

#[cfg(feature="std")]
impl From<Error> for io::Error {
    fn from(error: Error) -> Self {
        io::Error::new(io::ErrorKind::Other, error)
    }
}
