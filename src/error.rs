// Copyright 2017-2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Error types

use core::fmt;

#[cfg(feature="std")]
use std::error::Error as stdError;

/// Error kind which can be matched over.
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum ErrorKind {
    /// Permanent failure: likely not recoverable without user action.
    Unavailable,
    /// Temporary failure: recommended to retry a few times, but may also be
    /// irrecoverable.
    Transient,
    /// Not ready yet: recommended to try again a little later.
    NotReady,
    /// Uncategorised error
    Other,
    #[doc(hidden)]
    __Nonexhaustive,
}

impl ErrorKind {
    /// True if this kind of error may resolve itself on retry.
    /// 
    /// See also `should_wait()`.
    pub fn should_retry(self) -> bool {
        match self {
            ErrorKind::Transient | ErrorKind::NotReady => true,
            _ => false,
        }
    }
    
    /// True if we should retry but wait before retrying
    /// 
    /// This implies `should_retry()` is true.
    pub fn should_wait(self) -> bool {
        self == ErrorKind::NotReady
    }
    
    /// A description of this error kind
    pub fn description(self) -> &'static str {
        match self {
            ErrorKind::Unavailable => "permanent failure or unavailable",
            ErrorKind::Transient => "transient failure",
            ErrorKind::NotReady => "not ready yet",
            ErrorKind::Other => "uncategorised",
            ErrorKind::__Nonexhaustive => unreachable!(),
        }
    }
}

/// Error type of random number generators
/// 
/// This is a relatively simple error type, designed for compatibility with and
/// without the Rust `std` library. It embeds a "kind" code, a message (static
/// string only), and an optional chained cause (`std` only).
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
    msg: &'static str,
    #[cfg(feature="std")]
    cause: Option<Box<stdError + Send + Sync>>,
}

impl Error {
    /// Create a new instance, with specified kind and a message.
    pub fn new(kind: ErrorKind, msg: &'static str) -> Self {
        #[cfg(feature="std")] {
            Error { kind: kind, msg: msg, cause: None }
        }
        #[cfg(not(feature="std"))] {
            Error { kind: kind, msg: msg }
        }
    }
    
    /// Create a new instance, with specified kind, message, and a
    /// chained cause.
    /// 
    /// Note: `stdError` is an alias for `std::error::Error`.
    /// 
    /// If not targetting `std` (i.e. `no_std`), this function is replaced by
    /// another with the same prototype, except that there are no bounds on the
    /// type `E` (because both `Box` and `stdError` are unavailable), and the
    /// `cause` is ignored.
    #[cfg(feature="std")]
    pub fn with_cause<E>(kind: ErrorKind, msg: &'static str, cause: E) -> Self
        where E: Into<Box<stdError + Send + Sync>>
    {
        Error { kind: kind, msg: msg, cause: Some(cause.into()) }
    }
    
    /// Create a new instance, with specified kind, message, and a
    /// chained cause.
    /// 
    /// In `no_std` mode the *cause* is ignored.
    #[cfg(not(feature="std"))]
    pub fn with_cause<E>(kind: ErrorKind, msg: &'static str, _cause: E) -> Self {
        Error { kind: kind, msg: msg }
    }
    
    /// Get the error kind
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }
    
    /// Get the error message
    pub fn msg(&self) -> &'static str {
        self.msg
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RNG error [{}]: {}", self.kind.description(), self.msg())
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
