use rand_core::{Error, ErrorKind};
use core::fmt;

/// An error that can occur when [`JitterRng::test_timer`] fails.
///
/// [`JitterRng::test_timer`]: struct.JitterRng.html#method.test_timer
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimerError {
    /// No timer available.
    NoTimer,
    /// Timer too coarse to use as an entropy source.
    CoarseTimer,
    /// Timer is not monotonically increasing.
    NotMonotonic,
    /// Variations of deltas of time too small.
    TinyVariantions,
    /// Too many stuck results (indicating no added entropy).
    TooManyStuck,
    #[doc(hidden)]
    __Nonexhaustive,
}

impl TimerError {
    fn description(&self) -> &'static str {
        match *self {
            TimerError::NoTimer => "no timer available",
            TimerError::CoarseTimer => "coarse timer",
            TimerError::NotMonotonic => "timer not monotonic",
            TimerError::TinyVariantions => "time delta variations too small",
            TimerError::TooManyStuck => "too many stuck results",
            TimerError::__Nonexhaustive => unreachable!(),
        }
    }
}

impl fmt::Display for TimerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.description())
    }
}

#[cfg(feature = "std")]
impl ::std::error::Error for TimerError {
    fn description(&self) -> &str {
        self.description()
    }
}

impl From<TimerError> for Error {
    fn from(err: TimerError) -> Error {
        // Timer check is already quite permissive of failures so we don't
        // expect false-positive failures, i.e. any error is irrecoverable.
        Error::with_cause(ErrorKind::Unavailable,
                              "timer jitter failed basic quality tests", err)
    }
}

