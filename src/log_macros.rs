#![allow(unused)]

macro_rules! trace { ($($x:tt)*) => (
    #[cfg(feature = "log")]
    log::trace!($($x)*);

    #[cfg(not(feature = "log"))]
    let _ = || { let _ = format_args!($($x)*); };
) }

macro_rules! debug { ($($x:tt)*) => (
    #[cfg(feature = "log")]
    log::debug!($($x)*)

    #[cfg(not(feature = "log"))]
    let _ = || { let _ = format_args!($($x)*); };
) }

macro_rules! info { ($($x:tt)*) => (
    #[cfg(feature = "log")]
    log::info!($($x)*);

    #[cfg(not(feature = "log"))]
    let _ = || { let _ = format_args!($($x)*); };
) }

macro_rules! warn { ($($x:tt)*) => (
    #[cfg(feature = "log")]
    log::warn!($($x)*);

    #[cfg(not(feature = "log"))]
    let _ = || { let _ = format_args!($($x)*); };
) }

macro_rules! error { ($($x:tt)*) => (
    #[cfg(feature = "log")]
    log::error!($($x)*);

    #[cfg(not(feature = "log"))]
    let _ = || { let _ = format_args!($($x)*); };
) }
