#![forbid(missing_debug_implementations, unconditional_recursion)]
#![deny(unsafe_code, future_incompatible)]
// #![warn(missing_docs)]

#[cfg(feature = "concurrent")]
pub mod channel;
pub mod events;
