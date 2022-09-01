//! Types and Traits for efficient String storage and deduplication.
//!
//! Interning functionality is provided by the [`lasso`](lasso) crate.

mod traits;
pub use self::traits::*;

mod token_interner;
pub use token_interner::{MultiThreadTokenInterner, TokenInterner};

mod lasso_compat;

use core::fmt;
use std::num::NonZeroU32;

pub use fxhash::FxBuildHasher as Hasher;
pub use lasso;

/// The intern key type for the source text of [`GreenToken`s](crate::green::token::GreenToken).
/// Each unique key uniquely identifies a deduplicated, interned source string.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct TokenKey {
    inner: NonZeroU32,
}

// Safety: we match `+ 1` and `- 1`, so it is always possible to round-trip.
unsafe impl InternKey for TokenKey {
    #[inline]
    fn into_u32(self) -> u32 {
        self.inner.get() - 1
    }

    fn try_from_u32(key: u32) -> Option<Self> {
        (key < u32::MAX).then(|| Self {
            // Safety: non-zero by increment.
            // Overflow is impossible under the check above.
            inner: unsafe { NonZeroU32::new_unchecked(key + 1) },
        })
    }
}

impl fmt::Debug for TokenKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("TokenKey({})", self.inner))
    }
}

/// Constructs a new, single-threaded [`Interner`](traits::Interner).
///
/// If you need the interner to be multi-threaded, see [`new_threaded_interner`].
#[inline]
pub fn new_interner() -> TokenInterner {
    TokenInterner::new()
}

/// Constructs a new [`Interner`](traits::Interner) that can be used across multiple threads.
///
/// Note that you can use `&mut &MultiThreadTokenInterner` to access interning methods through a shared reference.
#[inline]
pub fn new_threaded_interner() -> MultiThreadTokenInterner {
    MultiThreadTokenInterner::new()
}
