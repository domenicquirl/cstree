//! Default interner implementations based on `lasso`.

#![cfg(feature = "lasso_compat")]

use std::{fmt, hash::BuildHasher, num::NonZeroUsize};

use lasso::{Capacity, Rodeo, ThreadedRodeo};
use rustc_hash::FxBuildHasher;

use crate::interning::{Interner, Resolver, TokenKey};

/// Default number of strings that the interner will initially allocate space for.
/// Value recommended by the author of `lasso`.
const DEFAULT_STRING_CAPACITY: usize = 512;

/// Default memory in bytes that the interner will initially allocate space for.
/// Value recommended by the author of `lasso`.
const DEFAULT_BYTE_CAPACITY: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(4096) };

macro_rules! impl_traits {
    (for $interner:ty $(, if #[cfg(feature = $feature:literal)])?) => {
        $(#[cfg_attr(doc_cfg, doc(cfg(feature = $feature)))])?
        impl Resolver<TokenKey> for $interner {
            #[inline]
            fn try_resolve(&self, key: TokenKey) -> Option<&str> {
                self.rodeo.try_resolve(&key)
            }

            #[inline]
            fn resolve(&self, key: TokenKey) -> &str {
                self.rodeo.resolve(&key)
            }
        }

        $(#[cfg_attr(doc_cfg, doc(cfg(feature = $feature)))])?
        impl Interner<TokenKey> for $interner {
            type Error = lasso::LassoError;

            #[inline]
            fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
                self.rodeo.try_get_or_intern(text)
            }

            #[inline]
            fn get_or_intern(&mut self, text: &str) -> TokenKey {
                self.rodeo.get_or_intern(text)
            }
        }
    };
}

/// The default [`Interner`] used to deduplicate green token strings.
pub struct TokenInterner {
    rodeo: Rodeo<TokenKey, FxBuildHasher>,
}

impl TokenInterner {
    pub(in crate::interning) fn new() -> Self {
        Self {
            rodeo: Rodeo::with_capacity_and_hasher(
                Capacity::new(DEFAULT_STRING_CAPACITY, DEFAULT_BYTE_CAPACITY),
                FxBuildHasher,
            ),
        }
    }

    /// Returns the [`Rodeo`] backing this interner.
    #[cfg_attr(doc_cfg, doc(cfg(feature = "lasso_compat")))]
    #[inline]
    pub fn into_inner(self) -> Rodeo<TokenKey, impl BuildHasher> {
        self.rodeo
    }
}

impl fmt::Debug for TokenInterner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("TokenInterner")
    }
}

impl_traits!(for TokenInterner);

#[cfg(feature = "multi_threaded_interning")]
pub use multi_threaded::MultiThreadedTokenInterner;

#[cfg(feature = "multi_threaded_interning")]
mod multi_threaded {
    use super::*;

    use std::sync::Arc as StdArc;

    /// A threadsafe [`Interner`] for deduplicating [`GreenToken`](crate::green::GreenToken) strings.
    ///
    /// Note that [`Interner`] and [`Resolver`] are also implemented for `&MultiThreadTokenInterner` and
    /// `Arc<MultiThreadTokenInterner>` so you can pass a mutable reference to either of these in shared contexts.
    #[cfg_attr(doc_cfg, doc(cfg(feature = "multi_threaded_interning")))]
    pub struct MultiThreadedTokenInterner {
        rodeo: ThreadedRodeo<TokenKey, FxBuildHasher>,
    }

    impl MultiThreadedTokenInterner {
        pub(in crate::interning) fn new() -> Self {
            Self {
                rodeo: ThreadedRodeo::with_capacity_and_hasher(
                    Capacity::new(DEFAULT_STRING_CAPACITY, DEFAULT_BYTE_CAPACITY),
                    FxBuildHasher,
                ),
            }
        }
    }

    impl fmt::Debug for MultiThreadedTokenInterner {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("MultiThreadedTokenInterner")
        }
    }

    impl_traits!(for MultiThreadedTokenInterner, if #[cfg(feature = "multi_threaded_interning")]);
    impl_traits!(for StdArc<MultiThreadedTokenInterner>, if #[cfg(feature = "multi_threaded_interning")]);
}
