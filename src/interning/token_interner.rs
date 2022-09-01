//! Default interner implementations based on `lasso`.

use std::num::NonZeroUsize;

use fxhash::FxBuildHasher as Hasher;
use lasso::{Capacity, Rodeo, ThreadedRodeo};

use super::{Interner, Resolver, TokenKey};

/// Default number of strings that the interner will initially allocate space for.
/// Value recommended by the author of `lasso`.
const DEFAULT_STRING_CAPACITY: usize = 512;

/// Default memory in bytes that the interner will initially allocate space for.
/// Value recommended by the author of `lasso`.
const DEFAULT_BYTE_CAPACITY: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(4096) };

macro_rules! impl_traits {
    (for $interner:ty) => {
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
#[derive(Debug)]
pub struct TokenInterner {
    rodeo: Rodeo<TokenKey, Hasher>,
}

impl TokenInterner {
    pub(in crate::interning) fn new() -> Self {
        Self {
            rodeo: Rodeo::with_capacity_and_hasher(
                Capacity::new(DEFAULT_STRING_CAPACITY, DEFAULT_BYTE_CAPACITY),
                Hasher::default(),
            ),
        }
    }
}

impl_traits!(for TokenInterner);

/// A threadsafe [`Interner`] for deduplicating [`GreenToken`](crate::green::token::GreenToken) strings.
///
/// Note that [`Interner`] and [`Resolver`] are also implemented for  `&MultiThreadTokenInterner` so you can pass `&mut
/// &interner` in shared contexts.
#[derive(Debug)]
pub struct MultiThreadTokenInterner {
    rodeo: ThreadedRodeo<TokenKey, Hasher>,
}

impl MultiThreadTokenInterner {
    pub(in crate::interning) fn new() -> Self {
        Self {
            rodeo: ThreadedRodeo::with_capacity_and_hasher(
                Capacity::new(DEFAULT_STRING_CAPACITY, DEFAULT_BYTE_CAPACITY),
                Hasher::default(),
            ),
        }
    }
}

impl_traits!(for MultiThreadTokenInterner);
impl_traits!(for &MultiThreadTokenInterner);
