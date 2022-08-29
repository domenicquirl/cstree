use super::{traits::*, TokenKey};

use std::num::NonZeroUsize;

use fxhash::FxBuildHasher as Hasher;
use lasso::{Capacity, Rodeo, Spur, ThreadedRodeo};

/// Default number of strings that the interner will initially allocate space for.
/// Value recommended by the author of `lasso`.
const DEFAULT_STRING_CAPACITY: usize = 512;

/// Default memory in bytes that the interner will initially allocate space for.
/// Value recommended by the author of `lasso`.
const DEFAULT_BYTE_CAPACITY: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(4096) };

/// The default [`Interner`] used to deduplicate green token strings.
#[derive(Debug)]
pub struct TokenInterner {
    rodeo: Rodeo<Spur, Hasher>,
}

impl TokenInterner {
    pub(super) fn new() -> Self {
        Self {
            rodeo: Rodeo::with_capacity_and_hasher(
                Capacity::new(DEFAULT_STRING_CAPACITY, DEFAULT_BYTE_CAPACITY),
                Hasher::default(),
            ),
        }
    }
}

impl Resolver<TokenKey> for TokenInterner {
    #[inline]
    fn try_resolve(&self, key: TokenKey) -> Option<&str> {
        <Rodeo<Spur, Hasher> as Resolver<TokenKey>>::try_resolve(&self.rodeo, key)
    }

    #[inline]
    fn resolve(&self, key: TokenKey) -> &str {
        <Rodeo<Spur, Hasher> as Resolver<TokenKey>>::resolve(&self.rodeo, key)
    }
}

impl Interner<TokenKey> for TokenInterner {
    type Error = <Rodeo<Spur, Hasher> as Interner<TokenKey>>::Error;

    #[inline]
    fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
        <Rodeo<Spur, Hasher> as Interner<TokenKey>>::try_get_or_intern(&mut self.rodeo, text)
    }

    #[inline]
    fn get_or_intern(&mut self, text: &str) -> TokenKey {
        <Rodeo<Spur, Hasher> as Interner<TokenKey>>::get_or_intern(&mut self.rodeo, text)
    }
}

/// A threadsafe [`Interner`] for deduplicating [`GreenToken`](crate::green::token::GreenToken) strings.
///
/// Note that [`Interner`] and [`Resolver`] are also implemented for  `&MultiThreadTokenInterner` so you can pass `&mut
/// &interner` in shared contexts.
#[derive(Debug)]
pub struct MultiThreadTokenInterner {
    rodeo: ThreadedRodeo<Spur, Hasher>,
}

impl MultiThreadTokenInterner {
    pub(super) fn new() -> Self {
        Self {
            rodeo: ThreadedRodeo::with_capacity_and_hasher(
                Capacity::new(DEFAULT_STRING_CAPACITY, DEFAULT_BYTE_CAPACITY),
                Hasher::default(),
            ),
        }
    }
}

impl Resolver<TokenKey> for MultiThreadTokenInterner {
    #[inline]
    fn try_resolve(&self, key: TokenKey) -> Option<&str> {
        <ThreadedRodeo<Spur, Hasher> as Resolver<TokenKey>>::try_resolve(&self.rodeo, key)
    }

    #[inline]
    fn resolve(&self, key: TokenKey) -> &str {
        <ThreadedRodeo<Spur, Hasher> as Resolver<TokenKey>>::resolve(&self.rodeo, key)
    }
}

impl Interner<TokenKey> for MultiThreadTokenInterner {
    type Error = <ThreadedRodeo<Spur, Hasher> as Interner<TokenKey>>::Error;

    #[inline]
    fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
        <ThreadedRodeo<Spur, Hasher> as Interner<TokenKey>>::try_get_or_intern(&mut self.rodeo, text)
    }

    #[inline]
    fn get_or_intern(&mut self, text: &str) -> TokenKey {
        <ThreadedRodeo<Spur, Hasher> as Interner<TokenKey>>::get_or_intern(&mut self.rodeo, text)
    }
}

impl Resolver<TokenKey> for &MultiThreadTokenInterner {
    #[inline]
    fn try_resolve(&self, key: TokenKey) -> Option<&str> {
        <ThreadedRodeo<Spur, Hasher> as Resolver<TokenKey>>::try_resolve(&self.rodeo, key)
    }

    #[inline]
    fn resolve(&self, key: TokenKey) -> &str {
        <ThreadedRodeo<Spur, Hasher> as Resolver<TokenKey>>::resolve(&self.rodeo, key)
    }
}

impl Interner<TokenKey> for &MultiThreadTokenInterner {
    type Error = <ThreadedRodeo<Spur, Hasher> as Interner<TokenKey>>::Error;

    #[inline]
    fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
        <&ThreadedRodeo<Spur, Hasher> as Interner<TokenKey>>::try_get_or_intern(&mut &self.rodeo, text)
    }

    #[inline]
    fn get_or_intern(&mut self, text: &str) -> TokenKey {
        <&ThreadedRodeo<Spur, Hasher> as Interner<TokenKey>>::get_or_intern(&mut &self.rodeo, text)
    }
}
