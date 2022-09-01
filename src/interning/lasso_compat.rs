//! Bridge between `cstree`'s and `lasso`'s types and traits.

use core::fmt;
use std::hash::{BuildHasher, Hash};

use super::{
    traits::{InternKey, Interner, Resolver},
    TokenKey,
};

// Safety: `InternKey` has the same invariant as `lasso::Key`
unsafe impl lasso::Key for TokenKey {
    fn into_usize(self) -> usize {
        self.into_u32() as usize
    }

    fn try_from_usize(int: usize) -> Option<Self> {
        let raw_key = u32::try_from(int).ok()?;
        Self::try_from_u32(raw_key)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LassoCompatError {
    LassoError(lasso::LassoError),
    KeyConversionError { lasso_key: usize },
}

impl From<lasso::LassoError> for LassoCompatError {
    #[inline]
    fn from(error: lasso::LassoError) -> Self {
        Self::LassoError(error)
    }
}

impl fmt::Display for LassoCompatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LassoCompatError::LassoError(lasso_error) => write!(f, "{lasso_error}"),
            LassoCompatError::KeyConversionError { lasso_key } => write!(
                f,
                "invalid key: failed to convert `lasso::Key` `{lasso_key}` to `InternKey`"
            ),
        }
    }
}

impl std::error::Error for LassoCompatError {}

macro_rules! compat_resolver {
    ($resolver:ident<K$(, $hasher:ident)?> $(where $($t:ident : $bound:ident),+)?) => {
        impl<K$(, $hasher)?> Resolver<TokenKey> for lasso::$resolver<K$(, $hasher)?>
        where
            K: lasso::Key,
            $($($t: $bound),+)?
        {
            fn try_resolve(&self, key: TokenKey) -> Option<&str> {
                let raw_key = TokenKey::into_u32(key);
                let lasso_key = K::try_from_usize(raw_key as usize)?;
                <Self as lasso::Resolver<K>>::try_resolve(self, &lasso_key)
            }

            fn resolve(&self, key: TokenKey) -> &str {
                let raw_key = TokenKey::into_u32(key);
                let lasso_key = K::try_from_usize(raw_key as usize).expect(&format!(
                    "invalid key: failed to convert `{key:?}` to `lasso::Key`"
                ));
                <Self as lasso::Resolver<K>>::resolve(self, &lasso_key)
            }
        }
    };
}

macro_rules! compat_interner {
    ($interner:ident<K, S> $(where $($t:ident : $bound:ident),+)?) => {
        impl<K, S> Interner<TokenKey> for lasso::$interner<K, S>
        where
            K: lasso::Key,
            S: BuildHasher,
            $($($t: $bound),+)?
        {
            type Error = LassoCompatError;

            fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
                let lasso_key = <Self as lasso::Interner<K>>::try_get_or_intern(self, text)?;
                let raw_key = K::into_usize(lasso_key);
                u32::try_from(raw_key)
                    .ok()
                    .and_then(TokenKey::try_from_u32)
                    .ok_or(LassoCompatError::KeyConversionError { lasso_key: raw_key })
            }

            fn get_or_intern(&mut self, text: &str) -> TokenKey {
                let lasso_key = <Self as lasso::Interner<K>>::get_or_intern(self, text);
                let raw_key = K::into_usize(lasso_key);
                u32::try_from(raw_key)
                    .ok()
                    .and_then(TokenKey::try_from_u32)
                    .ok_or(LassoCompatError::KeyConversionError { lasso_key: raw_key })
                    .unwrap_or_else(|_| panic!("invalid key: failed to convert `lasso::Key` `{raw_key}` to `InternKey` (failed to intern {text:?})"))
            }
        }
    };
}

compat_resolver!(RodeoReader<K, S>);
compat_resolver!(RodeoResolver<K>);

compat_resolver!(Rodeo<K, S>);
compat_interner!(Rodeo<K, S>);

compat_resolver!(ThreadedRodeo<K, S> where K: Hash, S: BuildHasher, S: Clone);
compat_interner!(ThreadedRodeo<K, S> where K: Hash, S: Clone);

impl<K, S> Resolver<TokenKey> for &lasso::ThreadedRodeo<K, S>
where
    K: lasso::Key + Hash,
    S: BuildHasher + Clone,
{
    #[inline]
    fn try_resolve(&self, key: TokenKey) -> Option<&str> {
        <lasso::ThreadedRodeo<K, S> as Resolver<TokenKey>>::try_resolve(self, key)
    }

    #[inline]
    fn resolve(&self, key: TokenKey) -> &str {
        <lasso::ThreadedRodeo<K, S> as Resolver<TokenKey>>::resolve(self, key)
    }
}

impl<K, S> Interner<TokenKey> for &lasso::ThreadedRodeo<K, S>
where
    K: lasso::Key + Hash,
    S: BuildHasher + Clone,
{
    type Error = <lasso::ThreadedRodeo<K, S> as Interner<TokenKey>>::Error;

    fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
        let lasso_key = <Self as lasso::Interner<K>>::try_get_or_intern(self, text)?;
        let raw_key = K::into_usize(lasso_key);
        u32::try_from(raw_key)
            .ok()
            .and_then(TokenKey::try_from_u32)
            .ok_or(LassoCompatError::KeyConversionError { lasso_key: raw_key })
    }

    fn get_or_intern(&mut self, text: &str) -> TokenKey {
        let lasso_key = <Self as lasso::Interner<K>>::get_or_intern(self, text);
        let raw_key = K::into_usize(lasso_key);
        u32::try_from(raw_key)
            .ok()
            .and_then(TokenKey::try_from_u32)
            .ok_or(LassoCompatError::KeyConversionError { lasso_key: raw_key })
            .unwrap_or_else(|_| panic!("invalid key: failed to convert `lasso::Key` `{raw_key}` to `InternKey` (failed to intern {text:?})"))
    }
}
