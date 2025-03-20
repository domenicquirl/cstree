#![cfg(not(feature = "lasso_compat"))]

use core::fmt;
use std::sync::Arc as StdArc;

use indexmap::IndexSet;
use rustc_hash::FxBuildHasher;

use super::{InternKey, Interner, Resolver, TokenKey};

/// The default [`Interner`] used to deduplicate green token strings.
#[derive(Debug)]
pub struct TokenInterner {
    id_set: IndexSet<String, FxBuildHasher>,
}

impl TokenInterner {
    pub(in crate::interning) fn new() -> Self {
        Self {
            id_set: IndexSet::default(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InternerError {
    KeySpaceExhausted,
}

impl fmt::Display for InternerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InternerError::KeySpaceExhausted => write!(f, "key space exhausted"),
        }
    }
}

impl std::error::Error for InternerError {}

impl Resolver<TokenKey> for TokenInterner {
    fn try_resolve(&self, key: TokenKey) -> Option<&str> {
        let index = key.into_u32() as usize;
        self.id_set.get_index(index).map(String::as_str)
    }
}

impl Resolver<TokenKey> for StdArc<TokenInterner> {
    fn try_resolve(&self, key: TokenKey) -> Option<&str> {
        let index = key.into_u32() as usize;
        self.id_set.get_index(index).map(String::as_str)
    }
}

// `TokenKey` can represent `1` to `u32::MAX` (due to the `NonNull` niche), so `u32::MAX` elements.
// Set indices start at 0, so everything shifts down by 1.
const N_INDICES: usize = u32::MAX as usize;

impl Interner<TokenKey> for TokenInterner {
    type Error = InternerError;

    fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
        if let Some(index) = self.id_set.get_index_of(text) {
            let raw_key = u32::try_from(index).unwrap_or_else(|_| {
                panic!("found interned text with invalid index `{index}` (index too high for keyspace)")
            });
            return Ok(TokenKey::try_from_u32(raw_key).unwrap_or_else(|| {
                panic!("found interned text with invalid index `{index}` (index too high for keyspace)")
            }));
        } else if self.id_set.len() >= N_INDICES {
            return Err(InternerError::KeySpaceExhausted);
        }

        let (index, added) = self.id_set.insert_full(text.to_string());
        debug_assert!(added, "tried to intern duplicate text");
        let raw_key = u32::try_from(index).unwrap_or_else(|_| panic!("interned `{index}` despite keyspace exhaustion"));
        TokenKey::try_from_u32(raw_key).ok_or(InternerError::KeySpaceExhausted)
    }
}
