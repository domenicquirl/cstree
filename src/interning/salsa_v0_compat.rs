#![cfg(feature = "salsa_v0_compat")]

use core::fmt;

use super::{InternKey, Resolver, TokenKey};

#[cfg_attr(doc_cfg, doc(cfg(feature = "salsa_v0_compat")))]
impl salsa_v0::InternKey for TokenKey {
    /// Create an instance of the intern-key from a `u32` value.
    ///
    /// # Panics
    /// Panics if the given `key` from `salsa` cannot be represented by a [`TokenKey`].
    fn from_intern_id(key: salsa_v0::InternId) -> Self {
        TokenKey::try_from_u32(key.as_u32())
            .unwrap_or_else(|| panic!("`salsa::InternId` is invalid for `TokenKey`'s keyspace: {key}"))
    }

    fn as_intern_id(&self) -> salsa_v0::InternId {
        salsa_v0::InternId::from(self.into_u32())
    }
}

pub struct InternWithDb<'db, Db: salsa_v0::Database> {
    db:     &'db Db,
    intern: fn(&Db, text: String) -> TokenKey,
    lookup: fn(&Db, TokenKey) -> String,
}

impl<'db, Db: salsa_v0::Database> fmt::Debug for InternWithDb<'db, Db> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("InternWithDb")
    }
}

impl<'db, Db: salsa_v0::Database> InternWithDb<'db, Db> {
    pub fn new(db: &'db Db, intern: fn(&Db, text: String) -> TokenKey, lookup: fn(&Db, TokenKey) -> String) -> Self {
        Self { db, intern, lookup }
    }
}

// impl<'db, Db: salsa_v0::Database> Resolver<TokenKey> for InternWithDb<'db, Db> {
//     fn try_resolve(&self, key: TokenKey) -> Option<&str> {
//         let text = (self.lookup)(&self.db, key);
//         Some(&text)
//     }
// }
