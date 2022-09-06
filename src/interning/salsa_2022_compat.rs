#![cfg(feature = "salsa_2022_compat")]

use core::fmt;

use super::{InternKey, Interner, Resolver, TokenKey};

#[cfg_attr(doc_cfg, doc(cfg(feature = "salsa_2022_compat")))]
impl salsa::AsId for TokenKey {
    fn as_id(self) -> salsa::Id {
        salsa::Id::from_u32(self.into_u32())
    }

    /// Create an instance of the intern-key from an ID.
    ///
    /// # Panics
    /// Panics if the given `id` from `salsa` cannot be represented by a [`TokenKey`].
    fn from_id(id: salsa::Id) -> Self {
        TokenKey::try_from_u32(id.as_u32())
            .unwrap_or_else(|| panic!("`salsa::Id` is invalid for `TokenKey`'s keyspace: {id:?}"))
    }
}

pub struct InternWithDb<'db, Db: salsa::Database, Id: salsa::interned::InternedId> {
    db:     &'db Db,
    intern: fn(&Db, text: String) -> Id,
    lookup: fn(&Db, Id) -> &str,
}

impl<'db, Db: salsa::Database, Id: salsa::interned::InternedId> fmt::Debug for InternWithDb<'db, Db, Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("InternWithDb")
    }
}

impl<'db, Db: salsa::Database, Id: salsa::interned::InternedId> InternWithDb<'db, Db, Id> {
    pub fn new(db: &'db Db, intern: fn(&Db, text: String) -> Id, lookup: fn(&Db, Id) -> &str) -> Self {
        Self { db, intern, lookup }
    }
}

impl<'db, Db: salsa::Database, Id: salsa::interned::InternedId> Resolver<TokenKey> for InternWithDb<'db, Db, Id> {
    fn try_resolve(&self, key: TokenKey) -> Option<&'db str> {
        use salsa::AsId;

        let key = Id::from_id(key.as_id());
        let text = (self.lookup)(self.db, key);
        Some(text)
    }
}

impl<'db, Db: salsa::Database, Id: salsa::interned::InternedId> Interner<TokenKey> for InternWithDb<'db, Db, Id> {
    type Error = std::convert::Infallible;

    fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
        use salsa::AsId;

        let id = (self.intern)(self.db, text.to_string());
        Ok(TokenKey::from_id(id.as_id()))
    }
}

impl<'db, Db: salsa::Database, Id: salsa::interned::InternedId> Resolver<TokenKey> for &InternWithDb<'db, Db, Id> {
    fn try_resolve(&self, key: TokenKey) -> Option<&'db str> {
        use salsa::AsId;

        let key = Id::from_id(key.as_id());
        let text = (self.lookup)(self.db, key);
        Some(text)
    }
}

impl<'db, Db: salsa::Database, Id: salsa::interned::InternedId> Interner<TokenKey> for &InternWithDb<'db, Db, Id> {
    type Error = std::convert::Infallible;

    fn try_get_or_intern(&mut self, text: &str) -> Result<TokenKey, Self::Error> {
        use salsa::AsId;

        let id = (self.intern)(self.db, text.to_string());
        Ok(TokenKey::from_id(id.as_id()))
    }
}
