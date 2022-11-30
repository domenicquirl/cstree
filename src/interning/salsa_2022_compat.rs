//! # Using a `salsa` database as the interner for `cstree`
//!
//! <p
//! style="background:rgba(255,181,77,0.16);padding:0.75em;white-space:normal;font:inherit;">
//!  <strong>Warning</strong>: Compatibility is only provided for "Salsa 2022".
//!  This version is currently under active development and <code style="background:rgba(41,24,0,0.9);">cstree</code>'s
//!  compatibility features are unstable until there is an official
//!  release.
//!  Older versions of `salsa` are not supported.
//! </p>
//!
//! If you are using the `salsa` query system, you already have access to an implemenation of interning through
//! [`#[salsa::interned]`](macro@salsa::interned). This is all that is needed to use `cstree` and this module provides
//! the utilities needed to use `salsa`'s interners for working with syntax trees.
//!
//! Note that the primary benefit of this is that it avoids additional dependencies because it uses an interner that you
//! already depend on, but it can also be beneficial to use an interner that is more specialized towards string
//! interning. In particular, using `salsa`'s interning requires allocating all strings that are interned even if they
//! are deduplicated because they already exist in the interner.
//!
//! ## How to do it
//!
//! ```
//! # use cstree::testing::*;
//! # use cstree::GreenNodeBuilder;
//! # use cstree::interning::salsa_2022_compat::salsa;
//! # use cstree::impl_cstree_interning_for_salsa;
//! // Define the `salsa` jar, database and intern Id
//! #[salsa::jar(db = Db)]
//! pub struct Jar(SourceId);
//!
//! pub trait Db: salsa::DbWithJar<Jar> {}
//! impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}
//!
//! // If you are not a doctest and can put `Jar` at the root of your crate,
//! // this can just be `#[salsa::interned]`.
//! #[salsa::interned(jar = Jar)]
//! pub struct SourceId {
//!     #[return_ref]
//!     pub text: String,
//! }
//!
//! #[derive(Default)]
//! #[salsa::db(Jar)]
//! struct Database {
//!     storage: salsa::Storage<Self>,
//! }
//! impl salsa::Database for Database {}
//!
//! // Let `cstree` define a conversion trait and implement it for your database.
//! // `Database` is your db type, `SourceId` is your interning id, and `text` is
//! // its text field (all as defined above).
//! impl_cstree_interning_for_salsa!(impl Interning for Database => text as SourceId);
//!
//! // Build a tree with the `salsa` interner
//! let db = Database::default();
//! let interner = db.as_interner(); // <-- conversion happens here
//! let mut shared_interner = &interner;
//! let mut builder: GreenNodeBuilder<TestLang, _> = GreenNodeBuilder::with_interner(&mut shared_interner);
//! let (tree, _no_interner_because_it_was_borrowed) = {
//!     builder.start_node(TestSyntaxKind::Plus);
//!     builder.token(TestSyntaxKind::Float, "2.05");
//!     builder.token(TestSyntaxKind::Whitespace, " ");
//!     builder.token(TestSyntaxKind::Plus, "+");
//!     builder.token(TestSyntaxKind::Whitespace, " ");
//!     builder.token(TestSyntaxKind::Float, "7.32");
//!     builder.finish_node();
//!     builder.finish()
//! };
//! let tree: SyntaxNode<TestLang> = SyntaxNode::new_root(tree);
//! assert_eq!(tree.resolve_text(shared_interner), "2.05 + 7.32");
//! ```
//!
//! ## Working with `InternWithDb` directly
//! If you don't want the trait, or macros, or if you just need more control about what happens during interning and
//! resolution, you can skip using [`impl_cstree_interning_for_salsa`](crate::impl_cstree_interning_for_salsa) and use
//! [`InternWithDb`] directly.
//!
//! Because `salsa` generates inherent methods (and not, for example, a trait implementation), we need information about
//! the used interning id either way. All that `as_interner` does is construct an instance of `InternWithDb` that uses
//! the generated methods to invoke `salsa`s interner. The implementation expands to
//! ```text
//! InternWithDb::new(
//!     db,
//!     |db, text| SourceId::new(db, text),
//!     |db, id| id.text(db),
//! )
//! ```
//! but you may provide any function that doesn't capture.

#![cfg(feature = "salsa_2022_compat")]

#[cfg_attr(doc_cfg, doc(cfg(feature = "salsa_2022_compat")))]
pub use salsa;

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

/// Generates an extension trait `SalsaAsInterner` that lets you call `db.as_interner()` on your [`salsa::Database`] to
/// obtain a `cstree` compatible [`Interner`].
///
/// The `as_interner` method returns an instance of [`InternWithDb`] that uses the functions generated by `salsa` for
/// your Id type to perform interning and resolution.
///
/// If you have defined your interned text as
/// ```ignore
/// #[salsa::interned]
/// pub struct SourceId {
///     #[return_ref]
///     pub text: String,
/// }
/// ```
/// the syntax is
/// ```ignore
/// impl_cstree_interning_for_salsa!(impl Interning for YourDatabase => text as SourceId);
/// ```
/// where `text` the name of the interned field.
/// Note that the use of `#[return_ref]` is required.
#[macro_export]
#[cfg_attr(doc_cfg, doc(cfg(feature = "salsa_2022_compat")))]
macro_rules! impl_cstree_interning_for_salsa {
    (impl Interning for $db:ty => $name:ident as $id:ty) => {
        trait SalsaAsInterner {
            fn as_interner(&self) -> ::cstree::interning::salsa_2022_compat::InternWithDb<'_, $db, $id>;
        }

        impl SalsaAsInterner for Database {
            fn as_interner(&self) -> ::cstree::interning::salsa_2022_compat::InternWithDb<'_, $db, $id> {
                ::cstree::interning::salsa_2022_compat::InternWithDb::new(
                    self,
                    |db, text| <$id>::new(db, text),
                    |db, id| id.$name(db),
                )
            }
        }
    };
}

/// This type allows you to wrap access to a [`salsa::Database`] together with an interning and a lookup function, which
/// makes it implement [`Interner`] and [`Resolver`]. The [module documentation](self) shows how to use this with your
/// own database, or you can use [`impl_cstree_interning_for_salsa`](crate::impl_cstree_interning_for_salsa).
///
/// The interning traits are also implemented by `&InternWithDb`, as the `salsa` database supports interning through
/// shared references (see also [the `interning` module documentation](super)).
#[cfg_attr(doc_cfg, doc(cfg(feature = "salsa_2022_compat")))]
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
    /// Create an [`Interner`] that works with `cstree` but uses the given `db` from `salsa`.
    /// To do this, you need to provide a function for interning new strings that creates the [`InternedId`] that you
    /// defined with [`#[salsa::interned]`](macro@salsa::interned), and a second one that resolves an Id using your
    /// database. See the [module documentation](self) for an example.
    ///
    /// [`InternedId`]: salsa::interned::InternedId
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
