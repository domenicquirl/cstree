use core::fmt;

use super::TokenKey;

/// Common interface for all intern keys via conversion to and from `u32`.
///
/// # Safety
/// Implementations must guarantee that keys can round-trip in both directions: going from `Self` to `u32` to `Self` and
/// going from `u32` to `Self` to `u32` must each yield the original value.
pub unsafe trait InternKey: Copy + Eq + fmt::Debug {
    /// Convert `self` into its raw representation.
    fn into_u32(self) -> u32;

    /// Try to reconstruct an intern key from its raw representation.
    /// Returns `None` if `key` is not a valid key.
    fn try_from_u32(key: u32) -> Option<Self>;
}

/// The read-only part of an interner.
/// Allows to perform lookups of intern keys to resolve them to their interned text.
pub trait Resolver<Key: InternKey = TokenKey> {
    /// Tries to resolve the given `key` and return its interned text.
    ///
    /// If `self` does not contain any text for `key`, `None` is returned.
    fn try_resolve(&self, key: Key) -> Option<&str>;

    /// Resolves `key` to its interned text.
    ///
    /// # Panics
    /// Panics if there is no text for `key`.
    ///
    /// Compatibility implementations for interners from other crates may also panic if `key` cannot be converted to the
    /// key type of the external interner. Please ensure you configure any external interners appropriately (for
    /// example by choosing an appropriately sized key type).
    fn resolve(&self, key: Key) -> &str {
        self.try_resolve(key)
            .unwrap_or_else(|| panic!("failed to resolve `{key:?}`"))
    }
}

/// A full interner, which can intern new strings returning intern keys and also resolve intern keys to the interned
/// value.
///
/// **Note:** Because single-threaded interners may require mutable access, the methods on this trait take `&mut self`.
/// In order to use a multi- (or single)-threaded interner that allows access through a shared reference, it is
/// implemented for `&`[`MultiThreadTokenInterner`](crate::interning::MultiThreadTokenInterner), allowing it to be used
/// with a `&mut &MultiThreadTokenInterner`.
pub trait Interner<Key: InternKey = TokenKey>: Resolver<Key> {
    /// Represents possible ways in which interning may fail.
    /// For example, this might be running out of fresh intern keys, or failure to allocate sufficient space for a new
    /// value.
    type Error;

    /// Interns `text` and returns a new intern key for it.
    /// If `text` was already previously interned, it will not be used and the existing intern key for its value will be
    /// returned.
    fn try_get_or_intern(&mut self, text: &str) -> Result<Key, Self::Error>;

    /// Interns `text` and returns a new intern key for it.
    ///
    /// # Panics
    /// Panics if the internment process raises an [`Error`](Interner::Error).
    fn get_or_intern(&mut self, text: &str) -> Key {
        self.try_get_or_intern(text)
            .unwrap_or_else(|_| panic!("failed to intern `{text:?}`"))
    }
}
