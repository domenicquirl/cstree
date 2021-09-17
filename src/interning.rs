//! Types and Traits for efficient String storage and deduplication.
//!
//! Interning functionality is provided by the [`lasso`](lasso) crate.

pub use fxhash::FxBuildHasher as Hasher;

pub use crate::green::TokenInterner;

/// The index type for all interners. Each key represents
pub type Key = lasso::Spur;
pub use lasso::{Interner, IntoReader, IntoReaderAndResolver, IntoResolver, Reader, Resolver};

/// A string interner that caches strings quickly with a minimal memory footprint, returning a unique key to re-access
/// it with `O(1)` times. By default, `Rodeo` uses an [`fxhash`] [`Hasher`].
pub type Rodeo<S = Hasher> = lasso::Rodeo<Key, S>;

/// Constructs a new, single-threaded interner.
///
/// If you need the interner to be multi-threaded, see [`new_threaded_interner`].
#[inline]
pub fn new_interner() -> Rodeo {
    Rodeo::with_hasher(Hasher::default())
}

/// A string interner that caches strings quickly with a minimal memory footprint, returning a unique key to re-access
/// it with `O(1)` times. By default, `ThreadedRodeo` uses an [`fxhash`] [`Hasher`].
pub type ThreadedRodeo<S = Hasher> = lasso::ThreadedRodeo<Key, S>;

/// Constructs a new interner that can be used across multiple threads.
#[inline]
pub fn new_threaded_interner() -> ThreadedRodeo {
    ThreadedRodeo::with_hasher(Hasher::default())
}

/// A read-only view of a [`Rodeo`] or [`ThreadedRodeo`] that allows contention-free access to interned strings, both
/// key to string resolution and string to key lookups.
///
/// The hasher is the same as the Rodeo or ThreadedRodeo that created it.
/// Can be acquired with the `into_reader` methods (see also [`IntoReader`]).
pub type RodeoReader<S = Hasher> = lasso::RodeoReader<Key, S>;

/// A read-only view of a [`Rodeo`] or [`ThreadedRodeo`] that allows contention-free access to interned strings with
/// only key to string resolution.
///
/// Can be acquired with the `into_resolver` methods (see also [`IntoResolver`]).
pub type RodeoResolver = lasso::RodeoResolver<Key>;
pub use lasso::{Capacity, Iter, LassoError, LassoErrorKind, LassoResult, MemoryLimits, Strings};
