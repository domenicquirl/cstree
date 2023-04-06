//! Types and Traits for efficient String storage and deduplication.
//!
//! Because `cstree` is aimed at _concrete_ syntax trees that faithfully represent all of the original program input,
//! `cstree` aks for the text of each token when building a syntax tree. You'll notice this when looking at
//! [`GreenNodeBuilder::token`], which takes the kind of token and a refernce to the text of the token in the source.
//!
//! Of course, there are tokens whose text will always be the same, such as punctuation (like a semicolon), keywords
//! (like `fn`), or operators (like `<=`). Use [`Language::static_text`] when implementing `Language` to make `cstree`
//! aware of such tokens.
//!
//! There is, however, another category of tokens whose text will appear repeatedly, but for which we cannot know the
//! text upfront. Any variable, type, or method that is user-defined will likely be named more than once, but there is
//! no way to know beforehand what names a user will choose.
//!
//! In order to avoid storing the source text for these tokens many times over, `cstree` _interns_ the text of its
//! tokens (if that text is not static). What this means is that each unique string is only stored once. When a new
//! token is added - say, a variable -, we check if we already know its contents (the variable name). If the text is
//! new, we save it and give it a unique Id. If we have seen the text before, we look up its unique Id and don't need to
//! keep the new data around. As an additional benefit, interning also makes it much cheaper to copy source text around
//! and also to compare it with other source text, since what is actually being copied or compared is just an integer.
//!
//! ## I just want to build a syntax tree
//!
//! If you don't want to worry about this for now, you (mostly) can! All required functionality is implemented in
//! `cstree` and you can just use [`GreenNodeBuilder::new`] to obtain a tree builder with everything set up (see the
//! [crate documentation] for more on how to get started). This will create an interner, which the builder returns
//! together with the syntax tree on [`finish`] as part of its node cache (call [`NodeCache::into_interner`] on the
//! result to get the interner out).
//!
//! Here begins the part where you do have to think about interning: `cstree` needs the interner you get when you want
//! to look at the source text for some part of the syntax tree, so you'll have to keep it around somehow until the
//! point where you need it.
//!
//! How best to do this depends on what you need the text for. If the code that accesses the text is close-by, it might
//! be enough to pass the return value to the functions that need it (within `cstree` or in your code). Other options
//! could be to store the interner together with the syntax tree. If you use [`SyntaxNode::new_root_with_resolver`], you
//! get a syntax tree that can handle text without any need to manage and pass an interner (the reason the method is
//! called `_with_resolver` and not `_with_interner` is that it doesn't actually needs a full [`Interner`] -- once the
//! tree is created, no more text will be added, so it just needs to be able to look up text. This part is called a
//! [`Resolver`]). Or you could put the interner somewhere "global", where you can easily access it from anywhere.
//!
//! ## Using other interners
//!
//! By default, `cstree` uses its own, simple interner implementation. You can obtain an interner by calling
//! [`new_interner`], or bring your own by implementing the [`Resolver`] and [`Interner`] traits defined in this module.
//! Most methods in `cstree` require that you support interning [`TokenKey`]s. `TokenKey` implements [`InternKey`], so
//! your implementation can use that to convert to whatever types it uses for its internal representation. Note that
//! there is no way to change the size of the internal representation.
//!
//! ### `lasso`
//! Using features, you can enable support for some third-party interners. The primary one is [`lasso`], a crate focused
//! on efficient interning of text strings. This is enabled via the `lasso_compat` feature and adds the necessary trait
//! implementation to make `lasso`'s interners work with `cstree` (as well as a re-export of the matching version of
//! `lasso` here). If enabled, `cstree`'s built-in interning functionality is replaced with `lasso`'s more efficient one
//! transparently, so you'll now be returned a `lasso` interner from [`new_interner`].
//!
//! ### `salsa`
//! If you are using the "2022" version of the `salsa` incremental query framework, it is possible to use its interning
//! capabilities with `cstree` as well. Support for this is experimental, and you have to opt in via the
//! `salsa_2022_compat` feature. For instructions on how to do this, and whether you actually want to, please refer to
//! [the `salsa_compat` module documentation].
//!
//! ## Multi-threaded interners
//! If you want to use your interner on more than one thread, the interner needs to support interning new text through
//! shared access. With the `multi_threaded_interning` feature, you can get such an interner by calling
//! [`new_threaded_interner`]. The feature also enables support for `ThreadedRodeo`, the multi-threaded interner from
//! `lasso`.
//!
//! **You can pass a reference to that interner to anything that expects an [`Interner`]!**
//! While the interning methods on [`Interner`] require a `&mut self` to also work for single-threaded interners, both
//! [`Resolver`] and [`Interner`] will be implemented for `&interner` if `interner` is multi-threaded:
//!
//! ```
//! # use cstree::testing::{*, interning::*, Language as _};
//!
//! let interner = new_threaded_interner();
//! let mut builder: GreenNodeBuilder<MyLanguage, &MultiThreadedTokenInterner> =
//!     GreenNodeBuilder::from_interner(&interner);
//!
//! # builder.start_node(Root);
//! # builder.token(Int, "42");
//! # builder.finish_node();
//! parse(&mut builder, "42");
//! let (tree, cache) = builder.finish();
//!
//! // Note that we get a cache and interner back, because we passed an "owned" reference to `from_interner`
//! let used_interner = cache.unwrap().into_interner().unwrap();
//! assert_eq!(used_interner as *const _, &interner as *const _);
//!
//! let int = tree.children().next().unwrap();
//! assert_eq!(int.as_token().unwrap().text(&interner), Some("42"));
//! ```
//!
//! Here, we use `from_interner`, but pass it only a shared reference to "own". Take care to denote the type signature
//! of the `GreenNodeBuilder` appropriately.
//!
//! [crate documentation]: crate
//! [`Language::static_text`]: crate::Language::static_text
//! [`GreenNodeBuilder::token`]: crate::GreenNodeBuilder::token
//! [`GreenNodeBuilder::new`]: crate::GreenNodeBuilder::new
//! [`finish`]: crate::GreenNodeBuilder::finish
//! [`NodeCache::into_interner`]: crate::NodeCache::into_interner
//! [`SyntaxNode::new_root_with_resolver`]: crate::SyntaxNode::new_root_with_resolver
//! [`lasso`]: lasso
//! [the `salsa_compat` module documentation]: salsa_compat

mod traits;
pub use self::traits::*;

mod default_interner;

#[cfg(not(feature = "lasso_compat"))]
#[doc(inline)]
pub use default_interner::TokenInterner;

#[cfg(feature = "lasso_compat")]
mod lasso_compat;

#[cfg(feature = "lasso_compat")]
#[doc(inline)]
pub use lasso_compat::TokenInterner;

#[cfg(feature = "multi_threaded_interning")]
#[doc(inline)]
pub use lasso_compat::MultiThreadedTokenInterner;

#[cfg(feature = "lasso_compat")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "lasso_compat")))]
pub use lasso;

#[cfg(feature = "salsa_2022_compat")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "salsa_2022_compat")))]
pub mod salsa_compat;

use core::fmt;
use std::num::NonZeroU32;

pub use fxhash::FxBuildHasher as Hasher;

/// The intern key type for the source text of [`GreenToken`s](crate::green::GreenToken).
/// Each unique key uniquely identifies a deduplicated, interned source string.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct TokenKey {
    inner: NonZeroU32,
}

// Safety: we match `+ 1` and `- 1`, so it is always possible to round-trip.
unsafe impl InternKey for TokenKey {
    #[inline]
    fn into_u32(self) -> u32 {
        self.inner.get() - 1
    }

    fn try_from_u32(key: u32) -> Option<Self> {
        (key < u32::MAX).then(|| Self {
            // Safety: non-zero by increment.
            // Overflow is impossible under the check above.
            inner: unsafe { NonZeroU32::new_unchecked(key + 1) },
        })
    }
}

impl fmt::Debug for TokenKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("TokenKey({})", self.inner))
    }
}

/// Constructs a new, single-threaded [`Interner`](traits::Interner).
///
/// If you need the interner to be multi-threaded, see [`new_threaded_interner`].
#[inline]
pub fn new_interner() -> TokenInterner {
    TokenInterner::new()
}

/// Constructs a new [`Interner`](traits::Interner) that can be used across multiple threads.
///
/// Note that you can use `&MultiThreadTokenInterner` to access interning methods through a shared reference, as well as
/// construct new syntax trees. See [the module documentation](self) for more information and examples.
#[cfg(feature = "multi_threaded_interning")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "multi_threaded_interning")))]
#[inline]
pub fn new_threaded_interner() -> MultiThreadedTokenInterner {
    MultiThreadedTokenInterner::new()
}
