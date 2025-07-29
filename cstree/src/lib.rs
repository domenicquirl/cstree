//! `cstree` is a generic library for creating and working with concrete syntax trees (CSTs).
//!
//! "Traditional" abstract syntax trees (ASTs) usually contain different types of nodes which
//! represent different syntactical elements of the source text of a document and reduce its
//! information to the minimal amount necessary to correctly interpret it. In contrast, CSTs are
//! lossless representations of the entire input where all tree nodes are represented homogeneously
//! (i.e., the nodes are _untyped_), but are tagged with a [`RawSyntaxKind`]  to determine the kind
//! of grammatical element they represent.
//!
//! One big advantage of this representation is that it cannot only recreate the original source
//! exactly, but also lends itself very well to the representation of _incomplete or erroneous_
//! trees and is thus highly suited for usage in contexts such as IDEs or any other application
//! where a user is _editing_ the source text.
//!
//! The concept of and the data structures for `cstree`'s syntax trees are inspired in part by
//! Swift's [libsyntax](https://github.com/apple/swift/tree/5e2c815edfd758f9b1309ce07bfc01c4bc20ec23/lib/Syntax).
//! Trees consist of two layers: the inner tree (called _green_ tree) contains the actual source
//! text as position independent green nodes. Tokens and nodes that appear identically at multiple
//! places in the source are deduplicated in this representation in order to store the tree
//! efficiently. This means that a green tree may not actually structurally be a tree. To remedy
//! this, the real syntax tree is constructed on top of the green tree as a secondary tree (called
//! the _red_ tree), which models the exact source structure.
//! As a possible third layer, a strongly typed AST [can be built] on top of the red tree.
//!
//! [can be built]: #ast-layer
//!
//! The `cstree` implementation is a fork of the excellent [`rowan`](https://github.com/rust-analyzer/rowan/),
//! developed by the authors of [rust-analyzer](https://github.com/rust-analyzer/rust-analyzer/) who
//! wrote up a conceptual overview of their implementation in
//! [their repository](https://github.com/rust-analyzer/rust-analyzer/blob/master/docs/dev/syntax.md#trees).
//! Notable differences of `cstree` compared to `rowan`:
//!
//! - Syntax trees (red trees) are created lazily, but are persistent. Once a red node has been
//!   created by `cstree`, it will remain allocated. In contrast, `rowan` re-creates the red layer on
//!   the fly on each traversal of the tree. Apart from the trade-off discussed
//!   [here](https://github.com/rust-analyzer/rust-analyzer/blob/master/docs/dev/syntax.md#memoized-rednodes),
//!   this helps to achieve good tree traversal speed while helping to provide the following:
//! - Syntax (red) nodes are `Send` and `Sync`, allowing to share realized trees across threads. This is achieved by
//!   atomically reference counting syntax trees as a whole, which also gets rid of the need to reference count
//!   individual nodes.
//! - [`SyntaxNode`](syntax::SyntaxNode)s can hold custom data.
//! - `cstree` trees are trees over interned strings. This means `cstree` will deduplicate the text of tokens with the
//!   same source string, such as identifiers with the same name. In this position, `rowan` stores each token's text
//!   together with its metadata as a custom DST (dynamically-sized type).
//! - `cstree` includes some performance optimizations for tree creation: it only allocates space for new nodes on the
//!   heap if they are not in cache and avoids recursively hashing subtrees by pre-hashing them.
//! - `cstree` includes some performance optimizations for tree traversal: persisting red nodes allows tree traversal
//!   methods to return references instead of cloning nodes, which involves updating the tree's reference count. You can
//!   still `clone` the reference to obtain an owned node, but you only pay that cost when you need to.
//! - The downside of offering thread safe syntax trees is that `cstree` cannot offer any mutability API for its CSTs.
//!   Trees can still be updated into new trees through [replacing] nodes, but cannot be mutated in place.
//!
//! [replacing]: syntax::SyntaxNode::replace_with
//!
//! ## Getting Started
//! If you're looking at `cstree`, you're probably looking at or already writing a parser and are considering using
//! concrete syntax trees as its output. We'll talk more about parsing below -- first, let's have a look at what needs
//! to happen to go from input text to a `cstree` syntax tree:
//!
//!  1. Define an enumeration of the types of tokens (like keywords) and nodes (like "an expression") that you want to
//!     have in your syntax and implement [`Syntax`]
//!
//!  2. Create a [`GreenNodeBuilder`](build::GreenNodeBuilder) and call
//!     [`start_node`](build::GreenNodeBuilder::start_node), [`token`](build::GreenNodeBuilder::token) and
//!     [`finish_node`](build::GreenNodeBuilder::finish_node) from your parser
//!
//!  3. Call [`SyntaxNode::new_root`](syntax::SyntaxNode::new_root) or
//!     [`SyntaxNode::new_root_with_resolver`](syntax::SyntaxNode::new_root_with_resolver) with the resulting
//!     [`GreenNode`](green::GreenNode) to obtain a syntax tree that you can traverse
//!
//! There's a full [getting started guide] that walks through each of the above steps in detail in the documentation for
//! the `getting_started` module. The walkthrough goes through the necessary steps bit by bit and skips the lexer, but
//! the full code plus a runnable interpreter for the small walkthrough language are available in the `readme` example.
//! [Additional examples] can be found in the `examples/` folder in the repository.
//! A good starting point is the `s_expressions` example, which implements a parser for a small S-Expression language
//! with guiding comments.
//!
//! [getting started guide]: getting_started/index.html
//! [Additional examples]: https://github.com/domenicquirl/cstree/tree/master/cstree/examples
//!
//! ## License
//!
//! `cstree` is primarily distributed under the terms of both the MIT license and the Apache License (Version 2.0).
//!
//! See `LICENSE-APACHE` and `LICENSE-MIT` for details.

#![forbid(missing_debug_implementations, unconditional_recursion)]
#![deny(unsafe_code, future_incompatible)]
#![allow(
    unstable_name_collisions, // strict provenance - must come after `future_incompatible` to take precedence
    unexpected_cfgs, // nightly docs.rs features and `salsa-2022` feature until that is figured out
    clippy::duplicated_attributes, // interning modules
)]
#![warn(missing_docs)]
// Docs.rs
#![doc(html_root_url = "https://docs.rs/cstree/0.12.2")]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

pub mod getting_started;

#[allow(unsafe_code)]
pub mod green;
#[allow(unsafe_code)]
pub mod syntax;

#[allow(unsafe_code)]
pub mod interning;

#[cfg(feature = "serialize")]
mod serde_impls;
#[allow(missing_docs)]
mod utility_types;

use std::fmt;

/// `RawSyntaxKind` is a type tag for each token or node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RawSyntaxKind(pub u32);

/// Typesafe representations of text ranges and sizes.
pub mod text {
    pub use crate::syntax::SyntaxText;
    pub use text_size::{TextLen, TextRange, TextSize};
}

/// A tree builder for the construction of syntax trees.
///
/// Please refer to the documentation on [`GreenNodeBuilder`](build::GreenNodeBuilder) itself and the ["getting started"
/// section](../index.html#getting-started) from the top-level documentation for an introduction to how to build a
/// syntax tree.
pub mod build {
    pub use crate::green::builder::{Checkpoint, GreenNodeBuilder, NodeCache};
}

/// A convenient collection of the most used parts of `cstree`.
pub mod prelude {
    pub use crate::{
        RawSyntaxKind,
        Syntax,
        build::GreenNodeBuilder,
        green::{GreenNode, GreenToken},
        syntax::{SyntaxElement, SyntaxNode, SyntaxToken},
    };
}

/// Types for syntax tree traversal / moving through trees.
pub mod traversal {
    pub use crate::utility_types::{Direction, WalkEvent};
}

/// Utility types. It shouldn't be needed to reference these directly, but they are returned in several places in
/// `cstree` and may come in handy.
pub mod util {
    pub use crate::utility_types::{NodeOrToken, TokenAtOffset};
}

/// Synchronization primitives.
pub mod sync {
    /// An atomically reference counted shared pointer.
    ///
    /// This is like [`Arc`](std::sync::Arc) in the standard library, but more efficient for how `cstree` stores
    /// syntax trees internally. This Arc does not support weak reference counting.
    pub use triomphe::Arc;
}

/// A type that represents what items in your language can be.
/// Typically, this is an `enum` with variants such as `Identifier`, `Literal`, ...
///
/// The `Syntax` trait is the bridge between the internal `cstree` representation and your
/// language's types.
/// This is essential for providing a [`SyntaxNode`] API that can be used with your types, as in the
/// `s_expressions` example:
///
/// ```
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, cstree::Syntax)]
/// # #[allow(non_camel_case_types)]
/// #[repr(u32)]
/// enum SyntaxKind {
///     #[static_text("+")]
///     Plus, // `+`
///     #[static_text("-")]
///     Minus, // `-`
///     Integer,    // like `15`
///     Expression, // combined expression, like `5 + 4 - 3`
///     Whitespace, // whitespace is explicit
/// }
/// ```
///
/// `cstree` provides a procedural macro called `cstree_derive` to automatically generate `Syntax` implementations for
/// syntax kind enums if its `derive` feature is enabled.
///
/// [`SyntaxNode`]: crate::syntax::SyntaxNode
pub trait Syntax: Sized + Copy + fmt::Debug + Eq {
    /// Construct a semantic item kind from the compact representation.
    fn from_raw(raw: RawSyntaxKind) -> Self;

    /// Convert a semantic item kind into a more compact representation.
    fn into_raw(self) -> RawSyntaxKind;

    /// Fixed text for a particular syntax kind.
    /// Implement for kinds that will only ever represent the same text, such as punctuation (like a
    /// semicolon), keywords (like `fn`), or operators (like `<=`).
    ///
    /// Indicating tokens that have a `static_text` this way allows `cstree` to store them more efficiently, which makes
    /// it faster to add them to a syntax tree and to look up their text. Since there can often be many occurrences
    /// of these tokens inside a file, doing so will improve the performance of using `cstree`.
    fn static_text(self) -> Option<&'static str>;
}

#[cfg(feature = "derive")]
#[allow(unused_imports)]
#[macro_use]
extern crate cstree_derive;

#[cfg(feature = "derive")]
/// Derive macro available if `cstree` is built with `features = ["derive"]`.
pub use cstree_derive::Syntax;

#[doc(hidden)]
#[allow(unsafe_code, unused)]
pub mod testing {
    pub use crate::prelude::*;
    pub fn parse<S: Syntax, I>(_b: &mut GreenNodeBuilder<S, I>, _s: &str) {}

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[repr(u32)]
    #[allow(non_camel_case_types)]
    pub enum TestSyntaxKind {
        Plus,
        Identifier,
        Int,
        Float,
        Operation,
        Root,
        Whitespace,
        __LAST,
    }
    pub type MySyntax = TestSyntaxKind;
    pub use TestSyntaxKind::*;

    impl Syntax for TestSyntaxKind {
        fn from_raw(raw: RawSyntaxKind) -> Self {
            assert!(raw.0 <= TestSyntaxKind::__LAST as u32);
            unsafe { std::mem::transmute::<u32, Self>(raw.0) }
        }

        fn into_raw(self) -> RawSyntaxKind {
            RawSyntaxKind(self as u32)
        }

        fn static_text(self) -> Option<&'static str> {
            match self {
                TestSyntaxKind::Plus => Some("+"),
                _ => None,
            }
        }
    }
}
