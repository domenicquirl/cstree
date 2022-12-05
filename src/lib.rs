//! `cstree` is a generic library for creating and working with concrete syntax trees.
//! "Traditional" abstract syntax trees (ASTs) usually contain different types of nodes which represent information
//! about the source text of a document and reduce this information to the minimal amount necessary to correctly
//! interpret it. In contrast, CSTs are lossless representations of the entire input where all tree nodes are
//! represented uniformly (i.e. the nodes are _untyped_), but include a [`SyntaxKind`] field to determine the kind of
//! node.
//! One of the big advantages of this representation is not only that it can recreate the original source exactly, but
//! also that it lends itself very well to the representation of _incomplete or erroneous_ trees and is thus very suited
//! for usage in contexts such as IDEs.
//!
//! The concept of and the data structures for CSTs are inspired in part by Swift's [libsyntax](https://github.com/apple/swift/tree/5e2c815edfd758f9b1309ce07bfc01c4bc20ec23/lib/Syntax).
//! Trees consist of two layers: the inner tree (called _green_ tree) contains the actual source text in _position
//! independent_ green nodes. Tokens and nodes that appear identically at multiple places in the source text are
//! _deduplicated_ in this representation in order to store the tree efficiently. This means that the green tree may not
//! structurally be a tree. To remedy this, the actual syntax tree is constructed on top of the green tree as a
//! secondary tree (called _red_ tree), which models the exact source structure.

//! The `cstree` implementation is a fork of the excellent [`rowan`](https://github.com/rust-analyzer/rowan/), developed by the authors of [rust-analyzer](https://github.com/rust-analyzer/rust-analyzer/) who wrote up a conceptual overview of their implementation in [their repository](https://github.com/rust-analyzer/rust-analyzer/blob/master/docs/dev/syntax.md#trees).
//! Notable differences of `cstree` compared to `rowan`:
//! - Syntax trees (red trees) are created lazily, but are persistent. Once a node has been created,
//!   it will remain allocated, while `rowan` re-creates the red layer on the fly. Apart from the
//!   trade-off discussed
//!   [here](https://github.com/rust-analyzer/rust-analyzer/blob/master/docs/dev/syntax.md#memoized-rednodes),
//!   this helps to achieve good tree traversal speed while providing the next points:
//! - Syntax (red) nodes are `Send` and `Sync`, allowing to share realized trees across threads. This is achieved by
//!   atomically reference counting syntax trees as a whole, which also gets rid of the need to reference count
//!   individual nodes (helping with the point above).
//! - Syntax nodes can hold custom data.
//! - `cstree` trees are trees over interned strings. This means `cstree` will deduplicate the text
//!   of tokens such as identifiers with the same name. In this position, `rowan` stores each string,
//!   with a small string optimization (see [`SmolStr`](https://crates.io/crates/smol_str)).
//! - Performance optimizations for tree creation: only allocate new nodes on the heap if they are not in cache, avoid
//!   recursively hashing subtrees
//! - Performance optimizations for tree traversal: persisting red nodes allows tree traversal methods to return
//!   references. You can still `clone` to obtain an owned node, but you only pay that cost when you need to.
//!
//! ## Getting Started
//! If you're looking at `cstree`, you're probably looking at or already writing a parser and are considering using
//! concrete syntax trees as its output. We'll talk more about parsing below -- first, let's have a look at what needs
//! to happen to go from input text to a `cstree` syntax tree:
//!
//!  1. Define a [`SyntaxKind`] enum and implement [`Language`]
//!  2. Create a [`GreenNodeBuilder`] and call [`start_node`](GreenNodeBuilder::start_node),
//! [`token`](GreenNodeBuilder::token) and [`finish_node`](GreenNodeBuilder::finish_node) from your parser
//!  3. Call [`SyntaxNode::new_root`] or [`SyntaxNode::new_root_with_resolver`] with the resulting [`GreenNode`] to
//! obtain a syntax tree that you can traverse
//!
//! ### Parsing into a green tree
//! In contrast to parsers that return abstract syntax trees,
//!   * the node for any element in the language grammar will have the same type: [`GreenNode`]
//!   * instead of parsing a lot of inner elements and then wrapping them in an outer AST struct, building trees with
//!     `cstree` follows the source code more closely in that you tell `cstree` about each new element you enter and all
//!     tokens that the parser consumes
//!
//! ### Further examples
//! More examples can be found in the `examples/` folder in the repository.
//! A good starting point is the `s_expressions` example, which implements a parser for a small S-Expression language
//! with guiding comments.
//!
//! ## AST Layer
//! While `cstree` is built for concrete syntax trees, applications are quite easily able to work with either a CST or
//! an AST representation, or freely switch between them. To do so, use `cstree` to build syntax and underlying green
//! tree and provide AST wrappers for your different kinds of nodes. An example of how this is done can be seen [here](https://github.com/rust-analyzer/rust-analyzer/blob/master/crates/syntax/src/ast/generated.rs)
//! and [here](https://github.com/rust-analyzer/rust-analyzer/blob/master/crates/syntax/src/ast/generated/nodes.rs)
//! (note that the latter file is automatically generated by a task using [`ungrammar`](https://crates.io/crates/ungrammar)).

#![forbid(missing_debug_implementations, unconditional_recursion)]
#![deny(unsafe_code, future_incompatible)]
#![allow(unstable_name_collisions)] // strict provenance - must come after `future_incompatible` to take precedence
#![warn(missing_docs)]
// Docs.rs
#![doc(html_root_url = "https://docs.rs/cstree/0.11.1")]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

#[allow(unsafe_code)]
mod green;
#[allow(unsafe_code)]
mod syntax;

#[allow(unsafe_code)]
pub mod interning;

#[cfg(feature = "serialize")]
mod serde_impls;
#[allow(missing_docs)]
mod utility_types;

use std::fmt;

// Reexport types for working with strings.
// TODO: wrap in submodule
pub use text_size::{TextLen, TextRange, TextSize};

// TODO: clean up module structure
#[doc(inline)]
pub use crate::syntax::*;
pub use crate::{
    green::{Checkpoint, GreenNode, GreenNodeBuilder, GreenNodeChildren, GreenToken, NodeCache, SyntaxKind},
    utility_types::{Direction, NodeOrToken, TokenAtOffset, WalkEvent},
};

/// Synchronization primitives.
pub mod sync {
    /// An atomically reference counted shared pointer.
    ///
    /// This is like [`Arc`](std::sync::Arc) in the standard library, but more efficient for how `cstree` stores
    /// syntax trees internally. This Arc does not support weak reference counting.
    pub use triomphe::Arc;
}

/// The `Language` trait is the bridge between the internal `cstree` representation and your
/// language's types.
/// This is essential for providing a [`SyntaxNode`] API that can be used with your types, as in the
/// `s_expressions` example:
///
/// ```
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// # #[allow(non_camel_case_types)]
/// #[repr(u16)]
/// enum SyntaxKind {
///     Plus,       // `+`
///     Minus,      // `-`
///     Integer,    // like `15`
///     Expression, // combined expression, like `5 + 4 - 3`
///     Whitespace, // whitespaces is explicit
///     #[doc(hidden)]
///     __LAST,
/// }
/// use SyntaxKind::*;
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// enum Lang {}
///
/// impl cstree::Language for Lang {
///     type Kind = SyntaxKind;
///
///     fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
///         assert!(raw.0 <= __LAST as u16);
///         unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
///     }
///
///     fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
///         cstree::SyntaxKind(kind as u16)
///     }
///
///     fn static_text(kind: Self::Kind) -> Option<&'static str> {
///         match kind {
///             Plus => Some("+"),
///             Minus => Some("-"),
///             _ => None,
///         }
///     }
/// }
/// ```
pub trait Language: Sized + Clone + Copy + fmt::Debug + Eq + Ord + std::hash::Hash {
    /// A type that represents what items in your Language can be.
    /// Typically, this is an `enum` with variants such as `Identifier`, `Literal`, ...
    type Kind: Sized + Clone + Copy + fmt::Debug;

    /// Construct a semantic item kind from the compact representation.
    fn kind_from_raw(raw: SyntaxKind) -> Self::Kind;

    /// Convert a semantic item kind into a more compact representation.
    fn kind_to_raw(kind: Self::Kind) -> SyntaxKind;

    /// Fixed text for a particular syntax kind.
    /// Implement for kinds that will only ever represent the same text, such as punctuation (like a
    /// semicolon), keywords (like `fn`), or operators (like `<=`).
    ///
    /// Indicating tokens that have a `static_text` this way allows `cstree` to store them more efficiently, which makes
    /// it faster to add them to a syntax tree and to look up their text. Since there can often be many occurrences
    /// of these tokens inside a file, doing so will improve the performance of using `cstree`.
    fn static_text(kind: Self::Kind) -> Option<&'static str>;
}

#[doc(hidden)]
#[allow(unsafe_code, unused)]
pub mod testing {
    pub use crate::*;
    pub fn parse<L: Language, I>(_b: &mut super::GreenNodeBuilder<L, I>, _s: &str) {}

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(u16)]
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
    pub use TestSyntaxKind::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum TestLang {}
    pub type MyLanguage = TestLang;
    impl Language for TestLang {
        type Kind = TestSyntaxKind;

        fn kind_from_raw(raw: SyntaxKind) -> Self::Kind {
            assert!(raw.0 <= TestSyntaxKind::__LAST as u16);
            unsafe { std::mem::transmute::<u16, TestSyntaxKind>(raw.0) }
        }

        fn kind_to_raw(kind: Self::Kind) -> SyntaxKind {
            SyntaxKind(kind as u16)
        }

        fn static_text(kind: Self::Kind) -> Option<&'static str> {
            match kind {
                TestSyntaxKind::Plus => Some("+"),
                _ => None,
            }
        }
    }
}
