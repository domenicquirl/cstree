//! `cstree` is a generic library for creating and working with concrete syntax trees.
//! "Traditional" abstract syntax trees (ASTs) usually contain different types of nodes which represent information
//! about the source text of a document and reduce this information to the minimal amount necessary to correctly
//! interpret it. In contrast, CSTs are lossless representations of the entire input where all tree nodes are
//! represented uniformly (i.e. the nodes are _untyped_), but include a [`RawSyntaxKind`] field to determine the kind of
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
//!  1. Define an enumeration of the types of tokens (like keywords) and nodes (like "an expression") that you want to
//! have in your syntax and implement [`Syntax`]
//!
//!  2. Create a [`GreenNodeBuilder`](build::GreenNodeBuilder) and call
//! [`start_node`](build::GreenNodeBuilder::start_node), [`token`](build::GreenNodeBuilder::token) and
//! [`finish_node`](build::GreenNodeBuilder::finish_node) from your parser  
//!
//!  3. Call [`SyntaxNode::new_root`](syntax::SyntaxNode::new_root) or
//! [`SyntaxNode::new_root_with_resolver`](syntax::SyntaxNode::new_root_with_resolver) with the resulting
//! [`GreenNode`](green::GreenNode) to obtain a syntax tree that you can traverse
//!
//! Let's walk through the motions of parsing a (very) simple language into `cstree` syntax trees.
//! We'll just support addition and subtraction on integers, from which the user is allowed to construct a single,
//! compound expression. They will, however, be allowed to write nested expressions in parentheses, like `1 - (2 + 5)`.
//!
//! ### Defining the language
//!
//! First, we need to list the different part of our language's grammar.
//! We can do that using an `enum` with a unit variant for any terminal and non-terminal.
//! The `enum` needs to be convertible to a `u32`, so we use the `repr` attribute to ensure it uses the correct
//! representation.
//!
//! ```rust,ignore
//! #[derive(Debug, Clone, Copy, PartialEq, Eq)]
//! #[repr(u32)]
//! enum SyntaxKind {
//!     /* Tokens */
//!     Int,    // 42
//!     Plus,   // +
//!     Minus,  // -
//!     LParen, // (
//!     RParen, // )
//!     /* Nodes */
//!     Expr,
//!     Root,
//! }
//! ```
//!
//! For convenience when we're working with generic `cstree` types like `SyntaxNode`, we'll also give a name to our
//! syntax as a whole and add a type alias for it. That way, we can match against `SyntaxKind`s using the original name,
//! but use the more informative `Node<Calculator>` to instantiate `cstree`'s types.
//!
//! ```rust,ignore
//! type Calculator = SyntaxKind;
//! ```
//!
//! Most of these are tokens to lex the input string into, like numbers (`Int`) and operators (`Plus`, `Minus`).
//! We only really need one type of node; expressions.
//! Our syntax tree's root node will have the special kind `Root`, all other nodes will be
//! expressions containing a sequence of arithmetic operations potentially involving further, nested
//! expression nodes.
//!
//! To use our `SyntaxKind`s with `cstree`, we need to tell it how to convert it back to just a number (the
//! `#[repr(u32)]` that we added) by implementing the [`Syntax`] trait. We can also tell `cstree` about tokens that
//! always have the same text through the `static_text` method on the trait. This is useful for the operators and
//! parentheses, but not possible for numbers, since an integer token may be produced from the input `3`, but also from
//! other numbers like `7` or `12`.
//!
//! ```rust,ignore
//! impl Syntax for Calculator {
//!     // The tokens and nodes we just defined
//!     type Kind = SyntaxKind;
//!
//!     fn from_raw(raw: RawSyntaxKind) -> Self {
//!         // This just needs to be the inverse of `kind_to_raw`, but could also
//!         // be an `impl TryFrom<u32> for SyntaxKind` or any other conversion.
//!         match raw.0 {
//!             0 => SyntaxKind::Int,
//!             1 => SyntaxKind::Plus,
//!             2 => SyntaxKind::Minus,
//!             3 => SyntaxKind::LParen,
//!             4 => SyntaxKind::RParen,
//!             5 => SyntaxKind::Expr,
//!             6 => SyntaxKind::Root,
//!             n => panic!("Unknown raw syntax kind: {n}"),
//!         }
//!     }
//!
//!     fn into_raw(self) -> RawSyntaxKind {
//!         RawSyntaxKind(self as u32)
//!     }
//!
//!     fn static_text(self) -> Option<&'static str> {
//!         match self {
//!             SyntaxKind::Plus => Some("+"),
//!             SyntaxKind::Minus => Some("-"),
//!             SyntaxKind::LParen => Some("("),
//!             SyntaxKind::RParen => Some(")"),
//!             _ => None,
//!         }
//!     }
//! }
//! ```
//!
//! ### Parsing into a green tree
//! With that out of the way, we can start writing the parser for our expressions.
//! For the purposes of this introduction to `cstree`, I'll assume that there is a lexer that yields the following
//! tokens:
//!
//! ```rust,ignore
//! #[derive(Debug, PartialEq, Eq, Clone, Copy)]
//! pub enum Token<'input> {
//!     // Note that number strings are not yet parsed into actual numbers,
//!     // we just remember the slice of the input that contains their digits
//!     Int(&'input str),
//!     Plus,
//!     Minus,
//!     LParen,
//!     RParen,
//!     // A special token that indicates that we have reached the end of the file
//!     EoF,
//! }
//! ```
//!
//! A simple lexer that yields such tokens is part of the full `readme` example, but we'll be busy enough with the
//! combination of `cstree` and the actual parser, which we define like this:
//!
//! ```rust,ignore
//! pub struct Parser<'input> {
//!     // `Peekable` is a standard library iterator adapter that allows
//!     // looking ahead at the next item without removing it from the iterator yet
//!     lexer:   Peekable<Lexer<'input>>,
//!     builder: GreenNodeBuilder<'static, 'static, Calculator>,
//! }
//!
//! impl<'input> Parser<'input> {
//!     pub fn new(input: &'input str) -> Self {
//!         Self {
//!             // we get `peekable` from implementing `Iterator` on `Lexer`
//!             lexer:   Lexer::new(input).peekable(),
//!             builder: GreenNodeBuilder::new(),
//!         }
//!     }
//!
//!     pub fn bump(&mut self) -> Option<Token<'input>> {
//!         self.lexer.next()
//!     }
//! }
//! ```
//!
//! In contrast to parsers that return abstract syntax trees, with `cstree` the syntax tree nodes
//! for all element in the language grammar will have the same type: [`GreenNode`](green::GreenNode)
//! for the inner ("green") tree and [`SyntaxNode`](syntax::SyntaxNode) for the outer ("red") tree.
//! Different kinds of nodes (and tokens) are differentiated by their `SyntaxKind` tag, which we defined above.
//!
//! You can implement many types of parsers with `cstree`. To get a feel for how it works, consider
//! a typical recursive descent parser. With a more traditional AST, one would define different AST
//! structs for struct or function definitions, statements, expressions and so on. Inside the
//! parser, the components of any element, such as all fields of a struct or all statements inside a
//! function, are parsed first and then the parser wraps them in the matching AST type, which is
//! returned from the corresponding parser function.
//!
//! Because `cstree`'s syntax trees are untyped, there is no explicit AST representation that the
//! parser would build. Instead, parsing into a CST using the
//! [`GreenNodeBuilder`](build::GreenNodeBuilder) follows the source code more closely in that you
//! tell `cstree` about each new element you enter and all tokens that the parser consumes. So, for
//! example, to parse a struct definition the parser first "enters" the struct definition node, then
//! parses the `struct` keyword and type name, then parses each field, and finally "finishes"
//! parsing the struct node.
//!
//! The most trivial example is the root node for our parser, which just creates a root node
//! containing the whole expression (we could do without a specific root node if any expression was
//! a node, in particular if we wrapped integer literal tokens inside `Expr` nodes).
//!
//! ```rust,ignore
//! pub fn parse(&mut self) -> Result<(), String> {
//!     self.builder.start_node(SyntaxKind::Root);
//!     self.parse_expr()?;
//!     self.builder.finish_node();
//!     Ok(())
//! }
//! ```
//!
//! As there isn't a static AST type to return, the parser is very flexible as to what is part of a
//! node. In the previous example, if the user is adding a new field to the struct and has not yet
//! typed the field's type, the CST node for the struct doesn't care if there is no child node for
//! it. Similarly, if the user is deleting fields and the source code currently contains a leftover
//! field name, this additional identifier can be a part of the struct node without any
//! modifications to the syntax tree definition. This property is the key to why CSTs are such a
//! good fit as a lossless input representation, which necessitates the syntax tree to mirror the
//! user-specific layout of whitespace and comments around the AST items.
//!
//! In the parser for our simple expression language, we'll also have to deal with the fact that,
//! when we see a number the parser doesn't yet know whether there will be additional operations
//! following that number. That is, in the expression `1 + 2`, it can only know that it is parsing
//! a binary operation once it sees the `+`. The event-like model of building trees in `cstree`,
//! however, implies that when reaching the `+`, the parser would have to have already entered an
//! expression node in order for the whole input to be part of the expression.
//!
//! To get around this, `GreenNodeBuilder` provides the
//! [`checkpoint`](build::GreenNodeBuilder::checkpoint) method, which we can call to "remember" the
//! current position in the input.  For example, we can create a checkpoint before the parser parses
//! the first `1`. Later, when it sees the following `+`, it can create an `Expr` node for the
//! whole expression using [`start_node_at`](build::GreenNodeBuilder::start_node_at):
//!
//! ```rust,ignore
//! fn parse_lhs(&mut self) -> Result<(), String> {
//!     // An expression may start either with a number, or with an opening parenthesis that is
//!     // the start of a parenthesized expression
//!     let next_token = *self.lexer.peek().unwrap();
//!     match next_token {
//!         Token::Int(n) => {
//!             self.bump();
//!             self.builder.token(SyntaxKind::Int, n);
//!         }
//!         Token::LParen => {
//!             // Wrap the grouped expression inside a node containing it and its parentheses
//!             self.builder.start_node(SyntaxKind::Expr);
//!             self.bump();
//!             self.builder.static_token(SyntaxKind::LParen);
//!             self.parse_expr()?; // Inner expression
//!             if self.bump() != Some(Token::RParen) {
//!                 return Err("Missing ')'".to_string());
//!             }
//!             self.builder.static_token(SyntaxKind::RParen);
//!             self.builder.finish_node();
//!         }
//!         Token::EoF => return Err("Unexpected end of file: expected expression".to_string()),
//!         t => return Err(format!("Unexpected start of expression: '{t:?}'")),
//!     }
//!     Ok(())
//! }
//!
//! fn parse_expr(&mut self) -> Result<(), String> {
//!     // Remember our current position
//!     let before_expr = self.builder.checkpoint();
//!
//!     // Parse the start of the expression
//!     self.parse_lhs()?;
//!
//!     // Check if the expression continues with `+ <more>` or `- <more>`
//!     let Some(next_token) = self.lexer.peek() else {
//!         return Ok(());
//!     };
//!     let op = match *next_token {
//!         Token::Plus => SyntaxKind::Plus,
//!         Token::Minus => SyntaxKind::Minus,
//!         Token::RParen | Token::EoF => return Ok(()),
//!         t => return Err(format!("Expected operator, found '{t:?}'")),
//!     };
//!
//!     // If so, retroactively wrap the (already parsed) LHS and the following RHS
//!     // inside an `Expr` node
//!     self.builder.start_node_at(before_expr, SyntaxKind::Expr);
//!     self.bump();
//!     self.builder.static_token(op);
//!     self.parse_expr()?; // RHS
//!     self.builder.finish_node();
//!     Ok(())
//! }
//! ```
//!
//! ### Obtaining the parser result
//!
//! Our parser is now capable of parsing our little arithmetic language, but it's methods don't
//! return anything. So how do we get our syntax tree out? The answer lies in
//! [`GreenNodeBuilder::finish`](build::GreenNodeBuilder::finish), which finally returns the tree
//! that we have painstakingly constructed.
//!
//! ```rust,ignore
//! impl Parser<'_> {
//!     pub fn finish(mut self) -> (GreenNode, impl Interner) {
//!         assert!(self.lexer.next().map(|t| t == Token::EoF).unwrap_or(true));
//!         let (tree, cache) = self.builder.finish();
//!         (tree, cache.unwrap().into_interner().unwrap())
//!     }
//! }
//! ```
//!
//! `finish` also returns the cache it used to deduplicate tree nodes and tokens, so you can re-use
//! it for parsing related inputs (e.g., different source files from the same crate may share a lot
//! of common function and type names that can be deduplicated). See `GreenNodeBuilder`'s
//! documentation for more information on this, in particular the `with_cache` and `from_cache`
//! methods. Most importantly for us, we can extract the [`Interner`](interning::Interner) that
//! contains the source text of the tree's tokens from the cache, which we need if we want to look
//! up things like variable names or the value of numbers for our calculator.
//!
//! To work with the syntax tree, you'll want to upgrade it to a [`SyntaxNode`](syntax::SyntaxNode)
//! using [`SyntaxNode::new_root`](syntax::SyntaxNode::new_root). You can also use
//! [`SyntaxNode::new_root_with_resolver`](syntax::SyntaxNode::new_root_with_resolver) to combine
//! tree and interner, which lets you directly retrieve source text and makes the nodes implement
//! `Display` and `Debug`. The same output can be produced from `SyntaxNode`s by calling the
//! `debug` or `display` method with a [`Resolver`](interning::Resolver). To visualize the whole
//! syntax tree, pass `true` for the `recursive` parameter on `debug`, or simply debug-print a
//! [`ResolvedNode`](syntax::ResolvedNode):
//!
//! ```rust,ignore
//! let input = "11 + 2-(5 + 4)";
//! let mut parser = Parser::new(input);
//! parser.parse().unwrap();
//! let (tree, interner) = parser.finish();
//! let root = SyntaxNode::<Calculator>::new_root_with_resolver(tree, interner);
//! dbg!(root);
//! ```
//!
//! ### Further examples
//! The parser we just built is available in full in the runnable `readme` example, which includes some additional code
//! to read expressions from the terminal and evaluate the parsed expressions - have it do a few calculations if you
//! like.
//! There are several more examples in the `examples/` folder in the repository.
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
#![doc(html_root_url = "https://docs.rs/cstree/0.12.0-rc.0")]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

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
        build::GreenNodeBuilder,
        green::{GreenNode, GreenToken},
        syntax::{SyntaxElement, SyntaxNode, SyntaxToken},
        RawSyntaxKind, Syntax,
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
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// # #[allow(non_camel_case_types)]
/// #[repr(u32)]
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
/// impl cstree::Syntax for SyntaxKind {
///     fn from_raw(raw: cstree::RawSyntaxKind) -> Self {
///         assert!(raw.0 <= __LAST as u32);
///         unsafe { std::mem::transmute::<u32, Self>(raw.0) }
///     }
///
///     fn into_raw(self) -> cstree::RawSyntaxKind {
///         cstree::RawSyntaxKind(self as u32)
///     }
///
///     fn static_text(self) -> Option<&'static str> {
///         match self {
///             Plus => Some("+"),
///             Minus => Some("-"),
///             _ => None,
///         }
///     }
/// }
/// ```
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
/// Derive macro available if `cstree` is build with `features = ["derive"]`.
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
