//! ## Getting Started
//! If you're looking at `cstree`, you're probably looking at or already writing a parser and are considering using
//! concrete syntax trees as its output. We'll talk more about parsing below -- first, let's have a look at what needs
//! to happen to go from input text to a `cstree` syntax tree:
//!
//!  1. Define an enumeration of the types of tokens (like keywords) and nodes (like "an expression") that you want to
//!     have in your syntax and implement [`Syntax`]
//!
//!  2. Create a [`GreenNodeBuilder`](crate::build::GreenNodeBuilder) and call
//!     [`start_node`](crate::build::GreenNodeBuilder::start_node), [`token`](crate::build::GreenNodeBuilder::token) and
//!     [`finish_node`](crate::build::GreenNodeBuilder::finish_node) from your parser
//!
//!  3. Call [`SyntaxNode::new_root`](crate::syntax::SyntaxNode::new_root) or
//!     [`SyntaxNode::new_root_with_resolver`](crate::syntax::SyntaxNode::new_root_with_resolver) with the resulting
//!     [`GreenNode`](crate::green::GreenNode) to obtain a syntax tree that you can traverse
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
//! ```rust,no_run
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
//! ```rust,no_run
//! # enum SyntaxKind {}
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
//! ```rust,no_run
//! # #[derive(Debug, Clone, Copy, PartialEq, Eq)]
//! # #[repr(u32)]
//! # enum SyntaxKind { Int, Plus, Minus, LParen, RParen, Expr, Root }
//! # type Calculator = SyntaxKind;
//! # use cstree::{Syntax, RawSyntaxKind};
//!
//! impl Syntax for Calculator {
//!     fn from_raw(raw: RawSyntaxKind) -> Self {
//!         // This just needs to be the inverse of `into_raw`, but could also
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
//! #### Deriving `Syntax`
//!
//! To save yourself the hassle of defining this conversion (and, perhaps more importantly,
//! continually updating it while your language's syntax is in flux), `cstree` includes a derive
//! macro for [`Syntax`](macro@crate::Syntax) when built with the `derive` feature. With the macro,
//! the `Syntax` trait implementation above can be replaced by simply adding `#[derive(Syntax)]` to
//! `SyntaxKind`.
//!
//! ### Parsing into a green tree
//!
//! With that out of the way, we can start writing the parser for our expressions.
//! For the purposes of this introduction to `cstree`, I'll assume that there is a lexer that yields the following
//! tokens:
//!
//! ```rust,no_run
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
//! ```rust,no_run
//! # use std::iter::Peekable;
//! # use cstree::build::GreenNodeBuilder;
//! # struct Lexer<'a> { input: &'a str }
//! # impl<'a> Lexer<'a> { fn new(input: &'a str) -> Self { Self { input } } }
//! # struct Token<'a> { input: &'a str }
//! # impl<'a> Iterator for Lexer<'a> {
//! #     type Item = Token<'a>;
//! #     fn next(&mut self) -> Option<Self::Item> { None }
//! # }
//! # #[derive(Debug, Clone, Copy, PartialEq, Eq, cstree::Syntax)]
//! # #[repr(u32)] enum Calculator { A }
//!
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
//! for all element in the language grammar will have the same type: [`GreenNode`](crate::green::GreenNode)
//! for the inner ("green") tree and [`SyntaxNode`](crate::syntax::SyntaxNode) for the outer ("red") tree.
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
//! [`GreenNodeBuilder`](crate::build::GreenNodeBuilder) follows the source code more closely in that you
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
//! [`checkpoint`](crate::build::GreenNodeBuilder::checkpoint) method, which we can call to "remember" the
//! current position in the input.  For example, we can create a checkpoint before the parser parses
//! the first `1`. Later, when it sees the following `+`, it can create an `Expr` node for the
//! whole expression using [`start_node_at`](crate::build::GreenNodeBuilder::start_node_at):
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
//! [`GreenNodeBuilder::finish`](crate::build::GreenNodeBuilder::finish), which finally returns the tree
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
//! methods. Most importantly for us, we can extract the [`Interner`](crate::interning::Interner) that
//! contains the source text of the tree's tokens from the cache, which we need if we want to look
//! up things like variable names or the value of numbers for our calculator.
//!
//! To work with the syntax tree, you'll want to upgrade it to a [`SyntaxNode`](crate::syntax::SyntaxNode)
//! using [`SyntaxNode::new_root`](crate::syntax::SyntaxNode::new_root). You can also use
//! [`SyntaxNode::new_root_with_resolver`](crate::syntax::SyntaxNode::new_root_with_resolver) to combine
//! tree and interner, which lets you directly retrieve source text and makes the nodes implement
//! `Display` and `Debug`. The same output can be produced from `SyntaxNode`s by calling the
//! `debug` or `display` method with a [`Resolver`](crate::interning::Resolver). To visualize the whole
//! syntax tree, pass `true` for the `recursive` parameter on `debug`, or simply debug-print a
//! [`ResolvedNode`](crate::syntax::ResolvedNode):
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
//! tree and provide AST wrappers for your different kinds of nodes. An example of how this is done can be seen
//! [here](https://github.com/rust-analyzer/rust-analyzer/blob/master/crates/syntax/src/ast/generated.rs)
//! and [here](https://github.com/rust-analyzer/rust-analyzer/blob/master/crates/syntax/src/ast/generated/nodes.rs)
//! (note that the latter file is automatically generated by a task using [`ungrammar`](https://crates.io/crates/ungrammar)).
