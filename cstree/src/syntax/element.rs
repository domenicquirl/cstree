use std::{fmt, sync::atomic::AtomicU32};

use text_size::{TextRange, TextSize};

use super::*;
use crate::{
    green::GreenElementRef,
    interning::{Resolver, TokenKey},
    util::{NodeOrToken, TokenAtOffset},
    RawSyntaxKind, Syntax,
};

/// An element of the tree, can be either a node or a token.
pub type SyntaxElement<S, D = ()> = NodeOrToken<SyntaxNode<S, D>, SyntaxToken<S, D>>;

impl<S: Syntax, D> From<SyntaxNode<S, D>> for SyntaxElement<S, D> {
    fn from(node: SyntaxNode<S, D>) -> SyntaxElement<S, D> {
        NodeOrToken::Node(node)
    }
}

impl<S: Syntax, D> From<SyntaxToken<S, D>> for SyntaxElement<S, D> {
    fn from(token: SyntaxToken<S, D>) -> SyntaxElement<S, D> {
        NodeOrToken::Token(token)
    }
}

impl<S: Syntax, D> SyntaxElement<S, D> {
    /// Returns this element's [`Display`](fmt::Display) representation as a string.
    ///
    /// To avoid allocating for every element, see [`write_display`](type.SyntaxElement.html#method.write_display).
    pub fn display<R>(&self, resolver: &R) -> String
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.display(resolver),
            NodeOrToken::Token(it) => it.display(resolver),
        }
    }

    /// Writes this element's [`Display`](fmt::Display) representation into the given `target`.
    pub fn write_display<R>(&self, resolver: &R, target: &mut impl fmt::Write) -> fmt::Result
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.write_display(resolver, target),
            NodeOrToken::Token(it) => it.write_display(resolver, target),
        }
    }

    /// Returns this element's [`Debug`](fmt::Debug) representation as a string.
    /// If `recursive` is `true`, prints the entire subtree rooted in this element.
    /// Otherwise, only this element's kind and range are written.
    ///
    /// To avoid allocating for every element, see [`write_debug`](type.SyntaxElement.html#method.write_debug).
    pub fn debug<R>(&self, resolver: &R, recursive: bool) -> String
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.debug(resolver, recursive),
            NodeOrToken::Token(it) => it.debug(resolver),
        }
    }

    /// Writes this element's [`Debug`](fmt::Debug) representation into the given `target`.
    /// If `recursive` is `true`, prints the entire subtree rooted in this element.
    /// Otherwise, only this element's kind and range are written.
    pub fn write_debug<R>(&self, resolver: &R, target: &mut impl fmt::Write, recursive: bool) -> fmt::Result
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.write_debug(resolver, target, recursive),
            NodeOrToken::Token(it) => it.write_debug(resolver, target),
        }
    }
}

/// A reference to an element of the tree, can be either a reference to a node or one to a token.
pub type SyntaxElementRef<'a, S, D = ()> = NodeOrToken<&'a SyntaxNode<S, D>, &'a SyntaxToken<S, D>>;

impl<'a, S: Syntax, D> From<&'a SyntaxNode<S, D>> for SyntaxElementRef<'a, S, D> {
    fn from(node: &'a SyntaxNode<S, D>) -> Self {
        NodeOrToken::Node(node)
    }
}

impl<'a, S: Syntax, D> From<&'a SyntaxToken<S, D>> for SyntaxElementRef<'a, S, D> {
    fn from(token: &'a SyntaxToken<S, D>) -> Self {
        NodeOrToken::Token(token)
    }
}

impl<'a, S: Syntax, D> From<&'a SyntaxElement<S, D>> for SyntaxElementRef<'a, S, D> {
    fn from(element: &'a SyntaxElement<S, D>) -> Self {
        match element {
            NodeOrToken::Node(it) => Self::Node(it),
            NodeOrToken::Token(it) => Self::Token(it),
        }
    }
}

impl<S: Syntax, D> SyntaxElementRef<'_, S, D> {
    /// Returns this element's [`Display`](fmt::Display) representation as a string.
    ///
    /// To avoid allocating for every element, see [`write_display`](type.SyntaxElementRef.html#method.write_display).
    pub fn display<R>(&self, resolver: &R) -> String
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.display(resolver),
            NodeOrToken::Token(it) => it.display(resolver),
        }
    }

    /// Writes this element's [`Display`](fmt::Display) representation into the given `target`.
    pub fn write_display<R>(&self, resolver: &R, target: &mut impl fmt::Write) -> fmt::Result
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.write_display(resolver, target),
            NodeOrToken::Token(it) => it.write_display(resolver, target),
        }
    }

    /// Returns this element's [`Debug`](fmt::Debug) representation as a string.
    /// If `recursive` is `true`, prints the entire subtree rooted in this element.
    /// Otherwise, only this element's kind and range are written.
    ///
    /// To avoid allocating for every element, see [`write_debug`](type.SyntaxElementRef.html#method.write_debug).
    pub fn debug<R>(&self, resolver: &R, recursive: bool) -> String
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.debug(resolver, recursive),
            NodeOrToken::Token(it) => it.debug(resolver),
        }
    }

    /// Writes this element's [`Debug`](fmt::Debug) representation into the given `target`.
    /// If `recursive` is `true`, prints the entire subtree rooted in this element.
    /// Otherwise, only this element's kind and range are written.
    pub fn write_debug<R>(&self, resolver: &R, target: &mut impl fmt::Write, recursive: bool) -> fmt::Result
    where
        R: Resolver<TokenKey> + ?Sized,
    {
        match self {
            NodeOrToken::Node(it) => it.write_debug(resolver, target, recursive),
            NodeOrToken::Token(it) => it.write_debug(resolver, target),
        }
    }
}

impl<S: Syntax, D> SyntaxElement<S, D> {
    pub(super) fn new(
        element: GreenElementRef<'_>,
        parent: &SyntaxNode<S, D>,
        index: u32,
        offset: TextSize,
        ref_count: *mut AtomicU32,
    ) -> SyntaxElement<S, D> {
        match element {
            NodeOrToken::Node(node) => SyntaxNode::new_child(node, parent, index, offset, ref_count).into(),
            NodeOrToken::Token(_) => SyntaxToken::new(parent, index, offset).into(),
        }
    }

    /// The range this element covers in the source text, in bytes.
    #[inline]
    pub fn text_range(&self) -> TextRange {
        match self {
            NodeOrToken::Node(it) => it.text_range(),
            NodeOrToken::Token(it) => it.text_range(),
        }
    }

    /// The internal representation of the kind of this element.
    #[inline]
    pub fn syntax_kind(&self) -> RawSyntaxKind {
        match self {
            NodeOrToken::Node(it) => it.syntax_kind(),
            NodeOrToken::Token(it) => it.syntax_kind(),
        }
    }

    /// The kind of this element in terms of your language.
    #[inline]
    pub fn kind(&self) -> S {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    /// The parent node of this element, except if this element is the root.
    #[inline]
    pub fn parent(&self) -> Option<&SyntaxNode<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    /// Return the leftmost token in the subtree of this element.
    #[inline]
    pub fn first_token(&self) -> Option<&SyntaxToken<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// Return the rightmost token in the subtree of this element.
    #[inline]
    pub fn last_token(&self) -> Option<&SyntaxToken<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// The tree element to the right of this one, i.e. the next child of this element's parent after this element.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, S, D>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    /// The tree element to the left of this one, i.e. the previous child of this element's parent after this element.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, S, D>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }
}

impl<'a, S: Syntax, D> SyntaxElementRef<'a, S, D> {
    /// The range this element covers in the source text, in bytes.
    #[inline]
    pub fn text_range(&self) -> TextRange {
        match self {
            NodeOrToken::Node(it) => it.text_range(),
            NodeOrToken::Token(it) => it.text_range(),
        }
    }

    /// The internal representation of the kind of this element.
    #[inline]
    pub fn syntax_kind(&self) -> RawSyntaxKind {
        match self {
            NodeOrToken::Node(it) => it.syntax_kind(),
            NodeOrToken::Token(it) => it.syntax_kind(),
        }
    }

    /// The kind of this element in terms of your language.
    #[inline]
    pub fn kind(&self) -> S {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    /// The parent node of this element, except if this element is the root.
    #[inline]
    pub fn parent(&self) -> Option<&'a SyntaxNode<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &'a SyntaxNode<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    /// Return the leftmost token in the subtree of this element.
    #[inline]
    pub fn first_token(&self) -> Option<&'a SyntaxToken<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// Return the rightmost token in the subtree of this element.
    #[inline]
    pub fn last_token(&self) -> Option<&'a SyntaxToken<S, D>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// The tree element to the right of this one, i.e. the next child of this element's parent after this element.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'a, S, D>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    /// The tree element to the left of this one, i.e. the previous child of this element's parent after this element.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'a, S, D>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }

    #[inline]
    pub(super) fn token_at_offset(&self, offset: TextSize) -> TokenAtOffset<SyntaxToken<S, D>> {
        assert!(self.text_range().start() <= offset && offset <= self.text_range().end());
        match self {
            NodeOrToken::Token(token) => TokenAtOffset::Single((*token).clone()),
            NodeOrToken::Node(node) => node.token_at_offset(offset),
        }
    }
}
