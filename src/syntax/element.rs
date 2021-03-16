use std::sync::atomic::AtomicU32;

use lasso::Resolver;
use text_size::{TextRange, TextSize};

use super::*;
use crate::{green::GreenElementRef, Language, NodeOrToken, SyntaxKind, TokenAtOffset};

/// An element of the tree, can be either a node or a token.
pub type SyntaxElement<L, D = (), R = ()> = NodeOrToken<SyntaxNode<L, D, R>, SyntaxToken<L, D, R>>;

impl<L: Language, D, R> From<SyntaxNode<L, D, R>> for SyntaxElement<L, D, R> {
    fn from(node: SyntaxNode<L, D, R>) -> SyntaxElement<L, D, R> {
        NodeOrToken::Node(node)
    }
}

impl<L: Language, D, R> From<SyntaxToken<L, D, R>> for SyntaxElement<L, D, R> {
    fn from(token: SyntaxToken<L, D, R>) -> SyntaxElement<L, D, R> {
        NodeOrToken::Token(token)
    }
}

impl<L: Language, D, R> SyntaxElement<L, D, R> {
    #[allow(missing_docs)]
    pub fn display(&self, resolver: &impl Resolver) -> String {
        match self {
            NodeOrToken::Node(it) => it.display(resolver),
            NodeOrToken::Token(it) => it.display(resolver),
        }
    }
}

/// A reference to an element of the tree, can be either a reference to a node or one to a token.
pub type SyntaxElementRef<'a, L, D = (), R = ()> = NodeOrToken<&'a SyntaxNode<L, D, R>, &'a SyntaxToken<L, D, R>>;

impl<'a, L: Language, D, R> From<&'a SyntaxNode<L, D, R>> for SyntaxElementRef<'a, L, D, R> {
    fn from(node: &'a SyntaxNode<L, D, R>) -> Self {
        NodeOrToken::Node(node)
    }
}

impl<'a, L: Language, D, R> From<&'a SyntaxToken<L, D, R>> for SyntaxElementRef<'a, L, D, R> {
    fn from(token: &'a SyntaxToken<L, D, R>) -> Self {
        NodeOrToken::Token(token)
    }
}

impl<'a, L: Language, D, R> From<&'a SyntaxElement<L, D, R>> for SyntaxElementRef<'a, L, D, R> {
    fn from(element: &'a SyntaxElement<L, D, R>) -> Self {
        match element {
            NodeOrToken::Node(it) => Self::Node(it),
            NodeOrToken::Token(it) => Self::Token(it),
        }
    }
}

impl<'a, L: Language, D, R> SyntaxElementRef<'a, L, D, R> {
    #[allow(missing_docs)]
    pub fn display(&self, resolver: &impl Resolver) -> String {
        match self {
            NodeOrToken::Node(it) => it.display(resolver),
            NodeOrToken::Token(it) => it.display(resolver),
        }
    }
}

impl<L: Language, D, R> SyntaxElement<L, D, R> {
    pub(super) fn new(
        element: GreenElementRef<'_>,
        parent: &SyntaxNode<L, D, R>,
        index: u32,
        offset: TextSize,
        ref_count: *mut AtomicU32,
    ) -> SyntaxElement<L, D, R> {
        match element {
            NodeOrToken::Node(node) => SyntaxNode::new_child(node, parent, index as u32, offset, ref_count).into(),
            NodeOrToken::Token(_) => SyntaxToken::new(parent, index as u32, offset).into(),
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
    pub fn syntax_kind(&self) -> SyntaxKind {
        match self {
            NodeOrToken::Node(it) => it.syntax_kind(),
            NodeOrToken::Token(it) => it.syntax_kind(),
        }
    }

    /// The kind of this element in terms of your language.
    #[inline]
    pub fn kind(&self) -> L::Kind {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    /// The parent node of this element, except if this element is the root.
    #[inline]
    pub fn parent(&self) -> Option<&SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    /// Return the leftmost token in the subtree of this element.
    #[inline]
    pub fn first_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// Return the rightmost token in the subtree of this element.
    #[inline]
    pub fn last_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// The tree element to the right of this one, i.e. the next child of this element's parent after this element.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    /// The tree element to the left of this one, i.e. the previous child of this element's parent after this element.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }
}

impl<'a, L: Language, D, R> SyntaxElementRef<'a, L, D, R> {
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
    pub fn syntax_kind(&self) -> SyntaxKind {
        match self {
            NodeOrToken::Node(it) => it.syntax_kind(),
            NodeOrToken::Token(it) => it.syntax_kind(),
        }
    }

    /// The kind of this element in terms of your language.
    #[inline]
    pub fn kind(&self) -> L::Kind {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    /// The parent node of this element, except if this element is the root.
    #[inline]
    pub fn parent(&self) -> Option<&'a SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &'a SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    /// Return the leftmost token in the subtree of this element.
    #[inline]
    pub fn first_token(&self) -> Option<&'a SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// Return the rightmost token in the subtree of this element.
    #[inline]
    pub fn last_token(&self) -> Option<&'a SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// The tree element to the right of this one, i.e. the next child of this element's parent after this element.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'a, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    /// The tree element to the left of this one, i.e. the previous child of this element's parent after this element.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'a, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }

    #[inline]
    pub(super) fn token_at_offset(&self, offset: TextSize) -> TokenAtOffset<SyntaxToken<L, D, R>> {
        assert!(self.text_range().start() <= offset && offset <= self.text_range().end());
        match self {
            NodeOrToken::Token(token) => TokenAtOffset::Single((*token).clone()),
            NodeOrToken::Node(node) => node.token_at_offset(offset),
        }
    }
}
