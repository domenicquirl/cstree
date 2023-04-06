//! Nodes, tokens, elements and their references which are guaranteed to belong to trees with
//! associated [`Resolver`]s(lasso::Resolver).
//!
//! This means they can implement `Debug` and `Display` and be (de-)serializable by default.

use std::{
    fmt,
    ops::{Deref, DerefMut},
    sync::Arc as StdArc,
};

use text_size::{TextRange, TextSize};

use crate::{
    green::GreenNode,
    interning::{Resolver, TokenKey},
    syntax::*,
    traversal::*,
    util::*,
    Language, RawSyntaxKind,
};

/// Syntax tree node that is guaranteed to belong to a tree that contains an associated
/// [`Resolver`](lasso::Resolver).
/// # See also
/// [`SyntaxNode`]
/// [`SyntaxNode::new_root_with_resolver`]
#[repr(transparent)]
pub struct ResolvedNode<L: Language, D: 'static = ()> {
    pub(super) syntax: SyntaxNode<L, D>,
}

impl<L: Language, D> ResolvedNode<L, D> {
    /// # Safety:
    /// `syntax` must belong to a tree that contains an associated inline resolver.
    pub(super) unsafe fn coerce_ref(syntax: &SyntaxNode<L, D>) -> &Self {
        &*(syntax as *const _ as *const Self)
    }

    /// Returns this node as a [`SyntaxNode`].
    pub fn syntax(&self) -> &SyntaxNode<L, D> {
        &self.syntax
    }
}

impl<L: Language, D> Clone for ResolvedNode<L, D> {
    fn clone(&self) -> Self {
        Self {
            syntax: self.syntax.clone(),
        }
    }
}

impl<L: Language, D> Deref for ResolvedNode<L, D> {
    type Target = SyntaxNode<L, D>;

    fn deref(&self) -> &Self::Target {
        &self.syntax
    }
}

impl<L: Language, D> DerefMut for ResolvedNode<L, D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.syntax
    }
}

/// Syntax tree token that is guaranteed to belong to a tree that contains an associated
/// [`Resolver`](lasso::Resolver).
/// # See also
/// [`SyntaxToken`]]
#[repr(transparent)]
pub struct ResolvedToken<L: Language, D: 'static = ()> {
    syntax: SyntaxToken<L, D>,
}

impl<L: Language, D> ResolvedToken<L, D> {
    /// # Safety:
    /// `syntax` must belong to a tree that contains an associated inline resolver.
    pub(super) unsafe fn coerce_ref(syntax: &SyntaxToken<L, D>) -> &Self {
        &*(syntax as *const _ as *const Self)
    }

    /// Returns this token as a [`SyntaxToken`].
    pub fn syntax(&self) -> &SyntaxToken<L, D> {
        &self.syntax
    }
}

impl<L: Language, D> Clone for ResolvedToken<L, D> {
    fn clone(&self) -> Self {
        Self {
            syntax: self.syntax.clone(),
        }
    }
}

impl<L: Language, D> Deref for ResolvedToken<L, D> {
    type Target = SyntaxToken<L, D>;

    fn deref(&self) -> &Self::Target {
        &self.syntax
    }
}

impl<L: Language, D> DerefMut for ResolvedToken<L, D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.syntax
    }
}

/// An element of the tree that is guaranteed to belong to a tree that contains an associated
/// [`Resolver`](lasso::Resolver), can be either a node or a token.
/// # See also
/// [`SyntaxElement`](crate::syntax::SyntaxElement)
pub type ResolvedElement<L, D = ()> = NodeOrToken<ResolvedNode<L, D>, ResolvedToken<L, D>>;

impl<L: Language, D> From<ResolvedNode<L, D>> for ResolvedElement<L, D> {
    fn from(node: ResolvedNode<L, D>) -> ResolvedElement<L, D> {
        NodeOrToken::Node(node)
    }
}

impl<L: Language, D> From<ResolvedToken<L, D>> for ResolvedElement<L, D> {
    fn from(token: ResolvedToken<L, D>) -> ResolvedElement<L, D> {
        NodeOrToken::Token(token)
    }
}

impl<L: Language, D> ResolvedElement<L, D> {
    #[allow(missing_docs)]
    pub fn display(&self, resolver: &impl Resolver<TokenKey>) -> String {
        match self {
            NodeOrToken::Node(it) => it.display(resolver),
            NodeOrToken::Token(it) => it.display(resolver),
        }
    }
}

/// A reference to an element of the tree that is guaranteed to belong to a tree that contains an
/// associated [`Resolver`](lasso::Resolver), can be either a reference to a node or one to a token.
/// # See also
/// [`SyntaxElementRef`]
pub type ResolvedElementRef<'a, L, D = ()> = NodeOrToken<&'a ResolvedNode<L, D>, &'a ResolvedToken<L, D>>;

impl<'a, L: Language, D> ResolvedElementRef<'a, L, D> {
    /// # Safety:
    /// `syntax` must belong to a tree that contains an associated inline resolver.
    pub(super) unsafe fn coerce_ref(syntax: SyntaxElementRef<'a, L, D>) -> Self {
        match syntax {
            NodeOrToken::Node(node) => Self::Node(ResolvedNode::coerce_ref(node)),
            NodeOrToken::Token(token) => Self::Token(ResolvedToken::coerce_ref(token)),
        }
    }
}

impl<'a, L: Language, D> From<&'a ResolvedNode<L, D>> for ResolvedElementRef<'a, L, D> {
    fn from(node: &'a ResolvedNode<L, D>) -> Self {
        NodeOrToken::Node(node)
    }
}

impl<'a, L: Language, D> From<&'a ResolvedToken<L, D>> for ResolvedElementRef<'a, L, D> {
    fn from(token: &'a ResolvedToken<L, D>) -> Self {
        NodeOrToken::Token(token)
    }
}

impl<'a, L: Language, D> From<&'a ResolvedElement<L, D>> for ResolvedElementRef<'a, L, D> {
    fn from(element: &'a ResolvedElement<L, D>) -> Self {
        match element {
            NodeOrToken::Node(it) => Self::Node(it),
            NodeOrToken::Token(it) => Self::Token(it),
        }
    }
}

impl<L: Language, D> ResolvedNode<L, D> {
    /// Uses the resolver associated with this tree to return an efficient representation of all
    /// source text covered by this node, i.e. the combined text of all token leafs of the subtree
    /// originating in this node.
    #[inline]
    pub fn text(&self) -> SyntaxText<'_, '_, dyn Resolver<TokenKey>, L, D> {
        SyntaxText::new(self, &**self.resolver())
    }
}

impl<L: Language, D> fmt::Debug for ResolvedNode<L, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write_debug(&**self.resolver(), f, f.alternate())
    }
}

impl<L: Language, D> fmt::Display for ResolvedNode<L, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write_display(&**self.resolver(), f)
    }
}

impl<L: Language, D> ResolvedToken<L, D> {
    /// Uses the resolver associated with this tree to return the source text of this token.
    #[inline]
    pub fn text(&self) -> &str {
        // one of the two must be present upon construction
        self.static_text()
            .or_else(|| self.green().text(&**self.resolver()))
            .unwrap()
    }
}

impl<L: Language, D> fmt::Debug for ResolvedToken<L, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write_debug(&**self.resolver(), f)
    }
}

impl<L: Language, D> fmt::Display for ResolvedToken<L, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.write_display(&**self.resolver(), f)
    }
}

#[cfg(feature = "serialize")]
impl<L, D> ResolvedNode<L, D>
where
    L: Language,
{
    /// Return an anonymous object that can be used to serialize this node,
    /// including the data for each node.
    pub fn as_serialize_with_data(&self) -> impl serde::Serialize + '_
    where
        D: serde::Serialize,
    {
        crate::serde_impls::SerializeWithData {
            node:     self,
            resolver: self.resolver().as_ref(),
        }
    }
}

/* It follows: wrapping all _traversal_ methods so they return `ResolvedXY`s */
macro_rules! forward {
    // safety: if we're starting from a `ResolvedXY`, then the tree must have a resolver
    ($e:expr) => {
        ($e).map(|e| unsafe { Self::coerce_ref(e) })
    };
}

macro_rules! forward_as_elem {
    // safety: if we're starting from a `ResolvedXY`, then the tree must have a resolver
    ($e:expr) => {
        ($e).map(|e| unsafe { ResolvedElementRef::coerce_ref(e) })
    };
}

macro_rules! forward_token {
    // safety: if we're starting from a `ResolvedXY`, then the tree must have a resolver
    ($e:expr) => {
        ($e).map(|e| unsafe { ResolvedToken::coerce_ref(e) })
    };
}

macro_rules! forward_node {
    // safety: if we're starting from a `ResolvedXY`, then the tree must have a resolver
    ($e:expr) => {
        ($e).map(|e| unsafe { ResolvedNode::coerce_ref(e) })
    };
}

impl<L: Language, D> ResolvedNode<L, D> {
    /// Returns the [`Resolver`] associated with this tree.
    pub fn resolver(&self) -> &StdArc<dyn Resolver<TokenKey>> {
        self.syntax.resolver().unwrap()
    }

    /// See [`SyntaxNode::new_root_with_resolver`].
    #[inline]
    pub fn new_root_with_resolver(green: GreenNode, resolver: impl Resolver<TokenKey> + 'static) -> Self {
        SyntaxNode::new_root_with_resolver(green, resolver)
    }

    /// Always returns `Some(self)`.
    ///
    /// This method mostly exists to allow the convenience of being agnostic over [`SyntaxNode`] vs [`ResolvedNode`].
    #[inline]
    pub fn try_resolved(&self) -> Option<&ResolvedNode<L, D>> {
        Some(self)
    }

    /// Always returns `self`.
    ///
    /// This method mostly exists to allow the convenience of being agnostic over [`SyntaxNode`] vs [`ResolvedNode`].
    #[inline]
    pub fn resolved(&self) -> &ResolvedNode<L, D> {
        self
    }

    /// The root of the tree this node belongs to.
    ///
    /// If this node is the root, returns `self`.
    #[inline]
    pub fn root(&self) -> &SyntaxNode<L, D> {
        unsafe { Self::coerce_ref(self.syntax.root()) }
    }

    /// The parent node of this node, except if this node is the root.
    #[inline]
    pub fn parent(&self) -> Option<&Self> {
        forward!(self.syntax.parent())
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &Self> {
        forward!(self.syntax.ancestors())
    }

    /// Returns an iterator over all nodes that are children of this node.
    ///
    /// If you want to also consider leafs, see [`children_with_tokens`](ResolvedNode::children_with_tokens).
    #[inline]
    pub fn children(&self) -> impl Iterator<Item = &Self> {
        forward!(self.syntax.children())
    }

    /// Returns an iterator over child elements of this node, including tokens.
    #[inline]
    pub fn children_with_tokens(&self) -> impl Iterator<Item = ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.children_with_tokens())
    }

    /// The first child node of this node, if any.
    ///
    /// If you want to also consider leafs, see [`first_child_or_token`](ResolvedNode::first_child_or_token).
    #[inline]
    pub fn first_child(&self) -> Option<&ResolvedNode<L, D>> {
        forward!(self.syntax.first_child())
    }

    /// The first child element of this node, if any, including tokens.
    #[inline]
    pub fn first_child_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.first_child_or_token())
    }

    /// The last child node of this node, if any.
    ///
    /// If you want to also consider leafs, see [`last_child_or_token`](ResolvedNode::last_child_or_token).
    #[inline]
    pub fn last_child(&self) -> Option<&ResolvedNode<L, D>> {
        forward!(self.syntax.last_child())
    }

    /// The last child element of this node, if any, including tokens.
    #[inline]
    pub fn last_child_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.last_child_or_token())
    }

    /// The first child node of this node starting at the (n + 1)-st, if any.
    /// Note that even if this method returns `Some`, the contained node may not actually be the (n +
    /// 1)-st child, but the next child from there that is a node.
    ///
    /// If you want to also consider leafs, see [`next_child_or_token_after`](ResolvedNode::next_child_or_token_after).
    #[inline]
    pub fn next_child_after(&self, n: usize, offset: TextSize) -> Option<&ResolvedNode<L, D>> {
        forward!(self.syntax.next_child_after(n, offset))
    }

    /// The first child element of this node starting at the (n + 1)-st, if any.
    /// If this method returns `Some`, the contained node is the (n + 1)-st child of this node.
    #[inline]
    pub fn next_child_or_token_after(&self, n: usize, offset: TextSize) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.next_child_or_token_after(n, offset))
    }

    /// The last child node of this node up to the nth, if any.
    /// Note that even if this method returns `Some`, the contained node may not actually be the (n -
    /// 1)-st child, but the previous child from there that is a node.
    ///
    /// If you want to also consider leafs, see
    /// [`prev_child_or_token_before`](ResolvedNode::prev_child_or_token_before).
    #[inline]
    pub fn prev_child_before(&self, n: usize, offset: TextSize) -> Option<&ResolvedNode<L, D>> {
        forward!(self.syntax.prev_child_before(n, offset))
    }

    /// The last child node of this node up to the nth, if any.
    /// If this method returns `Some`, the contained node is the (n - 1)-st child.
    #[inline]
    pub fn prev_child_or_token_before(&self, n: usize, offset: TextSize) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.prev_child_or_token_before(n, offset))
    }

    /// The node to the right of this one, i.e. the next child node (!) of this node's parent after this node.
    ///
    /// If you want to also consider leafs, see [`next_sibling_or_token`](ResolvedNode::next_sibling_or_token).
    #[inline]
    pub fn next_sibling(&self) -> Option<&ResolvedNode<L, D>> {
        forward!(self.syntax.next_sibling())
    }

    /// The tree element to the right of this one, i.e. the next child of this node's parent after this node.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.next_sibling_or_token())
    }

    /// The node to the left of this one, i.e. the previous child node (!) of this node's parent before this node.
    ///
    /// If you want to also consider leafs, see [`prev_sibling_or_token`](ResolvedNode::prev_sibling_or_token).
    #[inline]
    pub fn prev_sibling(&self) -> Option<&ResolvedNode<L, D>> {
        forward!(self.syntax.prev_sibling())
    }

    /// The tree element to the left of this one, i.e. the previous child of this node's parent before this node.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.prev_sibling_or_token())
    }

    /// Return the leftmost token in the subtree of this node
    #[inline]
    pub fn first_token(&self) -> Option<&ResolvedToken<L, D>> {
        forward_token!(self.syntax.first_token())
    }

    /// Return the rightmost token in the subtree of this node
    #[inline]
    pub fn last_token(&self) -> Option<&ResolvedToken<L, D>> {
        forward_token!(self.syntax.last_token())
    }

    /// Returns an iterator over all sibling nodes of this node in the given `direction`, i.e. all of
    /// this node's parent's child nodes (!) from this node on to the left or the right. The first
    /// item in the iterator will always be this node.
    ///
    /// If you want to also consider leafs, see [`siblings_with_tokens`](ResolvedNode::siblings_with_tokens).
    #[inline]
    pub fn siblings(&self, direction: Direction) -> impl Iterator<Item = &ResolvedNode<L, D>> {
        forward!(self.syntax.siblings(direction))
    }

    /// Returns an iterator over all siblings of this node in the given `direction`, i.e. all of this
    /// node's parent's children from this node on to the left or the right.
    /// The first item in the iterator will always be this node.
    #[inline]
    pub fn siblings_with_tokens(&self, direction: Direction) -> impl Iterator<Item = ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.siblings_with_tokens(direction))
    }

    /// Returns an iterator over all nodes (!) in the subtree starting at this node, including this node.
    ///
    /// If you want to also consider leafs, see [`descendants_with_tokens`](ResolvedNode::descendants_with_tokens).
    #[inline]
    pub fn descendants(&self) -> impl Iterator<Item = &ResolvedNode<L, D>> {
        forward!(self.syntax.descendants())
    }

    /// Returns an iterator over all elements in the subtree starting at this node, including this node.
    #[inline]
    pub fn descendants_with_tokens(&self) -> impl Iterator<Item = ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.descendants_with_tokens())
    }

    /// Traverse the subtree rooted at the current node (including the current
    /// node) in preorder, excluding tokens.
    #[inline(always)]
    pub fn preorder(&self) -> impl Iterator<Item = WalkEvent<&ResolvedNode<L, D>>> {
        self.syntax
            .preorder()
            .map(|event| event.map(|node| unsafe { Self::coerce_ref(node) }))
    }

    /// Traverse the subtree rooted at the current node (including the current
    /// node) in preorder, including tokens.
    #[inline(always)]
    pub fn preorder_with_tokens(&self) -> impl Iterator<Item = WalkEvent<ResolvedElementRef<'_, L, D>>> {
        self.syntax
            .preorder_with_tokens()
            .map(|event| event.map(|elem| unsafe { ResolvedElementRef::coerce_ref(elem) }))
    }

    /// Find a token in the subtree corresponding to this node, which covers the offset.
    /// Precondition: offset must be withing node's range.
    pub fn token_at_offset(&self, offset: TextSize) -> TokenAtOffset<ResolvedToken<L, D>> {
        self.syntax
            .token_at_offset(offset)
            .map(|token| ResolvedToken { syntax: token })
    }

    /// Return the deepest node or token in the current subtree that fully
    /// contains the range. If the range is empty and is contained in two leaf
    /// nodes, either one can be returned. Precondition: range must be contained
    /// withing the current node
    pub fn covering_element(&self, range: TextRange) -> ResolvedElementRef<'_, L, D> {
        unsafe { ResolvedElementRef::coerce_ref(self.syntax.covering_element(range)) }
    }
}

impl<L: Language, D> ResolvedToken<L, D> {
    /// Returns the [`Resolver`] associated with this tree.
    pub fn resolver(&self) -> &StdArc<dyn Resolver<TokenKey>> {
        self.syntax.resolver().unwrap()
    }

    /// Always returns `Some(self)`.
    ///
    /// This method mostly exists to allow the convenience of being agnostic over [`SyntaxToken`] vs [`ResolvedToken`].
    #[inline]
    pub fn try_resolved(&self) -> Option<&ResolvedToken<L, D>> {
        Some(self)
    }

    /// Always returns `self`.
    ///
    /// This method mostly exists to allow the convenience of being agnostic over [`SyntaxToken`] vs [`ResolvedToken`].
    #[inline]
    pub fn resolved(&self) -> &ResolvedToken<L, D> {
        self
    }

    /// The parent node of this token.
    #[inline]
    pub fn parent(&self) -> &ResolvedNode<L, D> {
        unsafe { ResolvedNode::coerce_ref(self.syntax.parent()) }
    }

    /// Returns an iterator along the chain of parents of this token.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &ResolvedNode<L, D>> {
        forward_node!(self.syntax.ancestors())
    }

    /// The tree element to the right of this one, i.e. the next child of this token's parent after this token.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.next_sibling_or_token())
    }

    /// The tree element to the left of this one, i.e. the previous child of this token's parent after this token.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.prev_sibling_or_token())
    }

    /// Returns an iterator over all siblings of this token in the given `direction`, i.e. all of this
    /// token's parent's children from this token on to the left or the right.
    /// The first item in the iterator will always be this token.
    #[inline]
    pub fn siblings_with_tokens(&self, direction: Direction) -> impl Iterator<Item = ResolvedElementRef<'_, L, D>> {
        forward_as_elem!(self.syntax.siblings_with_tokens(direction))
    }

    /// Returns the next token in the tree.
    /// This is not necessary a direct sibling of this token, but will always be further right in the tree.
    pub fn next_token(&self) -> Option<&ResolvedToken<L, D>> {
        forward!(self.syntax.next_token())
    }

    /// Returns the previous token in the tree.
    /// This is not necessary a direct sibling of this token, but will always be further left in the tree.
    pub fn prev_token(&self) -> Option<&ResolvedToken<L, D>> {
        forward!(self.syntax.prev_token())
    }
}

impl<L: Language, D> ResolvedElement<L, D> {
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
    pub fn kind(&self) -> L::Kind {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    /// The parent node of this element, except if this element is the root.
    #[inline]
    pub fn parent(&self) -> Option<&ResolvedNode<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &ResolvedNode<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    /// Return the leftmost token in the subtree of this element.
    #[inline]
    pub fn first_token(&self) -> Option<&ResolvedToken<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// Return the rightmost token in the subtree of this element.
    #[inline]
    pub fn last_token(&self) -> Option<&ResolvedToken<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// The tree element to the right of this one, i.e. the next child of this element's parent after this element.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    /// The tree element to the left of this one, i.e. the previous child of this element's parent after this element.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<ResolvedElementRef<'_, L, D>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }
}

impl<'a, L: Language, D> ResolvedElementRef<'a, L, D> {
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
    pub fn kind(&self) -> L::Kind {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    /// The parent node of this element, except if this element is the root.
    #[inline]
    pub fn parent(&self) -> Option<&'a ResolvedNode<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &'a ResolvedNode<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    /// Return the leftmost token in the subtree of this element.
    #[inline]
    pub fn first_token(&self) -> Option<&'a ResolvedToken<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// Return the rightmost token in the subtree of this element.
    #[inline]
    pub fn last_token(&self) -> Option<&'a ResolvedToken<L, D>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    /// The tree element to the right of this one, i.e. the next child of this element's parent after this element.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<ResolvedElementRef<'a, L, D>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    /// The tree element to the left of this one, i.e. the previous child of this element's parent after this element.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<ResolvedElementRef<'a, L, D>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }
}
