use std::hash::{Hash, Hasher};

use rustc_hash::{FxHashMap, FxHasher};
use text_size::TextSize;

use crate::{
    green::{GreenElement, GreenNode, GreenToken},
    interning::{new_interner, Interner, TokenInterner, TokenKey},
    util::NodeOrToken,
    utility_types::MaybeOwned,
    RawSyntaxKind, Syntax,
};

use super::{node::GreenNodeHead, token::GreenTokenData};

/// If `node.children() <= CHILDREN_CACHE_THRESHOLD`, we will not create
/// a new [`GreenNode`], but instead lookup in the cache if this node is
/// already present. If so we use the one in the cache, otherwise we insert
/// this node into the cache.
const CHILDREN_CACHE_THRESHOLD: usize = 3;

/// A `NodeCache` deduplicates identical tokens and small nodes during tree construction.
/// You can re-use the same cache for multiple similar trees with [`GreenNodeBuilder::with_cache`].
#[derive(Debug)]
pub struct NodeCache<'i, I = TokenInterner> {
    nodes:    FxHashMap<GreenNodeHead, GreenNode>,
    tokens:   FxHashMap<GreenTokenData, GreenToken>,
    interner: MaybeOwned<'i, I>,
}

impl NodeCache<'static> {
    /// Constructs a new, empty cache.
    ///
    /// By default, this will also create a default interner to deduplicate source text (strings) across
    /// tokens. To re-use an existing interner, see [`with_interner`](NodeCache::with_interner).
    /// # Examples
    /// ```
    /// # use cstree::testing::*;
    /// use cstree::build::NodeCache;
    ///
    /// // Build a tree
    /// let mut cache = NodeCache::new();
    /// let mut builder: GreenNodeBuilder<MySyntax> = GreenNodeBuilder::with_cache(&mut cache);
    /// # builder.start_node(Root);
    /// # builder.token(Int, "42");
    /// # builder.finish_node();
    /// parse(&mut builder, "42");
    /// let (tree, _) = builder.finish();
    ///
    /// // Check it out!
    /// assert_eq!(tree.kind(), MySyntax::into_raw(Root));
    /// let int = tree.children().next().unwrap();
    /// assert_eq!(int.kind(), MySyntax::into_raw(Int));
    /// ```
    pub fn new() -> Self {
        Self {
            nodes:    FxHashMap::default(),
            tokens:   FxHashMap::default(),
            interner: MaybeOwned::Owned(new_interner()),
        }
    }
}

impl Default for NodeCache<'static> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'i, I> NodeCache<'i, I>
where
    I: Interner<TokenKey>,
{
    /// Constructs a new, empty cache that will use the given interner to deduplicate source text
    /// (strings) across tokens.
    /// # Examples
    /// ```
    /// # use cstree::testing::*;
    /// # use cstree::interning::*;
    /// use cstree::build::NodeCache;
    ///
    /// // Create the builder from a custom interner
    /// let mut interner = new_interner();
    /// let mut cache = NodeCache::with_interner(&mut interner);
    /// let mut builder: GreenNodeBuilder<MySyntax, TokenInterner> =
    ///     GreenNodeBuilder::with_cache(&mut cache);
    ///
    /// // Construct the tree
    /// # builder.start_node(Root);
    /// # builder.token(Int, "42");
    /// # builder.finish_node();
    /// parse(&mut builder, "42");
    /// let (tree, _) = builder.finish();
    ///
    /// // Use the tree
    /// assert_eq!(tree.kind(), MySyntax::into_raw(Root));
    /// let int = tree.children().next().unwrap();
    /// assert_eq!(int.kind(), MySyntax::into_raw(Int));
    /// assert_eq!(int.as_token().unwrap().text(&interner), Some("42"));
    /// ```
    #[inline]
    pub fn with_interner(interner: &'i mut I) -> Self {
        Self {
            nodes:    FxHashMap::default(),
            tokens:   FxHashMap::default(),
            interner: MaybeOwned::Borrowed(interner),
        }
    }

    /// Constructs a new, empty cache that will use the given interner to deduplicate source text
    /// (strings) across tokens.
    /// # Examples
    /// ```
    /// # use cstree::testing::*;
    /// # use cstree::interning::*;
    /// use cstree::build::NodeCache;
    ///
    /// // Create the builder from a custom interner
    /// let mut interner = new_interner();
    /// let cache = NodeCache::from_interner(interner);
    /// let mut builder: GreenNodeBuilder<MySyntax, TokenInterner> =
    ///     GreenNodeBuilder::from_cache(cache);
    ///
    /// // Construct the tree
    /// # builder.start_node(Root);
    /// # builder.token(Int, "42");
    /// # builder.finish_node();
    /// parse(&mut builder, "42");
    /// let (tree, cache) = builder.finish();
    ///
    /// // Use the tree
    /// let interner = cache.unwrap().into_interner().unwrap();
    /// assert_eq!(tree.kind(), MySyntax::into_raw(Root));
    /// let int = tree.children().next().unwrap();
    /// assert_eq!(int.kind(), MySyntax::into_raw(Int));
    /// assert_eq!(int.as_token().unwrap().text(&interner), Some("42"));
    /// ```
    #[inline]
    pub fn from_interner(interner: I) -> Self {
        Self {
            nodes:    FxHashMap::default(),
            tokens:   FxHashMap::default(),
            interner: MaybeOwned::Owned(interner),
        }
    }

    /// Get a reference to the interner used to deduplicate source text (strings).
    ///
    /// See also [`interner_mut`](NodeCache::interner_mut).
    #[inline]
    pub fn interner(&self) -> &I {
        &self.interner
    }

    /// Get a mutable reference to the interner used to deduplicate source text (strings).
    /// # Examples
    /// ```
    /// # use cstree::*;
    /// # use cstree::build::*;
    /// # use cstree::interning::*;
    /// let mut cache = NodeCache::new();
    /// let interner = cache.interner_mut();
    /// let key = interner.get_or_intern("foo");
    /// assert_eq!(interner.resolve(key), "foo");
    /// ```
    #[inline]
    pub fn interner_mut(&mut self) -> &mut I {
        &mut self.interner
    }

    /// If this node cache was constructed with [`new`](NodeCache::new) or
    /// [`from_interner`](NodeCache::from_interner), returns the interner used to deduplicate source
    /// text (strings) to allow resolving tree tokens back to text and re-using the interner to build
    /// additonal trees.
    #[inline]
    pub fn into_interner(self) -> Option<I> {
        self.interner.into_owned()
    }

    fn node<S: Syntax>(&mut self, kind: S, all_children: &mut Vec<GreenElement>, offset: usize) -> GreenNode {
        // NOTE: this fn must remove all children starting at `first_child` from `all_children` before returning
        let kind = S::into_raw(kind);
        let mut hasher = FxHasher::default();
        let mut text_len: TextSize = 0.into();
        for child in &all_children[offset..] {
            text_len += child.text_len();
            child.hash(&mut hasher);
        }
        let child_hash = hasher.finish() as u32;

        // Green nodes are fully immutable, so it's ok to deduplicate them.
        // This is the same optimization that Roslyn does
        // https://github.com/KirillOsenkov/Bliki/wiki/Roslyn-Immutable-Trees
        //
        // For example, all `#[inline]` in this file share the same green node!
        // For `libsyntax/parse/parser.rs`, measurements show that deduping saves
        // 17% of the memory for green nodes!
        let children = all_children.drain(offset..);
        if children.len() <= CHILDREN_CACHE_THRESHOLD {
            self.get_cached_node(kind, children, text_len, child_hash)
        } else {
            GreenNode::new_with_len_and_hash(kind, children, text_len, child_hash)
        }
    }

    #[inline(always)]
    fn intern(&mut self, text: &str) -> TokenKey {
        self.interner.get_or_intern(text)
    }

    /// Creates a [`GreenNode`] by looking inside the cache or inserting
    /// a new node into the cache if it's a cache miss.
    #[inline]
    fn get_cached_node(
        &mut self,
        kind: RawSyntaxKind,
        children: std::vec::Drain<'_, GreenElement>,
        text_len: TextSize,
        child_hash: u32,
    ) -> GreenNode {
        let head = GreenNodeHead {
            kind,
            text_len,
            child_hash,
        };
        self.nodes
            .entry(head)
            .or_insert_with_key(|head| GreenNode::from_head_and_children(head.clone(), children))
            .clone()
    }

    fn token<S: Syntax>(&mut self, kind: S, text: Option<TokenKey>, len: u32) -> GreenToken {
        let text_len = TextSize::from(len);
        let kind = S::into_raw(kind);
        let data = GreenTokenData { kind, text, text_len };
        self.tokens
            .entry(data)
            .or_insert_with_key(|data| GreenToken::new(*data))
            .clone()
    }
}

/// A checkpoint for maybe wrapping a node. See [`GreenNodeBuilder::checkpoint`] for details.
#[derive(Clone, Copy, Debug)]
pub struct Checkpoint {
    parent_idx: usize,
    child_idx:  usize,
}

/// A builder for green trees.
/// Construct with [`new`](GreenNodeBuilder::new), [`with_cache`](GreenNodeBuilder::with_cache), or
/// [`from_cache`](GreenNodeBuilder::from_cache). To add tree nodes, start them with
/// [`start_node`](GreenNodeBuilder::start_node), add [`token`](GreenNodeBuilder::token)s and then
/// [`finish_node`](GreenNodeBuilder::finish_node). When the whole tree is constructed, call
/// [`finish`](GreenNodeBuilder::finish) to obtain the root.
///
/// # Examples
/// ```
/// # use cstree::testing::*;
/// // Build a tree
/// let mut builder: GreenNodeBuilder<MySyntax> = GreenNodeBuilder::new();
/// builder.start_node(Root);
/// builder.token(Int, "42");
/// builder.finish_node();
/// let (tree, cache) = builder.finish();
///
/// // Check it out!
/// assert_eq!(tree.kind(), MySyntax::into_raw(Root));
/// let int = tree.children().next().unwrap();
/// assert_eq!(int.kind(), MySyntax::into_raw(Int));
/// let resolver = cache.unwrap().into_interner().unwrap();
/// assert_eq!(int.as_token().unwrap().text(&resolver), Some("42"));
/// ```
#[derive(Debug)]
pub struct GreenNodeBuilder<'cache, 'interner, S: Syntax, I = TokenInterner> {
    cache:    MaybeOwned<'cache, NodeCache<'interner, I>>,
    parents:  Vec<(S, usize)>,
    children: Vec<GreenElement>,
}

impl<S: Syntax> GreenNodeBuilder<'static, 'static, S> {
    /// Creates new builder with an empty [`NodeCache`].
    pub fn new() -> Self {
        Self {
            cache:    MaybeOwned::Owned(NodeCache::new()),
            parents:  Vec::with_capacity(8),
            children: Vec::with_capacity(8),
        }
    }
}

impl<S: Syntax> Default for GreenNodeBuilder<'static, 'static, S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'cache, 'interner, S, I> GreenNodeBuilder<'cache, 'interner, S, I>
where
    S: Syntax,
    I: Interner<TokenKey>,
{
    /// Reusing a [`NodeCache`] between multiple builders saves memory, as it allows to structurally
    /// share underlying trees.
    pub fn with_cache(cache: &'cache mut NodeCache<'interner, I>) -> Self {
        Self {
            cache:    MaybeOwned::Borrowed(cache),
            parents:  Vec::with_capacity(8),
            children: Vec::with_capacity(8),
        }
    }

    /// Reusing a [`NodeCache`] between multiple builders saves memory, as it allows to structurally
    /// share underlying trees.
    /// The `cache` given will be returned on [`finish`](GreenNodeBuilder::finish).
    /// # Examples
    /// ```
    /// # use cstree::testing::*;
    /// # use cstree::build::*;
    /// // Construct a builder from our own cache
    /// let cache = NodeCache::new();
    /// let mut builder: GreenNodeBuilder<MySyntax> = GreenNodeBuilder::from_cache(cache);
    ///
    /// // Build a tree
    /// # builder.start_node(Root);
    /// # builder.token(Int, "42");
    /// # builder.finish_node();
    /// parse(&mut builder, "42");
    /// let (tree, cache) = builder.finish();
    ///
    /// // Use the tree
    /// let interner = cache.unwrap().into_interner().unwrap();
    /// assert_eq!(tree.kind(), MySyntax::into_raw(Root));
    /// let int = tree.children().next().unwrap();
    /// assert_eq!(int.kind(), MySyntax::into_raw(Int));
    /// assert_eq!(int.as_token().unwrap().text(&interner), Some("42"));
    /// ```
    pub fn from_cache(cache: NodeCache<'interner, I>) -> Self {
        Self {
            cache:    MaybeOwned::Owned(cache),
            parents:  Vec::with_capacity(8),
            children: Vec::with_capacity(8),
        }
    }

    /// Shortcut to construct a builder that uses an existing interner.
    ///
    /// This is equivalent to using [`from_cache`](GreenNodeBuilder::from_cache) with a node cache
    /// obtained from [`NodeCache::with_interner`].
    #[inline]
    pub fn with_interner(interner: &'interner mut I) -> Self {
        let cache = NodeCache::with_interner(interner);
        Self::from_cache(cache)
    }

    /// Shortcut to construct a builder that uses an existing interner.
    ///
    /// This is equivalent to using [`from_cache`](GreenNodeBuilder::from_cache) with a node cache
    /// obtained from [`NodeCache::from_interner`].
    #[inline]
    pub fn from_interner(interner: I) -> Self {
        let cache = NodeCache::from_interner(interner);
        Self::from_cache(cache)
    }

    /// Get a reference to the interner used to deduplicate source text (strings).
    ///
    /// This is the same interner as used by the underlying [`NodeCache`].
    /// See also [`interner_mut`](GreenNodeBuilder::interner_mut).
    #[inline]
    pub fn interner(&self) -> &I {
        &self.cache.interner
    }

    /// Get a mutable reference to the interner used to deduplicate source text (strings).
    ///
    /// This is the same interner as used by the underlying [`NodeCache`].
    /// # Examples
    /// ```
    /// # use cstree::testing::*;
    /// # use cstree::build::*;
    /// # use cstree::interning::*;
    /// let mut builder: GreenNodeBuilder<MySyntax> = GreenNodeBuilder::new();
    /// let interner = builder.interner_mut();
    /// let key = interner.get_or_intern("foo");
    /// assert_eq!(interner.resolve(key), "foo");
    /// ```
    #[inline]
    pub fn interner_mut(&mut self) -> &mut I {
        &mut self.cache.interner
    }

    /// Add a new token with the given `text` to the current node.
    ///
    /// ## Panics
    /// In debug mode, if `kind` has static text, this function will verify that `text` matches that text.
    #[inline]
    pub fn token(&mut self, kind: S, text: &str) {
        let token = match S::static_text(kind) {
            Some(static_text) => {
                debug_assert_eq!(
                    static_text, text,
                    r#"Received `{kind:?}` token which should have text "{static_text}", but "{text}" was given."#
                );
                self.cache.token::<S>(kind, None, static_text.len() as u32)
            }
            None => {
                let len = text.len() as u32;
                let text = self.cache.intern(text);
                self.cache.token::<S>(kind, Some(text), len)
            }
        };
        self.children.push(token.into());
    }

    /// Add a new token to the current node without storing an explicit section of text.
    /// This is be useful if the text can always be inferred from the token's `kind`, for example
    /// when using kinds for specific operators or punctuation.
    ///
    /// For tokens whose textual representation is not static, such as numbers or identifiers, use
    /// [`token`](GreenNodeBuilder::token).
    ///
    /// ## Panics
    /// If `kind` does not have static text, i.e., `L::static_text(kind)` returns `None`.
    #[inline]
    pub fn static_token(&mut self, kind: S) {
        let static_text = S::static_text(kind).unwrap_or_else(|| panic!("Missing static text for '{kind:?}'"));
        let token = self.cache.token::<S>(kind, None, static_text.len() as u32);
        self.children.push(token.into());
    }

    /// Start new node of the given `kind` and make it current.
    #[inline]
    pub fn start_node(&mut self, kind: S) {
        let len = self.children.len();
        self.parents.push((kind, len));
    }

    /// Finish the current branch and restore the previous branch as current.
    #[inline]
    pub fn finish_node(&mut self) {
        let (kind, first_child) = self.parents.pop().unwrap();
        // NOTE: we rely on the node cache to remove all children starting at `first_child` from `self.children`
        let node = self.cache.node::<S>(kind, &mut self.children, first_child);
        self.children.push(node.into());
    }

    /// Take a snapshot of the builder's state, which can be used to retroactively insert surrounding nodes by calling
    /// [`start_node_at`](GreenNodeBuilder::start_node_at), or for backtracking by allowing to
    /// [`revert_to`](GreenNodeBuilder::revert_to) the returned checkpoint.
    ///
    /// Checkpoints are _invalidated_ and can no longer be used if nodes older than (started before) the checkpoint are
    /// finished, and also if the builder is reverted past them to an even earlier checkpoint.
    ///
    /// # Examples
    /// ```
    /// # use cstree::testing::*;
    /// # use cstree::build::GreenNodeBuilder;
    /// # struct Parser;
    /// # impl Parser {
    /// #     fn peek(&self) -> Option<TestSyntaxKind> { None }
    /// #     fn parse_expr(&mut self) {}
    /// # }
    /// # let mut builder: GreenNodeBuilder<MySyntax> = GreenNodeBuilder::new();
    /// # let mut parser = Parser;
    /// let checkpoint = builder.checkpoint();
    /// parser.parse_expr();
    /// if let Some(Plus) = parser.peek() {
    ///     // 1 + 2 = Add(1, 2)
    ///     builder.start_node_at(checkpoint, Operation);
    ///     parser.parse_expr();
    ///     builder.finish_node();
    /// }
    /// ```
    #[inline]
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            parent_idx: self.parents.len(),
            child_idx:  self.children.len(),
        }
    }

    /// Restore the builder's state to when the [`Checkpoint`] was taken.
    ///
    /// This is useful for backtracking parsers. It will delete any nodes that were started but not finished since the
    /// checkpoint was taken, as well as any tokens that were recorded since. Checkpoints can be nested, but reverting
    /// to a checkpoint invalidates all other checkpoints that were taken after it.
    ///
    /// ## Panics
    ///
    /// When using checkpoints, calls to [`start_node`](GreenNodeBuilder::start_node) and
    /// [`finish_node`](GreenNodeBuilder::finish_node) must always be balanced in between the call
    /// to [`checkpoint`](GreenNodeBuilder::checkpoint) and a call to either `revert_to` or
    /// [`start_node_at`](GreenNodeBuilder::start_node_at).
    /// Since it is impossible to revert the finishing of any node started before taking the checkpoint, this function
    /// will panic if it detects that this is the case.
    ///
    /// Example:
    /// ```rust
    /// # use cstree::testing::*;
    /// # use cstree::build::GreenNodeBuilder;
    /// # struct Parser;
    /// # impl Parser {
    /// #     fn peek(&self) -> Option<TestSyntaxKind> { None }
    /// #     fn parse_expr(&mut self) {}
    /// # }
    /// # let mut builder: GreenNodeBuilder<MySyntax> = GreenNodeBuilder::new();
    /// # let mut parser = Parser;
    /// let checkpoint = builder.checkpoint();
    /// parser.parse_expr();
    /// if let Some(Plus) = parser.peek() {
    ///     // 1 + 2 = Add(1, 2)
    ///     builder.start_node_at(checkpoint, Operation);
    ///     parser.parse_expr();
    ///     builder.finish_node();
    /// } else {
    ///     builder.revert_to(checkpoint);
    /// }
    /// ```
    pub fn revert_to(&mut self, checkpoint: Checkpoint) {
        let Checkpoint { parent_idx, child_idx } = checkpoint;
        // NOTE: This doesn't catch scenarios where we've read more tokens since the previous revert
        // (see test `misuse3`), but it'll catch simple cases of reverting to the past and then
        // trying to revert to the future (see tests `misuse` and `misuse2`).
        //
        // See `start_node_at` for a general explanation of the conditions here. As opposed to `start_node_at`,
        // unfinished nodes are fine here (since we're going to revert them), so a `parent_idx` less than
        // `self.parents.len()` is valid.
        assert!(
            parent_idx <= self.parents.len(),
            "checkpoint no longer valid, was `finish_node` called early or did you already `revert_to`?"
        );
        assert!(
            child_idx <= self.children.len(),
            "checkpoint no longer valid after reverting to an earlier checkpoint"
        );
        if let Some(&(_, first_child)) = self.parents.last() {
            assert!(
                child_idx >= first_child,
                "checkpoint no longer valid, was an unmatched start_node_at called?"
            );
        }

        self.parents.truncate(parent_idx);
        self.children.truncate(child_idx);
    }

    /// Start a node at the given [`checkpoint`](GreenNodeBuilder::checkpoint), wrapping all nodes
    /// and tokens created since the checkpoint was taken.
    ///
    /// ## Panics
    ///
    /// When using checkpoints, calls to [`start_node`](GreenNodeBuilder::start_node) and
    /// [`finish_node`](GreenNodeBuilder::finish_node) must always be balanced in between the call
    /// to [`checkpoint`](GreenNodeBuilder::checkpoint) and a call to either
    /// [`revert_to`](GreenNodeBuilder::revert_to) or `start_node_at`:
    ///
    /// It is impossible to start a node retroactively if one or more nodes started before taking
    /// the checkpoint have already been finished when trying to call this function. This function
    /// will panic if it detects that this is the case.
    ///
    /// This function will also panic if one or more nodes were started _after_ the checkpoint was
    /// taken and were not yet finished, which would leave these nodes simultaneously inside and
    /// outside the newly started node (neither node would contain the other).
    #[inline]
    pub fn start_node_at(&mut self, checkpoint: Checkpoint, kind: S) {
        let Checkpoint { parent_idx, child_idx } = checkpoint;
        // NOTE: Due to the requirement to balance `start_node` and `finish_node` in between the calls to `checkpoint`
        // and this function, there must be exactly the same number of `self.parents` now as there were when the
        // checkpoint was created (`start_node` creates a new parent and `finish_node` moves it to `self.children`).
        //
        // We assert both inequalities separately to give better error messages: if the checkpoint points past the end
        // of `self.parents`, this indicates that a node outside the scope of the checkpoint was already finished (or
        // reverted), while there being parents past the checkpointed index indicates that new nodes were started that
        // were left unfinished.
        assert!(
            parent_idx <= self.parents.len(),
            "checkpoint no longer valid, was `finish_node` called early or did you already `revert_to`?"
        );
        assert!(
            parent_idx >= self.parents.len(),
            "checkpoint contains one or more unfinished nodes"
        );

        // NOTE: The checkpoint can only point past the end of children if there were children on the stack when it was
        // taken that got removed before it was used. Since any nodes started after taking the checkpoint will
        // point to a `first_child` >= the checkpoint's `child_idx`, they cannot remove such children when they
        // are finished. The are only two ways to remove them:
        //   1. to finish a node which was already started at the time of taking the checkpoint and which may thus point
        //      to an earlier child as its `first_child`, or
        //   2. to `revert_to` an earlier checkpoint before trying to start a new node at this one.
        //
        // Since we require calls to `start_node` and `finish_node` to be balanced between taking and using the
        // checkpoint, (1) will be caught by the assert against the `parent_idx` above. This will also catch (2) in
        // cases where at least one node is started between the earlier checkpoint and this one. However, it may be the
        // case that only tokens are recorded in between the two, in which case we need to check the `child_idx` too.
        assert!(
            child_idx <= self.children.len(),
            "checkpoint no longer valid after reverting to an earlier checkpoint"
        );

        // NOTE: When `start_node` is called after `checkpoint`, the new node gets pushed to `parents`.
        // However, `start_node` and `finish_node` must be balanced inbetween the calls to `checkpoint` and
        // `start_node_at`, and `finish_node` causes the topmost parent to become a child instead.
        // Therefore, the topmost parent _at the time of calling `start_node_at`_ must still be pointing
        // "behind" the checkpoint in the list of children.
        if let Some(&(_, first_child)) = self.parents.last() {
            assert!(
                child_idx >= first_child,
                "checkpoint no longer valid, was an unmatched `start_node` or `start_node_at` called?"
            );
        }

        self.parents.push((kind, child_idx));
    }

    /// Complete building the tree.
    ///
    /// Make sure that calls to [`start_node`](GreenNodeBuilder::start_node) /
    /// [`start_node_at`](GreenNodeBuilder::start_node_at) and
    /// [`finish_node`](GreenNodeBuilder::finish_node) are balanced, i.e. that every started node has
    /// been completed!
    ///
    /// If this builder was constructed with [`new`](GreenNodeBuilder::new) or
    /// [`from_cache`](GreenNodeBuilder::from_cache), this method returns the cache used to deduplicate tree nodes
    ///  as its second return value to allow re-using the cache or extracting the underlying string
    ///  [`Interner`]. See also [`NodeCache::into_interner`].
    #[inline]
    pub fn finish(mut self) -> (GreenNode, Option<NodeCache<'interner, I>>) {
        assert_eq!(self.children.len(), 1);
        let cache = self.cache.into_owned();
        match self.children.pop().unwrap() {
            NodeOrToken::Node(node) => (node, cache),
            NodeOrToken::Token(_) => panic!("called `finish` on a `GreenNodeBuilder` which only contained a token"),
        }
    }
}
