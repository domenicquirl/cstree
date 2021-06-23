use std::{
    convert::TryFrom,
    hash::{Hash, Hasher},
};

use fxhash::{FxHashMap, FxHasher32};
use text_size::TextSize;

use crate::{
    green::{interner::TokenInterner, GreenElement, GreenNode, GreenToken, SyntaxKind},
    interning::Interner,
    NodeOrToken,
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
    /// # use cstree::*;
    /// # const ROOT: SyntaxKind = SyntaxKind(0);
    /// # const INT: SyntaxKind = SyntaxKind(1);
    /// # fn parse(b: &mut GreenNodeBuilder, s: &str) {}
    /// let mut cache = NodeCache::new();
    /// let mut builder = GreenNodeBuilder::with_cache(&mut cache);
    /// # builder.start_node(ROOT);
    /// # builder.token(INT, "42");
    /// # builder.finish_node();
    /// parse(&mut builder, "42");
    /// let (tree, _) = builder.finish();
    /// assert_eq!(tree.kind(), ROOT);
    /// let int = tree.children().next().unwrap();
    /// assert_eq!(int.kind(), INT);
    /// ```
    pub fn new() -> Self {
        Self {
            nodes:    FxHashMap::default(),
            tokens:   FxHashMap::default(),
            interner: MaybeOwned::Owned(TokenInterner::new()),
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
    I: Interner,
{
    /// Constructs a new, empty cache that will use the given interner to deduplicate source text
    /// (strings) across tokens.
    /// # Examples
    /// ```
    /// # use cstree::*;
    /// use lasso::Rodeo;
    /// # const ROOT: SyntaxKind = SyntaxKind(0);
    /// # const INT: SyntaxKind = SyntaxKind(1);
    /// # fn parse(b: &mut GreenNodeBuilder<Rodeo>, s: &str) {}
    /// let mut interner = Rodeo::new();
    /// let mut cache = NodeCache::with_interner(&mut interner);
    /// let mut builder = GreenNodeBuilder::with_cache(&mut cache);
    /// # builder.start_node(ROOT);
    /// # builder.token(INT, "42");
    /// # builder.finish_node();
    /// parse(&mut builder, "42");
    /// let (tree, _) = builder.finish();
    /// assert_eq!(tree.kind(), ROOT);
    /// let int = tree.children().next().unwrap();
    /// assert_eq!(int.kind(), INT);
    /// ```
    pub fn with_interner(interner: &'i mut I) -> Self {
        Self {
            nodes:    FxHashMap::default(),
            tokens:   FxHashMap::default(),
            interner: MaybeOwned::Borrowed(interner),
        }
    }

    fn node<It>(&mut self, kind: SyntaxKind, children: It) -> GreenNode
    where
        It: IntoIterator<Item = GreenElement>,
        It::IntoIter: ExactSizeIterator,
    {
        let children = children.into_iter();

        // Green nodes are fully immutable, so it's ok to deduplicate them.
        // This is the same optimization that Roslyn does
        // https://github.com/KirillOsenkov/Bliki/wiki/Roslyn-Immutable-Trees
        //
        // For example, all `#[inline]` in this file share the same green node!
        // For `libsyntax/parse/parser.rs`, measurements show that deduping saves
        // 17% of the memory for green nodes!
        if children.len() <= CHILDREN_CACHE_THRESHOLD {
            self.get_cached_node(kind, children)
        } else {
            GreenNode::new(kind, children)
        }
    }

    /// Creates a [`GreenNode`] by looking inside the cache or inserting
    /// a new node into the cache if it's a cache miss.
    fn get_cached_node<It>(&mut self, kind: SyntaxKind, children: It) -> GreenNode
    where
        It: IntoIterator<Item = GreenElement>,
        It::IntoIter: ExactSizeIterator,
    {
        #[derive(Clone)]
        struct ChildrenIter {
            data: [Option<GreenElement>; CHILDREN_CACHE_THRESHOLD],
            idx:  usize,
            len:  usize,
        }

        impl ChildrenIter {
            fn new() -> Self {
                ChildrenIter {
                    data: [None, None, None],
                    idx:  0,
                    len:  0,
                }
            }
        }

        impl Iterator for ChildrenIter {
            type Item = GreenElement;

            fn next(&mut self) -> Option<Self::Item> {
                let item = self.data.get_mut(self.idx)?;
                self.idx += 1;
                item.take()
            }
        }

        impl ExactSizeIterator for ChildrenIter {
            fn len(&self) -> usize {
                self.len - self.idx
            }
        }

        let mut new_children = ChildrenIter::new();
        let mut hasher = FxHasher32::default();
        let mut text_len: TextSize = 0.into();
        for (i, child) in children.into_iter().enumerate() {
            text_len += child.text_len();
            child.hash(&mut hasher);
            new_children.data[i] = Some(child);
            new_children.len += 1;
        }

        let head = GreenNodeHead {
            kind,
            text_len,
            child_hash: hasher.finish() as u32,
        };
        self.nodes
            .entry(head)
            .or_insert_with_key(|head| GreenNode::from_head_and_children(head.clone(), new_children))
            .clone()
    }

    fn token(&mut self, kind: SyntaxKind, text: &str) -> GreenToken {
        let text_len = TextSize::try_from(text.len()).unwrap();
        let text = self.interner.get_or_intern(text);
        let data = GreenTokenData { kind, text, text_len };
        self.tokens
            .entry(data)
            .or_insert_with_key(|data| GreenToken::new(*data))
            .clone()
    }
}

#[derive(Debug)]
enum MaybeOwned<'a, T> {
    Owned(T),
    Borrowed(&'a mut T),
}

impl<T> MaybeOwned<'_, T> {
    fn into_owned(self) -> Option<T> {
        match self {
            MaybeOwned::Owned(owned) => Some(owned),
            MaybeOwned::Borrowed(_) => None,
        }
    }
}

impl<T> std::ops::Deref for MaybeOwned<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            MaybeOwned::Owned(it) => it,
            MaybeOwned::Borrowed(it) => *it,
        }
    }
}

impl<T> std::ops::DerefMut for MaybeOwned<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        match self {
            MaybeOwned::Owned(it) => it,
            MaybeOwned::Borrowed(it) => *it,
        }
    }
}

impl<T: Default> Default for MaybeOwned<'_, T> {
    fn default() -> Self {
        MaybeOwned::Owned(T::default())
    }
}

/// A checkpoint for maybe wrapping a node. See [`GreenNodeBuilder::checkpoint`] for details.
#[derive(Clone, Copy, Debug)]
pub struct Checkpoint(usize);

/// A builder for green trees.
/// Construct with [`new`](GreenNodeBuilder::new) or [`with_cache`](GreenNodeBuilder::with_cache). To
/// add tree nodes, start them with [`start_node`](GreenNodeBuilder::start_node), add
/// [`token`](GreenNodeBuilder::token)s and then [`finish_node`](GreenNodeBuilder::finish_node). When
/// the whole tree is constructed, call [`finish`](GreenNodeBuilder::finish) to obtain the root.
///
/// # Examples
/// ```
/// # use cstree::{*, interning::IntoResolver};
/// # const ROOT: SyntaxKind = SyntaxKind(0);
/// # const INT: SyntaxKind = SyntaxKind(1);
/// let mut builder = GreenNodeBuilder::new();
/// builder.start_node(ROOT);
/// builder.token(INT, "42");
/// builder.finish_node();
/// let (tree, interner) = builder.finish();
/// assert_eq!(tree.kind(), ROOT);
/// let int = tree.children().next().unwrap();
/// assert_eq!(int.kind(), INT);
/// let resolver = interner.unwrap().into_resolver();
/// assert_eq!(int.as_token().unwrap().text(&resolver), "42");
/// ```
#[derive(Debug)]
pub struct GreenNodeBuilder<'cache, 'interner, I = TokenInterner> {
    cache:    MaybeOwned<'cache, NodeCache<'interner, I>>,
    parents:  Vec<(SyntaxKind, usize)>,
    children: Vec<GreenElement>,
}

impl GreenNodeBuilder<'static, 'static> {
    /// Creates new builder with an empty [`NodeCache`].
    pub fn new() -> Self {
        Self {
            cache:    MaybeOwned::Owned(NodeCache::new()),
            parents:  Vec::with_capacity(8),
            children: Vec::with_capacity(8),
        }
    }
}

impl Default for GreenNodeBuilder<'static, 'static> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'cache, 'interner, I> GreenNodeBuilder<'cache, 'interner, I>
where
    I: Interner,
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

    /// Add new token to the current branch.
    #[inline]
    pub fn token(&mut self, kind: SyntaxKind, text: &str) {
        let token = self.cache.token(kind, text);
        self.children.push(token.into());
    }

    /// Start new node of the given `kind` and make it current.
    #[inline]
    pub fn start_node(&mut self, kind: SyntaxKind) {
        let len = self.children.len();
        self.parents.push((kind, len));
    }

    /// Finish the current branch and restore the previous branch as current.
    #[inline]
    pub fn finish_node(&mut self) {
        let (kind, first_child) = self.parents.pop().unwrap();
        let children = self.children.drain(first_child..);
        let node = self.cache.node(kind, children);
        self.children.push(node.into());
    }

    /// Prepare for maybe wrapping the next node with a surrounding node.
    ///
    /// The way wrapping works is that you first get a checkpoint, then you add nodes and tokens as
    /// normal, and then you *maybe* call [`start_node_at`](GreenNodeBuilder::start_node_at).
    ///
    /// # Examples
    /// ```
    /// # use cstree::{GreenNodeBuilder, SyntaxKind};
    /// # const PLUS: SyntaxKind = SyntaxKind(0);
    /// # const OPERATION: SyntaxKind = SyntaxKind(1);
    /// # struct Parser;
    /// # impl Parser {
    /// #     fn peek(&self) -> Option<SyntaxKind> { None }
    /// #     fn parse_expr(&mut self) {}
    /// # }
    /// # let mut builder = GreenNodeBuilder::new();
    /// # let mut parser = Parser;
    /// let checkpoint = builder.checkpoint();
    /// parser.parse_expr();
    /// if parser.peek() == Some(PLUS) {
    ///     // 1 + 2 = Add(1, 2)
    ///     builder.start_node_at(checkpoint, OPERATION);
    ///     parser.parse_expr();
    ///     builder.finish_node();
    /// }
    /// ```
    #[inline]
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint(self.children.len())
    }

    /// Wrap the previous branch marked by [`checkpoint`](GreenNodeBuilder::checkpoint) in a new
    /// branch and make it current.
    #[inline]
    pub fn start_node_at(&mut self, checkpoint: Checkpoint, kind: SyntaxKind) {
        let Checkpoint(checkpoint) = checkpoint;
        assert!(
            checkpoint <= self.children.len(),
            "checkpoint no longer valid, was finish_node called early?"
        );

        if let Some(&(_, first_child)) = self.parents.last() {
            assert!(
                checkpoint >= first_child,
                "checkpoint no longer valid, was an unmatched start_node_at called?"
            );
        }

        self.parents.push((kind, checkpoint));
    }

    /// Complete building the tree.
    ///
    /// Make sure that calls to [`start_node`](GreenNodeBuilder::start_node) /
    /// [`start_node_at`](GreenNodeBuilder::start_node_at) and
    /// [`finish_node`](GreenNodeBuilder::finish_node) are balanced, i.e. that every started node has
    /// been completed!
    ///
    /// If this builder was constructed with [`new`](GreenNodeBuilder::new), this method returns the
    /// interner used to deduplicate source text (strings) as its second return value to allow
    /// resolving tree tokens back to text and re-using the interner to build additonal trees.
    #[inline]
    pub fn finish(mut self) -> (GreenNode, Option<I>) {
        assert_eq!(self.children.len(), 1);
        let resolver = self.cache.into_owned().and_then(|cache| cache.interner.into_owned());
        match self.children.pop().unwrap() {
            NodeOrToken::Node(node) => (node, resolver),
            NodeOrToken::Token(_) => panic!("called `finish` on a `GreenNodeBuilder` which only contained a token"),
        }
    }
}
