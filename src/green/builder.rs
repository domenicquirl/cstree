use std::{convert::TryFrom, num::NonZeroUsize};

use fxhash::{FxBuildHasher, FxHashMap};
use lasso::{Capacity, Rodeo, Spur};
use text_size::TextSize;

use crate::{
    green::{GreenElement, GreenNode, GreenToken, SyntaxKind},
    interning::Interner,
    NodeOrToken,
};

use super::{node::GreenNodeHead, token::GreenTokenData};

#[derive(Debug)]
pub struct NodeCache {
    nodes: FxHashMap<GreenNodeHead, GreenNode>,
    tokens: FxHashMap<GreenTokenData, GreenToken>,
    interner: Rodeo<Spur, FxBuildHasher>,
}

impl NodeCache {
    pub fn new() -> Self {
        Self {
            nodes: FxHashMap::default(),
            tokens: FxHashMap::default(),
            interner: Rodeo::with_capacity_and_hasher(
                // capacity values suggested by author of `lasso`
                Capacity::new(512, unsafe { NonZeroUsize::new_unchecked(4096) }),
                FxBuildHasher::default(),
            ),
        }
    }

    fn node<I>(&mut self, kind: SyntaxKind, children: I) -> GreenNode
    where
        I: IntoIterator<Item = GreenElement>,
        I::IntoIter: ExactSizeIterator,
    {
        let children = children.into_iter();
        // Green nodes are fully immutable, so it's ok to deduplicate them.
        // This is the same optimization that Roslyn does
        // https://github.com/KirillOsenkov/Bliki/wiki/Roslyn-Immutable-Trees
        //
        // For example, all `#[inline]` in this file share the same green node!
        // For `libsyntax/parse/parser.rs`, measurements show that deduping saves
        // 17% of the memory for green nodes!
        if children.len() <= 3 {
            #[derive(Clone)]
            struct ChildrenIter {
                data: [Option<GreenElement>; 3],
                idx: usize,
                len: usize,
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

            let mut data: [Option<GreenElement>; 3] = [None, None, None];
            let mut count = 0;

            for child in children {
                data[count] = Some(child);
                count += 1;
            }
            let children = ChildrenIter {
                data,
                idx: 0,
                len: count,
            };

            let head = GreenNodeHead::from_child_iter(kind, children.clone());
            self.nodes
                .entry(head.clone())
                .or_insert_with(|| GreenNode::from_head_and_children(head, children))
                .clone()
        } else {
            GreenNode::new(kind, children)
        }
    }

    fn token(&mut self, kind: SyntaxKind, text: &str) -> GreenToken {
        let text_len = TextSize::try_from(text.len()).unwrap();
        let text = self.interner.get_or_intern(text);
        let data = GreenTokenData { kind, text, text_len };
        self.tokens
            .entry(data.clone())
            .or_insert_with(|| GreenToken::new(data))
            .clone()
    }
}

#[derive(Debug)]
enum MaybeOwned<'a, T> {
    Owned(T),
    Borrowed(&'a mut T),
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

/// A checkpoint for maybe wrapping a node. See `GreenNodeBuilder::checkpoint` for details.
#[derive(Clone, Copy, Debug)]
pub struct Checkpoint(usize);

/// A builder for a green tree.
#[derive(Debug)]
pub struct GreenNodeBuilder<'cache> {
    cache: MaybeOwned<'cache, NodeCache>,
    parents: Vec<(SyntaxKind, usize)>,
    children: Vec<GreenElement>,
}

impl GreenNodeBuilder<'_> {
    /// Creates new builder.
    pub fn new() -> GreenNodeBuilder<'static> {
        GreenNodeBuilder {
            cache: MaybeOwned::Owned(NodeCache::new()),
            parents: Vec::with_capacity(8),
            children: Vec::with_capacity(8),
        }
    }

    /// Reusing `NodeCache` between different `GreenNodeBuilder`s saves memory.
    /// It allows to structurally share underlying trees.
    pub fn with_cache(cache: &mut NodeCache) -> GreenNodeBuilder<'_> {
        GreenNodeBuilder {
            cache: MaybeOwned::Borrowed(cache),
            parents: Vec::with_capacity(8),
            children: Vec::with_capacity(8),
        }
    }

    /// Adds new token to the current branch.
    #[inline]
    pub fn token(&mut self, kind: SyntaxKind, text: &str) {
        let token = self.cache.token(kind, text);
        self.children.push(token.into());
    }

    /// Start new node and make it current.
    #[inline]
    pub fn start_node(&mut self, kind: SyntaxKind) {
        let len = self.children.len();
        self.parents.push((kind, len));
    }

    /// Finish current branch and restore previous
    /// branch as current.
    #[inline]
    pub fn finish_node(&mut self) {
        let (kind, first_child) = self.parents.pop().unwrap();
        let children = self.children.drain(first_child..);
        let node = self.cache.node(kind, children);
        self.children.push(node.into());
    }

    /// Prepare for maybe wrapping the next node.
    /// The way wrapping works is that you first of all get a checkpoint,
    /// then you place all tokens you want to wrap, and then *maybe* call
    /// `start_node_at`.
    /// Example:
    /// ```rust
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

    /// Wrap the previous branch marked by `checkpoint` in a new branch and
    /// make it current.
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

    /// Complete tree building. Make sure that
    /// `start_node_at` and `finish_node` calls
    /// are paired!
    #[inline]
    pub fn finish(mut self) -> (GreenNode, Option<impl Interner<Spur>>) {
        assert_eq!(self.children.len(), 1);
        let resolver = match self.cache {
            MaybeOwned::Owned(cache) => Some(cache.interner),
            MaybeOwned::Borrowed(_) => None,
        };
        match self.children.pop().unwrap() {
            NodeOrToken::Node(node) => (node, resolver),
            NodeOrToken::Token(_) => panic!(),
        }
    }
}
