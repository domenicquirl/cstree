use super::*;
#[cfg(feature = "serde1")]
use crate::serde_impls::{SerializeWithData, SerializeWithResolver};
use crate::{
    arc::Arc,
    green::{GreenElementRef, SyntaxKind},
    interning::Resolver,
    *,
};
use parking_lot::RwLock;
use std::{
    cell::UnsafeCell,
    fmt::Write,
    hash::{Hash, Hasher},
    iter, ptr,
    sync::{
        atomic::{AtomicU32, Ordering},
        Arc as StdArc,
    },
};

/// Inner syntax tree node.
/// Syntax nodes can be shared between threads.
/// Every syntax tree is reference counted as a whole and nodes are pointer-sized, so copying
/// individual nodes is relatively cheap.
#[repr(transparent)]
pub struct SyntaxNode<L: Language, D: 'static = ()> {
    data: *mut NodeData<L, D>,
}

unsafe impl<L: Language, D: 'static> Send for SyntaxNode<L, D> {}
unsafe impl<L: Language, D: 'static> Sync for SyntaxNode<L, D> {}

impl<L: Language, D> SyntaxNode<L, D> {
    #[allow(missing_docs)]
    pub fn debug<R>(&self, resolver: &R, recursive: bool) -> String
    where
        R: Resolver + ?Sized,
    {
        // NOTE: `fmt::Write` methods on `String` never fail
        let mut res = String::new();
        if recursive {
            let mut level = 0;
            for event in self.preorder_with_tokens() {
                match event {
                    WalkEvent::Enter(element) => {
                        for _ in 0..level {
                            write!(res, "  ").unwrap();
                        }
                        writeln!(
                            res,
                            "{}",
                            match element {
                                NodeOrToken::Node(node) => node.debug(resolver, false),
                                NodeOrToken::Token(token) => token.debug(resolver),
                            },
                        )
                        .unwrap();
                        level += 1;
                    }
                    WalkEvent::Leave(_) => level -= 1,
                }
            }
            assert_eq!(level, 0);
        } else {
            write!(res, "{:?}@{:?}", self.kind(), self.text_range()).unwrap();
        }
        res
    }

    #[allow(missing_docs)]
    pub fn display<R>(&self, resolver: &R) -> String
    where
        R: Resolver + ?Sized,
    {
        let mut res = String::new();
        self.preorder_with_tokens()
            .filter_map(|event| match event {
                WalkEvent::Enter(NodeOrToken::Token(token)) => Some(token),
                _ => None,
            })
            .try_for_each(|it| write!(res, "{}", it.display(resolver)))
            .unwrap();
        res
    }

    /// If there is a resolver associated with this tree, returns it.
    pub fn resolver(&self) -> Option<&StdArc<dyn Resolver>> {
        match &self.root().data().kind {
            Kind::Root(_, resolver) => resolver.as_ref(),
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn try_resolved(&self) -> Option<&ResolvedNode<L, D>> {
        // safety: we only coerce if `resolver` exists
        self.resolver().map(|_| unsafe { ResolvedNode::coerce_ref(self) })
    }

    #[inline]
    pub fn resolved(&self) -> &ResolvedNode<L, D> {
        self.try_resolved().expect("tried to resolve a node without resolver")
    }
}

impl<L: Language, D> Clone for SyntaxNode<L, D> {
    fn clone(&self) -> Self {
        // safety:: the ref count is only dropped when there are no more external references (see below)
        // since we are currently cloning such a reference, there is still at least one
        let ref_count = unsafe { &mut *self.data().ref_count };
        ref_count.fetch_add(1, Ordering::AcqRel);
        self.clone_uncounted()
    }
}

impl<L: Language, D> Drop for SyntaxNode<L, D> {
    fn drop(&mut self) {
        // safety:: the ref count is only dropped when there are no more external references (see below)
        // and all nodes but the root have been dropped.
        // if we are the last external reference, we have not yet dropped the ref count
        // if we aren't we won't enter the `if` below
        let ref_count = unsafe { &*self.data().ref_count };
        let refs = ref_count.fetch_sub(1, Ordering::AcqRel);
        if refs == 1 {
            // drop from parent
            // NOTE regarding drop orders: since `SyntaxNode<L>::drop` looks at the `ref_count`, we
            // need to first drop the `root` and only then its `root_data` and the contained
            // `ref_count`
            let root = self.root();
            let mut root = root.clone_uncounted();
            let ref_count = root.data().ref_count;
            root.drop_recursive();
            let root_data = root.data;
            drop(root);
            unsafe { drop(Box::from_raw(root_data)) };
            unsafe { drop(Box::from_raw(ref_count)) };
        }
    }
}

impl<L: Language, D> SyntaxNode<L, D> {
    #[inline]
    fn data(&self) -> &NodeData<L, D> {
        unsafe { &*self.data }
    }

    /// # Safety:
    /// Caller must ensure that the access to the underlying data is unique (no active _mutable or immutable_
    /// references).
    #[inline]
    #[allow(clippy::mut_from_ref)]
    unsafe fn data_mut(&self) -> &mut NodeData<L, D> {
        &mut *self.data
    }

    #[inline]
    pub(super) fn clone_uncounted(&self) -> Self {
        Self { data: self.data }
    }

    pub fn root(&self) -> &SyntaxNode<L, D> {
        let mut current = self;
        while let Some(parent) = current.parent() {
            current = parent;
        }
        current
    }

    fn drop_recursive(&mut self) {
        let data = self.data();
        for i in 0..data.children.len() {
            // safety: `child_locks` and `children` are pre-allocated to the same length
            let _write = unsafe { data.child_locks.get_unchecked(i).write() };
            // safety: protected by the write lock
            let slot = unsafe { &mut *data.children.get_unchecked(i).get() };
            let mut child_data = None;
            if let Some(NodeOrToken::Node(node)) = slot {
                // Tokens have no children that point to them, so if there are no external pointers
                // and the pointer from the parent is dropped they will be dropped.
                // Nodes may be pointed to by their children, hence we check them first.
                node.drop_recursive();
                child_data = Some(node.data);
            }
            // if the above `if let` was true, this drops `child`
            *slot = None;
            if let Some(data) = child_data {
                // the current `slot` contained a child, which was a node with `data`

                // safety: since there are no more `parent` pointers from the children of the
                // node this data belonged to, and we have just dropped the node, there are now
                // no more references to `data`
                let data = unsafe { Box::from_raw(data) };
                drop(data);
            }
        }
    }
}

// Identity semantics for hash & eq
impl<L: Language, D> PartialEq for SyntaxNode<L, D> {
    fn eq(&self, other: &SyntaxNode<L, D>) -> bool {
        self.data == other.data
    }
}

impl<L: Language, D> Eq for SyntaxNode<L, D> {}

impl<L: Language, D> Hash for SyntaxNode<L, D> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        ptr::hash(self.data, state);
    }
}

enum Kind<L: Language, D: 'static> {
    Root(GreenNode, Option<StdArc<dyn Resolver>>),
    Child {
        parent: SyntaxNode<L, D>,
        index:  u32,
        offset: TextSize,
    },
}

impl<L: Language, D> Kind<L, D> {
    fn as_child(&self) -> Option<(&SyntaxNode<L, D>, u32, TextSize)> {
        match self {
            Kind::Child { parent, index, offset } => Some((parent, *index, *offset)),
            _ => None,
        }
    }
}

pub(super) struct NodeData<L: Language, D: 'static> {
    kind:        Kind<L, D>,
    green:       ptr::NonNull<GreenNode>,
    ref_count:   *mut AtomicU32,
    data:        RwLock<Option<Arc<D>>>,
    children:    Vec<UnsafeCell<Option<SyntaxElement<L, D>>>>,
    child_locks: Vec<RwLock<()>>,
}

impl<L: Language, D> NodeData<L, D> {
    fn new(
        kind: Kind<L, D>,
        green: ptr::NonNull<GreenNode>,
        ref_count: *mut AtomicU32,
        n_children: usize,
    ) -> *mut Self {
        let mut children = Vec::with_capacity(n_children);
        let mut child_locks = Vec::with_capacity(n_children);
        children.extend((0..n_children).map(|_| Default::default()));
        child_locks.extend((0..n_children).map(|_| Default::default()));
        Box::into_raw(Box::new(Self {
            kind,
            green,
            ref_count,
            data: RwLock::default(),
            children,
            child_locks,
        }))
    }
}

impl<L: Language, D> SyntaxNode<L, D> {
    /// Build a new syntax tree on top of a green tree.
    ///
    /// # Example
    /// ```
    /// # use cstree::*;
    /// # #[allow(non_camel_case_types)]
    /// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// #[repr(u16)]
    /// enum SyntaxKind {
    ///     ROOT,
    /// }
    /// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// enum Lang {}
    /// impl cstree::Language for Lang {
    ///     // ...
    /// #     type Kind = SyntaxKind;
    /// #
    /// #     fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
    /// #         assert!(raw.0 <= SyntaxKind::ROOT as u16);
    /// #         unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    /// #     }
    /// #
    /// #     fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
    /// #         cstree::SyntaxKind(kind as u16)
    /// #     }
    /// }
    /// # let mut builder = GreenNodeBuilder::new();
    /// # builder.start_node(SyntaxKind(0));
    /// # builder.finish_node();
    /// # let (green, _) = builder.finish();
    /// let root: SyntaxNode<Lang> = SyntaxNode::new_root(green);
    /// assert_eq!(root.kind(), SyntaxKind::ROOT);
    /// ```
    #[inline]
    pub fn new_root(green: GreenNode) -> Self {
        Self::make_new_root(green, None)
    }

    pub(super) fn new(data: *mut NodeData<L, D>) -> Self {
        Self { data }
    }

    fn make_new_root(green: GreenNode, resolver: Option<StdArc<dyn Resolver>>) -> Self {
        let ref_count = Box::new(AtomicU32::new(1));
        let n_children = green.children().count();
        let data = NodeData::new(
            Kind::Root(green, resolver),
            ptr::NonNull::dangling(),
            Box::into_raw(ref_count),
            n_children,
        );
        let ret = Self::new(data);
        let green: ptr::NonNull<GreenNode> = match &ret.data().kind {
            Kind::Root(green, _resolver) => green.into(),
            _ => unreachable!(),
        };
        // safety: we have just created `ret` and have not shared it
        unsafe { ret.data_mut() }.green = green;
        ret
    }

    /// Build a new syntax tree on top of a green tree and associate a resolver with the tree to
    /// resolve interned Strings.
    ///
    /// # Example
    /// ```
    /// # use cstree::*;
    /// # #[allow(non_camel_case_types)]
    /// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// #[repr(u16)]
    /// enum SyntaxKind {
    ///     TOKEN,
    ///     ROOT,
    /// }
    /// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// enum Lang {}
    /// impl cstree::Language for Lang {
    ///     // ...
    /// #     type Kind = SyntaxKind;
    /// #
    /// #     fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
    /// #         assert!(raw.0 <= SyntaxKind::ROOT as u16);
    /// #         unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    /// #     }
    /// #
    /// #     fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
    /// #         cstree::SyntaxKind(kind as u16)
    /// #     }
    /// }
    /// # const ROOT: cstree::SyntaxKind = cstree::SyntaxKind(0);
    /// # const TOKEN: cstree::SyntaxKind = cstree::SyntaxKind(1);
    /// # type SyntaxNode<L> = cstree::SyntaxNode<L, ()>;
    /// let mut builder = GreenNodeBuilder::new();
    /// builder.start_node(ROOT);
    /// builder.token(TOKEN, "content");
    /// builder.finish_node();
    /// let (green, resolver) = builder.finish();
    /// let root: ResolvedNode<Lang> = SyntaxNode::new_root_with_resolver(green, resolver.unwrap());
    /// assert_eq!(root.text(), "content");
    /// ```
    #[inline]
    pub fn new_root_with_resolver(green: GreenNode, resolver: impl Resolver + 'static) -> ResolvedNode<L, D> {
        let ptr: StdArc<dyn Resolver> = StdArc::new(resolver);
        ResolvedNode {
            syntax: SyntaxNode::make_new_root(green, Some(ptr)),
        }
    }

    // Technically, unsafe, but private so that's OK.
    // Safety: `green` must be a descendent of `parent.green`
    pub(super) fn new_child(
        green: &GreenNode,
        parent: &Self,
        index: u32,
        offset: TextSize,
        ref_count: *mut AtomicU32,
    ) -> Self {
        let n_children = green.children().count();
        let data = NodeData::new(
            Kind::Child {
                parent: parent.clone_uncounted(),
                index,
                offset,
            },
            green.into(),
            ref_count,
            n_children,
        );
        Self::new(data)
    }

    /// Stores custom data for this node.
    /// If there was previous data associated with this node, it will be replaced.
    pub fn set_data(&self, data: D) -> Arc<D> {
        let mut ptr = self.data().data.write();
        let data = Arc::new(data);
        *ptr = Some(Arc::clone(&data));
        data
    }

    /// Stores custom data for this node, but only if no data was previously set.
    /// If it was, the given data is returned unchanged.
    pub fn try_set_data(&self, data: D) -> Result<Arc<D>, D> {
        let mut ptr = self.data().data.write();
        if ptr.is_some() {
            return Err(data);
        }
        let data = Arc::new(data);
        *ptr = Some(Arc::clone(&data));
        Ok(data)
    }

    /// Returns the data associated with this node, if any.
    pub fn get_data(&self) -> Option<Arc<D>> {
        let ptr = self.data().data.read();
        (*ptr).as_ref().map(|ptr| Arc::clone(ptr))
    }

    /// Removes the data associated with this node.
    pub fn clear_data(&self) {
        let mut ptr = self.data().data.write();
        *ptr = None;
    }

    #[inline]
    fn read(&self, index: usize) -> Option<SyntaxElementRef<'_, L, D>> {
        // safety: children are pre-allocated and indices are determined internally
        let _read = unsafe { self.data().child_locks.get_unchecked(index).read() };
        // safety: mutable accesses to the slot only occur below and have to take the lock
        let slot = unsafe { &*self.data().children.get_unchecked(index).get() };
        slot.as_ref().map(|elem| elem.into())
    }

    fn try_write(&self, index: usize, elem: SyntaxElement<L, D>) {
        // safety: children are pre-allocated and indices are determined internally
        let _write = unsafe { self.data().child_locks.get_unchecked(index).write() };
        // safety: we are the only writer and there are no readers as evidenced by the write lock
        let slot = unsafe { &mut *self.data().children.get_unchecked(index).get() };
        if slot.is_none() {
            // we are first to initialize the child
            *slot = Some(elem);
        } else {
            // another thread got the write lock first and already initialized it
            match elem {
                SyntaxElement::Node(node) => {
                    // There are three things to handle here:
                    //   1) `node` was just created, which allocated `NodeData` that we now need to
                    //      drop, and
                    //   2) dropping `node` will decrement the global `ref_count`, even though the
                    //      count was not incremented when creating `node` (because it is an
                    //      internal reference). Thus, we need to bump the count up by one.
                    //   3) dropping `node`'s `NodeData` will drop its `parent` reference, which
                    //      will again decrement the `ref_count`. Thus, we have to offset by 2
                    //      overall.

                    // safety: `node` was just created and has not been shared
                    let ref_count = unsafe { &*node.data().ref_count };
                    ref_count.fetch_add(2, Ordering::AcqRel);
                    let node_data = node.data;
                    drop(node);
                    unsafe { drop(Box::from_raw(node_data)) };
                }
                SyntaxElement::Token(token) => {
                    // We don't have to worry about `NodeData` or `SyntaxToken<L>`'s own `Drop` here,
                    // but we will still drop `token`'s `parent`, which decreases the `ref_count`
                    // by one.

                    // safety: as above
                    let ref_count = unsafe { &*token.parent().data().ref_count };
                    ref_count.fetch_add(1, Ordering::AcqRel);
                    drop(token);
                }
            }
        }
    }

    #[inline(always)]
    fn get_or_add_node(&self, node: &GreenNode, index: usize, offset: TextSize) -> SyntaxElementRef<'_, L, D> {
        if let Some(elem) = self.read(index) {
            debug_assert_eq!(elem.text_range().start(), offset);
            return elem;
        }
        self.try_write(
            index,
            Self::new_child(node, self, index as u32, offset, self.data().ref_count).into(),
        );
        self.read(index).unwrap()
    }

    #[inline(always)]
    fn get_or_add_element(
        &self,
        element: GreenElementRef<'_>,
        index: usize,
        offset: TextSize,
    ) -> SyntaxElementRef<'_, L, D> {
        if let Some(elem) = self.read(index) {
            debug_assert_eq!(elem.text_range().start(), offset);
            return elem;
        }
        self.try_write(
            index,
            SyntaxElement::new(element, self, index as u32, offset, self.data().ref_count),
        );
        self.read(index).unwrap()
    }

    /// Returns a green tree, equal to the green tree this node
    /// belongs two, except with this node substitute. The complexity
    /// of operation is proportional to the depth of the tree
    pub fn replace_with(&self, replacement: GreenNode) -> GreenNode {
        assert_eq!(self.syntax_kind(), replacement.kind());
        match self.data().kind.as_child() {
            None => replacement, // `None` means `self` is the root
            Some((parent, me, _offset)) => {
                let mut replacement = Some(replacement);
                let children = parent.green().children().enumerate().map(|(i, child)| {
                    if i as u32 == me {
                        replacement.take().unwrap().into()
                    } else {
                        child.cloned()
                    }
                });
                let new_parent = GreenNode::new(parent.syntax_kind(), children);
                parent.replace_with(new_parent)
            }
        }
    }

    /// The internal representation of the kind of this node.
    #[inline]
    pub fn syntax_kind(&self) -> SyntaxKind {
        self.green().kind()
    }

    /// The kind of this node in terms of your language.
    #[inline]
    pub fn kind(&self) -> L::Kind {
        L::kind_from_raw(self.syntax_kind())
    }

    /// The range this node covers in the source text, in bytes.
    #[inline]
    pub fn text_range(&self) -> TextRange {
        let offset = match self.data().kind.as_child() {
            Some((_, _, it)) => it,
            _ => 0.into(),
        };
        TextRange::at(offset, self.green().text_len())
    }

    /// Uses the provided resolver to return an efficient representation of all source text covered
    /// by this node, i.e. the combined text of all token leafs of the subtree originating in this
    /// node.
    #[inline]
    pub fn resolve_text<'n, 'i, I>(&'n self, resolver: &'i I) -> SyntaxText<'n, 'i, I, L, D>
    where
        I: Resolver + ?Sized,
    {
        SyntaxText::new(self, resolver)
    }

    /// Returns the unterlying green tree node of this node.
    #[inline]
    pub fn green(&self) -> &GreenNode {
        unsafe { self.data().green.as_ref() }
    }

    /// The parent node of this node, except if this node is the root.
    #[inline]
    pub fn parent(&self) -> Option<&SyntaxNode<L, D>> {
        match &self.data().kind {
            Kind::Root(_, _) => None,
            Kind::Child { parent, .. } => Some(parent),
        }
    }

    /// The number of child nodes (!) of this node.
    ///
    /// If you want to also consider leafs, see [`arity_with_tokens`](SyntaxNode::arity_with_tokens).
    #[inline]
    pub fn arity(&self) -> usize {
        self.green().iter().filter(|&child| child.is_node()).count()
    }

    /// The number of children of this node.
    #[inline]
    pub fn arity_with_tokens(&self) -> usize {
        self.data().children.len()
    }

    /// Returns an iterator along the chain of parents of this node.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<L, D>> {
        iter::successors(Some(self), |&node| node.parent())
    }

    /// Returns an iterator over all nodes that are children of this node.
    ///
    /// If you want to also consider leafs, see [`children_with_tokens`](SyntaxNode::children_with_tokens).
    #[inline]
    pub fn children(&self) -> SyntaxNodeChildren<'_, L, D> {
        SyntaxNodeChildren::new(self)
    }

    /// Returns an iterator over child elements of this node, including tokens.
    #[inline]
    pub fn children_with_tokens(&self) -> SyntaxElementChildren<'_, L, D> {
        SyntaxElementChildren::new(self)
    }

    /// The first child node of this node, if any.
    ///
    /// If you want to also consider leafs, see [`first_child_or_token`](SyntaxNode::first_child_or_token).
    #[inline]
    #[allow(clippy::map_clone)]
    pub fn first_child(&self) -> Option<&SyntaxNode<L, D>> {
        let (node, (index, offset)) = filter_nodes(self.green().children_from(0, self.text_range().start())).next()?;
        self.get_or_add_node(node, index, offset).as_node().map(|node| *node)
    }

    /// The first child element of this node, if any, including tokens.
    #[inline]
    pub fn first_child_or_token(&self) -> Option<SyntaxElementRef<'_, L, D>> {
        let (element, (index, offset)) = self.green().children_from(0, self.text_range().start()).next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    /// The last child node of this node, if any.
    ///
    /// If you want to also consider leafs, see [`last_child_or_token`](SyntaxNode::last_child_or_token).
    #[inline]
    #[allow(clippy::map_clone)]
    pub fn last_child(&self) -> Option<&SyntaxNode<L, D>> {
        let (node, (index, offset)) = filter_nodes(
            self.green()
                .children_to(self.green().children().len(), self.text_range().end()),
        )
        .next()?;
        self.get_or_add_node(node, index, offset).as_node().map(|node| *node)
    }

    /// The last child element of this node, if any, including tokens.
    #[inline]
    pub fn last_child_or_token(&self) -> Option<SyntaxElementRef<'_, L, D>> {
        let (element, (index, offset)) = self
            .green()
            .children_to(self.green().children().len(), self.text_range().end())
            .next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    /// The first child node of this node starting at the (n + 1)-st, if any.
    /// Note that even if this method returns `Some`, the contained node may not actually be the (n +
    /// 1)-st child, but the next child from there that is a node.
    ///
    /// If you want to also consider leafs, see [`next_child_or_token_after`](SyntaxNode::next_child_or_token_after).
    #[inline]
    pub fn next_child_after(&self, n: usize, offset: TextSize) -> Option<&SyntaxNode<L, D>> {
        let (node, (index, offset)) = filter_nodes(self.green().children_from(n + 1, offset)).next()?;
        self.get_or_add_node(node, index, offset).as_node().copied()
    }

    /// The first child element of this node starting at the (n + 1)-st, if any.
    /// If this method returns `Some`, the contained node is the (n + 1)-st child of this node.
    #[inline]
    pub fn next_child_or_token_after(&self, n: usize, offset: TextSize) -> Option<SyntaxElementRef<'_, L, D>> {
        let (element, (index, offset)) = self.green().children_from(n + 1, offset).next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    /// The last child node of this node up to the nth, if any.
    /// Note that even if this method returns `Some`, the contained node may not actually be the (n -
    /// 1)-st child, but the previous child from there that is a node.
    ///
    /// If you want to also consider leafs, see [`prev_child_or_token_before`](SyntaxNode::prev_child_or_token_before).
    #[inline]
    pub fn prev_child_before(&self, n: usize, offset: TextSize) -> Option<&SyntaxNode<L, D>> {
        let (node, (index, offset)) = filter_nodes(self.green().children_to(n, offset)).next()?;
        self.get_or_add_node(node, index, offset).as_node().copied()
    }

    /// The last child node of this node up to the nth, if any.
    /// If this method returns `Some`, the contained node is the (n - 1)-st child.
    #[inline]
    pub fn prev_child_or_token_before(&self, n: usize, offset: TextSize) -> Option<SyntaxElementRef<'_, L, D>> {
        let (element, (index, offset)) = self.green().children_to(n, offset).next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    /// The node to the right of this one, i.e. the next child node (!) of this node's parent after this node.
    ///
    /// If you want to also consider leafs, see [`next_sibling_or_token`](SyntaxNode::next_sibling_or_token).
    #[inline]
    pub fn next_sibling(&self) -> Option<&SyntaxNode<L, D>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (node, (index, offset)) = filter_nodes(
            parent
                .green()
                .children_from((index + 1) as usize, self.text_range().end()),
        )
        .next()?;
        parent.get_or_add_node(node, index, offset).as_node().copied()
    }

    /// The tree element to the right of this one, i.e. the next child of this node's parent after this node.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (element, (index, offset)) = parent
            .green()
            .children_from((index + 1) as usize, self.text_range().end())
            .next()?;
        Some(parent.get_or_add_element(element, index, offset))
    }

    /// The node to the left of this one, i.e. the previous child node (!) of this node's parent before this node.
    ///
    /// If you want to also consider leafs, see [`prev_sibling_or_token`](SyntaxNode::prev_sibling_or_token).
    #[inline]
    pub fn prev_sibling(&self) -> Option<&SyntaxNode<L, D>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (node, (index, offset)) =
            filter_nodes(parent.green().children_to(index as usize, self.text_range().start())).next()?;
        parent.get_or_add_node(node, index, offset).as_node().copied()
    }

    /// The tree element to the left of this one, i.e. the previous child of this node's parent before this node.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (element, (index, offset)) = parent
            .green()
            .children_to(index as usize, self.text_range().start())
            .next()?;
        Some(parent.get_or_add_element(element, index, offset))
    }

    /// Return the leftmost token in the subtree of this node
    #[inline]
    pub fn first_token(&self) -> Option<&SyntaxToken<L, D>> {
        self.first_child_or_token()?.first_token()
    }

    /// Return the rightmost token in the subtree of this node
    #[inline]
    pub fn last_token(&self) -> Option<&SyntaxToken<L, D>> {
        self.last_child_or_token()?.last_token()
    }

    /// Returns an iterator over all sibling nodes of this node in the given `direction`, i.e. all of
    /// this node's parent's child nodes (!) from this node on to the left or the right. The first
    /// item in the iterator will always be this node.
    ///
    /// If you want to also consider leafs, see [`siblings_with_tokens`](SyntaxNode::siblings_with_tokens).
    #[inline]
    pub fn siblings(&self, direction: Direction) -> impl Iterator<Item = &SyntaxNode<L, D>> {
        iter::successors(Some(self), move |node| match direction {
            Direction::Next => node.next_sibling(),
            Direction::Prev => node.prev_sibling(),
        })
    }

    /// Returns an iterator over all siblings of this node in the given `direction`, i.e. all of this
    /// node's parent's children from this node on to the left or the right.
    /// The first item in the iterator will always be this node.
    #[inline]
    pub fn siblings_with_tokens(&self, direction: Direction) -> impl Iterator<Item = SyntaxElementRef<'_, L, D>> {
        let me: SyntaxElementRef<'_, L, D> = self.into();
        iter::successors(Some(me), move |el| match direction {
            Direction::Next => el.next_sibling_or_token(),
            Direction::Prev => el.prev_sibling_or_token(),
        })
    }

    /// Returns an iterator over all nodes (!) in the subtree starting at this node, including this node.
    ///
    /// If you want to also consider leafs, see [`descendants_with_tokens`](SyntaxNode::descendants_with_tokens).
    #[inline]
    pub fn descendants(&self) -> impl Iterator<Item = &SyntaxNode<L, D>> {
        self.preorder().filter_map(|event| match event {
            WalkEvent::Enter(node) => Some(node),
            WalkEvent::Leave(_) => None,
        })
    }

    /// Returns an iterator over all elements in the subtree starting at this node, including this node.
    #[inline]
    pub fn descendants_with_tokens(&self) -> impl Iterator<Item = SyntaxElementRef<'_, L, D>> {
        self.preorder_with_tokens().filter_map(|event| match event {
            WalkEvent::Enter(it) => Some(it),
            WalkEvent::Leave(_) => None,
        })
    }

    /// Traverse the subtree rooted at the current node (including the current
    /// node) in preorder, excluding tokens.
    #[inline(always)]
    pub fn preorder(&self) -> impl Iterator<Item = WalkEvent<&SyntaxNode<L, D>>> {
        iter::successors(Some(WalkEvent::Enter(self)), move |pos| {
            let next = match pos {
                WalkEvent::Enter(node) => match node.first_child() {
                    Some(child) => WalkEvent::Enter(child),
                    None => WalkEvent::Leave(*node),
                },
                WalkEvent::Leave(node) => {
                    if node == &self {
                        return None;
                    }
                    match node.next_sibling() {
                        Some(sibling) => WalkEvent::Enter(sibling),
                        None => WalkEvent::Leave(node.parent().unwrap()),
                    }
                }
            };
            Some(next)
        })
    }

    /// Traverse the subtree rooted at the current node (including the current
    /// node) in preorder, including tokens.
    #[inline(always)]
    pub fn preorder_with_tokens(&self) -> impl Iterator<Item = WalkEvent<SyntaxElementRef<'_, L, D>>> {
        let me = self.into();
        iter::successors(Some(WalkEvent::Enter(me)), move |pos| {
            let next = match pos {
                WalkEvent::Enter(el) => match el {
                    NodeOrToken::Node(node) => match node.first_child_or_token() {
                        Some(child) => WalkEvent::Enter(child),
                        None => WalkEvent::Leave((*node).into()),
                    },
                    NodeOrToken::Token(token) => WalkEvent::Leave((*token).into()),
                },
                WalkEvent::Leave(el) => {
                    if el == &me {
                        return None;
                    }
                    match el.next_sibling_or_token() {
                        Some(sibling) => WalkEvent::Enter(sibling),
                        None => WalkEvent::Leave(el.parent().unwrap().into()),
                    }
                }
            };
            Some(next)
        })
    }

    /// Find a token in the subtree corresponding to this node, which covers the offset.
    /// Precondition: offset must be withing node's range.
    pub fn token_at_offset(&self, offset: TextSize) -> TokenAtOffset<SyntaxToken<L, D>> {
        // TODO: this could be faster if we first drill-down to node, and only
        // then switch to token search. We should also replace explicit
        // recursion with a loop.
        let range = self.text_range();
        assert!(
            range.start() <= offset && offset <= range.end(),
            "Bad offset: range {:?} offset {:?}",
            range,
            offset
        );
        if range.is_empty() {
            return TokenAtOffset::None;
        }

        let mut children = self.children_with_tokens().filter(|child| {
            let child_range = child.text_range();
            !child_range.is_empty() && (child_range.start() <= offset && offset <= child_range.end())
        });

        let left = children.next().unwrap();
        let right = children.next();
        assert!(children.next().is_none());

        if let Some(right) = right {
            match (left.token_at_offset(offset), right.token_at_offset(offset)) {
                (TokenAtOffset::Single(left), TokenAtOffset::Single(right)) => TokenAtOffset::Between(left, right),
                _ => unreachable!(),
            }
        } else {
            left.token_at_offset(offset)
        }
    }

    /// Return the deepest node or token in the current subtree that fully
    /// contains the range. If the range is empty and is contained in two leaf
    /// nodes, either one can be returned. Precondition: range must be contained
    /// withing the current node
    pub fn covering_element(&self, range: TextRange) -> SyntaxElementRef<'_, L, D> {
        let mut res: SyntaxElementRef<'_, L, D> = self.into();
        loop {
            assert!(
                res.text_range().contains_range(range),
                "Bad range: node range {:?}, range {:?}",
                res.text_range(),
                range,
            );
            res = match &res {
                NodeOrToken::Token(_) => return res,
                NodeOrToken::Node(node) => {
                    match node
                        .children_with_tokens()
                        .find(|child| child.text_range().contains_range(range))
                    {
                        Some(child) => child,
                        None => return res,
                    }
                }
            };
        }
    }
}

#[cfg(feature = "serde1")]
impl<L, D> SyntaxNode<L, D>
where
    L: Language,
{
    /// Return an anonymous object that can be used to serialize this node,
    /// including the data and by using an external resolver.
    pub fn as_serialize_with_data_with_resolver<'node>(
        &'node self,
        resolver: &'node impl Resolver,
    ) -> impl serde::Serialize + 'node
    where
        D: serde::Serialize,
    {
        SerializeWithData { node: self, resolver }
    }

    /// Return an anonymous object that can be used to serialize this node,
    /// which uses the given resolver instead of the resolver inside the tree.
    pub fn as_serialize_with_resolver<'node>(
        &'node self,
        resolver: &'node impl Resolver,
    ) -> impl serde::Serialize + 'node {
        SerializeWithResolver { node: self, resolver }
    }
}

#[derive(Clone, Debug)]
struct Iter<'n> {
    green:  Children<'n>,
    offset: TextSize,
    index:  usize,
}

impl<'n> Iter<'n> {
    fn new<L: Language, D>(parent: &'n SyntaxNode<L, D>) -> Self {
        let offset = parent.text_range().start();
        let green: Children<'_> = parent.green().children();
        Iter {
            green,
            offset,
            index: 0,
        }
    }

    #[inline(always)]
    fn next(&mut self) -> Option<(GreenElementRef, usize, TextSize)> {
        self.green.next().map(|element| {
            let offset = self.offset;
            let index = self.index;
            self.offset += element.text_len();
            self.index += 1;
            (element, index, offset)
        })
    }
}

/// An iterator over the child nodes of a [`SyntaxNode`].
#[derive(Clone)]
pub struct SyntaxNodeChildren<'n, L: Language, D: 'static = ()> {
    inner:  Iter<'n>,
    parent: &'n SyntaxNode<L, D>,
}

impl<'n, L: Language, D> SyntaxNodeChildren<'n, L, D> {
    #[inline]
    fn new(parent: &'n SyntaxNode<L, D>) -> Self {
        Self {
            inner: Iter::new(parent),
            parent,
        }
    }
}

impl<'n, L: Language, D> Iterator for SyntaxNodeChildren<'n, L, D> {
    type Item = &'n SyntaxNode<L, D>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((element, index, offset)) = self.inner.next() {
            if let Some(&node) = element.as_node() {
                return Some(self.parent.get_or_add_node(node, index, offset).as_node().unwrap());
            }
        }
        None
    }
}

/// An iterator over the children of a [`SyntaxNode`].
#[derive(Clone)]
pub struct SyntaxElementChildren<'n, L: Language, D: 'static = ()> {
    inner:  Iter<'n>,
    parent: &'n SyntaxNode<L, D>,
}

impl<'n, L: Language, D> SyntaxElementChildren<'n, L, D> {
    #[inline]
    fn new(parent: &'n SyntaxNode<L, D>) -> Self {
        Self {
            inner: Iter::new(parent),
            parent,
        }
    }
}

impl<'n, L: Language, D> Iterator for SyntaxElementChildren<'n, L, D> {
    type Item = SyntaxElementRef<'n, L, D>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let parent = self.parent;
        self.inner
            .next()
            .map(|(green, index, offset)| parent.get_or_add_element(green, index, offset))
    }
}

impl GreenNode {
    #[inline(always)]
    fn children_from(
        &self,
        start_index: usize,
        mut offset: TextSize,
    ) -> impl Iterator<Item = (GreenElementRef, (usize, TextSize))> {
        self.children()
            .skip(start_index)
            .enumerate()
            .map(move |(index, element)| {
                let element_offset = offset;
                offset += element.text_len();
                (element, (start_index + index, element_offset))
            })
    }

    #[inline(always)]
    fn children_to(
        &self,
        end_index: usize,
        mut offset: TextSize,
    ) -> impl Iterator<Item = (GreenElementRef, (usize, TextSize))> {
        self.children()
            .take(end_index)
            .rev()
            .enumerate()
            .map(move |(index, element)| {
                offset -= element.text_len();
                (element, (end_index - index - 1, offset))
            })
    }
}

#[inline(always)]
fn filter_nodes<'a, I: Iterator<Item = (GreenElementRef<'a>, T)>, T>(
    iter: I,
) -> impl Iterator<Item = (&'a GreenNode, T)> {
    iter.filter_map(|(element, data)| match element {
        NodeOrToken::Node(it) => Some((it, data)),
        NodeOrToken::Token(_) => None,
    })
}
