use std::{
    cell::UnsafeCell,
    fmt::{self, Write},
    hash::{Hash, Hasher},
    iter, ptr,
    sync::atomic::{AtomicU32, Ordering},
};

#[cfg(feature = "serde1")]
use crate::serde_impls::{SerializeWithData, SerializeWithResolver};
use parking_lot::RwLock;
use servo_arc::Arc;

use crate::{
    green::{GreenElementRef, SyntaxKind},
    interning::Resolver,
    Children, Direction, GreenNode, GreenToken, Language, NodeOrToken, SyntaxText, TextRange, TextSize, TokenAtOffset,
    WalkEvent,
};

// A note on `#[inline]` usage in this file:
// In `rowan`, there are two layers of `SyntaxXY`s: the `cursor` layer and the `api` layer.
// The `cursor` layer handles all of the actual methods on the tree, while the `api` layer is
// generic over the `Language` of the tree and otherwise forwards its implementation to the `cursor`
// layer.
// Here, we have unified the `cursor` and the `api` layer into the `syntax` layer.
// This means that all of our types here are generic over a `Language`, including the
// implementations which, in `rowan`, are part of the `cursor` layer.
// Very apparently, this makes the compiler less willing to inline. Almost every "regular use"
// method in this file has some kind of `#[inline]` annotation to counteract that. This is _NOT_
// just for fun, not inlining decreases tree traversal speed by approx. 50% at the time of writing
// this.
//
//   - DQ 01/2021

#[repr(transparent)]
pub struct SyntaxNode<L: Language, D: 'static = (), R: 'static = ()> {
    data: *mut NodeData<L, D, R>,
}

unsafe impl<L: Language, D: 'static, R: 'static> Send for SyntaxNode<L, D, R> {}
unsafe impl<L: Language, D: 'static, R: 'static> Sync for SyntaxNode<L, D, R> {}

impl<L: Language, D, R> SyntaxNode<L, D, R> {
    pub fn debug(&self, resolver: &impl Resolver, recursive: bool) -> String {
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

    pub fn display(&self, resolver: &impl Resolver) -> String {
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
}

impl<L: Language, D, R> Clone for SyntaxNode<L, D, R> {
    fn clone(&self) -> Self {
        // safety:: the ref count is only dropped when there are no more external references (see below)
        // since we are currently cloning such a reference, there is still at least one
        let ref_count = unsafe { &mut *self.data().ref_count };
        ref_count.fetch_add(1, Ordering::AcqRel);
        self.clone_uncounted()
    }
}

impl<L: Language, D, R> Drop for SyntaxNode<L, D, R> {
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

impl<L: Language, D, R> SyntaxNode<L, D, R> {
    #[inline]
    fn data(&self) -> &NodeData<L, D, R> {
        unsafe { &*self.data }
    }

    /// # Safety:
    /// Caller must ensure that the access to the underlying data is unique (no active _mutable or immutable_
    /// references).
    #[inline]
    #[allow(clippy::mut_from_ref)]
    unsafe fn data_mut(&self) -> &mut NodeData<L, D, R> {
        &mut *self.data
    }

    #[inline]
    fn clone_uncounted(&self) -> Self {
        Self { data: self.data }
    }

    fn root(&self) -> &SyntaxNode<L, D, R> {
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
            if let Some(child) = slot {
                // Tokens have no children that point to them, so if there are no external pointers
                // and the pointer from the parent is dropped they will be dropped.
                // Nodes may be pointed to by their children, hence we check them first.
                if let NodeOrToken::Node(node) = child {
                    node.drop_recursive();
                    child_data = Some(node.data);
                }
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
impl<L: Language, D, R> PartialEq for SyntaxNode<L, D, R> {
    fn eq(&self, other: &SyntaxNode<L, D, R>) -> bool {
        self.green().ptr() == other.green().ptr() && self.text_range().start() == other.text_range().start()
    }
}

impl<L: Language, D, R> Eq for SyntaxNode<L, D, R> {}

impl<L: Language, D, R> Hash for SyntaxNode<L, D, R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        ptr::hash(self.green().ptr(), state);
        self.text_range().start().hash(state);
    }
}

pub struct SyntaxToken<L: Language, D: 'static = (), R: 'static = ()> {
    parent: SyntaxNode<L, D, R>,
    index:  u32,
    offset: TextSize,
}

impl<L: Language, D, R> Clone for SyntaxToken<L, D, R> {
    fn clone(&self) -> Self {
        Self {
            parent: self.parent.clone(),
            index:  self.index,
            offset: self.offset,
        }
    }
}

impl<L: Language, D, R> Hash for SyntaxToken<L, D, R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.parent.hash(state);
        self.index.hash(state);
        self.offset.hash(state);
    }
}

impl<L: Language, D, R> PartialEq for SyntaxToken<L, D, R> {
    fn eq(&self, other: &SyntaxToken<L, D, R>) -> bool {
        self.parent == other.parent && self.index == other.index && self.offset == other.offset
    }
}

impl<L: Language, D, R> Eq for SyntaxToken<L, D, R> {}

impl<L: Language, D, R> SyntaxToken<L, D, R> {
    pub fn debug(&self, resolver: &impl Resolver) -> String {
        let mut res = String::new();
        write!(res, "{:?}@{:?}", self.kind(), self.text_range()).unwrap();
        if self.resolve_text(resolver).len() < 25 {
            write!(res, " {:?}", self.resolve_text(resolver)).unwrap();
            return res;
        }
        let text = self.resolve_text(resolver);
        for idx in 21..25 {
            if text.is_char_boundary(idx) {
                let text = format!("{} ...", &text[..idx]);
                write!(res, " {:?}", text).unwrap();
                return res;
            }
        }
        unreachable!()
    }

    pub fn display(&self, resolver: &impl Resolver) -> String {
        self.resolve_text(resolver).to_string()
    }
}

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
    pub fn display(&self, resolver: &impl Resolver) -> String {
        match self {
            NodeOrToken::Node(it) => it.display(resolver),
            NodeOrToken::Token(it) => it.display(resolver),
        }
    }
}

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
    pub fn display(&self, resolver: &impl Resolver) -> String {
        match self {
            NodeOrToken::Node(it) => it.display(resolver),
            NodeOrToken::Token(it) => it.display(resolver),
        }
    }
}

enum Kind<L: Language, D: 'static, R: 'static> {
    Root(GreenNode, Arc<R>),
    Child {
        parent: SyntaxNode<L, D, R>,
        index:  u32,
        offset: TextSize,
    },
}

impl<L: Language, D, R> Kind<L, D, R> {
    fn as_child(&self) -> Option<(&SyntaxNode<L, D, R>, u32, TextSize)> {
        match self {
            Kind::Child { parent, index, offset } => Some((parent, *index, *offset)),
            _ => None,
        }
    }
}

struct NodeData<L: Language, D: 'static, R: 'static> {
    kind:        Kind<L, D, R>,
    green:       ptr::NonNull<GreenNode>,
    ref_count:   *mut AtomicU32,
    data:        RwLock<Option<Arc<D>>>,
    children:    Vec<UnsafeCell<Option<SyntaxElement<L, D, R>>>>,
    child_locks: Vec<RwLock<()>>,
}

impl<L: Language, D, R> NodeData<L, D, R> {
    fn new(
        kind: Kind<L, D, R>,
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

impl<L: Language, D> SyntaxNode<L, D, ()> {
    pub fn new_root(green: GreenNode) -> Self {
        Self::make_new_root(green, ())
    }
}

impl<L: Language, D, R> SyntaxNode<L, D, R> {
    fn new(data: *mut NodeData<L, D, R>) -> Self {
        Self { data }
    }

    fn make_new_root(green: GreenNode, resolver: R) -> Self {
        let ref_count = Box::new(AtomicU32::new(1));
        let n_children = green.children().count();
        let data = NodeData::new(
            Kind::Root(green, Arc::new(resolver)),
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

    pub fn new_root_with_resolver(green: GreenNode, resolver: R) -> Self
    where
        R: Resolver,
    {
        Self::make_new_root(green, resolver)
    }

    // Technically, unsafe, but private so that's OK.
    // Safety: `green` must be a descendent of `parent.green`
    fn new_child(green: &GreenNode, parent: &Self, index: u32, offset: TextSize, ref_count: *mut AtomicU32) -> Self {
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

    pub fn set_data(&self, data: D) -> Arc<D> {
        let mut ptr = self.data().data.write();
        let data = Arc::new(data);
        *ptr = Some(Arc::clone(&data));
        data
    }

    pub fn try_set_data(&self, data: D) -> Result<Arc<D>, D> {
        let mut ptr = self.data().data.write();
        if ptr.is_some() {
            return Err(data);
        }
        let data = Arc::new(data);
        *ptr = Some(Arc::clone(&data));
        Ok(data)
    }

    pub fn get_data(&self) -> Option<Arc<D>> {
        let ptr = self.data().data.read();
        (*ptr).as_ref().map(|ptr| Arc::clone(ptr))
    }

    pub fn clear_data(&self) {
        let mut ptr = self.data().data.write();
        *ptr = None;
    }

    pub fn resolver(&self) -> &Arc<R> {
        match &self.root().data().kind {
            Kind::Root(_, resolver) => resolver,
            _ => unreachable!(),
        }
    }

    #[inline]
    fn read(&self, index: usize) -> Option<SyntaxElementRef<'_, L, D, R>> {
        // safety: children are pre-allocated and indices are determined internally
        let _read = unsafe { self.data().child_locks.get_unchecked(index).read() };
        // safety: mutable accesses to the slot only occur below and have to take the lock
        let slot = unsafe { &*self.data().children.get_unchecked(index).get() };
        slot.as_ref().map(|elem| elem.into())
    }

    fn try_write(&self, index: usize, elem: SyntaxElement<L, D, R>) {
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
                    let ref_count = unsafe { Box::from_raw(node.data().ref_count) };
                    ref_count.fetch_add(2, Ordering::AcqRel);
                    let node_data = node.data;
                    drop(node);
                    unsafe { drop(Box::from_raw(node_data)) };
                    drop(ref_count);
                }
                SyntaxElement::Token(token) => {
                    // We don't have to worry about `NodeData` or `SyntaxToken<L>`'s own `Drop` here,
                    // but we will still drop `token`'s `parent`, which decreases the `ref_count`
                    // by one.

                    // safety: as above
                    let ref_count = unsafe { &*token.parent.data().ref_count };
                    ref_count.fetch_add(1, Ordering::AcqRel);
                    drop(token);
                }
            }
        }
    }

    #[inline(always)]
    fn get_or_add_node(&self, node: &GreenNode, index: usize, offset: TextSize) -> SyntaxElementRef<'_, L, D, R> {
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
    ) -> SyntaxElementRef<'_, L, D, R> {
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

    #[inline]
    pub fn syntax_kind(&self) -> SyntaxKind {
        self.green().kind()
    }

    #[inline]
    pub fn kind(&self) -> L::Kind {
        L::kind_from_raw(self.syntax_kind())
    }

    #[inline]
    pub fn text_range(&self) -> TextRange {
        let offset = match self.data().kind.as_child() {
            Some((_, _, it)) => it,
            _ => 0.into(),
        };
        TextRange::at(offset, self.green().text_len())
    }

    #[inline]
    pub fn resolve_text<'n, 'i, I>(&'n self, resolver: &'i I) -> SyntaxText<'n, 'i, I, L, D, R>
    where
        I: Resolver + ?Sized,
    {
        SyntaxText::new(self, resolver)
    }

    #[inline]
    pub fn green(&self) -> &GreenNode {
        unsafe { self.data().green.as_ref() }
    }

    #[inline]
    pub fn parent(&self) -> Option<&SyntaxNode<L, D, R>> {
        match &self.data().kind {
            Kind::Root(_, _) => None,
            Kind::Child { parent, .. } => Some(parent),
        }
    }

    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<L, D, R>> {
        iter::successors(Some(self), |&node| node.parent())
    }

    #[inline]
    pub fn children(&self) -> SyntaxNodeChildren<'_, L, D, R> {
        SyntaxNodeChildren::new(self)
    }

    #[inline]
    pub fn children_with_tokens(&self) -> SyntaxElementChildren<'_, L, D, R> {
        SyntaxElementChildren::new(self)
    }

    #[inline]
    #[allow(clippy::map_clone)]
    pub fn first_child(&self) -> Option<&SyntaxNode<L, D, R>> {
        let (node, (index, offset)) = filter_nodes(self.green().children_from(0, self.text_range().start())).next()?;
        self.get_or_add_node(node, index, offset).as_node().map(|node| *node)
    }

    #[inline]
    pub fn first_child_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        let (element, (index, offset)) = self.green().children_from(0, self.text_range().start()).next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    #[inline]
    #[allow(clippy::map_clone)]
    pub fn last_child(&self) -> Option<&SyntaxNode<L, D, R>> {
        let (node, (index, offset)) = filter_nodes(
            self.green()
                .children_to(self.green().children().len(), self.text_range().end()),
        )
        .next()?;
        self.get_or_add_node(node, index, offset).as_node().map(|node| *node)
    }

    #[inline]
    pub fn last_child_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        let (element, (index, offset)) = self
            .green()
            .children_to(self.green().children().len(), self.text_range().end())
            .next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    #[inline]
    pub fn next_child_after(&self, n: usize, offset: TextSize) -> Option<&SyntaxNode<L, D, R>> {
        let (node, (index, offset)) = filter_nodes(self.green().children_from(n + 1, offset)).next()?;
        self.get_or_add_node(node, index, offset).as_node().copied()
    }

    #[inline]
    pub fn next_child_or_token_after(&self, n: usize, offset: TextSize) -> Option<SyntaxElementRef<'_, L, D, R>> {
        let (element, (index, offset)) = self.green().children_from(n + 1, offset).next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    #[inline]
    pub fn prev_child_before(&self, n: usize, offset: TextSize) -> Option<&SyntaxNode<L, D, R>> {
        let (node, (index, offset)) = filter_nodes(self.green().children_to(n, offset)).next()?;
        self.get_or_add_node(node, index, offset).as_node().copied()
    }

    #[inline]
    pub fn prev_child_or_token_before(&self, n: usize, offset: TextSize) -> Option<SyntaxElementRef<'_, L, D, R>> {
        let (element, (index, offset)) = self.green().children_to(n, offset).next()?;
        Some(self.get_or_add_element(element, index, offset))
    }

    #[inline]
    pub fn next_sibling(&self) -> Option<&SyntaxNode<L, D, R>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (node, (index, offset)) = filter_nodes(
            parent
                .green()
                .children_from((index + 1) as usize, self.text_range().end()),
        )
        .next()?;
        parent.get_or_add_node(node, index, offset).as_node().copied()
    }

    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (element, (index, offset)) = parent
            .green()
            .children_from((index + 1) as usize, self.text_range().end())
            .next()?;
        Some(parent.get_or_add_element(element, index, offset))
    }

    #[inline]
    pub fn prev_sibling(&self) -> Option<&SyntaxNode<L, D, R>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (node, (index, offset)) =
            filter_nodes(parent.green().children_to(index as usize, self.text_range().start())).next()?;
        parent.get_or_add_node(node, index, offset).as_node().copied()
    }

    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        let (parent, index, _) = self.data().kind.as_child()?;

        let (element, (index, offset)) = parent
            .green()
            .children_to(index as usize, self.text_range().start())
            .next()?;
        Some(parent.get_or_add_element(element, index, offset))
    }

    /// Return the leftmost token in the subtree of this node
    #[inline]
    pub fn first_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        self.first_child_or_token()?.first_token()
    }

    /// Return the rightmost token in the subtree of this node
    #[inline]
    pub fn last_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        self.last_child_or_token()?.last_token()
    }

    #[inline]
    pub fn siblings(&self, direction: Direction) -> impl Iterator<Item = &SyntaxNode<L, D, R>> {
        iter::successors(Some(self), move |node| match direction {
            Direction::Next => node.next_sibling(),
            Direction::Prev => node.prev_sibling(),
        })
    }

    #[inline]
    pub fn siblings_with_tokens(&self, direction: Direction) -> impl Iterator<Item = SyntaxElementRef<'_, L, D, R>> {
        let me: SyntaxElementRef<'_, L, D, R> = self.into();
        iter::successors(Some(me), move |el| match direction {
            Direction::Next => el.next_sibling_or_token(),
            Direction::Prev => el.prev_sibling_or_token(),
        })
    }

    #[inline]
    pub fn descendants(&self) -> impl Iterator<Item = &SyntaxNode<L, D, R>> {
        self.preorder().filter_map(|event| match event {
            WalkEvent::Enter(node) => Some(node),
            WalkEvent::Leave(_) => None,
        })
    }

    #[inline]
    pub fn descendants_with_tokens(&self) -> impl Iterator<Item = SyntaxElementRef<'_, L, D, R>> {
        self.preorder_with_tokens().filter_map(|event| match event {
            WalkEvent::Enter(it) => Some(it),
            WalkEvent::Leave(_) => None,
        })
    }

    /// Traverse the subtree rooted at the current node (including the current
    /// node) in preorder, excluding tokens.
    #[inline(always)]
    pub fn preorder(&self) -> impl Iterator<Item = WalkEvent<&SyntaxNode<L, D, R>>> {
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
    pub fn preorder_with_tokens(&self) -> impl Iterator<Item = WalkEvent<SyntaxElementRef<'_, L, D, R>>> {
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
    pub fn token_at_offset(&self, offset: TextSize) -> TokenAtOffset<SyntaxToken<L, D, R>> {
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
    pub fn covering_element(&self, range: TextRange) -> SyntaxElementRef<'_, L, D, R> {
        let mut res: SyntaxElementRef<'_, L, D, R> = self.into();
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

impl<L: Language, D, R> SyntaxNode<L, D, R>
where
    R: Resolver,
{
    #[inline]
    pub fn text(&self) -> SyntaxText<'_, '_, R, L, D, R> {
        SyntaxText::new(self, self.resolver().as_ref())
    }
}

#[cfg(feature = "serde1")]
impl<L, D, R> SyntaxNode<L, D, R>
where
    L: Language,
{
    /// Return an anonymous object that can be used to serialize this node,
    /// including the data for each node.
    pub fn as_serialize_with_data(&self) -> impl serde::Serialize + '_
    where
        R: Resolver,
        D: serde::Serialize,
    {
        SerializeWithData {
            node:     self,
            resolver: self.resolver().as_ref(),
        }
    }

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

impl<L: Language, D, R> fmt::Debug for SyntaxNode<L, D, R>
where
    R: Resolver,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::debug(self, self.resolver().as_ref(), f.alternate()))
    }
}

impl<L: Language, D, R> fmt::Display for SyntaxNode<L, D, R>
where
    R: Resolver,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::display(self, self.resolver().as_ref()))
    }
}

impl<L: Language, D, R> SyntaxToken<L, D, R> {
    fn new(parent: &SyntaxNode<L, D, R>, index: u32, offset: TextSize) -> SyntaxToken<L, D, R> {
        Self {
            parent: parent.clone_uncounted(),
            index,
            offset,
        }
    }

    /// Returns a green tree, equal to the green tree this token
    /// belongs two, except with this token substitute. The complexity
    /// of operation is proportional to the depth of the tree
    pub fn replace_with(&self, replacement: GreenToken) -> GreenNode {
        assert_eq!(self.syntax_kind(), replacement.kind());
        let mut replacement = Some(replacement);
        let parent = self.parent();
        let me = self.index;

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

    #[inline]
    pub fn syntax_kind(&self) -> SyntaxKind {
        self.green().kind()
    }

    #[inline]
    pub fn kind(&self) -> L::Kind {
        L::kind_from_raw(self.syntax_kind())
    }

    #[inline]
    pub fn text_range(&self) -> TextRange {
        TextRange::at(self.offset, self.green().text_len())
    }

    #[inline]
    pub fn resolve_text<'i, I>(&self, resolver: &'i I) -> &'i str
    where
        I: Resolver + ?Sized,
    {
        self.green().text(resolver)
    }

    pub fn green(&self) -> &GreenToken {
        self.parent
            .green()
            .children()
            .nth(self.index as usize)
            .unwrap()
            .as_token()
            .unwrap()
    }

    #[inline]
    pub fn parent(&self) -> &SyntaxNode<L, D, R> {
        &self.parent
    }

    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<L, D, R>> {
        self.parent().ancestors()
    }

    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        self.parent()
            .next_child_or_token_after(self.index as usize, self.text_range().end())
    }

    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        self.parent()
            .prev_child_or_token_before(self.index as usize, self.text_range().start())
    }

    #[inline]
    pub fn siblings_with_tokens(&self, direction: Direction) -> impl Iterator<Item = SyntaxElementRef<'_, L, D, R>> {
        let me: SyntaxElementRef<'_, L, D, R> = self.into();
        iter::successors(Some(me), move |el| match direction {
            Direction::Next => el.next_sibling_or_token(),
            Direction::Prev => el.prev_sibling_or_token(),
        })
    }

    /// Next token in the tree (i.e, not necessary a sibling)
    pub fn next_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self.next_sibling_or_token() {
            Some(element) => element.first_token(),
            None => self
                .parent()
                .ancestors()
                .find_map(|it| it.next_sibling_or_token())
                .and_then(|element| element.first_token()),
        }
    }

    /// Previous token in the tree (i.e, not necessary a sibling)
    pub fn prev_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self.prev_sibling_or_token() {
            Some(element) => element.last_token(),
            None => self
                .parent()
                .ancestors()
                .find_map(|it| it.prev_sibling_or_token())
                .and_then(|element| element.last_token()),
        }
    }
}

impl<L: Language, D, R> SyntaxToken<L, D, R>
where
    R: Resolver,
{
    #[inline]
    pub fn text(&self) -> &str {
        self.green().text(self.parent().resolver().as_ref())
    }
}

impl<L: Language, D, R> fmt::Debug for SyntaxToken<L, D, R>
where
    R: Resolver,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::debug(self, self.parent().resolver().as_ref()))
    }
}

impl<L: Language, D, R> fmt::Display for SyntaxToken<L, D, R>
where
    R: Resolver,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::display(self, self.parent().resolver().as_ref()))
    }
}

impl<L: Language, D, R> SyntaxElement<L, D, R> {
    fn new(
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

    #[inline]
    pub fn text_range(&self) -> TextRange {
        match self {
            NodeOrToken::Node(it) => it.text_range(),
            NodeOrToken::Token(it) => it.text_range(),
        }
    }

    #[inline]
    pub fn syntax_kind(&self) -> SyntaxKind {
        match self {
            NodeOrToken::Node(it) => it.syntax_kind(),
            NodeOrToken::Token(it) => it.syntax_kind(),
        }
    }

    #[inline]
    pub fn kind(&self) -> L::Kind {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    #[inline]
    pub fn parent(&self) -> Option<&SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    #[inline]
    pub fn first_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    #[inline]
    pub fn last_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }
}

impl<'a, L: Language, D, R> SyntaxElementRef<'a, L, D, R> {
    #[inline]
    pub fn text_range(&self) -> TextRange {
        match self {
            NodeOrToken::Node(it) => it.text_range(),
            NodeOrToken::Token(it) => it.text_range(),
        }
    }

    #[inline]
    pub fn syntax_kind(&self) -> SyntaxKind {
        match self {
            NodeOrToken::Node(it) => it.syntax_kind(),
            NodeOrToken::Token(it) => it.syntax_kind(),
        }
    }

    #[inline]
    pub fn kind(&self) -> L::Kind {
        match self {
            NodeOrToken::Node(it) => it.kind(),
            NodeOrToken::Token(it) => it.kind(),
        }
    }

    #[inline]
    pub fn parent(&self) -> Option<&'a SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.parent(),
            NodeOrToken::Token(it) => Some(it.parent()),
        }
    }

    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &'a SyntaxNode<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.ancestors(),
            NodeOrToken::Token(it) => it.parent().ancestors(),
        }
    }

    #[inline]
    pub fn first_token(&self) -> Option<&'a SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.first_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    #[inline]
    pub fn last_token(&self) -> Option<&'a SyntaxToken<L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.last_token(),
            NodeOrToken::Token(it) => Some(it),
        }
    }

    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'a, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.next_sibling_or_token(),
            NodeOrToken::Token(it) => it.next_sibling_or_token(),
        }
    }

    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'a, L, D, R>> {
        match self {
            NodeOrToken::Node(it) => it.prev_sibling_or_token(),
            NodeOrToken::Token(it) => it.prev_sibling_or_token(),
        }
    }

    #[inline]
    fn token_at_offset(&self, offset: TextSize) -> TokenAtOffset<SyntaxToken<L, D, R>> {
        assert!(self.text_range().start() <= offset && offset <= self.text_range().end());
        match self {
            NodeOrToken::Token(token) => TokenAtOffset::Single((*token).clone()),
            NodeOrToken::Node(node) => node.token_at_offset(offset),
        }
    }
}

#[derive(Clone, Debug)]
struct Iter<'n> {
    green:  Children<'n>,
    offset: TextSize,
    index:  usize,
}

impl<'n> Iter<'n> {
    fn new<L: Language, D, R>(parent: &'n SyntaxNode<L, D, R>) -> Self {
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

#[derive(Clone)]
pub struct SyntaxNodeChildren<'n, L: Language, D: 'static = (), R: 'static = ()> {
    inner:  Iter<'n>,
    parent: &'n SyntaxNode<L, D, R>,
}

impl<'n, L: Language, D, R> SyntaxNodeChildren<'n, L, D, R> {
    #[inline]
    fn new(parent: &'n SyntaxNode<L, D, R>) -> Self {
        Self {
            inner: Iter::new(parent),
            parent,
        }
    }
}

impl<'n, L: Language, D, R> Iterator for SyntaxNodeChildren<'n, L, D, R> {
    type Item = &'n SyntaxNode<L, D, R>;

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

#[derive(Clone)]
pub struct SyntaxElementChildren<'n, L: Language, D: 'static = (), R: 'static = ()> {
    inner:  Iter<'n>,
    parent: &'n SyntaxNode<L, D, R>,
}

impl<'n, L: Language, D, R> SyntaxElementChildren<'n, L, D, R> {
    #[inline]
    fn new(parent: &'n SyntaxNode<L, D, R>) -> Self {
        Self {
            inner: Iter::new(parent),
            parent,
        }
    }
}

impl<'n, L: Language, D, R> Iterator for SyntaxElementChildren<'n, L, D, R> {
    type Item = SyntaxElementRef<'n, L, D, R>;

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
