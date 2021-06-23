use std::{
    hash::{Hash, Hasher},
    iter::FusedIterator,
    slice,
};

use fxhash::FxHasher32;

use crate::{
    green::{GreenElement, GreenElementRef, PackedGreenElement, SyntaxKind},
    TextSize,
};
use triomphe::{Arc, HeaderWithLength, ThinArc};

#[repr(align(2))] //to use 1 bit for pointer tagging. NB: this is an at-least annotation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct GreenNodeHead {
    pub(super) kind:       SyntaxKind,
    pub(super) text_len:   TextSize,
    pub(super) child_hash: u32,
}

/// Internal node in the immutable "green" tree.
/// It contains other nodes and tokens as its children.
#[derive(Clone)]
pub struct GreenNode {
    pub(super) data: ThinArc<GreenNodeHead, PackedGreenElement>,
}

impl std::fmt::Debug for GreenNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data.with_arc(|data| data.fmt(f))
    }
}

impl GreenNode {
    /// Creates a new Node.
    #[inline]
    pub fn new<I>(kind: SyntaxKind, children: I) -> GreenNode
    where
        I: IntoIterator<Item = GreenElement>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut hasher = FxHasher32::default();
        let mut text_len: TextSize = 0.into();
        let children = children
            .into_iter()
            .inspect(|it| {
                text_len += it.text_len();
                it.hash(&mut hasher);
            })
            .map(PackedGreenElement::from);
        let header = HeaderWithLength::new(
            GreenNodeHead {
                kind,
                text_len: 0.into(),
                child_hash: 0,
            },
            children.len(),
        );
        let mut data = Arc::from_header_and_iter(header, children);

        // XXX: fixup `text_len` and `child_hash` after construction, because
        // we can't iterate `children` twice.
        let header = &mut Arc::get_mut(&mut data).unwrap().header.header;
        header.text_len = text_len;
        header.child_hash = hasher.finish() as u32;
        GreenNode {
            data: Arc::into_thin(data),
        }
    }

    #[inline]
    pub(super) fn from_head_and_children<I>(header: GreenNodeHead, children: I) -> GreenNode
    where
        I: IntoIterator<Item = GreenElement>,
        I::IntoIter: ExactSizeIterator,
    {
        let children = children.into_iter().map(PackedGreenElement::from);
        let header = HeaderWithLength::new(header, children.len());
        GreenNode {
            data: Arc::into_thin(Arc::from_header_and_iter(header, children)),
        }
    }

    /// [`SyntaxKind`] of this node.
    #[inline]
    pub fn kind(&self) -> SyntaxKind {
        self.data.header.header.kind
    }

    /// Returns the length of text covered by this node.
    #[inline]
    pub fn text_len(&self) -> TextSize {
        self.data.header.header.text_len
    }

    #[inline]
    pub(crate) fn iter(&self) -> slice::Iter<'_, PackedGreenElement> {
        self.data.slice.iter()
    }

    /// Iterator over all children of this node.
    #[inline]
    pub fn children(&self) -> Children<'_> {
        Children {
            inner: self.data.slice.iter(),
        }
    }
}

impl Hash for GreenNode {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.data.header.header.hash(state);
    }
}

impl PartialEq for GreenNode {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl Eq for GreenNode {}

/// An iterator over a [`GreenNode`]'s children.
#[derive(Debug, Clone)]
pub struct Children<'a> {
    inner: slice::Iter<'a, PackedGreenElement>,
}

// NB: forward everything stable that iter::Slice specializes as of Rust 1.39.0
impl ExactSizeIterator for Children<'_> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> Iterator for Children<'a> {
    type Item = GreenElementRef<'a>;

    #[inline]
    fn next(&mut self) -> Option<GreenElementRef<'a>> {
        self.inner.next().map(PackedGreenElement::as_ref)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.inner.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.inner.nth(n).map(PackedGreenElement::as_ref)
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    #[inline]
    fn fold<Acc, Fold>(self, init: Acc, mut f: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut accum = init;
        for x in self {
            accum = f(accum, x);
        }
        accum
    }
}

impl<'a> DoubleEndedIterator for Children<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(PackedGreenElement::as_ref)
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.inner.nth_back(n).map(PackedGreenElement::as_ref)
    }

    #[inline]
    fn rfold<Acc, Fold>(mut self, init: Acc, mut f: Fold) -> Acc
    where
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut accum = init;
        while let Some(x) = self.next_back() {
            accum = f(accum, x);
        }
        accum
    }
}

impl FusedIterator for Children<'_> {}
