use std::{
    hash::{Hash, Hasher},
    slice,
};

use rustc_hash::FxHasher;

use crate::{
    green::{iter::GreenNodeChildren, GreenElement, PackedGreenElement},
    text::TextSize,
    RawSyntaxKind,
};
use triomphe::{Arc, HeaderWithLength, ThinArc};

#[repr(align(2))] //to use 1 bit for pointer tagging. NB: this is an at-least annotation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct GreenNodeHead {
    pub(super) kind:       RawSyntaxKind,
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
    pub fn new<I>(kind: RawSyntaxKind, children: I) -> GreenNode
    where
        I: IntoIterator<Item = GreenElement>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut hasher = FxHasher::default();
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

    /// Creates a new Node.
    #[inline]
    pub(super) fn new_with_len_and_hash<I>(
        kind: RawSyntaxKind,
        children: I,
        text_len: TextSize,
        child_hash: u32,
    ) -> GreenNode
    where
        I: IntoIterator<Item = GreenElement>,
        I::IntoIter: ExactSizeIterator,
    {
        let children = children.into_iter().map(PackedGreenElement::from);
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
        header.child_hash = child_hash;
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

    /// [`RawSyntaxKind`] of this node.
    #[inline]
    pub fn kind(&self) -> RawSyntaxKind {
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
    pub fn children(&self) -> GreenNodeChildren<'_> {
        GreenNodeChildren {
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
