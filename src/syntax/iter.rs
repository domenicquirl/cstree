//! Red tree iterators.

use std::iter::FusedIterator;

use text_size::TextSize;

use crate::{green::GreenElementRef, GreenNodeChildren, Language, SyntaxElementRef, SyntaxNode};

#[derive(Clone, Debug)]
struct Iter<'n> {
    green:  GreenNodeChildren<'n>,
    offset: TextSize,
    index:  usize,
}

impl<'n> Iter<'n> {
    fn new<L: Language, D>(parent: &'n SyntaxNode<L, D>) -> Self {
        let offset = parent.text_range().start();
        let green: GreenNodeChildren<'_> = parent.green().children();
        Iter {
            green,
            offset,
            index: 0,
        }
    }
}

impl<'n> Iterator for Iter<'n> {
    type Item = (GreenElementRef<'n>, usize, TextSize);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.green.next().map(|element| {
            let offset = self.offset;
            let index = self.index;
            self.offset += element.text_len();
            self.index += 1;
            (element, index, offset)
        })
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.green.size_hint()
    }

    #[inline(always)]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.green.count()
    }
}

impl<'n> ExactSizeIterator for Iter<'n> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.green.len()
    }
}
impl<'n> FusedIterator for Iter<'n> {}

/// An iterator over the child nodes of a [`SyntaxNode`].
#[derive(Clone, Debug)]
pub struct SyntaxNodeChildren<'n, L: Language, D: 'static = ()> {
    inner:  Iter<'n>,
    parent: &'n SyntaxNode<L, D>,
}

impl<'n, L: Language, D> SyntaxNodeChildren<'n, L, D> {
    #[inline]
    pub(super) fn new(parent: &'n SyntaxNode<L, D>) -> Self {
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
        for (element, index, offset) in &mut self.inner {
            if let Some(&node) = element.as_node() {
                return Some(self.parent.get_or_add_node(node, index, offset).as_node().unwrap());
            }
        }
        None
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline(always)]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.inner.count()
    }
}

impl<'n, L: Language, D> ExactSizeIterator for SyntaxNodeChildren<'n, L, D> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<'n, L: Language, D> FusedIterator for SyntaxNodeChildren<'n, L, D> {}

/// An iterator over the children of a [`SyntaxNode`].
#[derive(Clone, Debug)]
pub struct SyntaxElementChildren<'n, L: Language, D: 'static = ()> {
    inner:  Iter<'n>,
    parent: &'n SyntaxNode<L, D>,
}

impl<'n, L: Language, D> SyntaxElementChildren<'n, L, D> {
    #[inline]
    pub(super) fn new(parent: &'n SyntaxNode<L, D>) -> Self {
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

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline(always)]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.inner.count()
    }
}

impl<'n, L: Language, D> ExactSizeIterator for SyntaxElementChildren<'n, L, D> {
    #[inline(always)]
    fn len(&self) -> usize {
        self.inner.len()
    }
}
impl<'n, L: Language, D> FusedIterator for SyntaxElementChildren<'n, L, D> {}
