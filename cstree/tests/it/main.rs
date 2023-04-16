mod basic;
mod regressions;
mod sendsync;
#[cfg(feature = "serialize")]
mod serde;

use cstree::{
    build::{GreenNodeBuilder, NodeCache},
    green::GreenNode,
    interning::Interner,
    RawSyntaxKind, Syntax,
};

pub type SyntaxNode<D = ()> = cstree::syntax::SyntaxNode<SyntaxKind, D>;
pub type SyntaxToken<D = ()> = cstree::syntax::SyntaxToken<SyntaxKind, D>;
pub type SyntaxElement<D = ()> = cstree::syntax::SyntaxElement<SyntaxKind, D>;
pub type SyntaxElementRef<'a, D = ()> = cstree::syntax::SyntaxElementRef<'a, SyntaxKind, D>;

pub type ResolvedNode<D = ()> = cstree::syntax::ResolvedNode<SyntaxKind, D>;
pub type ResolvedToken<D = ()> = cstree::syntax::ResolvedToken<SyntaxKind, D>;
pub type ResolvedElement<D = ()> = cstree::syntax::ResolvedElement<SyntaxKind, D>;
pub type ResolvedElementRef<'a, D = ()> = cstree::syntax::ResolvedElementRef<'a, SyntaxKind, D>;

#[derive(Debug)]
pub enum Element<'s> {
    Node(Vec<Element<'s>>),
    Token(&'s str),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct SyntaxKind(u32);

impl Syntax for SyntaxKind {
    fn from_raw(raw: RawSyntaxKind) -> Self {
        Self(raw.0)
    }

    fn into_raw(self) -> RawSyntaxKind {
        RawSyntaxKind(self.0)
    }

    fn static_text(self) -> Option<&'static str> {
        None
    }
}

pub fn build_tree_with_cache<I>(root: &Element<'_>, cache: &mut NodeCache<'_, I>) -> GreenNode
where
    I: Interner,
{
    let mut builder: GreenNodeBuilder<SyntaxKind, I> = GreenNodeBuilder::with_cache(cache);
    build_recursive(root, &mut builder, 0);
    let (node, cache) = builder.finish();
    assert!(cache.is_none());
    node
}

pub fn build_recursive<I>(
    root: &Element<'_>,
    builder: &mut GreenNodeBuilder<'_, '_, SyntaxKind, I>,
    mut from: u32,
) -> u32
where
    I: Interner,
{
    match root {
        Element::Node(children) => {
            builder.start_node(SyntaxKind(from));
            for child in children {
                from = build_recursive(child, builder, from + 1);
            }
            builder.finish_node();
        }
        Element::Token(text) => {
            builder.token(SyntaxKind(from), text);
        }
    }
    from
}
