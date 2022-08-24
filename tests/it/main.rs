mod basic;
mod regressions;
mod sendsync;
#[cfg(feature = "serialize")]
mod serde;

use cstree::{GreenNode, GreenNodeBuilder, Language, NodeCache, SyntaxKind};
use lasso::Interner;

pub type SyntaxNode<D = ()> = cstree::SyntaxNode<TestLang, D>;
pub type SyntaxToken<D = ()> = cstree::SyntaxToken<TestLang, D>;
pub type SyntaxElement<D = ()> = cstree::SyntaxElement<TestLang, D>;
pub type SyntaxElementRef<'a, D = ()> = cstree::SyntaxElementRef<'a, TestLang, D>;

pub type ResolvedNode<D = ()> = cstree::ResolvedNode<TestLang, D>;
pub type ResolvedToken<D = ()> = cstree::ResolvedToken<TestLang, D>;
pub type ResolvedElement<D = ()> = cstree::ResolvedElement<TestLang, D>;
pub type ResolvedElementRef<'a, D = ()> = cstree::ResolvedElementRef<'a, TestLang, D>;

#[derive(Debug)]
pub enum Element<'s> {
    Node(Vec<Element<'s>>),
    Token(&'s str),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum TestLang {}
impl Language for TestLang {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: SyntaxKind) -> Self::Kind {
        raw
    }

    fn kind_to_raw(kind: Self::Kind) -> SyntaxKind {
        kind
    }

    fn static_text(_kind: Self::Kind) -> Option<&'static str> {
        None
    }
}

pub fn build_tree_with_cache<'c, 'i, I>(root: &Element<'_>, cache: &'c mut NodeCache<'i, I>) -> GreenNode
where
    I: Interner,
{
    let mut builder: GreenNodeBuilder<TestLang, I> = GreenNodeBuilder::with_cache(cache);
    build_recursive(root, &mut builder, 0);
    let (node, cache) = builder.finish();
    assert!(cache.is_none());
    node
}

pub fn build_recursive<'c, 'i, L, I>(
    root: &Element<'_>,
    builder: &mut GreenNodeBuilder<'c, 'i, L, I>,
    mut from: u16,
) -> u16
where
    L: Language<Kind = SyntaxKind>,
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
            builder.token(SyntaxKind(from), *text);
        }
    }
    from
}
