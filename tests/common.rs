#![allow(unused)]

use cstree::{
    interning::{Interner, Resolver},
    GreenNode, GreenNodeBuilder, Language, NodeCache, SyntaxKind,
};

pub type SyntaxNode<D = (), R = ()> = cstree::SyntaxNode<TestLang, D, R>;

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
}

#[derive(Debug)]
pub enum Element<'s> {
    Node(Vec<Element<'s>>),
    Token(&'s str),
}

pub fn two_level_tree() -> Element<'static> {
    use Element::*;
    Node(vec![
        Node(vec![Token("0.0"), Token("0.1")]),
        Node(vec![Token("1.0")]),
        Node(vec![Token("2.0"), Token("2.1"), Token("2.2")]),
    ])
}

pub fn big_tree() -> Element<'static> {
    use Element::*;

    Node(vec![
        Node(vec![Node(vec![Token("foo"), Token("bar")]), Token("baz")]),
        Node(vec![Token("pub"), Token("fn"), Token("tree")]),
    ])
}

pub fn build_tree<D>(root: &Element<'_>) -> (SyntaxNode<D>, impl Resolver) {
    let mut builder = GreenNodeBuilder::new();
    build_recursive(root, &mut builder, 0);
    let (node, interner) = builder.finish();
    (SyntaxNode::new_root(node), interner.unwrap())
}

pub fn build_tree_with_cache<'c, 'i, I>(root: &Element<'_>, cache: &'c mut NodeCache<'i, I>) -> GreenNode
where
    I: Interner,
{
    let mut builder = GreenNodeBuilder::with_cache(cache);
    build_recursive(root, &mut builder, 0);
    let (node, interner) = builder.finish();
    assert!(interner.is_none());
    node
}

pub fn build_recursive<'c, 'i, I>(root: &Element<'_>, builder: &mut GreenNodeBuilder<'c, 'i, I>, mut from: u16) -> u16
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
            builder.token(SyntaxKind(from), *text);
        }
    }
    from
}
