mod basic;
mod regressions;
mod rollback;
mod sendsync;
#[cfg(feature = "serialize")]
mod serde;

use cstree::{
    build::{GreenNodeBuilder, NodeCache},
    green::GreenNode,
    interning::{Interner, Resolver},
    util::NodeOrToken,
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

#[track_caller]
pub fn assert_tree_eq(
    (left, left_res): (&SyntaxNode, &impl Resolver),
    (right, right_res): (&SyntaxNode, &impl Resolver),
) {
    if left.green() == right.green() {
        return;
    }

    if left.kind() != right.kind() || left.children_with_tokens().len() != right.children_with_tokens().len() {
        panic!("{} !=\n{}", left.debug(left_res, true), right.debug(right_res, true))
    }

    for elem in left.children_with_tokens().zip(right.children_with_tokens()) {
        match elem {
            (NodeOrToken::Node(ln), NodeOrToken::Node(rn)) => assert_tree_eq((ln, left_res), (rn, right_res)),
            (NodeOrToken::Node(n), NodeOrToken::Token(t)) => {
                panic!("{} != {}", n.debug(left_res, true), t.debug(right_res))
            }
            (NodeOrToken::Token(t), NodeOrToken::Node(n)) => {
                panic!("{} != {}", t.debug(left_res), n.debug(right_res, true))
            }
            (NodeOrToken::Token(lt), NodeOrToken::Token(rt)) => {
                if lt.syntax_kind() != rt.syntax_kind() || lt.resolve_text(left_res) != rt.resolve_text(right_res) {
                    panic!("{} != {}", lt.debug(left_res), rt.debug(right_res))
                }
            }
        }
    }
}
