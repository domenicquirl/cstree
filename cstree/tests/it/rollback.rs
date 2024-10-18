use super::*;
use cstree::interning::Resolver;

type GreenNodeBuilder<'cache, 'interner> = cstree::build::GreenNodeBuilder<'cache, 'interner, SyntaxKind>;

fn with_builder(f: impl FnOnce(&mut GreenNodeBuilder)) -> (SyntaxNode, impl Resolver) {
    let mut builder = GreenNodeBuilder::new();
    f(&mut builder);
    let (node, cache) = builder.finish();
    (SyntaxNode::new_root(node), cache.unwrap().into_interner().unwrap())
}

#[test]
#[should_panic = "`left == right` failed"]
fn comparison_works() {
    let (first, res1) = with_builder(|_| {});
    let (second, res2) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));
        builder.token(SyntaxKind(1), "hi");
        builder.finish_node();
    });
    assert_tree_eq((&first, &res1), (&second, &res2));
}

#[test]
fn simple() {
    let (first, res1) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));
        builder.finish_node();
    });
    let (second, res2) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));

        // Add a token, then remove it.
        let initial = builder.checkpoint();
        builder.token(SyntaxKind(1), "hi");
        builder.revert(initial);

        builder.finish_node();
    });
    assert_tree_eq((&first, &res1), (&second, &res2));
}

#[test]
fn nested() {
    let (first, res1) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));
        builder.finish_node();
    });

    let (second, res2) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));
        // Add two tokens, then remove both.
        let initial = builder.checkpoint();
        builder.token(SyntaxKind(1), "hi");
        builder.token(SyntaxKind(2), "hello");
        builder.revert(initial);

        builder.finish_node();
    });

    let (third, res3) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));
        builder.finish_node();
    });

    assert_tree_eq((&first, &res1), (&second, &res2));
    assert_tree_eq((&first, &res1), (&third, &res3));
}

#[test]
#[should_panic = "checkpoint in the future"]
fn misuse() {
    with_builder(|builder| {
        builder.start_node(SyntaxKind(0));

        // Add two tokens, but remove them in the wrong order.
        let initial = builder.checkpoint();
        builder.token(SyntaxKind(1), "hi");
        let new = builder.checkpoint();
        builder.token(SyntaxKind(2), "hello");
        builder.revert(initial);
        builder.revert(new);

        builder.finish_node();
    });
}

#[test]
fn misuse2() {
    let (first, res1) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));
        builder.token(SyntaxKind(3), "no");
        builder.finish_node();
    });

    let (second, res2) = with_builder(|builder| {
        builder.start_node(SyntaxKind(0));

        // Add two tokens, revert to the initial state, add three tokens, and try to revert to an earlier checkpoint.
        let initial = builder.checkpoint();
        builder.token(SyntaxKind(1), "hi");
        let new = builder.checkpoint();
        builder.token(SyntaxKind(2), "hello");
        builder.revert(initial);

        // This is wrong, but there's not a whole lot the library can do about it.
        builder.token(SyntaxKind(3), "no");
        builder.token(SyntaxKind(4), "bad");
        builder.token(SyntaxKind(4), "wrong");
        builder.revert(new);

        builder.finish_node();
    });

    assert_tree_eq((&first, &res1), (&second, &res2));
}
