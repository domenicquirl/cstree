use cstree::Syntax;

#[test]
fn empty_tree_arc() {
    // this test is not here for the test itself, but to run it through MIRI, who complained about out-of-bound
    // `ThinArc` pointers for a root `GreenNode` with no children

    use cstree::{build::GreenNodeBuilder, syntax::SyntaxNode};
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
    #[repr(u32)]
    enum SyntaxKind {
        Root,
    }

    let mut builder: GreenNodeBuilder<SyntaxKind> = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root);
    builder.finish_node();
    let (green, _) = builder.finish();
    let root: SyntaxNode<SyntaxKind> = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), SyntaxKind::Root);
}
