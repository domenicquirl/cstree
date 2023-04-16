#[test]
fn empty_tree_arc() {
    // this test is not here for the test itself, but to run it through MIRI, who complained about out-of-bound
    // `ThinArc` pointers for a root `GreenNode` with no children

    use cstree::{build::GreenNodeBuilder, syntax::SyntaxNode};
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[repr(u32)]
    enum SyntaxKind {
        Root,
    }

    impl cstree::Syntax for SyntaxKind {
        fn from_raw(raw: cstree::RawSyntaxKind) -> Self {
            assert!(raw.0 <= SyntaxKind::Root as u32);
            unsafe { std::mem::transmute::<u32, SyntaxKind>(raw.0) }
        }

        fn into_raw(self) -> cstree::RawSyntaxKind {
            cstree::RawSyntaxKind(self as u32)
        }

        fn static_text(self) -> Option<&'static str> {
            None
        }
    }
    let mut builder: GreenNodeBuilder<SyntaxKind> = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root);
    builder.finish_node();
    let (green, _) = builder.finish();
    let root: SyntaxNode<SyntaxKind> = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), SyntaxKind::Root);
}
