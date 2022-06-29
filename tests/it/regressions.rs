#[test]
fn empty_tree_arc() {
    // this test is not here for the test itself, but to run it through MIRI, who complained about out-of-bound
    // `ThinArc` pointers for a root `GreenNode` with no children

    use cstree::*;
    #[allow(non_camel_case_types)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(u16)]
    enum SyntaxKind {
        Root,
    }
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    enum Lang {}
    impl cstree::Language for Lang {
        // ...
        type Kind = SyntaxKind;

        fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
            assert!(raw.0 <= SyntaxKind::Root as u16);
            unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
        }

        fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
            cstree::SyntaxKind(kind as u16)
        }

        fn static_text(kind: Self::Kind) -> Option<&'static str> {
            None
        }
    }
    let mut builder: GreenNodeBuilder<Lang> = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root);
    builder.finish_node();
    let (green, _) = builder.finish();
    let root: SyntaxNode<Lang> = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), SyntaxKind::Root);
}
