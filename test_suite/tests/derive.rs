use cstree::{RawSyntaxKind, Syntax};

#[test]
fn basic() {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
    #[repr(u32)]
    pub enum SyntaxKind {
        A,
        #[static_text("b")]
        B,
    }
    pub type MySyntax = SyntaxKind;

    assert_eq!(MySyntax::into_raw(SyntaxKind::A), RawSyntaxKind(0));
    assert_eq!(MySyntax::into_raw(SyntaxKind::B), RawSyntaxKind(1));

    assert_eq!(MySyntax::from_raw(RawSyntaxKind(0)), SyntaxKind::A);
    assert_eq!(MySyntax::from_raw(RawSyntaxKind(1)), SyntaxKind::B);

    assert!(MySyntax::static_text(SyntaxKind::A).is_none());
    assert_eq!(MySyntax::static_text(SyntaxKind::B), Some("b"));
}
