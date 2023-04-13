use cstree::Language;

#[test]
fn basic() {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Language)]
    #[repr(u32)]
    #[language_name = "TestLang"]
    pub enum SyntaxKind {
        A,
    }

    assert!(TestLang::static_text(SyntaxKind::A).is_none());
}
