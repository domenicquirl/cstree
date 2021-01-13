use cstree::{Language, SyntaxKind};

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
