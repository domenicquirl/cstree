use cstree::Syntax;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
pub enum SyntaxKind {
    A,
    #[static_text("b")]
    B,
}

fn main() {}
