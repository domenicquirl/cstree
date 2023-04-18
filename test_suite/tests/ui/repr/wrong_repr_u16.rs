use cstree::Syntax;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
#[repr(u16)]
pub enum SyntaxKind {
    A,
    #[static_text("b")]
    B,
}

fn main() {}
