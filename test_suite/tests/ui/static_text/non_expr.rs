use cstree::Syntax;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
#[repr(u32)]
pub enum SyntaxKind {
    A,
    #[static_text(SyntaxKind)]
    B,
}

fn main() {}
