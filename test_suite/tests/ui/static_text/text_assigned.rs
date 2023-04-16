use cstree::Syntax;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
#[repr(u32)]
pub enum SyntaxKind {
    A,
    #[static_text = "b"]
    B,
}

fn main() {}
