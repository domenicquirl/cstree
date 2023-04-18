use cstree::Syntax;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
#[repr(u32)]
pub enum SyntaxKind {
    A,
    #[static_text(foo + 3)]
    B,
}

fn main() {}
