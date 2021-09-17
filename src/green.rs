//! Implementation of the inner, "green" tree.
//! The [`GreenNodeBuilder`] is the main entry point to constructing [`GreenNode`]s and
//! [`GreenToken`]s.

mod builder;
mod element;
mod interner;
mod iter;
mod node;
mod token;

pub(crate) use self::element::GreenElementRef;
use self::element::{GreenElement, PackedGreenElement};

pub use self::{
    builder::{Checkpoint, GreenNodeBuilder, NodeCache},
    interner::TokenInterner,
    iter::GreenNodeChildren,
    node::GreenNode,
    token::GreenToken,
};

/// SyntaxKind is a type tag for each token or node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxKind(pub u16);

#[cfg(test)]
mod tests {
    use node::GreenNodeHead;
    use token::GreenTokenData;

    use super::*;

    #[test]
    fn assert_send_sync() {
        fn f<T: Send + Sync>() {}
        f::<GreenNode>();
        f::<GreenToken>();
        f::<GreenElement>();
        f::<PackedGreenElement>();
    }

    #[test]
    #[rustfmt::skip]
    fn assert_green_sizes() {
        use std::mem::size_of;

        assert_eq!(size_of::<GreenNode>(),          size_of::<*const u8>());
        assert_eq!(size_of::<GreenToken>(),         size_of::<*const u8>());
        assert_eq!(size_of::<GreenNodeHead>(),      size_of::<u32>() * 3);
        assert_eq!(size_of::<GreenTokenData>(),     size_of::<u32>() * 3);
        assert_eq!(size_of::<GreenElement>(),       size_of::<*const u8>() * 2);
        assert_eq!(size_of::<PackedGreenElement>(), size_of::<*const u8>());
    }
}
