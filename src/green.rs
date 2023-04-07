//! Implementation of the inner, "green" tree.
//! The [`GreenNodeBuilder`](crate::build::GreenNodeBuilder) from the [`build` module](crate::build) is the main entry
//! point to constructing [`GreenNode`]s and [`GreenToken`]s.

pub(super) mod builder;
mod element;
mod iter;
mod node;
mod token;

pub(crate) use self::element::GreenElementRef;
use self::element::{GreenElement, PackedGreenElement};

pub use self::{iter::GreenNodeChildren, node::GreenNode, token::GreenToken};

#[cfg(test)]
mod tests {
    use super::*;
    use node::GreenNodeHead;
    use token::GreenTokenData;

    #[test]
    #[cfg_attr(miri, ignore)]
    fn assert_send_sync() {
        fn f<T: Send + Sync>() {}
        f::<GreenNode>();
        f::<GreenToken>();
        f::<GreenElement>();
        f::<PackedGreenElement>();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
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
