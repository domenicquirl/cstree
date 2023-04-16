//! Implementation of the outer, "red" tree.
//!
//! Inner [`SyntaxNode`]s represent only structural information, but can hold additional, user-defined data.
//! Leaf [`SyntaxToken`]s represent individual pieces of source text.
//! Use [`SyntaxNode::new_root`] and [`SyntaxNode::new_root_with_resolver`] to construct a syntax
//! tree on top of a green tree.

mod element;
pub use element::{SyntaxElement, SyntaxElementRef};
mod node;
pub use node::SyntaxNode;
mod token;
pub use token::SyntaxToken;
mod resolved;
pub use resolved::{ResolvedElement, ResolvedElementRef, ResolvedNode, ResolvedToken};
mod iter;
pub use iter::{SyntaxElementChildren, SyntaxNodeChildren};

mod text;
pub use text::SyntaxText;

// A note on `#[inline]` usage in this module:
// In `rowan`, there are two layers of `SyntaxXY`s: the `cursor` layer and the `api` layer.
// The `cursor` layer handles all of the actual methods on the tree, while the `api` layer is
// generic over the `Syntax` of the tree and otherwise forwards its implementation to the `cursor`
// layer.
// Here, we have unified the `cursor` and the `api` layer into the `syntax` layer.
// This means that all of our types here are generic over a `Syntax`, including the
// implementations which, in `rowan`, are part of the `cursor` layer.
// Very apparently, this makes the compiler less willing to inline. Almost every "regular use"
// method in this file has some kind of `#[inline]` annotation to counteract that. This is _NOT_
// just for fun, not inlining decreases tree traversal speed by approx. 50% at the time of writing
// this.
//
//   - DQ 01/2021

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::*;

    #[test]
    #[cfg_attr(miri, ignore)]
    fn assert_send_sync() {
        fn f<T: Send + Sync>() {}
        f::<SyntaxNode<TestSyntaxKind>>();
        f::<SyntaxToken<TestSyntaxKind>>();
        f::<SyntaxElement<TestSyntaxKind>>();
        f::<SyntaxElementRef<'static, TestSyntaxKind>>();

        f::<ResolvedNode<TestSyntaxKind>>();
        f::<ResolvedToken<TestSyntaxKind>>();
        f::<ResolvedElement<TestSyntaxKind>>();
        f::<ResolvedElementRef<'static, TestSyntaxKind>>();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[rustfmt::skip]
    fn assert_syntax_sizes() {
        use std::mem::size_of;

        assert_eq!(size_of::<SyntaxNode<TestSyntaxKind>>(),          size_of::<*const u8>());
        // verify niche opt of `NonNull`
        assert_eq!(size_of::<Option<SyntaxNode<TestSyntaxKind>>>(),  size_of::<*const u8>()); 
        // parent + child index + text len
        assert_eq!(size_of::<SyntaxToken<TestSyntaxKind>>(),         size_of::<SyntaxNode<TestSyntaxKind>>() + size_of::<u32>() * 2);
    }
}
