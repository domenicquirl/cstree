use std::{fmt, hash, mem::ManuallyDrop, ptr};

use crate::{
    green::SyntaxKind,
    interning::{Key, Resolver},
    TextSize,
};
use sptr::Strict;
use triomphe::Arc;

#[repr(align(2))] // to use 1 bit for pointer tagging. NB: this is an at-least annotation
#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub(super) struct GreenTokenData {
    pub(super) kind:     SyntaxKind,
    pub(super) text:     Option<Key>,
    pub(super) text_len: TextSize,
}

/// Leaf node in the immutable "green" tree.
pub struct GreenToken {
    ptr: ptr::NonNull<GreenTokenData>,
}

unsafe impl Send for GreenToken {} // where GreenTokenData: Send + Sync
unsafe impl Sync for GreenToken {} // where GreenTokenData: Send + Sync

pub(super) const IS_TOKEN_TAG: usize = 0x1;
impl GreenToken {
    fn add_tag(ptr: ptr::NonNull<GreenTokenData>) -> ptr::NonNull<GreenTokenData> {
        unsafe {
            let ptr = ptr.as_ptr().map_addr(|addr| addr | IS_TOKEN_TAG);
            ptr::NonNull::new_unchecked(ptr)
        }
    }

    fn remove_tag(ptr: ptr::NonNull<GreenTokenData>) -> ptr::NonNull<GreenTokenData> {
        unsafe {
            let ptr = ptr.as_ptr().map_addr(|addr| addr & !IS_TOKEN_TAG);
            ptr::NonNull::new_unchecked(ptr)
        }
    }

    fn data(&self) -> &GreenTokenData {
        unsafe { &*Self::remove_tag(self.ptr).as_ptr() }
    }

    /// Creates a new Token.
    #[inline]
    pub(super) fn new(data: GreenTokenData) -> GreenToken {
        let ptr = Arc::into_raw(Arc::new(data));
        let ptr = ptr::NonNull::new(ptr as *mut _).unwrap();
        GreenToken {
            ptr: Self::add_tag(ptr),
        }
    }

    /// [`SyntaxKind`] of this Token.
    #[inline]
    pub fn kind(&self) -> SyntaxKind {
        self.data().kind
    }

    /// The original source text of this Token.
    #[inline]
    pub fn text<'i, I>(&self, resolver: &'i I) -> Option<&'i str>
    where
        I: Resolver + ?Sized,
    {
        self.data().text.map(|key| resolver.resolve(&key))
    }

    /// Returns the length of text covered by this token.
    #[inline]
    pub fn text_len(&self) -> TextSize {
        self.data().text_len
    }

    /// Returns the interned key of text covered by this token.
    /// This key may be used for comparisons with other keys of strings interned by the same interner.
    ///
    /// See also [`text`](GreenToken::text).
    #[inline]
    pub fn text_key(&self) -> Option<Key> {
        self.data().text
    }
}

impl fmt::Debug for GreenToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let data = self.data();
        f.debug_struct("GreenToken")
            .field("kind", &data.kind)
            .field("text", &data.text)
            .finish()
    }
}

impl Clone for GreenToken {
    fn clone(&self) -> Self {
        let ptr = Self::remove_tag(self.ptr);
        let ptr = unsafe {
            let arc = ManuallyDrop::new(Arc::from_raw(ptr.as_ptr()));
            Arc::into_raw(Arc::clone(&arc))
        };
        let ptr = unsafe { ptr::NonNull::new_unchecked(ptr as *mut _) };
        GreenToken {
            ptr: Self::add_tag(ptr),
        }
    }
}

impl Eq for GreenToken {}
impl PartialEq for GreenToken {
    fn eq(&self, other: &Self) -> bool {
        self.data() == other.data()
    }
}

impl hash::Hash for GreenToken {
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        self.data().hash(state)
    }
}

impl Drop for GreenToken {
    fn drop(&mut self) {
        unsafe {
            Arc::from_raw(Self::remove_tag(self.ptr).as_ptr());
        }
    }
}
