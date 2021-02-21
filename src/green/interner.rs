use std::num::NonZeroUsize;

use fxhash::FxBuildHasher;
use lasso::{Capacity, Interner, IntoReader, IntoReaderAndResolver, IntoResolver, Reader, Resolver, Rodeo, Spur};

/// The default [`Interner`] used to deduplicate green token strings.
pub struct TokenInterner {
    rodeo: Rodeo<Spur, FxBuildHasher>,
}

impl TokenInterner {
    pub(super) fn new() -> Self {
        Self {
            rodeo: Rodeo::with_capacity_and_hasher(
                // capacity values suggested by author of `lasso`
                Capacity::new(512, unsafe { NonZeroUsize::new_unchecked(4096) }),
                FxBuildHasher::default(),
            ),
        }
    }
}

impl Resolver for TokenInterner {
    #[inline]
    fn resolve<'a>(&'a self, key: &Spur) -> &'a str {
        self.rodeo.resolve(key)
    }

    #[inline]
    fn try_resolve<'a>(&'a self, key: &Spur) -> Option<&'a str> {
        self.rodeo.try_resolve(key)
    }

    #[inline]
    unsafe fn resolve_unchecked<'a>(&'a self, key: &Spur) -> &'a str {
        self.rodeo.resolve_unchecked(key)
    }

    #[inline]
    fn contains_key(&self, key: &Spur) -> bool {
        self.rodeo.contains_key(key)
    }

    #[inline]
    fn len(&self) -> usize {
        self.rodeo.len()
    }
}

impl Reader for TokenInterner {
    #[inline]
    fn get(&self, val: &str) -> Option<Spur> {
        self.rodeo.get(val)
    }

    #[inline]
    fn contains(&self, val: &str) -> bool {
        self.rodeo.contains(val)
    }
}

impl IntoResolver for TokenInterner {
    type Resolver = <Rodeo<Spur, FxBuildHasher> as IntoResolver>::Resolver;

    #[inline]
    fn into_resolver(self) -> Self::Resolver
    where
        Self: 'static,
    {
        self.rodeo.into_resolver()
    }

    #[inline]
    fn into_resolver_boxed(self: Box<Self>) -> Self::Resolver
    where
        Self: 'static,
    {
        Rodeo::<Spur, FxBuildHasher>::into_resolver_boxed(Box::new(self.rodeo))
    }
}

impl Interner for TokenInterner {
    #[inline]
    fn get_or_intern(&mut self, val: &str) -> Spur {
        self.rodeo.get_or_intern(val)
    }

    #[inline]
    fn try_get_or_intern(&mut self, val: &str) -> lasso::LassoResult<Spur> {
        self.rodeo.try_get_or_intern(val)
    }

    #[inline]
    fn get_or_intern_static(&mut self, val: &'static str) -> Spur {
        self.rodeo.get_or_intern_static(val)
    }

    #[inline]
    fn try_get_or_intern_static(&mut self, val: &'static str) -> lasso::LassoResult<Spur> {
        self.rodeo.try_get_or_intern_static(val)
    }
}

impl IntoReader for TokenInterner {
    type Reader = <Rodeo<Spur, FxBuildHasher> as IntoReader>::Reader;

    #[inline]
    fn into_reader(self) -> Self::Reader
    where
        Self: 'static,
    {
        self.rodeo.into_reader()
    }

    fn into_reader_boxed(self: Box<Self>) -> Self::Reader
    where
        Self: 'static,
    {
        Rodeo::<Spur, FxBuildHasher>::into_reader_boxed(Box::new(self.rodeo))
    }
}

impl IntoReaderAndResolver for TokenInterner {}
