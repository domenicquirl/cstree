use std::collections::{HashMap, VecDeque};

use cstree::interning::{new_interner, Interner, Resolver as _, TokenInterner, TokenKey};
use fxhash::{FxBuildHasher, FxHashMap};

use super::{Span, Token, TokenSource};

#[derive(Debug)]
pub struct TextTokenSource<T, I = TokenInterner> {
    tokens: VecDeque<T>,
    furthest_position: u32,
    ident_map: FxHashMap<Span, TokenKey>,
    idents: I,
}

impl<T> TextTokenSource<T>
where
    T: Token,
{
    pub fn new(input: &str, tokens: &[T]) -> Self {
        let idents = new_interner();
        Self::with_interner(tokens, input, idents)
    }
}

impl<T, I> TextTokenSource<T, I>
where
    T: Token,
    I: Interner,
{
    pub fn with_interner(tokens: &[T], input: &str, mut idents: I) -> Self {
        let mut ident_map = HashMap::with_capacity_and_hasher(tokens.len() / 2, FxBuildHasher::default());
        let mut my_tokens = VecDeque::with_capacity(tokens.len());
        my_tokens.extend(
            tokens
                .iter()
                // skip trivia so we don't have to worry about them during parser
                .filter(|&token| !token.is_trivia())
                .inspect(|&token| {
                    if token.is_ident() {
                        // remember identifiers so we can resolve them later
                        let name = idents.get_or_intern(token.get_text(input));
                        ident_map.insert(token.span(), name);
                    }
                }),
        );
        Self {
            tokens: my_tokens,
            furthest_position: 0,
            ident_map,
            idents,
        }
    }
}

impl<T: Token> TokenSource<T> for TextTokenSource<T> {
    fn next(&mut self) -> Option<T> {
        self.tokens.pop_front().map(|token| {
            self.furthest_position = u32::max(self.furthest_position, token.span().end);
            token
        })
    }

    fn advance_n(&mut self, n: usize) {
        if let Some(last) = self.tokens.drain(..n).last() {
            self.furthest_position = u32::max(self.furthest_position, last.span().end);
        }
    }

    fn peek(&self, n: usize) -> Option<T> {
        assert!(n > 0);
        self.tokens.get(n - 1).copied()
    }

    fn resolve_ident(&self, ident: T) -> &str {
        self.idents.resolve(
            self.ident_map
                .get(&ident.span())
                .copied()
                .unwrap_or_else(|| panic!("Unknown identifier: {:?}", ident)),
        )
    }

    #[inline]
    fn size_hint(&self) -> Option<usize> {
        // we will at least see each token. for nodes, we will enter and exit them. approximate:
        Some(2 * self.tokens.len())
    }
}

impl<T, I> TextTokenSource<T, I> {
    /// The end of the latest span of any token that has been consumed from the source.
    /// This will be the maximal end byte index of tokens produced by [`next`] or skipped over using [`advance_n`], but
    /// **does not include** tokens that were [`peek`]ed.
    ///
    /// [`next`]: TokenSource::next
    /// [`advance_n`]: TokenSource::advance_n
    /// [`peek`]: TokenSource::peek
    pub fn furthest_position(&self) -> u32 {
        self.furthest_position
    }
}
