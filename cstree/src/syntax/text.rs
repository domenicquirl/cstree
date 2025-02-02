//! Efficient representation of the source text that is covered by a [`SyntaxNode`].

use std::fmt;

use crate::{
    interning::{Resolver, TokenKey},
    syntax::{SyntaxNode, SyntaxToken},
    text::{TextRange, TextSize},
    Syntax,
};

/// An efficient representation of the text that is covered by a [`SyntaxNode`], i.e. the combined
/// source text of all tokens that are descendants of the node.
///
/// Offers methods to work with the text distributed across multiple [`SyntaxToken`]s while avoiding
/// the construction of intermediate strings where possible.
/// This includes efficient comparisons with itself and with strings and conversion `to_string()`.
///
/// # Example
/// ```
/// # use cstree::testing::*;
/// # use cstree::syntax::ResolvedNode;
/// #
/// fn parse_float_literal(s: &str) -> ResolvedNode<MySyntax> {
///     // parsing...
/// #     let mut builder: GreenNodeBuilder<MySyntax> = GreenNodeBuilder::new();
/// #     builder.start_node(Float);
/// #     builder.token(Float, s);
/// #     builder.finish_node();
/// #     let (root, cache) = builder.finish();
/// #     let resolver = cache.unwrap().into_interner().unwrap();
/// #     SyntaxNode::new_root_with_resolver(root, resolver)
/// }
/// let float_node = parse_float_literal("2.748E2");
/// let text = float_node.text();
/// assert_eq!(text.len(), 7.into());
/// assert!(text.contains_char('E'));
/// assert_eq!(text.find_char('E'), Some(5.into()));
/// assert_eq!(text.char_at(1.into()), Some('.'));
/// let sub = text.slice(2.into()..5.into());
/// assert_eq!(sub, "748");
/// ```
#[derive(Clone)]
pub struct SyntaxText<'n, 'i, I: ?Sized, S: Syntax, D: 'static = ()> {
    node:     &'n SyntaxNode<S, D>,
    range:    TextRange,
    resolver: &'i I,
}

impl<'n, 'i, I: Resolver<TokenKey> + ?Sized, S: Syntax, D> SyntaxText<'n, 'i, I, S, D> {
    pub(crate) fn new(node: &'n SyntaxNode<S, D>, resolver: &'i I) -> Self {
        let range = node.text_range();
        SyntaxText { node, range, resolver }
    }

    /// The combined length of this text, in bytes.
    pub fn len(&self) -> TextSize {
        self.range.len()
    }

    /// Returns `true` if [`self.len()`](SyntaxText::len) is zero.
    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    /// Returns `true` if `c` appears anywhere in this text.
    pub fn contains_char(&self, c: char) -> bool {
        self.try_for_each_chunk(|chunk| if chunk.contains(c) { Err(()) } else { Ok(()) })
            .is_err()
    }

    /// If `self.contains_char(c)`, returns `Some(pos)`, where `pos` is the byte position of the
    /// first appearance of `c`. Otherwise, returns `None`.
    pub fn find_char(&self, c: char) -> Option<TextSize> {
        let mut acc: TextSize = 0.into();
        let res = self.try_for_each_chunk(|chunk| {
            if let Some(pos) = chunk.find(c) {
                let pos: TextSize = (pos as u32).into();
                return Err(acc + pos);
            }
            acc += TextSize::of(chunk);
            Ok(())
        });
        found(res)
    }

    /// If `offset < self.len()`, returns `Some(c)`, where `c` is the first `char` at or after
    /// `offset` (in bytes). Otherwise, returns `None`.
    pub fn char_at(&self, offset: TextSize) -> Option<char> {
        let mut start: TextSize = 0.into();
        let res = self.try_for_each_chunk(|chunk| {
            let end = start + TextSize::of(chunk);
            if start <= offset && offset < end {
                let off: usize = u32::from(offset - start) as usize;
                return Err(chunk[off..].chars().next().unwrap());
            }
            start = end;
            Ok(())
        });
        found(res)
    }

    /// Indexes this text by the given `range` and returns a `SyntaxText` that represents the
    /// corresponding slice of this text.
    ///
    /// # Panics
    /// The end of `range` must be equal of higher than its start.
    /// Further, `range` must be contained within `0..self.len()`.
    pub fn slice<Ra: private::SyntaxTextRange>(&self, range: Ra) -> Self {
        let start = range.start().unwrap_or_default();
        let end = range.end().unwrap_or_else(|| self.len());
        assert!(start <= end);
        let len = end - start;
        let start = self.range.start() + start;
        let end = start + len;
        assert!(
            start <= end,
            "invalid slice, range: {:?}, slice: {:?}",
            self.range,
            (range.start(), range.end()),
        );
        let range = TextRange::new(start, end);
        assert!(
            self.range.contains_range(range),
            "invalid slice, range: {:?}, slice: {:?}",
            self.range,
            range,
        );
        SyntaxText {
            node: self.node,
            range,
            resolver: self.resolver,
        }
    }

    /// Applies the given function to text chunks (from [`SyntaxToken`]s) that are part of this text
    /// as long as it returns `Ok`, starting from the initial value `init`.
    ///
    /// If `f` returns `Err`, the error is propagated immediately.
    /// Otherwise, the result of the current call to `f` will be passed to the invocation of `f` on
    /// the next token, producing a final value if `f` succeeds on all chunks.
    ///
    /// See also [`fold_chunks`](SyntaxText::fold_chunks) for folds that always succeed.
    pub fn try_fold_chunks<T, F, E>(&self, init: T, mut f: F) -> Result<T, E>
    where
        F: FnMut(T, &str) -> Result<T, E>,
    {
        self.tokens_with_ranges().try_fold(init, move |acc, (token, range)| {
            f(acc, &token.resolve_text(self.resolver)[range])
        })
    }

    /// Applies the given function to all text chunks (from [`SyntaxToken`]s) that are part of this
    /// text, starting from the initial value `init`.
    ///
    /// The result of the current call to `f` will be passed to the invocation of `f` on the next
    /// token, producing a final value after `f` was called on all chunks.
    ///
    /// See also [`try_fold_chunks`](SyntaxText::try_fold_chunks), which performs the same operation
    /// for fallible functions `f`.
    pub fn fold_chunks<T, F>(&self, init: T, mut f: F) -> T
    where
        F: FnMut(T, &str) -> T,
    {
        enum Void {}
        match self.try_fold_chunks(init, |acc, chunk| Ok::<T, Void>(f(acc, chunk))) {
            Ok(t) => t,
            Err(void) => match void {},
        }
    }

    /// Applies the given function to all text chunks that this text is comprised of, in order,
    /// as long as `f` completes successfully.
    ///
    /// If `f` returns `Err`, this method returns immediately and will not apply `f` to any further
    /// chunks.
    ///
    /// See also [`try_fold_chunks`](SyntaxText::try_fold_chunks).
    pub fn try_for_each_chunk<F: FnMut(&str) -> Result<(), E>, E>(&self, mut f: F) -> Result<(), E> {
        self.try_fold_chunks((), move |(), chunk| f(chunk))
    }

    /// Applies the given function to all text chunks that this text is comprised of, in order.
    ///
    /// See also [`fold_chunks`](SyntaxText::fold_chunks),
    /// [`try_for_each_chunk`](SyntaxText::try_for_each_chunk).
    pub fn for_each_chunk<F: FnMut(&str)>(&self, mut f: F) {
        self.fold_chunks((), |(), chunk| f(chunk))
    }

    fn tokens_with_ranges(&self) -> impl Iterator<Item = (&SyntaxToken<S, D>, TextRange)> {
        let text_range = self.range;
        self.node
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter_map(move |token| {
                let token_range = token.text_range();
                let range = text_range.intersect(token_range)?;
                Some((token, range - token_range.start()))
            })
    }
}

fn found<T>(res: Result<(), T>) -> Option<T> {
    match res {
        Ok(()) => None,
        Err(it) => Some(it),
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> fmt::Debug for SyntaxText<'_, '_, I, S, D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.to_string(), f)
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> fmt::Display for SyntaxText<'_, '_, I, S, D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.try_for_each_chunk(|chunk| fmt::Display::fmt(chunk, f))
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> From<SyntaxText<'_, '_, I, S, D>> for String {
    fn from(text: SyntaxText<'_, '_, I, S, D>) -> String {
        text.to_string()
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> PartialEq<str> for SyntaxText<'_, '_, I, S, D> {
    fn eq(&self, mut rhs: &str) -> bool {
        self.try_for_each_chunk(|chunk| {
            if !rhs.starts_with(chunk) {
                return Err(());
            }
            rhs = &rhs[chunk.len()..];
            Ok(())
        })
        .is_ok()
            && rhs.is_empty()
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> PartialEq<SyntaxText<'_, '_, I, S, D>> for str {
    fn eq(&self, rhs: &SyntaxText<'_, '_, I, S, D>) -> bool {
        rhs == self
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> PartialEq<&'_ str> for SyntaxText<'_, '_, I, S, D> {
    fn eq(&self, rhs: &&str) -> bool {
        self == *rhs
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> PartialEq<SyntaxText<'_, '_, I, S, D>> for &'_ str {
    fn eq(&self, rhs: &SyntaxText<'_, '_, I, S, D>) -> bool {
        rhs == self
    }
}

impl<I1, I2, S1, S2, D1, D2> PartialEq<SyntaxText<'_, '_, I2, S2, D2>> for SyntaxText<'_, '_, I1, S1, D1>
where
    S1: Syntax,
    S2: Syntax,
    I1: Resolver<TokenKey> + ?Sized,
    I2: Resolver<TokenKey> + ?Sized,
{
    fn eq(&self, other: &SyntaxText<'_, '_, I2, S2, D2>) -> bool {
        if self.range.len() != other.range.len() {
            return false;
        }
        let mut lhs = self.tokens_with_ranges();
        let mut rhs = other.tokens_with_ranges();
        zip_texts(&mut lhs, &mut rhs, self.resolver, other.resolver).is_none()
            && lhs.all(|it| it.1.is_empty())
            && rhs.all(|it| it.1.is_empty())
    }
}

fn zip_texts<'it1, 'it2, It1, It2, I1, I2, S1, S2, D1, D2>(
    xs: &mut It1,
    ys: &mut It2,
    resolver_x: &I1,
    resolver_y: &I2,
) -> Option<()>
where
    It1: Iterator<Item = (&'it1 SyntaxToken<S1, D1>, TextRange)>,
    It2: Iterator<Item = (&'it2 SyntaxToken<S2, D2>, TextRange)>,
    I1: Resolver<TokenKey> + ?Sized,
    I2: Resolver<TokenKey> + ?Sized,
    D1: 'static,
    D2: 'static,
    S1: Syntax + 'it1,
    S2: Syntax + 'it2,
{
    let mut x = xs.next()?;
    let mut y = ys.next()?;
    loop {
        while x.1.is_empty() {
            x = xs.next()?;
        }
        while y.1.is_empty() {
            y = ys.next()?;
        }
        let x_text = &x.0.resolve_text(resolver_x)[x.1];
        let y_text = &y.0.resolve_text(resolver_y)[y.1];
        if !(x_text.starts_with(y_text) || y_text.starts_with(x_text)) {
            return Some(());
        }
        let advance = std::cmp::min(x.1.len(), y.1.len());
        x.1 = TextRange::new(x.1.start() + advance, x.1.end());
        y.1 = TextRange::new(y.1.start() + advance, y.1.end());
    }
}

impl<I: Resolver<TokenKey> + ?Sized, S: Syntax, D> Eq for SyntaxText<'_, '_, I, S, D> {}

mod private {
    use std::ops;

    use crate::text::{TextRange, TextSize};

    pub trait SyntaxTextRange {
        fn start(&self) -> Option<TextSize>;
        fn end(&self) -> Option<TextSize>;
    }

    impl SyntaxTextRange for TextRange {
        fn start(&self) -> Option<TextSize> {
            Some(TextRange::start(*self))
        }

        fn end(&self) -> Option<TextSize> {
            Some(TextRange::end(*self))
        }
    }

    impl SyntaxTextRange for ops::Range<TextSize> {
        fn start(&self) -> Option<TextSize> {
            Some(self.start)
        }

        fn end(&self) -> Option<TextSize> {
            Some(self.end)
        }
    }

    impl SyntaxTextRange for ops::RangeFrom<TextSize> {
        fn start(&self) -> Option<TextSize> {
            Some(self.start)
        }

        fn end(&self) -> Option<TextSize> {
            None
        }
    }

    impl SyntaxTextRange for ops::RangeTo<TextSize> {
        fn start(&self) -> Option<TextSize> {
            None
        }

        fn end(&self) -> Option<TextSize> {
            Some(self.end)
        }
    }

    impl SyntaxTextRange for ops::RangeFull {
        fn start(&self) -> Option<TextSize> {
            None
        }

        fn end(&self) -> Option<TextSize> {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{build::GreenNodeBuilder, RawSyntaxKind};

    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    #[repr(transparent)]
    pub struct SyntaxKind(u32);

    impl Syntax for SyntaxKind {
        fn from_raw(raw: RawSyntaxKind) -> Self {
            Self(raw.0)
        }

        fn into_raw(self) -> RawSyntaxKind {
            RawSyntaxKind(self.0)
        }

        fn static_text(self) -> Option<&'static str> {
            match self.0 {
                1 => Some("{"),
                2 => Some("}"),
                _ => None,
            }
        }
    }

    fn build_tree(chunks: &[&str]) -> (SyntaxNode<SyntaxKind, ()>, impl Resolver<TokenKey>) {
        let mut builder: GreenNodeBuilder<SyntaxKind> = GreenNodeBuilder::new();
        builder.start_node(SyntaxKind(62));
        for &chunk in chunks.iter() {
            let kind = match chunk {
                "{" => 1,
                "}" => 2,
                _ => 3,
            };
            builder.token(SyntaxKind(kind), chunk);
        }
        builder.finish_node();
        let (node, cache) = builder.finish();
        (SyntaxNode::new_root(node), cache.unwrap().into_interner().unwrap())
    }

    #[test]
    fn test_text_equality() {
        fn do_check(t1: &[&str], t2: &[&str]) {
            let (t1, resolver) = build_tree(t1);
            let t1 = t1.resolve_text(&resolver);
            let (t2, resolver) = build_tree(t2);
            let t2 = t2.resolve_text(&resolver);
            let expected = t1.to_string() == t2.to_string();
            let actual = t1 == t2;
            assert_eq!(expected, actual, "`{}` (SyntaxText) `{}` (SyntaxText)", t1, t2);
            let actual = t1 == t2.to_string().as_str();
            assert_eq!(expected, actual, "`{}` (SyntaxText) `{}` (&str)", t1, t2);
        }
        fn check(t1: &[&str], t2: &[&str]) {
            do_check(t1, t2);
            do_check(t2, t1)
        }

        check(&[""], &[""]);
        check(&["a"], &[""]);
        check(&["a"], &["a"]);
        check(&["abc"], &["def"]);
        check(&["hello", "world"], &["hello", "world"]);
        check(&["hellowo", "rld"], &["hell", "oworld"]);
        check(&["hel", "lowo", "rld"], &["helloworld"]);
        check(&["{", "abc", "}"], &["{", "123", "}"]);
        check(&["{", "abc", "}", "{"], &["{", "123", "}"]);
        check(&["{", "abc", "}"], &["{", "123", "}", "{"]);
        check(&["{", "abc", "}ab"], &["{", "abc", "}", "ab"]);
    }
}
