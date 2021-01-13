use std::fmt;

use crate::{interning::Resolver, Language, SyntaxNode, SyntaxToken, TextRange, TextSize};

#[derive(Clone)]
pub struct SyntaxText<'n, 'i, I: ?Sized, L: Language, D: 'static = ()> {
    node:     &'n SyntaxNode<L, D>,
    range:    TextRange,
    resolver: &'i I,
}

impl<'n, 'i, I: Resolver + ?Sized, L: Language, D> SyntaxText<'n, 'i, I, L, D> {
    pub(crate) fn new(node: &'n SyntaxNode<L, D>, resolver: &'i I) -> Self {
        let range = node.text_range();
        SyntaxText { node, range, resolver }
    }

    pub fn len(&self) -> TextSize {
        self.range.len()
    }

    pub fn is_empty(&self) -> bool {
        self.range.is_empty()
    }

    pub fn contains_char(&self, c: char) -> bool {
        self.try_for_each_chunk(|chunk| if chunk.contains(c) { Err(()) } else { Ok(()) })
            .is_err()
    }

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

    pub fn char_at(&self, offset: TextSize) -> Option<char> {
        let offset = offset.into();
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

    pub fn slice<R: private::SyntaxTextRange>(&self, range: R) -> Self {
        let start = range.start().unwrap_or_default();
        let end = range.end().unwrap_or(self.len());
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

    pub fn try_fold_chunks<T, F, E>(&self, init: T, mut f: F) -> Result<T, E>
    where
        F: FnMut(T, &str) -> Result<T, E>,
    {
        self.tokens_with_ranges().try_fold(init, move |acc, (token, range)| {
            f(acc, &token.text(self.resolver)[range])
        })
    }

    pub fn try_for_each_chunk<F: FnMut(&str) -> Result<(), E>, E>(&self, mut f: F) -> Result<(), E> {
        self.try_fold_chunks((), move |(), chunk| f(chunk))
    }

    pub fn for_each_chunk<F: FnMut(&str)>(&self, mut f: F) {
        enum Void {}
        match self.try_for_each_chunk(|chunk| Ok::<(), Void>(f(chunk))) {
            Ok(()) => (),
            Err(void) => match void {},
        }
    }

    fn tokens_with_ranges(&self) -> impl Iterator<Item = (&SyntaxToken<L, D>, TextRange)> {
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

impl<I: Resolver + ?Sized, L: Language, D> fmt::Debug for SyntaxText<'_, '_, I, L, D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.to_string(), f)
    }
}

impl<I: Resolver + ?Sized, L: Language, D> fmt::Display for SyntaxText<'_, '_, I, L, D> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.try_for_each_chunk(|chunk| fmt::Display::fmt(chunk, f))
    }
}

impl<I: Resolver + ?Sized, L: Language, D> From<SyntaxText<'_, '_, I, L, D>> for String {
    fn from(text: SyntaxText<'_, '_, I, L, D>) -> String {
        text.to_string()
    }
}

impl<I: Resolver + ?Sized, L: Language, D> PartialEq<str> for SyntaxText<'_, '_, I, L, D> {
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

impl<I: Resolver + ?Sized, L: Language, D> PartialEq<SyntaxText<'_, '_, I, L, D>> for str {
    fn eq(&self, rhs: &SyntaxText<'_, '_, I, L, D>) -> bool {
        rhs == self
    }
}

impl<I: Resolver + ?Sized, L: Language, D> PartialEq<&'_ str> for SyntaxText<'_, '_, I, L, D> {
    fn eq(&self, rhs: &&str) -> bool {
        self == *rhs
    }
}

impl<I: Resolver + ?Sized, L: Language, D> PartialEq<SyntaxText<'_, '_, I, L, D>> for &'_ str {
    fn eq(&self, rhs: &SyntaxText<'_, '_, I, L, D>) -> bool {
        rhs == self
    }
}

impl<'n1, 'i1, 'n2, 'i2, I1, I2, D1, D2, L1, L2> PartialEq<SyntaxText<'n2, 'i2, I2, L2, D2>>
    for SyntaxText<'n1, 'i1, I1, L1, D1>
where
    L1: Language,
    L2: Language,
    I1: Resolver + ?Sized,
    I2: Resolver + ?Sized,
{
    fn eq(&self, other: &SyntaxText<'_, '_, I2, L2, D2>) -> bool {
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

fn zip_texts<'it1, 'it2, It1, It2, I1, I2, L1, L2, D1, D2>(
    xs: &mut It1,
    ys: &mut It2,
    resolver_x: &I1,
    resolver_y: &I2,
) -> Option<()>
where
    It1: Iterator<Item = (&'it1 SyntaxToken<L1, D1>, TextRange)>,
    It2: Iterator<Item = (&'it2 SyntaxToken<L2, D2>, TextRange)>,
    I1: Resolver + ?Sized,
    I2: Resolver + ?Sized,
    D1: 'static,
    D2: 'static,
    L1: Language + 'it1,
    L2: Language + 'it2,
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
        let x_text = &x.0.text(resolver_x)[x.1];
        let y_text = &y.0.text(resolver_y)[y.1];
        if !(x_text.starts_with(y_text) || y_text.starts_with(x_text)) {
            return Some(());
        }
        let advance = std::cmp::min(x.1.len(), y.1.len());
        x.1 = TextRange::new(x.1.start() + advance, x.1.end());
        y.1 = TextRange::new(y.1.start() + advance, y.1.end());
    }
}

impl<I: Resolver + ?Sized, L: Language, D> Eq for SyntaxText<'_, '_, I, L, D> {}

mod private {
    use std::ops;

    use crate::{TextRange, TextSize};

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
    use crate::{green::SyntaxKind, GreenNodeBuilder};

    use super::*;

    #[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub enum TestLang {}
    impl Language for TestLang {
        type Kind = SyntaxKind;

        fn kind_from_raw(raw: SyntaxKind) -> Self::Kind {
            raw
        }

        fn kind_to_raw(kind: Self::Kind) -> SyntaxKind {
            kind
        }
    }

    fn build_tree(chunks: &[&str]) -> (SyntaxNode<TestLang, ()>, impl Resolver) {
        let mut builder = GreenNodeBuilder::new();
        builder.start_node(SyntaxKind(62));
        for &chunk in chunks.iter() {
            builder.token(SyntaxKind(92), chunk.into())
        }
        builder.finish_node();
        let (node, interner) = builder.finish();
        (SyntaxNode::new_root(node), interner.unwrap())
    }

    #[test]
    fn test_text_equality() {
        fn do_check(t1: &[&str], t2: &[&str]) {
            let (t1, resolver) = build_tree(t1);
            let t1 = t1.text(&resolver);
            let (t2, resolver) = build_tree(t2);
            let t2 = t2.text(&resolver);
            let expected = t1.to_string() == t2.to_string();
            let actual = t1 == t2;
            assert_eq!(expected, actual, "`{}` (SyntaxText) `{}` (SyntaxText)", t1, t2);
            let actual = t1 == &*t2.to_string();
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
