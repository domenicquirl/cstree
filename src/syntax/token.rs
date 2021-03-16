use std::{
    fmt::{self, Write},
    hash::{Hash, Hasher},
    iter,
};

use lasso::Resolver;
use text_size::{TextRange, TextSize};

use super::*;
use crate::{Direction, GreenNode, GreenToken, Language, SyntaxKind};

/// Syntax tree token.
pub struct SyntaxToken<L: Language, D: 'static = (), R: 'static = ()> {
    parent: SyntaxNode<L, D, R>,
    index:  u32,
    offset: TextSize,
}

impl<L: Language, D, R> Clone for SyntaxToken<L, D, R> {
    fn clone(&self) -> Self {
        Self {
            parent: self.parent.clone(),
            index:  self.index,
            offset: self.offset,
        }
    }
}

impl<L: Language, D, R> Hash for SyntaxToken<L, D, R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.parent.hash(state);
        self.index.hash(state);
        self.offset.hash(state);
    }
}

impl<L: Language, D, R> PartialEq for SyntaxToken<L, D, R> {
    fn eq(&self, other: &SyntaxToken<L, D, R>) -> bool {
        self.parent == other.parent && self.index == other.index && self.offset == other.offset
    }
}

impl<L: Language, D, R> Eq for SyntaxToken<L, D, R> {}

impl<L: Language, D, R> SyntaxToken<L, D, R> {
    #[allow(missing_docs)]
    pub fn debug(&self, resolver: &impl Resolver) -> String {
        let mut res = String::new();
        write!(res, "{:?}@{:?}", self.kind(), self.text_range()).unwrap();
        if self.resolve_text(resolver).len() < 25 {
            write!(res, " {:?}", self.resolve_text(resolver)).unwrap();
            return res;
        }
        let text = self.resolve_text(resolver);
        for idx in 21..25 {
            if text.is_char_boundary(idx) {
                let text = format!("{} ...", &text[..idx]);
                write!(res, " {:?}", text).unwrap();
                return res;
            }
        }
        unreachable!()
    }

    #[allow(missing_docs)]
    pub fn display(&self, resolver: &impl Resolver) -> String {
        self.resolve_text(resolver).to_string()
    }
}

impl<L: Language, D, R> SyntaxToken<L, D, R> {
    pub(super) fn new(parent: &SyntaxNode<L, D, R>, index: u32, offset: TextSize) -> SyntaxToken<L, D, R> {
        Self {
            parent: parent.clone_uncounted(),
            index,
            offset,
        }
    }

    /// Returns a green tree, equal to the green tree this token
    /// belongs two, except with this token substitute. The complexity
    /// of operation is proportional to the depth of the tree
    pub fn replace_with(&self, replacement: GreenToken) -> GreenNode {
        assert_eq!(self.syntax_kind(), replacement.kind());
        let mut replacement = Some(replacement);
        let parent = self.parent();
        let me = self.index;

        let children = parent.green().children().enumerate().map(|(i, child)| {
            if i as u32 == me {
                replacement.take().unwrap().into()
            } else {
                child.cloned()
            }
        });
        let new_parent = GreenNode::new(parent.syntax_kind(), children);
        parent.replace_with(new_parent)
    }

    /// The internal representation of the kind of this token.
    #[inline]
    pub fn syntax_kind(&self) -> SyntaxKind {
        self.green().kind()
    }

    /// The kind of this token in terms of your language.
    #[inline]
    pub fn kind(&self) -> L::Kind {
        L::kind_from_raw(self.syntax_kind())
    }

    /// The range this token covers in the source text, in bytes.
    #[inline]
    pub fn text_range(&self) -> TextRange {
        TextRange::at(self.offset, self.green().text_len())
    }

    /// Uses the provided resolver to return the source text of this token.
    #[inline]
    pub fn resolve_text<'i, I>(&self, resolver: &'i I) -> &'i str
    where
        I: Resolver + ?Sized,
    {
        self.green().text(resolver)
    }

    /// Returns the unterlying green tree token of this token.
    pub fn green(&self) -> &GreenToken {
        self.parent
            .green()
            .children()
            .nth(self.index as usize)
            .unwrap()
            .as_token()
            .unwrap()
    }

    /// The parent node of this token.
    #[inline]
    pub fn parent(&self) -> &SyntaxNode<L, D, R> {
        &self.parent
    }

    /// Returns an iterator along the chain of parents of this token.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<L, D, R>> {
        self.parent().ancestors()
    }

    /// The tree element to the right of this one, i.e. the next child of this token's parent after this token.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        self.parent()
            .next_child_or_token_after(self.index as usize, self.text_range().end())
    }

    /// The tree element to the left of this one, i.e. the previous child of this token's parent after this token.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D, R>> {
        self.parent()
            .prev_child_or_token_before(self.index as usize, self.text_range().start())
    }

    /// Returns an iterator over all siblings of this token in the given `direction`, i.e. all of this
    /// token's parent's children from this token on to the left or the right.
    /// The first item in the iterator will always be this token.
    #[inline]
    pub fn siblings_with_tokens(&self, direction: Direction) -> impl Iterator<Item = SyntaxElementRef<'_, L, D, R>> {
        let me: SyntaxElementRef<'_, L, D, R> = self.into();
        iter::successors(Some(me), move |el| match direction {
            Direction::Next => el.next_sibling_or_token(),
            Direction::Prev => el.prev_sibling_or_token(),
        })
    }

    /// Returns the next token in the tree.
    /// This is not necessary a direct sibling of this token, but will always be further right in the tree.
    pub fn next_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self.next_sibling_or_token() {
            Some(element) => element.first_token(),
            None => self
                .parent()
                .ancestors()
                .find_map(|it| it.next_sibling_or_token())
                .and_then(|element| element.first_token()),
        }
    }

    /// Returns the previous token in the tree.
    /// This is not necessary a direct sibling of this token, but will always be further left in the tree.
    pub fn prev_token(&self) -> Option<&SyntaxToken<L, D, R>> {
        match self.prev_sibling_or_token() {
            Some(element) => element.last_token(),
            None => self
                .parent()
                .ancestors()
                .find_map(|it| it.prev_sibling_or_token())
                .and_then(|element| element.last_token()),
        }
    }
}

impl<L: Language, D, R> SyntaxToken<L, D, R>
where
    R: Resolver,
{
    /// Uses the resolver associated with this tree to return the source text of this token.
    #[inline]
    pub fn text(&self) -> &str {
        self.green().text(self.parent().resolver().as_ref())
    }
}

impl<L: Language, D, R> fmt::Debug for SyntaxToken<L, D, R>
where
    R: Resolver,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::debug(self, self.parent().resolver().as_ref()))
    }
}

impl<L: Language, D, R> fmt::Display for SyntaxToken<L, D, R>
where
    R: Resolver,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", Self::display(self, self.parent().resolver().as_ref()))
    }
}
