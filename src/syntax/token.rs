use std::{
    fmt,
    hash::{Hash, Hasher},
    iter,
    sync::Arc as StdArc,
};

use lasso::Resolver;
use text_size::{TextRange, TextSize};

use super::*;
use crate::{interning::Key, Direction, GreenNode, GreenToken, Language, SyntaxKind};

/// Syntax tree token.
#[derive(Debug)]
pub struct SyntaxToken<L: Language, D: 'static = ()> {
    parent: SyntaxNode<L, D>,
    index:  u32,
    offset: TextSize,
}

impl<L: Language, D> Clone for SyntaxToken<L, D> {
    fn clone(&self) -> Self {
        Self {
            parent: self.parent.clone(),
            index:  self.index,
            offset: self.offset,
        }
    }
}

impl<L: Language, D> Hash for SyntaxToken<L, D> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.parent.hash(state);
        self.index.hash(state);
        self.offset.hash(state);
    }
}

impl<L: Language, D> PartialEq for SyntaxToken<L, D> {
    fn eq(&self, other: &SyntaxToken<L, D>) -> bool {
        self.parent == other.parent && self.index == other.index && self.offset == other.offset
    }
}

impl<L: Language, D> Eq for SyntaxToken<L, D> {}

impl<L: Language, D> SyntaxToken<L, D> {
    /// Writes this token's [`Debug`](fmt::Debug) representation into the given `target`.
    pub fn write_debug<R>(&self, resolver: &R, target: &mut impl fmt::Write) -> fmt::Result
    where
        R: Resolver + ?Sized,
    {
        write!(target, "{:?}@{:?}", self.kind(), self.text_range())?;
        let text = self.resolve_text(resolver);
        if text.len() < 25 {
            return write!(target, " {:?}", text);
        }

        for idx in 21..25 {
            if text.is_char_boundary(idx) {
                let text = format!("{} ...", &text[..idx]);
                return write!(target, " {:?}", text);
            }
        }
        unreachable!()
    }

    /// Returns this token's [`Debug`](fmt::Debug) representation as a string.
    ///
    /// To avoid allocating for every token, see [`write_debug`](SyntaxToken::write_debug).
    #[inline]
    pub fn debug<R>(&self, resolver: &R) -> String
    where
        R: Resolver + ?Sized,
    {
        // NOTE: `fmt::Write` methods on `String` never fail
        let mut res = String::new();
        self.write_debug(resolver, &mut res).unwrap();
        res
    }

    /// Writes this token's [`Display`](fmt::Display) representation into the given `target`.
    #[inline]
    pub fn write_display<R>(&self, resolver: &R, target: &mut impl fmt::Write) -> fmt::Result
    where
        R: Resolver + ?Sized,
    {
        write!(target, "{}", self.resolve_text(resolver))
    }

    /// Returns this token's [`Display`](fmt::Display) representation as a string.
    ///
    /// To avoid allocating for every token, see [`write_display`](SyntaxToken::write_display).
    #[inline]
    pub fn display<R>(&self, resolver: &R) -> String
    where
        R: Resolver + ?Sized,
    {
        self.resolve_text(resolver).to_string()
    }

    /// If there is a resolver associated with this tree, returns it.
    #[inline]
    pub fn resolver(&self) -> Option<&StdArc<dyn Resolver>> {
        self.parent.resolver()
    }

    /// Turns this token into a [`ResolvedToken`], but only if there is a resolver associated with this tree.
    #[inline]
    pub fn try_resolved(&self) -> Option<&ResolvedToken<L, D>> {
        // safety: we only coerce if `resolver` exists
        self.resolver().map(|_| unsafe { ResolvedToken::coerce_ref(self) })
    }

    /// Turns this token into a [`ResolvedToken`].
    /// # Panics
    /// If there is no resolver associated with this tree.
    #[inline]
    pub fn resolved(&self) -> &ResolvedToken<L, D> {
        self.try_resolved().expect("tried to resolve a node without resolver")
    }
}

impl<L: Language, D> SyntaxToken<L, D> {
    pub(super) fn new(parent: &SyntaxNode<L, D>, index: u32, offset: TextSize) -> SyntaxToken<L, D> {
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
    ///
    /// If no text is explicitly associated with the token, returns its [`static_text`](SyntaxToken::static_text)
    /// instead.
    #[inline]
    pub fn resolve_text<'i, I>(&self, resolver: &'i I) -> &'i str
    where
        I: Resolver + ?Sized,
    {
        // one of the two must be present upon construction
        self.static_text().or_else(|| self.green().text(resolver)).unwrap()
    }

    /// If the syntax kind of this token always represents the same text, retrieve that text.
    ///
    /// # Examples
    /// If there is a `SyntaxKind::Plus` that represents just the `+` operator and we implement
    /// [`Language::static_text`] for it, we can retrieve this text in the resulting syntax tree. ```
    /// # use cstree::*;
    /// # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// # #[repr(u16)]
    /// # enum SyntaxKind {
    /// #     ROOT,
    /// #     IDENT,
    /// #     INT,
    /// #     OP,
    /// #     WS,
    /// # }
    /// # use SyntaxKind::*;
    /// # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// # enum Lang {}
    /// # impl cstree::Language for Lang {
    /// #     type Kind = SyntaxKind;
    /// #
    /// #     fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
    /// #         assert!(raw.0 <= SyntaxKind::WS as u16);
    /// #         unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    /// #     }
    /// #
    /// #     fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
    /// #         cstree::SyntaxKind(kind as u16)
    /// #     }
    /// #
    /// #     fn static_text(kind: Self::Kind) -> Option<&'static str> {
    /// #         match kind {
    /// #             OP => "+",
    /// #             _ => None,
    /// #         }
    /// #     }
    /// # }
    /// # type SyntaxNode<L> = cstree::SyntaxNode<L, ()>;
    /// # fn parse(b: &mut GreenNodeBuilder<Rodeo>, s: &str) {}
    /// #
    /// let mut builder = GreenNodeBuilder::new();
    /// # builder.start_node(ROOT);
    /// # builder.token_with_text(IDENT, "x");
    /// # builder.token_with_text(WS, " ");
    /// # builder.token(OP);
    /// # builder.token_with_text(WS, " ");
    /// # builder.token_with_text(INT, "3");
    /// # builder.finish_node();
    /// # let tree = SyntaxNode::<Lang>::new_root(builder.finish().0);
    /// let tree = parse(&mut builder, "x + 3");
    /// let plus = tree.children_with_tokens().nth(2).unwrap().into_token().unwrap();
    /// assert_eq!(plus.static_text(), Some("+"));
    /// ```
    #[inline(always)]
    pub fn static_text(&self) -> Option<&'static str> {
        L::static_text(self.kind())
    }

    /// Returns `true` if `self` and `other` represent equal source text.
    ///
    /// This method is different from the `PartialEq` and `Eq` implementations in that it compares
    /// only the token text and not its source position.
    /// It is more efficient than comparing the result of
    /// [`resolve_text`](SyntaxToken::resolve_text) because it compares the tokens' interned
    /// [`text_key`s](SyntaxToken::text_key) (if their text is not static) or their kind (if it is).
    /// Therefore, it also does not require a [`Resolver`].
    ///
    /// **Note** that the result of the comparison may be wrong when comparing two tokens from
    /// different trees that use different interners.
    ///  
    /// # Examples
    /// ```
    /// # use cstree::*;
    /// # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// # #[repr(u16)]
    /// # enum SyntaxKind {
    /// #     ROOT,
    /// #     IDENT,
    /// #     INT,
    /// #     OP,
    /// #     WS,
    /// # }
    /// # use SyntaxKind::*;
    /// # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// # enum Lang {}
    /// # impl cstree::Language for Lang {
    /// #     type Kind = SyntaxKind;
    /// #
    /// #     fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
    /// #         assert!(raw.0 <= SyntaxKind::WS as u16);
    /// #         unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    /// #     }
    /// #
    /// #     fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
    /// #         cstree::SyntaxKind(kind as u16)
    /// #     }
    /// #
    /// #     fn static_text(kind: Self::Kind) -> Option<&'static str> {
    /// #         match kind {
    /// #             OP => Some("+"),
    /// #             _ => None,
    /// #         }
    /// #     }
    /// # }
    /// # type SyntaxNode<L> = cstree::SyntaxNode<L, ()>;
    /// # fn parse(b: &mut GreenNodeBuilder<Rodeo>, s: &str) {}
    /// #
    /// let mut builder = GreenNodeBuilder::new();
    /// # builder.start_node(ROOT);
    /// # builder.token_with_text(IDENT, "x");
    /// # builder.token_with_text(WS, " ");
    /// # builder.token(OP);
    /// # builder.token_with_text(WS, " ");
    /// # builder.token_with_text(IDENT, "x");
    /// # builder.token_with_text(WS, " ");
    /// # builder.token(OP);
    /// # builder.token_with_text(INT, "3");
    /// # builder.finish_node();
    /// # let tree = SyntaxNode::<Lang>::new_root(builder.finish().0);
    /// let tree = parse(&mut builder, "x + x + 3");
    /// let first_x = tree.children_with_tokens().next().unwrap().into_token().unwrap();
    /// let second_x = tree.children_with_tokens().nth(4).unwrap().into_token().unwrap();
    /// assert!(first_x.text_eq(&second_x));
    /// let first_plus = tree.children_with_tokens().nth(2).unwrap().into_token().unwrap();
    /// let second_plus = tree.children_with_tokens().nth(6).unwrap().into_token().unwrap();
    /// assert!(first_plus.text_eq(&second_plus));
    /// ```
    #[inline]
    pub fn text_eq(&self, other: &Self) -> bool {
        if let Some(k1) = self.green().text_key() {
            match other.green().text_key() {
                Some(k2) => return k1 == k2,
                None => return false, // a kind with static text cannot be equal to one with non-static text
            }
        }

        debug_assert!(self.static_text().is_some());
        debug_assert!(other.static_text().is_some());
        self.syntax_kind() == other.syntax_kind()
    }

    /// Returns the interned key of text covered by this token, if any.
    /// This key may be used for comparisons with other keys of strings interned by the same interner.
    ///
    /// See also [`resolve_text`](SyntaxToken::resolve_text) and [`text_eq`](SyntaxToken::text_eq).
    ///
    /// # Examples
    /// If you intern strings inside of your application, e.g. inside of a compiler, you can use
    /// token's text keys to cross-reference between the syntax tree and the rest of your
    /// implementation by re-using the interner in both.
    /// ```
    /// # use cstree::*;
    /// # use cstree::interning::{Hasher, Rodeo, Key, new_interner};
    /// # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// # #[repr(u16)]
    /// # enum SyntaxKind {
    /// #     ROOT,
    /// #     INT,
    /// # }
    /// # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    /// # enum Lang {}
    /// # impl cstree::Language for Lang {
    /// #     type Kind = SyntaxKind;
    /// #
    /// #     fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
    /// #         assert!(raw.0 <= SyntaxKind::INT as u16);
    /// #         unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    /// #     }
    /// #
    /// #     fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
    /// #         cstree::SyntaxKind(kind as u16)
    /// #     }
    /// # }
    /// # type SyntaxNode<L> = cstree::SyntaxNode<L, ()>;
    /// # const ROOT:  cstree::SyntaxKind = cstree::SyntaxKind(0);
    /// # const IDENT: cstree::SyntaxKind = cstree::SyntaxKind(1);
    /// # fn parse(b: &mut GreenNodeBuilder<Rodeo>, s: &str) {}
    /// #
    /// struct TypeTable {
    ///     // ...
    /// }
    /// impl TypeTable {
    ///     fn type_of(&self, ident: Key) -> &str {
    ///         // ...
    /// #     ""
    ///     }
    /// }
    /// # struct State {
    /// #   interner: Rodeo,
    /// #   type_table: TypeTable,
    /// # }
    /// # let interner = new_interner();
    /// # let state = &mut State { interner, type_table: TypeTable{} };
    /// let mut builder = GreenNodeBuilder::with_interner(&mut state.interner);
    /// # let input = "";
    /// # builder.start_node(ROOT);
    /// # builder.token_with_text(IDENT, "x");
    /// # builder.finish_node();
    /// let tree = parse(&mut builder, "x");
    /// # let tree = SyntaxNode::<Lang>::new_root(builder.finish().0);
    /// let type_table = &state.type_table;
    /// let ident = tree.children_with_tokens().next().unwrap().into_token().unwrap();
    /// let typ = type_table.type_of(ident.text_key().unwrap());
    /// ```
    #[inline]
    pub fn text_key(&self) -> Option<Key> {
        self.green().text_key()
    }

    /// Returns the unterlying green tree token of this token.
    #[inline]
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
    pub fn parent(&self) -> &SyntaxNode<L, D> {
        &self.parent
    }

    /// Returns an iterator along the chain of parents of this token.
    #[inline]
    pub fn ancestors(&self) -> impl Iterator<Item = &SyntaxNode<L, D>> {
        self.parent().ancestors()
    }

    /// The tree element to the right of this one, i.e. the next child of this token's parent after this token.
    #[inline]
    pub fn next_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D>> {
        self.parent()
            .next_child_or_token_after(self.index as usize, self.text_range().end())
    }

    /// The tree element to the left of this one, i.e. the previous child of this token's parent after this token.
    #[inline]
    pub fn prev_sibling_or_token(&self) -> Option<SyntaxElementRef<'_, L, D>> {
        self.parent()
            .prev_child_or_token_before(self.index as usize, self.text_range().start())
    }

    /// Returns an iterator over all siblings of this token in the given `direction`, i.e. all of this
    /// token's parent's children from this token on to the left or the right.
    /// The first item in the iterator will always be this token.
    #[inline]
    pub fn siblings_with_tokens(&self, direction: Direction) -> impl Iterator<Item = SyntaxElementRef<'_, L, D>> {
        let me: SyntaxElementRef<'_, L, D> = self.into();
        iter::successors(Some(me), move |el| match direction {
            Direction::Next => el.next_sibling_or_token(),
            Direction::Prev => el.prev_sibling_or_token(),
        })
    }

    /// Returns the next token in the tree.
    /// This is not necessary a direct sibling of this token, but will always be further right in the tree.
    #[inline]
    pub fn next_token(&self) -> Option<&SyntaxToken<L, D>> {
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
    #[inline]
    pub fn prev_token(&self) -> Option<&SyntaxToken<L, D>> {
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
