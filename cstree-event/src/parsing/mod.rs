use core::fmt;

mod source;
pub use source::TextTokenSource;
mod span;
pub use span::Span;

pub trait Token: Copy + fmt::Debug {
    fn is_trivia(self) -> bool;
    fn is_ident(self) -> bool;
    /// `source` is the full input text, which is provided in case tokens are only storing spans, but not the text
    /// itself
    fn get_text(self, source: &str) -> &str;
    fn span(self) -> Span;
}

pub trait TokenSource<T> {
    fn next(&mut self) -> Option<T>;

    fn advance_n(&mut self, n: usize) {
        for _ in 0..n {
            self.next();
        }
    }

    fn peek(&self, n: usize) -> Option<T>;

    #[inline(always)]
    fn peek_next(&self) -> Option<T> {
        self.peek(1)
    }

    fn resolve_ident(&self, ident: T) -> &str;

    fn size_hint(&self) -> Option<usize> {
        None
    }
}

pub trait TreeSink<S: cstree::Syntax> {
    fn token(&mut self, kind: S);

    fn start_node(&mut self, kind: S);

    fn finish_node(&mut self);
}
