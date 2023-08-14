use core::fmt;

mod sink;
pub use sink::TextTreeSink;
mod source;
pub use source::TextTokenSource;
mod span;
pub use span::Span;

#[allow(clippy::len_without_is_empty)]
pub trait Token: Copy + fmt::Debug {
    type Syntax: cstree::Syntax;

    fn kind(self) -> Self::Syntax;
    fn is_trivia(self) -> bool;
    fn is_ident(self) -> bool;
    /// `source` is the full input text, which is provided in case tokens are only storing spans, but not the text
    /// itself
    fn get_text(self, source: &str) -> &str;
    fn span(self) -> Span;
    fn len(self) -> usize {
        self.span().len()
    }
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
    /// `n_input_tokens` can be > 1 to "glue" tokens together. For example, a `>` followed by a `=` could be glued
    /// together by the parser to a single `>=` token. Note that this operation is only valid if there is no trivia
    /// between the two input tokens.
    fn output_token(&mut self, kind: S, n_input_tokens: usize);

    fn start_node<A: TriviaAttachment<S>>(&mut self, kind: S, attacher: A);

    fn finish_node(&mut self);
}

pub trait TriviaAttachment<S: cstree::Syntax> {
    /// Given the list of trivia tokens immediately following the current position in the token stream,
    /// decide how many of these (starting from the back) should be attached to a new node of the given `kind`.
    ///
    /// This method is called from [`TreeSink::start_node`] to decide what part of the trivia left in the input goes
    /// before and what goes inside the node.
    fn trivias_to_attach<T: Token>(&self, kind: S, current_trivias: &[T], input: &str) -> usize;

    /// Implement to declare certain `kind`s of nodes as always forwarding all trivia tokens to inside the node.
    ///
    /// Doing so will move any following trivia tokens to inside the node and defer the trivia attachment decision (via
    /// `trivias_to_attach`) to the next node (for which this method does not return `true`). This can be useful if
    /// there are node kinds that exist for purely grammatical reasons, but do not carry semantic meaning.
    fn forwards_trivia(&self, #[allow(unused)] kind: S) -> bool {
        false
    }
}

// fn trivias_to_attach<T: Token>(current_trivias: &[T], input: &str) -> usize {
//     // go backwards to find comments right before the next node
//     let trivias = current_trivias.iter().rev().enumerate();
//     let mut res = 0;

//     for (i, token) in trivias {
//         match token.kind {
//             SyntaxKind::Comment => res = i + 1,
//             SyntaxKind::Whitespace => {
//                 let text = token.resolve_to_text(input);
//                 if text.chars().filter(|&c| c == '\n').count() >= 2 {
//                     // Stop attaching after double newline
//                     break;
//                 }
//             }
//             _ => unreachable!("Can only attach trivias"),
//         }
//     }
//     res
// }

// fn forwards_trivia(kind: SyntaxKind) -> bool {
//     use SyntaxKind::*;
//     matches!(kind, ContainerContent)
// }
