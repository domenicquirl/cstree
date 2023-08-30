use core::mem;

use cstree::{
    build::{GreenNodeBuilder, NodeCache},
    green::GreenNode,
    interning::{Interner, TokenInterner},
    Syntax,
};

#[cfg(feature = "concurrent")]
use crate::events::ConcurrentEventSource;
use crate::events::{Event, EventSource};

use super::{Token, TreeSink, TriviaAttachment};

#[derive(Debug)]
pub struct TextTreeSink<'input, 'cache, 'interner, T, S: Syntax, I> {
    input:        &'input str,
    current_byte: usize,
    tokens:       &'input [T],
    state:        State,
    inner:        GreenNodeBuilder<'cache, 'interner, S, I>,
}

impl<'input, 'cache, 'interner, T, S: Syntax, I> TextTreeSink<'input, 'cache, 'interner, T, S, I>
where
    T: Token<Syntax = S>,
    I: cstree::interning::Interner,
{
    pub fn build<E: EventSource<Syntax = S>, A: TriviaAttachment<S>>(&mut self, source: &mut E, attacher: &A) {
        let events = source.events_mut();
        let mut preceded_nodes = Vec::new();

        for i in 0..events.len() {
            match mem::replace(&mut events[i], Event::Placeholder) {
                Event::Placeholder => {}
                // The sequential builder does not optimize concurrently
                #[cfg(feature = "concurrent")]
                Event::DeOpt | Event::Opt => panic!("opt guard received in sequential builder"),
                Event::Enter { kind, preceded_by } => {
                    // reorder the enter events according to the `preceded_by` pointers
                    preceded_nodes.push(kind);

                    let mut idx = i;
                    let mut preceded_by = preceded_by;
                    while let Some(rel_diff) = preceded_by {
                        idx += rel_diff.get();
                        preceded_by = match mem::replace(&mut events[idx], Event::Placeholder) {
                            Event::Enter { kind, preceded_by } => {
                                preceded_nodes.push(kind);
                                preceded_by
                            }
                            _ => unreachable!(),
                        }
                    }

                    for kind in preceded_nodes.drain(..).rev() {
                        self.start_node(kind, attacher);
                    }
                }
                Event::Exit => {
                    self.finish_node();
                }
                Event::Token { kind, n_input_tokens } => self.output_token(kind, n_input_tokens),
            }
        }
    }

    #[cfg(feature = "concurrent")]
    pub fn build_concurrent<C: ConcurrentEventSource<Syntax = S>, A: TriviaAttachment<S>>(
        &mut self,
        source: &C,
        attacher: &A,
    ) {
        let mut buffer = false;
        let mut events = Vec::with_capacity(8);

        while !source.is_closed() {
            for event in source.take_buffered_events() {
                match event {
                    Event::DeOpt => {
                        assert!(!buffer);
                        buffer = true;
                    }
                    Event::Opt => {
                        assert!(buffer);
                        buffer = false;

                        // reorder the buffered events according to the `preceded_by` pointers
                        for i in 0..events.len() {
                            match mem::replace(&mut events[i], Event::Placeholder) {
                                Event::Placeholder => {}
                                Event::Enter { kind, preceded_by } => {
                                    let mut preceded_nodes = vec![kind];

                                    let mut idx = i;
                                    let mut preceded_by = preceded_by;
                                    while let Some(rel_diff) = preceded_by {
                                        idx += rel_diff.get();
                                        preceded_by = match mem::replace(&mut events[idx], Event::Placeholder) {
                                            Event::Enter { kind, preceded_by } => {
                                                preceded_nodes.push(kind);
                                                preceded_by
                                            }
                                            _ => unreachable!(),
                                        }
                                    }

                                    for kind in preceded_nodes.drain(..).rev() {
                                        self.start_node(kind, attacher);
                                    }
                                }
                                Event::Exit { .. } => self.finish_node(),
                                Event::Token { kind, n_input_tokens } => self.output_token(kind, n_input_tokens),
                                _ => unreachable!(),
                            }
                        }
                        events.clear();
                    }
                    e @ Event::Enter { .. } | e @ Event::Exit | e @ Event::Token { .. } if buffer => events.push(e),
                    Event::Enter { kind, preceded_by } => {
                        // Preceding is not allowed in opt regions
                        assert!(preceded_by.is_none());
                        self.start_node(kind, attacher);
                    }
                    Event::Exit => self.finish_node(),
                    Event::Token { kind, n_input_tokens } => self.output_token(kind, n_input_tokens),
                    Event::Placeholder => panic!("received placeholder event from concurrent source"),
                }
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum State {
    Empty,
    Balanced,
    FinishNode,
}

impl<'input, 'cache, 'interner, T, I, S: Syntax> TreeSink<S> for TextTreeSink<'input, 'cache, 'interner, T, S, I>
where
    T: Token<Syntax = S>,
    I: Interner,
{
    fn output_token(&mut self, kind: S, n_input_tokens: usize) {
        match mem::replace(&mut self.state, State::Balanced) {
            State::Empty => unreachable!("Cannot start tree with token (needs root node)"),
            State::Balanced => {}
            State::FinishNode => self.inner.finish_node(),
        }

        self.consume_trivia();
        self.add_token(kind, n_input_tokens);
    }

    fn start_node<A: TriviaAttachment<S>>(&mut self, kind: S, attacher: &A) {
        let forwards_trivia = attacher.forwards_trivia(kind);
        match mem::replace(&mut self.state, State::Balanced) {
            State::Empty => {
                // If we are just starting the tree, we immediately start the root node and don't do
                // trivia attachment (since there is no previous node)
                self.inner.start_node(kind);
                return;
            }
            State::Balanced => {}
            State::FinishNode => self.inner.finish_node(),
        }

        if forwards_trivia {
            // For things like `ContainerContent`, we _do_ want to attach comments to nodes, but
            // _not_ to the `ContainerContent` wrapper. Thus we don't consume trivia for these nodes
            // and instead defer the handling to the first child node.
            self.inner.start_node(kind);
            return;
        }

        let n_current_trivias = self.tokens.iter().take_while(|&token| token.is_trivia()).count();
        let current_trivias = &self.tokens[..n_current_trivias];
        let attach_n_trivias = attacher.trivias_to_attach(kind, current_trivias, self.input);
        self.consume_n_trivias(n_current_trivias - attach_n_trivias);
        self.inner.start_node(kind);
        self.consume_n_trivias(attach_n_trivias);
    }

    fn finish_node(&mut self) {
        match mem::replace(&mut self.state, State::FinishNode) {
            State::Empty => unreachable!("No node to finish"),
            State::Balanced => {}
            State::FinishNode => self.inner.finish_node(),
        }
    }
}

impl<'input, T, S: Syntax> TextTreeSink<'input, 'static, 'static, T, S, TokenInterner> {
    pub fn new(tokens: &'input [T], input: &'input str) -> Self {
        Self {
            input,
            current_byte: 0,
            tokens,
            state: State::Empty,
            inner: GreenNodeBuilder::new(),
        }
    }
}

impl<'input, 'cache, 'interner, T, S: Syntax, I> TextTreeSink<'input, 'cache, 'interner, T, S, I>
where
    T: Token<Syntax = S>,
    I: cstree::interning::Interner,
{
    pub fn with_cache(tokens: &'input [T], input: &'input str, cache: &'cache mut NodeCache<'interner, I>) -> Self {
        Self {
            input,
            current_byte: 0,
            tokens,
            state: State::Empty,
            inner: GreenNodeBuilder::with_cache(cache),
        }
    }

    pub fn finish(mut self) -> (GreenNode, Option<I>) {
        match mem::replace(&mut self.state, State::FinishNode) {
            State::Empty | State::Balanced => unreachable!("Must finish the root node"),
            State::FinishNode => {
                // Consume remaining trivia before finishing root node
                self.consume_trivia();
                self.inner.finish_node();
            }
        }
        let (node, cache) = self.inner.finish();
        (node, cache.and_then(|cache| cache.into_interner()))
    }

    fn consume_trivia(&mut self) {
        for token in self.tokens.iter().take_while(|&token| token.is_trivia()) {
            self.add_token(token.kind(), 1);
        }
    }

    fn consume_n_trivias(&mut self, n: usize) {
        for _ in 0..n {
            let token = self.tokens[0];
            debug_assert!(token.is_trivia());
            self.add_token(token.kind(), 1);
        }
    }

    fn add_token(&mut self, kind: S, n_input_tokens: usize) {
        let text_len: usize = self.tokens[..n_input_tokens].iter().map(|token| token.len()).sum();
        let text = self.input[self.current_byte..(self.current_byte + text_len)].into();
        self.tokens = &self.tokens[n_input_tokens..];
        self.current_byte += text_len;
        self.inner.token(kind, text);
    }
}
