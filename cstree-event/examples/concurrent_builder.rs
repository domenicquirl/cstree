//! A copy of the `cstree_readme` example with a slightly reduced expression grammar (only addition) that showcases how
//! to run tree building in parallel to your parser.
//!
//! The parser and the [`TextTreeSink`] builder are spawned onto different threads in `main`.
//! Note how [`Parser::parse_expression`] wraps the actual expression parsing (in [`Parser::do_parse_expression`]) in
//! optimization guards to allow for backtracking / preceding events / extending expressions when more terms are
//! encountered. This pauses tree building until the end of an expression before it continues building the syntax tree
//! while the next expression is parsed. This pauses tree building until the end of an expression before it continues
//! building the syntax tree while the next expression is parsed.
use std::{io::Write, thread};

use cstree::{
    prelude::*,
    syntax::{ResolvedElementRef, ResolvedNode},
};
use cstree_event::{
    events::{CompletedNode, ConcurrentEventSink, EventSink as _},
    parsing::{NoopAttacher, TextTokenSource, TextTreeSink, Token, TokenSource as _},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
#[repr(u32)]
pub enum SyntaxKind {
    /* Tokens */
    Int, // e.g. 42
    #[static_text("+")]
    Plus,
    #[static_text("[")]
    LBrace,
    #[static_text("]")]
    RBrace,
    #[static_text(",")]
    Comma,
    Whitespace,
    EoF,
    /* Nodes */
    Expr,
    List,
    Root,
}
type Calculator = SyntaxKind;

mod lexer {
    use cstree_event::parsing::Span;

    use super::SyntaxKind;

    pub fn lex(input: &str) -> Vec<Token> {
        let lexer = Lexer::new(input);
        lexer.into_iter().collect()
    }

    #[derive(Debug, Clone, Copy)]
    pub struct Token {
        kind: SyntaxKind,
        span: Span,
    }

    impl cstree_event::parsing::Token for Token {
        type Syntax = SyntaxKind;

        fn kind(self) -> Self::Syntax {
            self.kind
        }

        fn is_trivia(self) -> bool {
            matches!(self.kind, SyntaxKind::Whitespace)
        }

        fn is_ident(self) -> bool {
            false
        }

        fn get_text(self, source: &str) -> &str {
            &source[self.span]
        }

        fn span(self) -> Span {
            self.span
        }
    }

    pub struct Lexer<'input> {
        input:  &'input str,
        at_eof: bool,
        pos:    u32,
    }

    impl<'input> Lexer<'input> {
        pub fn new(input: &'input str) -> Self {
            Self {
                input,
                at_eof: false,
                pos: 0,
            }
        }

        fn next_token(&mut self) -> Result<Token, String> {
            let start = self.pos;
            let Some(next_char) = self.input.chars().next() else {
                self.at_eof = true;
                return Ok(Token {
                    kind: SyntaxKind::EoF,
                    span: Span::from(start..start),
                });
            };

            let kind = match next_char {
                '+' => SyntaxKind::Plus,
                ',' => SyntaxKind::Comma,
                '[' => SyntaxKind::LBrace,
                ']' => SyntaxKind::RBrace,
                c if c.is_ascii_digit() => {
                    let (last_digit_idx, _char) = self
                        .input
                        .char_indices()
                        .take_while(|(_idx, c)| c.is_ascii_digit())
                        .last()
                        .expect("matched at least one");
                    // Advance lexer
                    self.pos += last_digit_idx as u32 + 1;
                    self.input = &self.input[(last_digit_idx + 1)..];
                    return Ok(Token {
                        kind: SyntaxKind::Int,
                        span: Span::from(start..self.pos),
                    });
                }
                c if c.is_whitespace() => {
                    // Skip whitespace
                    let (last_ws_idx, _char) = self
                        .input
                        .char_indices()
                        .take_while(|(_idx, c)| c.is_whitespace())
                        .last()
                        .expect("matched at least one");
                    // Advance lexer
                    self.pos += last_ws_idx as u32 + 1;
                    self.input = &self.input[(last_ws_idx + 1)..];
                    return Ok(Token {
                        kind: SyntaxKind::Whitespace,
                        span: Span::from(start..self.pos),
                    });
                }
                c => return Err(format!("Unknown start of token: '{c}'")),
            };

            // Advance lexer
            self.pos += 1;
            self.input = &self.input[1..];
            Ok(Token {
                kind,
                span: Span::from(start..self.pos),
            })
        }
    }

    impl<'input> Iterator for Lexer<'input> {
        type Item = Token;

        fn next(&mut self) -> Option<Self::Item> {
            if self.at_eof {
                None
            } else {
                Some(self.next_token().expect("Failed to lex input"))
            }
        }
    }
}

pub struct Parser {
    source: TextTokenSource<lexer::Token>,
    events: ConcurrentEventSink<Calculator>,
}

impl Parser {
    pub fn new(input: &str, tokens: &[lexer::Token], events: ConcurrentEventSink<Calculator>) -> Self {
        Self {
            source: TextTokenSource::new(input, tokens),
            events,
        }
    }

    pub fn consume(&mut self, expected: SyntaxKind) -> Result<(), String> {
        if let Some(next) = self.source.peek(1) {
            if next.kind() == expected {
                self.token(expected);
                return Ok(());
            }
            return Err(format!(
                "Unexpected token: expected `{expected:?}`, but found `{found:?}`",
                found = next.kind()
            ));
        }
        Err(format!("Unexpected end of input: expected `{expected:?}`"))
    }

    pub fn token(&mut self, kind: SyntaxKind) {
        self.source.advance_n(1);
        self.events.token(kind);
    }

    pub fn bump(&mut self) {
        self.token(self.source.peek(1).expect("unexpected end of input").kind());
    }

    pub fn parse(&mut self) -> Result<(), String> {
        let root = self.events.enter_node(SyntaxKind::Root);
        self.parse_list()?;
        self.events.complete(root);
        Ok(())
    }

    fn parse_list(&mut self) -> Result<(), String> {
        let list = self.events.enter_node(SyntaxKind::List);
        self.consume(SyntaxKind::LBrace)?;
        while !matches!(
            self.source.peek_next().map(Token::kind).unwrap_or(SyntaxKind::EoF),
            SyntaxKind::RBrace | SyntaxKind::EoF
        ) {
            self.parse_expr()?;
            if self.source.peek_next().map(Token::kind) != Some(SyntaxKind::RBrace) {
                self.consume(SyntaxKind::Comma)?;
            }
        }
        self.consume(SyntaxKind::RBrace)?;
        self.events.complete(list);
        Ok(())
    }

    fn parse_expr(&mut self) -> Result<(), String> {
        // Expression parsing may alter the sequence of events by using `CompletedNode::precede`,
        // therefore we must pause tree building while the parser is recursing through an expression.
        // We can do this by sending a `DeOpt` event.
        let guard = self.events.deopt();
        // Now we can parse the expression.
        self.do_parse_expr()?;
        // Afterwards, we `complete` the `DeOpt` event, which sends an `Opt` event to the builder
        // that notifies it that it can continue building.
        self.events.complete(guard);
        Ok(())
    }

    fn parse_lhs(&mut self) -> Result<CompletedNode, String> {
        // Only supports integer literals.
        let next_token = self.source.peek(1).unwrap();
        let expr = match next_token.kind() {
            SyntaxKind::Int => {
                let node = self.events.enter_node(SyntaxKind::Int);
                self.consume(SyntaxKind::Int)?;
                self.events.complete(node)
            }
            SyntaxKind::EoF => return Err("Unexpected end of file: expected expression".to_string()),
            t => return Err(format!("Unexpected start of expression: '{t:?}'")),
        };
        Ok(expr)
    }

    fn do_parse_expr(&mut self) -> Result<(), String> {
        // Parse the start of the expression
        let lhs = self.parse_lhs()?;

        // Check if the expression continues with `+ <more>`
        let Some(next_token) = self.source.peek(1) else {
            return Ok(());
        };
        let op = match next_token.kind() {
            op @ SyntaxKind::Plus => op,
            SyntaxKind::Comma | SyntaxKind::RBrace | SyntaxKind::EoF => return Ok(()),
            t => return Err(format!("Expected operator, found '{t:?}'")),
        };

        // If so, retroactively wrap the (already parsed) LHS and the following RHS inside an `Expr` node
        let expr = self.events.precede(lhs, SyntaxKind::Expr);
        self.consume(op)?;
        self.do_parse_expr()?; // RHS
        self.events.complete(expr);
        Ok(())
    }

    pub fn finish(mut self) {
        assert!(self.source.next().map(|t| t.kind() == SyntaxKind::EoF).unwrap_or(true));
        self.events.assert_complete();
    }
}

fn main() {
    use std::io;

    let mut buf = String::new();
    loop {
        print!("Enter expression: ");
        io::stdout().flush().unwrap();
        buf.clear();
        if let Err(e) = io::stdin().read_line(&mut buf) {
            eprintln!("Error reading input: {e}");
            continue;
        }
        let tokens = lexer::lex(&buf);
        let (event_sink, event_receiver) = ConcurrentEventSink::new();
        let parse_result = thread::scope(|s| {
            let parser = s.spawn(|| event_sink.with(|events| Parser::new(&buf, &tokens, events).parse()));
            let builder = s.spawn(|| TextTreeSink::new(&buf, &tokens).build_concurrent(&event_receiver, &NoopAttacher));
            let parse_result = parser.join().expect("parser panicked");
            let (tree, interner) = builder.join().expect("builder panicked");
            parse_result.map(|()| (tree, interner))
        });

        let (tree, interner) = match parse_result {
            Ok((tree, interner)) => (tree, interner),
            Err(e) => {
                eprintln!("Parse error: {e}");
                continue;
            }
        };

        let root = SyntaxNode::<Calculator>::new_root_with_resolver(tree, interner.unwrap());
        if let Some(expr) = root.first_child_or_token() {
            let result = eval_elem(expr);
            println!("Result: {result:?}");
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Value {
    List(Vec<i64>),
    Int(i64),
}

impl Value {
    #[track_caller]
    fn expect_int(self) -> i64 {
        match self {
            Value::Int(i) => i,
            Value::List(_) => panic!("expected int"),
        }
    }
}

fn eval(node: &ResolvedNode<Calculator>) -> Value {
    match node.kind() {
        SyntaxKind::Int => eval_elem(
            node.children_with_tokens()
                .next()
                .expect("number node without number token"),
        ),
        SyntaxKind::Expr => {
            let mut children = node
                .children_with_tokens()
                .filter(|elem| elem.kind() != SyntaxKind::Whitespace);
            let lhs = eval_elem(children.next().expect("empty expr")).expect_int();
            let Some(op) = children.next().map(|elem| elem.kind()) else {
                // Literal expression
                return Value::Int(lhs);
            };
            let rhs = eval_elem(children.next().expect("missing RHS")).expect_int();

            match op {
                SyntaxKind::Plus => Value::Int(lhs + rhs),
                _ => unreachable!("invalid op"),
            }
        }
        SyntaxKind::List => Value::List(node.children().map(eval).map(Value::expect_int).collect()),
        kind => panic!("unsupported node '{kind:?}'"),
    }
}

fn eval_elem(expr: ResolvedElementRef<'_, Calculator>) -> Value {
    use cstree::util::NodeOrToken;

    match expr {
        NodeOrToken::Node(n) => match n.kind() {
            SyntaxKind::Int => eval_elem(
                n.children_with_tokens()
                    .next()
                    .expect("number node without number token"),
            ),
            _ => eval(n),
        },
        NodeOrToken::Token(t) => match t.kind() {
            SyntaxKind::Int => {
                let number_str = t.text();
                let n: i64 = number_str.parse().expect("parsed int could not be evaluated");
                Value::Int(n)
            }
            kind => unreachable!("invalid start of expression: {kind:?}"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex() {
        let input = "[11 + 2, 9]";
        let tokens: Vec<_> = lexer::lex(input).into_iter().map(|token| token.kind()).collect();
        assert_eq!(
            tokens,
            vec![
                SyntaxKind::LBrace,
                SyntaxKind::Int,
                SyntaxKind::Whitespace,
                SyntaxKind::Plus,
                SyntaxKind::Whitespace,
                SyntaxKind::Int,
                SyntaxKind::Comma,
                SyntaxKind::Whitespace,
                SyntaxKind::Int,
                SyntaxKind::RBrace,
                SyntaxKind::EoF
            ]
        );
    }

    #[test]
    fn parse_and_eval() {
        let input = "[11 + 2, 9]";
        let tokens = lexer::lex(input);
        let (events, receiver) = ConcurrentEventSink::new();
        events.with(|events| Parser::new(input, &tokens, events).parse().unwrap());
        let (tree, interner) = TextTreeSink::new(input, &tokens).build_concurrent(&receiver, &NoopAttacher);
        let root = SyntaxNode::<Calculator>::new_root_with_resolver(tree, interner.unwrap());
        assert_eq!(eval(root.children().next().unwrap()), Value::List(vec![13, 9]));
    }
}
