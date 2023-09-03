//! This is the same parser as in `cstree`'s "getting started" guide and `readme` example, but adapted to use
//! `cstree-events`.

use std::io::Write;

use cstree::{
    prelude::*,
    syntax::{ResolvedElementRef, ResolvedNode},
};
use cstree_event::{
    events::{CompletedNode, Event, EventSink as _, SequentialEventSink},
    parsing::{NoopAttacher, TextTokenSource, TextTreeSink, Token, TokenSource as _},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Syntax)]
#[repr(u32)]
pub enum SyntaxKind {
    /* Tokens */
    Int, // e.g. 42
    #[static_text("+")]
    Plus,
    #[static_text("-")]
    Minus,
    #[static_text("(")]
    LParen,
    #[static_text(")")]
    RParen,
    Whitespace,
    EoF,
    /* Nodes */
    Expr,
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
                '-' => SyntaxKind::Minus,
                '(' => SyntaxKind::LParen,
                ')' => SyntaxKind::RParen,
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
    events: SequentialEventSink<Calculator>,
}

impl Parser {
    pub fn new(input: &str, tokens: &[lexer::Token]) -> Self {
        Self {
            source: TextTokenSource::new(input, tokens),
            events: SequentialEventSink::new(),
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
        self.parse_expr()?;
        self.events.complete(root);
        Ok(())
    }

    fn parse_lhs(&mut self) -> Result<CompletedNode, String> {
        // An expression may start either with a number, or with an opening parenthesis that is the start of a
        // parenthesized expression
        let next_token = self.source.peek(1).unwrap();
        let expr = match next_token.kind() {
            SyntaxKind::Int => {
                let node = self.events.enter_node(SyntaxKind::Int);
                self.consume(SyntaxKind::Int)?;
                self.events.complete(node)
            }
            SyntaxKind::LParen => {
                // Wrap the grouped expression inside a node containing it and its parentheses
                let expr = self.events.enter_node(SyntaxKind::Expr);
                self.consume(SyntaxKind::LParen)?;
                self.parse_expr()?; // Inner expression
                self.consume(SyntaxKind::RParen)?;
                self.events.complete(expr)
            }
            SyntaxKind::EoF => return Err("Unexpected end of file: expected expression".to_string()),
            t => return Err(format!("Unexpected start of expression: '{t:?}'")),
        };
        Ok(expr)
    }

    fn parse_expr(&mut self) -> Result<(), String> {
        // Parse the start of the expression
        let lhs = self.parse_lhs()?;

        // Check if the expression continues with `+ <more>` or `- <more>`
        let Some(next_token) = self.source.peek(1) else {
            return Ok(());
        };
        let op = match next_token.kind() {
            op @ SyntaxKind::Plus | op @ SyntaxKind::Minus => op,
            SyntaxKind::RParen | SyntaxKind::EoF => return Ok(()),
            t => return Err(format!("Expected operator, found '{t:?}'")),
        };

        // If so, retroactively wrap the (already parsed) LHS and the following RHS inside an `Expr` node
        let expr = self.events.precede(lhs, SyntaxKind::Expr);
        self.consume(op)?;
        self.parse_expr()?; // RHS
        self.events.complete(expr);
        Ok(())
    }

    pub fn finish(mut self) -> Vec<Event<SyntaxKind>> {
        assert!(self.source.next().map(|t| t.kind() == SyntaxKind::EoF).unwrap_or(true));
        self.events.assert_complete();
        self.events.into_inner()
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
        let mut parser = Parser::new(&buf, &tokens);
        if let Err(e) = parser.parse() {
            eprintln!("Parse error: {e}");
            continue;
        }

        let mut events = parser.finish();
        let (tree, interner) = TextTreeSink::new(&buf, &tokens).build(&mut events, &NoopAttacher);
        let root = SyntaxNode::<Calculator>::new_root_with_resolver(tree, interner.unwrap());

        if let Some(expr) = root.first_child_or_token() {
            let result = eval_elem(expr, &mut root.children_with_tokens());
            println!("Result: {result}");
        }
    }
}

fn eval(expr: &ResolvedNode<Calculator>) -> i64 {
    let mut children = expr
        .children_with_tokens()
        .filter(|elem| elem.kind() != SyntaxKind::Whitespace);
    let lhs = eval_elem(children.next().expect("empty expr"), &mut children);
    let Some(op) = children.next().map(|elem| elem.kind()) else {
        // Literal expression
        return lhs;
    };
    let rhs = eval_elem(children.next().expect("missing RHS"), &mut children);

    match op {
        SyntaxKind::Plus => lhs + rhs,
        SyntaxKind::Minus => lhs - rhs,
        _ => unreachable!("invalid op"),
    }
}

fn eval_elem<'e>(
    expr: ResolvedElementRef<'_, Calculator>,
    children: &mut impl Iterator<Item = ResolvedElementRef<'e, Calculator>>,
) -> i64 {
    use cstree::util::NodeOrToken;

    match expr {
        NodeOrToken::Node(n) => match n.kind() {
            SyntaxKind::Int => eval_elem(
                n.children_with_tokens()
                    .next()
                    .expect("number node without number token"),
                children,
            ),
            _ => eval(n),
        },
        NodeOrToken::Token(t) => match t.kind() {
            SyntaxKind::Int => {
                let number_str = t.text();
                number_str.parse().expect("parsed int could not be evaluated")
            }
            SyntaxKind::LParen => {
                let inner = children.next().expect("missing content inside parens");
                // It's important that we consume the `)` here, as otherwise `eval` might mistake it for an operator
                assert_eq!(
                    children
                        .next()
                        .and_then(|elem| elem.into_token())
                        .map(|token| token.kind()),
                    Some(SyntaxKind::RParen)
                );
                eval_elem(inner, children)
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
        let input = "11 + 2-(5 + 4)";
        let tokens: Vec<_> = lexer::lex(input).into_iter().map(|token| token.kind()).collect();
        assert_eq!(
            tokens,
            vec![
                SyntaxKind::Int,
                SyntaxKind::Plus,
                SyntaxKind::Int,
                SyntaxKind::Minus,
                SyntaxKind::LParen,
                SyntaxKind::Int,
                SyntaxKind::Plus,
                SyntaxKind::Int,
                SyntaxKind::RParen,
                SyntaxKind::EoF
            ]
        );
    }

    #[test]
    fn parse() {
        let input = "11 + 2-(5 + 4)";
        let tokens = lexer::lex(input);
        let mut parser = Parser::new(input, &tokens);
        parser.parse().unwrap();
        let mut events = parser.finish();
        let (tree, interner) = TextTreeSink::new(input, &tokens).build(&mut events, &NoopAttacher);
        let root = SyntaxNode::<Calculator>::new_root_with_resolver(tree, interner.unwrap());
        dbg!(root);
    }
}
