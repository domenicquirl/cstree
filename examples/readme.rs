use std::{io::Write, iter::Peekable};

use cstree::{
    interning::Interner,
    prelude::*,
    syntax::{ResolvedElementRef, ResolvedNode},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum SyntaxKind {
    /* Tokens */
    Int,    // 42
    Plus,   // +
    Minus,  // -
    LParen, // (
    RParen, // )
    /* Nodes */
    Expr,
    Root,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Calculator;
impl Language for Calculator {
    // The tokens and nodes we just defined
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: RawSyntaxKind) -> Self::Kind {
        // This just needs to be the inverse of `kind_to_raw`, but could also
        // be an `impl TryFrom<u16> for SyntaxKind` or any other conversion.
        match raw.0 {
            0 => SyntaxKind::Int,
            1 => SyntaxKind::Plus,
            2 => SyntaxKind::Minus,
            3 => SyntaxKind::LParen,
            4 => SyntaxKind::RParen,
            5 => SyntaxKind::Expr,
            6 => SyntaxKind::Root,
            n => panic!("Unknown raw syntax kind: {n}"),
        }
    }

    fn kind_to_raw(kind: Self::Kind) -> RawSyntaxKind {
        RawSyntaxKind(kind as u16)
    }

    fn static_text(kind: Self::Kind) -> Option<&'static str> {
        match kind {
            SyntaxKind::Plus => Some("+"),
            SyntaxKind::Minus => Some("-"),
            SyntaxKind::LParen => Some("("),
            SyntaxKind::RParen => Some(")"),
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token<'input> {
    Int(&'input str),
    Plus,
    Minus,
    LParen,
    RParen,
    EoF,
}

pub struct Lexer<'input> {
    input:  &'input str,
    at_eof: bool,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Self { input, at_eof: false }
    }

    fn next_token(&mut self) -> Result<Token<'input>, String> {
        loop {
            let Some(next_char) =  self.input.chars().next() else {
                self.at_eof = true;
                return Ok(Token::EoF);
            };

            let token = match next_char {
                '+' => Token::Plus,
                '-' => Token::Minus,
                '(' => Token::LParen,
                ')' => Token::RParen,
                c if c.is_ascii_digit() => {
                    let (last_digit_idx, _char) = self
                        .input
                        .char_indices()
                        .take_while(|(_idx, c)| c.is_ascii_digit())
                        .last()
                        .expect("matched at least one");
                    // Advance lexer
                    let number = Token::Int(&self.input[..=last_digit_idx]);
                    self.input = &self.input[(last_digit_idx + 1)..];
                    return Ok(number);
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
                    self.input = &self.input[(last_ws_idx + 1)..];
                    continue;
                }
                c => return Err(format!("Unknown start of token: '{c}'")),
            };

            // Advance lexer
            self.input = &self.input[1..];
            return Ok(token);
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Token<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.at_eof {
            None
        } else {
            Some(self.next_token().expect("Failed to lex input"))
        }
    }
}

pub struct Parser<'input> {
    lexer:   Peekable<Lexer<'input>>,
    builder: GreenNodeBuilder<'static, 'static, Calculator>,
}

impl<'input> Parser<'input> {
    pub fn new(input: &'input str) -> Self {
        Self {
            lexer:   Lexer::new(input).peekable(),
            builder: GreenNodeBuilder::new(),
        }
    }

    pub fn bump(&mut self) -> Option<Token<'input>> {
        self.lexer.next()
    }

    pub fn parse(&mut self) -> Result<(), String> {
        self.builder.start_node(SyntaxKind::Root);
        self.parse_expr()?;
        self.builder.finish_node();
        Ok(())
    }

    fn parse_lhs(&mut self) -> Result<(), String> {
        // An expression may start either with a number, or with an opening parenthesis that is the start of a
        // parenthesized expression
        let next_token = *self.lexer.peek().unwrap();
        match next_token {
            Token::Int(n) => {
                self.bump();
                self.builder.token(SyntaxKind::Int, n);
            }
            Token::LParen => {
                // Wrap the grouped expression inside a node containing it and its parentheses
                self.builder.start_node(SyntaxKind::Expr);
                self.bump();
                self.builder.static_token(SyntaxKind::LParen);
                self.parse_expr()?; // Inner expression
                if self.bump() != Some(Token::RParen) {
                    return Err("Missing ')'".to_string());
                }
                self.builder.static_token(SyntaxKind::RParen);
                self.builder.finish_node();
            }
            Token::EoF => return Err("Unexpected end of file: expected expression".to_string()),
            t => return Err(format!("Unexpected start of expression: '{t:?}'")),
        }
        Ok(())
    }

    fn parse_expr(&mut self) -> Result<(), String> {
        // Remember our current position
        let before_expr = self.builder.checkpoint();

        // Parse the start of the expression
        self.parse_lhs()?;

        // Check if the expression continues with `+ <more>` or `- <more>`
        let Some(next_token) = self.lexer.peek() else {
            return Ok(());
        };
        let op = match *next_token {
            Token::Plus => SyntaxKind::Plus,
            Token::Minus => SyntaxKind::Minus,
            Token::RParen | Token::EoF => return Ok(()),
            t => return Err(format!("Expected operator, found '{t:?}'")),
        };

        // If so, retroactively wrap the (already parsed) LHS and the following RHS inside an `Expr` node
        self.builder.start_node_at(before_expr, SyntaxKind::Expr);
        self.bump();
        self.builder.static_token(op);
        self.parse_expr()?; // RHS
        self.builder.finish_node();
        Ok(())
    }

    pub fn finish(mut self) -> (GreenNode, impl Interner) {
        assert!(self.lexer.next().map(|t| t == Token::EoF).unwrap_or(true));
        let (tree, cache) = self.builder.finish();
        (tree, cache.unwrap().into_interner().unwrap())
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
        let mut parser = Parser::new(&buf);
        if let Err(e) = parser.parse() {
            eprintln!("Parse error: {e}");
            continue;
        }

        let (tree, interner) = parser.finish();
        let root = SyntaxNode::<Calculator>::new_root_with_resolver(tree, interner);

        if let Some(expr) = root.first_child_or_token() {
            let result = eval_elem(expr, &mut root.children_with_tokens());
            println!("Result: {result}");
        }
    }
}

fn eval(expr: &ResolvedNode<Calculator>) -> i64 {
    let mut children = expr.children_with_tokens();
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
        NodeOrToken::Node(n) => {
            assert_eq!(n.kind(), SyntaxKind::Expr);
            eval(n)
        }
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
            _ => unreachable!("invalid start of expression"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex() {
        let input = "11 + 2-(5 + 4)";
        let lexer = Lexer::new(input);
        let tokens: Vec<_> = lexer.into_iter().collect();
        assert_eq!(
            tokens,
            vec![
                Token::Int("11"),
                Token::Plus,
                Token::Int("2"),
                Token::Minus,
                Token::LParen,
                Token::Int("5"),
                Token::Plus,
                Token::Int("4"),
                Token::RParen,
                Token::EoF
            ]
        );
    }

    #[test]
    fn parse() {
        let input = "11 + 2-(5 + 4)";
        let mut parser = Parser::new(input);
        parser.parse().unwrap();
        let (tree, interner) = parser.finish();
        let root = SyntaxNode::<Calculator>::new_root_with_resolver(tree, interner);
        dbg!(root);
    }
}
