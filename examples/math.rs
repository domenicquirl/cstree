//! Example that takes the input
//! 1 + 2 * 3 + 4
//! and builds the tree
//! - Marker(Root)
//!   - Marker(Operation)
//!     - Marker(Operation)
//!       - "1" Token(Number)
//!       - "+" Token(Add)
//!       - Marker(Operation)
//!         - "2" Token(Number)
//!         - "*" Token(Mul)
//!         - "3" Token(Number)
//!     - "+" Token(Add)
//!     - "4" Token(Number)

use cstree::{interning::Resolver, GreenNodeBuilder, NodeOrToken};
use std::iter::Peekable;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(non_camel_case_types)]
#[repr(u16)]
enum SyntaxKind {
    WHITESPACE = 0,

    ADD,
    SUB,
    MUL,
    DIV,

    NUMBER,
    ERROR,
    OPERATION,
    ROOT,
}
use SyntaxKind::*;

impl From<SyntaxKind> for cstree::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u16)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Lang {}
impl cstree::Language for Lang {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: cstree::SyntaxKind) -> Self::Kind {
        assert!(raw.0 <= ROOT as u16);
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }

    fn kind_to_raw(kind: Self::Kind) -> cstree::SyntaxKind {
        kind.into()
    }
}

type SyntaxNode = cstree::SyntaxNode<Lang>;
#[allow(unused)]
type SyntaxToken = cstree::SyntaxToken<Lang>;
#[allow(unused)]
type SyntaxElement = cstree::NodeOrToken<SyntaxNode, SyntaxToken>;
type SyntaxElementRef<'a> = cstree::NodeOrToken<&'a SyntaxNode, &'a SyntaxToken>;

struct Parser<'input, I: Iterator<Item = (SyntaxKind, &'input str)>> {
    builder: GreenNodeBuilder<'static, 'static>,
    iter:    Peekable<I>,
}
impl<'input, I: Iterator<Item = (SyntaxKind, &'input str)>> Parser<'input, I> {
    fn peek(&mut self) -> Option<SyntaxKind> {
        while self.iter.peek().map(|&(t, _)| t == WHITESPACE).unwrap_or(false) {
            self.bump();
        }
        self.iter.peek().map(|&(t, _)| t)
    }

    fn bump(&mut self) {
        if let Some((token, string)) = self.iter.next() {
            self.builder.token(token.into(), string);
        }
    }

    fn parse_val(&mut self) {
        match self.peek() {
            Some(NUMBER) => self.bump(),
            _ => {
                self.builder.start_node(ERROR.into());
                self.bump();
                self.builder.finish_node();
            }
        }
    }

    fn handle_operation(&mut self, tokens: &[SyntaxKind], next: fn(&mut Self)) {
        let checkpoint = self.builder.checkpoint();
        next(self);
        while self.peek().map(|t| tokens.contains(&t)).unwrap_or(false) {
            self.builder.start_node_at(checkpoint, OPERATION.into());
            self.bump();
            next(self);
            self.builder.finish_node();
        }
    }

    fn parse_mul(&mut self) {
        self.handle_operation(&[MUL, DIV], Self::parse_val)
    }

    fn parse_add(&mut self) {
        self.handle_operation(&[ADD, SUB], Self::parse_mul)
    }

    fn parse(mut self) -> (SyntaxNode, impl Resolver) {
        self.builder.start_node(ROOT.into());
        self.parse_add();
        self.builder.finish_node();

        let (tree, resolver) = self.builder.finish();
        (SyntaxNode::new_root(tree), resolver.unwrap().into_resolver())
    }
}

fn print(indent: usize, element: SyntaxElementRef<'_>, resolver: &impl Resolver) {
    let kind = element.kind();
    print!("{:indent$}", "", indent = indent);
    match element {
        NodeOrToken::Node(node) => {
            println!("- {:?}", kind);
            for child in node.children_with_tokens() {
                print(indent + 2, child, resolver);
            }
        }

        NodeOrToken::Token(token) => println!("- {:?} {:?}", token.resolve_text(resolver), kind),
    }
}

fn main() {
    let (ast, resolver) = Parser {
        builder: GreenNodeBuilder::new(),
        iter:    vec![
            // 1 + 2 * 3 + 4
            (NUMBER, "1"),
            (WHITESPACE, " "),
            (ADD, "+"),
            (WHITESPACE, " "),
            (NUMBER, "2"),
            (WHITESPACE, " "),
            (MUL, "*"),
            (WHITESPACE, " "),
            (NUMBER, "3"),
            (WHITESPACE, " "),
            (ADD, "+"),
            (WHITESPACE, " "),
            (NUMBER, "4"),
        ]
        .into_iter()
        .peekable(),
    }
    .parse();
    print(0, (&ast).into(), &resolver);
}
