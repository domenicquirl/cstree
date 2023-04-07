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

use cstree::{build::GreenNodeBuilder, interning::Resolver, util::NodeOrToken};
use std::iter::Peekable;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u32)]
enum SyntaxKind {
    Whitespace = 0,

    Add,
    Sub,
    Mul,
    Div,

    Number,
    Error,
    Operation,
    Root,
}
use SyntaxKind::*;

impl From<SyntaxKind> for cstree::RawSyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        Self(kind as u32)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Lang {}
impl cstree::Language for Lang {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: cstree::RawSyntaxKind) -> Self::Kind {
        assert!(raw.0 <= Root as u32);
        unsafe { std::mem::transmute::<u32, SyntaxKind>(raw.0) }
    }

    fn kind_to_raw(kind: Self::Kind) -> cstree::RawSyntaxKind {
        kind.into()
    }

    fn static_text(kind: Self::Kind) -> Option<&'static str> {
        match kind {
            Add => Some("+"),
            Sub => Some("-"),
            Mul => Some("*"),
            Div => Some("/"),
            _ => None,
        }
    }
}

type SyntaxNode = cstree::syntax::SyntaxNode<Lang>;
#[allow(unused)]
type SyntaxToken = cstree::syntax::SyntaxToken<Lang>;
#[allow(unused)]
type SyntaxElement = cstree::util::NodeOrToken<SyntaxNode, SyntaxToken>;
type SyntaxElementRef<'a> = cstree::util::NodeOrToken<&'a SyntaxNode, &'a SyntaxToken>;

struct Parser<'input, I: Iterator<Item = (SyntaxKind, &'input str)>> {
    builder: GreenNodeBuilder<'static, 'static, Lang>,
    iter:    Peekable<I>,
}
impl<'input, I: Iterator<Item = (SyntaxKind, &'input str)>> Parser<'input, I> {
    fn peek(&mut self) -> Option<SyntaxKind> {
        while self.iter.peek().map(|&(t, _)| t == Whitespace).unwrap_or(false) {
            self.bump();
        }
        self.iter.peek().map(|&(t, _)| t)
    }

    fn bump(&mut self) {
        if let Some((token, string)) = self.iter.next() {
            self.builder.token(token, string);
        }
    }

    fn parse_val(&mut self) {
        match self.peek() {
            Some(Number) => self.bump(),
            _ => {
                self.builder.start_node(Error);
                self.bump();
                self.builder.finish_node();
            }
        }
    }

    fn handle_operation(&mut self, tokens: &[SyntaxKind], next: fn(&mut Self)) {
        let checkpoint = self.builder.checkpoint();
        next(self);
        while self.peek().map(|t| tokens.contains(&t)).unwrap_or(false) {
            self.builder.start_node_at(checkpoint, Operation);
            self.bump();
            next(self);
            self.builder.finish_node();
        }
    }

    fn parse_mul(&mut self) {
        self.handle_operation(&[Mul, Div], Self::parse_val)
    }

    fn parse_add(&mut self) {
        self.handle_operation(&[Add, Sub], Self::parse_mul)
    }

    fn parse(mut self) -> (SyntaxNode, impl Resolver) {
        self.builder.start_node(Root);
        self.parse_add();
        self.builder.finish_node();

        let (tree, cache) = self.builder.finish();
        (SyntaxNode::new_root(tree), cache.unwrap().into_interner().unwrap())
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
            (Number, "1"),
            (Whitespace, " "),
            (Add, "+"),
            (Whitespace, " "),
            (Number, "2"),
            (Whitespace, " "),
            (Mul, "*"),
            (Whitespace, " "),
            (Number, "3"),
            (Whitespace, " "),
            (Add, "+"),
            (Whitespace, " "),
            (Number, "4"),
        ]
        .into_iter()
        .peekable(),
    }
    .parse();
    print(0, (&ast).into(), &resolver);
}
