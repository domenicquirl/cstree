use crate::{build_recursive, build_tree_with_cache, ResolvedNode};

use super::{Element, SyntaxNode, TestLang};
use cstree::{interning::new_interner, GreenNodeBuilder, NodeCache, NodeOrToken};
use serde_test::Token;
use std::fmt;

/// Macro for generating a list of `serde_test::Token`s using a simpler DSL.
macro_rules! event_tokens {
    ($($name:ident($($token:tt)*)),*) => {
        [
            $(
                event_tokens!(@token, $name($($token)*))
            ),*
        ].concat()
    };

    (@token, token($kind:expr, $str:expr)) => {
        [
            Token::Struct { name: "Event", len: 2 },
            Token::BorrowedStr("t"),
            Token::BorrowedStr("Token"),
            Token::BorrowedStr("c"),
            Token::Tuple { len: 2 },
            Token::U16($kind),
            Token::BorrowedStr($str),
            Token::TupleEnd,
            Token::StructEnd,
        ].as_ref()
    };

    (@token, node($kind:expr, $data:expr)) => {
        [
            Token::Struct { name: "Event", len: 2 },
            Token::BorrowedStr("t"),
            Token::BorrowedStr("EnterNode"),
            Token::BorrowedStr("c"),
            Token::Tuple { len: 2 },
            Token::U16($kind),
            Token::Bool($data),
            Token::TupleEnd,
            Token::StructEnd,
        ].as_ref()
    };

    (@token, leave_node()) => {
        [
            Token::Struct { name: "Event", len: 1 },
            Token::BorrowedStr("t"),
            Token::BorrowedStr("LeaveNode"),
            Token::StructEnd,
        ].as_ref()
    };

    (@token, data($data:expr)) => {
        [Token::Str($data)].as_ref()
    };

    (@token, seq($len:expr)) => {
        [Token::Seq { len: Option::Some($len) }].as_ref()
    };

    (@token, seq_end()) => {
        [Token::SeqEnd].as_ref()
    };

    (@token, tuple($len:expr)) => {
        [Token::Tuple { len: $len }].as_ref()
    };

    (@token, tuple_end()) => {
        [Token::TupleEnd].as_ref()
    };

    (@token,) => {};
}

fn three_level_tree_with_data_tokens() -> Vec<Token> {
    event_tokens!(
        tuple(2),
        seq(14),
        node(0, true),
        node(1, true),
        node(2, true),
        token(3, "foo"),
        token(4, "bar"),
        leave_node(),
        token(5, "baz"),
        leave_node(),
        node(6, true),
        token(7, "pub"),
        token(8, "fn"),
        token(9, "tree"),
        leave_node(),
        leave_node(),
        seq_end(),
        seq(4),
        data("1"),
        data("2"),
        data("3"),
        data("4"),
        seq_end(),
        tuple_end()
    )
}

fn three_level_tree_tokens() -> Vec<Token> {
    event_tokens!(
        tuple(2),
        seq(14),
        node(0, false),
        node(1, false),
        node(2, false),
        token(3, "foo"),
        token(4, "bar"),
        leave_node(),
        token(5, "baz"),
        leave_node(),
        node(6, false),
        token(7, "pub"),
        token(8, "fn"),
        token(9, "tree"),
        leave_node(),
        leave_node(),
        seq_end(),
        seq(0),
        seq_end(),
        tuple_end()
    )
}

struct NonSerializable;

/// Serializable SyntaxNode that doesn't have a identity `PartialEq` implementation,
/// but checks if both trees have equal nodes and tokens.
struct TestNode {
    node:      ResolvedNode<String>,
    with_data: bool,
}

impl TestNode {
    fn new(node: ResolvedNode<String>) -> Self {
        Self { node, with_data: false }
    }

    fn with_data(node: ResolvedNode<String>) -> Self {
        Self { node, with_data: true }
    }
}

impl fmt::Debug for TestNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.node, f)
    }
}

impl serde::Serialize for TestNode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if self.with_data {
            self.node.as_serialize_with_data().serialize(serializer)
        } else {
            self.node.serialize(serializer)
        }
    }
}

impl<'de> serde::Deserialize<'de> for TestNode {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self {
            node:      ResolvedNode::deserialize(deserializer)?,
            with_data: true,
        })
    }
}

impl PartialEq for TestNode {
    fn eq(&self, other: &TestNode) -> bool {
        self.node.kind() == other.node.kind()
            && self.node.get_data() == other.node.get_data()
            && self.node.text_range() == other.node.text_range()
            && self
                .node
                .children_with_tokens()
                .zip(other.node.children_with_tokens())
                .all(|(this, other)| match (this, other) {
                    (NodeOrToken::Node(this), NodeOrToken::Node(other)) => {
                        TestNode::new(this.clone()) == TestNode::new(other.clone())
                    }
                    (NodeOrToken::Token(this), NodeOrToken::Token(other)) => {
                        this.kind() == other.kind() && this.text_range() == other.text_range()
                    }
                    _ => unreachable!(),
                })
    }
}

#[rustfmt::skip]
fn three_level_tree() -> Element<'static> {
    use Element::*;

    Node(vec![
        Node(vec![
             Node(vec![
                  Token("foo"),
                  Token("bar")
             ]),
             Token("baz")
        ]),
        Node(vec![
             Token("pub"),
             Token("fn"),
             Token("tree")
        ]),
    ])
}

fn build_tree(root: Element<'_>) -> ResolvedNode<String> {
    let mut builder: GreenNodeBuilder<TestLang> = GreenNodeBuilder::new();
    build_recursive(&root, &mut builder, 0);
    let (node, cache) = builder.finish();
    SyntaxNode::new_root_with_resolver(node, cache.unwrap().into_interner().unwrap())
}

fn attach_data(node: &SyntaxNode<String>) {
    node.descendants().enumerate().for_each(|(idx, node)| {
        node.set_data(format!("{}", idx + 1));
    });
}

#[test]
fn serialize_tree_with_data_with_resolver() {
    let mut interner = new_interner();
    let mut cache = NodeCache::with_interner(&mut interner);

    let root = three_level_tree();
    let root = build_tree_with_cache(&root, &mut cache);
    let tree = SyntaxNode::<String>::new_root(root.clone());
    attach_data(&tree);

    let serialized = serde_json::to_string(&tree.as_serialize_with_data_with_resolver(&interner)).unwrap();
    let deserialized: TestNode = serde_json::from_str(&serialized).unwrap();

    let expected = SyntaxNode::new_root_with_resolver(root, interner);
    attach_data(&expected);
    assert_eq!(TestNode::new(expected), deserialized);
}

#[test]
fn serialize_tree_with_resolver() {
    let mut interner = new_interner();
    let mut cache = NodeCache::with_interner(&mut interner);

    let root = three_level_tree();
    let root = build_tree_with_cache(&root, &mut cache);
    let tree = SyntaxNode::<NonSerializable>::new_root(root.clone());

    let serialized = serde_json::to_string(&tree.as_serialize_with_resolver(&interner)).unwrap();
    let deserialized: TestNode = serde_json::from_str(&serialized).unwrap();

    let expected = SyntaxNode::new_root_with_resolver(root, interner);
    assert_eq!(TestNode::new(expected), deserialized);
}

#[test]
fn serialize_tree_with_data() {
    let tree = build_tree(three_level_tree());
    let tree = TestNode::with_data(tree);
    attach_data(&tree.node);

    serde_test::assert_tokens(&tree, three_level_tree_with_data_tokens().as_slice());
}

#[test]
fn serialize_tree_without_data() {
    let tree = build_tree(three_level_tree());
    let tree = TestNode::new(tree);

    serde_test::assert_tokens(&tree, three_level_tree_tokens().as_slice());
}
