#![cfg(feature = "serde1")]

mod common;

use common::TestLang;
use cstree::{GreenNodeBuilder, NodeOrToken, SyntaxNode};
use serde_test::assert_tokens;

type Rodeo = lasso::Rodeo<lasso::Spur, fxhash::FxBuildHasher>;

fn build_tree() -> SyntaxNode<TestLang, String, Rodeo> {
    let tree = common::big_tree();
    let mut builder = GreenNodeBuilder::new();
    common::build_recursive(&tree, &mut builder, 0);
    let (node, interner) = builder.finish();

    SyntaxNode::<TestLang, _, _>::new_root_with_resolver(node, interner.unwrap())
}

/// Serializable SyntaxNode that doesn't have a identity `PartialEq` implementation,
/// but checks if both trees have equal nodes and tokens.
#[derive(Debug)]
struct TestNode(SyntaxNode<TestLang, String, Rodeo>);

impl serde::Serialize for TestNode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de> serde::Deserialize<'de> for TestNode {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self(SyntaxNode::deserialize(deserializer)?))
    }
}

impl PartialEq<TestNode> for TestNode {
    fn eq(&self, other: &TestNode) -> bool {
        self.0.kind() == other.0.kind()
            && self.0.get_data() == other.0.get_data()
            && self.0.text_range() == other.0.text_range()
            && self
                .0
                .children_with_tokens()
                .zip(other.0.children_with_tokens())
                .all(|(this, other)| match (this, other) {
                    (NodeOrToken::Node(this), NodeOrToken::Node(other)) => {
                        TestNode(this.clone()) == TestNode(other.clone())
                    }
                    (NodeOrToken::Token(this), NodeOrToken::Token(other)) => {
                        this.kind() == other.kind() && this.text_range() == other.text_range()
                    }
                    _ => unreachable!(),
                })
    }
}

#[test]
fn serialize_json_big_tree() {
    let tree = TestNode(build_tree());
    tree.0.children().enumerate().for_each(|(idx, node)| {
        node.set_data(format!("{}", idx));
    });

    let serialized = serde_json::to_string_pretty(&tree).unwrap();
    let deserialized = serde_json::from_str::<TestNode>(&serialized).unwrap();
    assert_eq!(tree, deserialized);
}

#[test]
fn serialize_big_tree() {
    use serde_test::Token::*;

    let tree = TestNode(build_tree());

    #[rustfmt::skip]
    assert_tokens(
        &tree,
        &[
            Tuple { len: 2 },

            Seq { len: Option::Some(14) },
            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("EnterNode"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(0),
            U32(0),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("EnterNode"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(1),
            U32(0),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("EnterNode"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(2),
            U32(0),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("Token"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(3),
            BorrowedStr("foo"),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("Token"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(4),
            BorrowedStr("bar"),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 1 },
            BorrowedStr("t"),
            BorrowedStr("LeaveNode"),
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("Token"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(5),
            BorrowedStr("baz"),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 1 },
            BorrowedStr("t"),
            BorrowedStr("LeaveNode"),
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("EnterNode"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(6),
            U32(0),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("Token"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(7),
            BorrowedStr("pub"),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("Token"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(8),
            BorrowedStr("fn"),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("Token"),
            BorrowedStr("c"),
            Tuple { len: 2 },
            U16(9),
            BorrowedStr("tree"),
            TupleEnd,
            StructEnd,

            Struct { name: "Event", len: 1 },
            BorrowedStr("t"),
            BorrowedStr("LeaveNode"),
            StructEnd,

            Struct { name: "Event", len: 1 },
            BorrowedStr("t"),
            BorrowedStr("LeaveNode"),
            StructEnd,
            SeqEnd,

            Seq { len: Option::Some(0) },
            SeqEnd,

            TupleEnd,
        ],
    );
}
