mod common;

use common::TestLang;
use cstree::{GreenNodeBuilder, SyntaxNode};
use serde_test::{assert_tokens, Token::*};

type Rodeo = lasso::Rodeo<lasso::Spur, fxhash::FxBuildHasher>;

fn build_tree() -> SyntaxNode<TestLang, (), Rodeo> {
    let tree = common::big_tree();
    let mut builder = GreenNodeBuilder::new();
    common::build_recursive(&tree, &mut builder, 0);
    let (node, interner) = builder.finish();

    SyntaxNode::<TestLang, (), _>::new_root_with_resolver(node, interner.unwrap())
}

/// Serializable SyntaxNode that doesn't have a identity `PartialEq` implementation.
#[derive(Debug)]
struct TestNode(SyntaxNode<TestLang, (), Rodeo>);

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
        self.0.kind() == other.0.kind() && self.0.text_range() == other.0.text_range()
    }
}

#[test]
fn serialize_big_tree() {
    let tree = TestNode(build_tree());
    print!("{}", serde_json::to_string_pretty(&tree).unwrap());

    #[rustfmt::skip]
    assert_tokens(
        &tree,
        &[
            Seq { len: Option::None },

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("EnterNode"),
            BorrowedStr("c"),
            U16(0),
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("EnterNode"),
            BorrowedStr("c"),
            U16(1),
            StructEnd,

            Struct { name: "Event", len: 2 },
            BorrowedStr("t"),
            BorrowedStr("EnterNode"),
            BorrowedStr("c"),
            U16(2),
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
            U16(6),
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
        ],
    );
}
