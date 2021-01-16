//! Serialization and Deserialization for syntax trees.

use crate::{interning::Resolver, GreenNodeBuilder, Language, NodeOrToken, SyntaxKind, SyntaxNode, WalkEvent};
use serde::{
    de::{SeqAccess, Visitor},
    Deserialize, Serialize,
};
use std::{fmt, marker::PhantomData};

type Rodeo = lasso::Rodeo<lasso::Spur, fxhash::FxBuildHasher>;

#[derive(Deserialize, Serialize)]
#[serde(tag = "t", content = "c")]
enum Event<'text, L: Language> {
    EnterNode(L::Kind),
    Token(L::Kind, &'text str),
    LeaveNode,
}

impl<L, D, R> Serialize for SyntaxNode<L, D, R>
where
    L: Language,
    <L as Language>::Kind: Serialize,
    R: Resolver,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let events = self.preorder_with_tokens().filter_map(|event| match event {
            WalkEvent::Enter(NodeOrToken::Node(node)) => Some(Event::<L>::EnterNode(node.kind())),
            WalkEvent::Enter(NodeOrToken::Token(tok)) => Some(Event::Token(tok.kind(), tok.text())),

            WalkEvent::Leave(NodeOrToken::Node(_)) => Some(Event::LeaveNode),
            WalkEvent::Leave(NodeOrToken::Token(_)) => None,
        });

        serializer.collect_seq(events)
    }
}

impl<'de, L, D> Deserialize<'de> for SyntaxNode<L, D, Rodeo>
where
    L: Language,
    <L as Language>::Kind: Deserialize<'de>,
{
    fn deserialize<DE>(deserializer: DE) -> Result<Self, DE::Error>
    where
        DE: serde::Deserializer<'de>,
    {
        struct EventVisitor<L: Language, D: 'static> {
            _marker: PhantomData<SyntaxNode<L, D, Rodeo>>,
        }

        impl<'de, L, D> Visitor<'de> for EventVisitor<L, D>
        where
            L: Language,
            <L as Language>::Kind: Deserialize<'de>,
        {
            type Value = SyntaxNode<L, D, Rodeo>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a list of tree events")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut builder = GreenNodeBuilder::new();

                while let Some(next) = seq.next_element::<Event<'_, L>>()? {
                    match next {
                        Event::EnterNode(kind) => builder.start_node(L::kind_to_raw(kind)),
                        Event::Token(kind, text) => builder.token(L::kind_to_raw(kind), text),
                        Event::LeaveNode => builder.finish_node(),
                    }
                }

                let (tree, resolver) = builder.finish();
                Ok(SyntaxNode::new_root_with_resolver(tree, resolver.unwrap()))
            }
        }

        deserializer.deserialize_seq(EventVisitor { _marker: PhantomData })
    }
}

impl Serialize for SyntaxKind {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u16(self.0)
    }
}

impl<'de> Deserialize<'de> for SyntaxKind {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self(u16::deserialize(deserializer)?))
    }
}
