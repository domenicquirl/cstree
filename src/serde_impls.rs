//! Serialization and Deserialization for syntax trees.

use crate::{interning::Resolver, GreenNodeBuilder, Language, NodeOrToken, SyntaxKind, SyntaxNode, WalkEvent};
use serde::{
    de::{SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize, Serialize,
};
use std::{fmt, marker::PhantomData};

type Rodeo = lasso::Rodeo<lasso::Spur, fxhash::FxBuildHasher>;

#[derive(Deserialize, Serialize)]
#[serde(tag = "t", content = "c")]
enum Event<'text, L: Language> {
    /// The second parameter represents the data of the node.
    /// `0` means there's no data, otherwise it's the `idx + 1`,
    /// where `idx` is the element inside the data list.
    EnterNode(L::Kind, u32),
    Token(L::Kind, &'text str),
    LeaveNode,
}

impl<L, D, R> Serialize for SyntaxNode<L, D, R>
where
    L: Language,
    <L as Language>::Kind: Serialize,
    D: Serialize,
    R: Resolver,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut counter = 0;
        let mut data_list = Vec::new();

        let events = self.preorder_with_tokens().filter_map(|event| match event {
            WalkEvent::Enter(NodeOrToken::Node(node)) => {
                let id = node
                    .get_data()
                    .map(|data| {
                        data_list.push(data);
                        counter += 1;
                        counter
                    })
                    .unwrap_or(0);

                Some(Event::<L>::EnterNode(node.kind(), id))
            }
            WalkEvent::Enter(NodeOrToken::Token(tok)) => Some(Event::Token(tok.kind(), tok.text())),

            WalkEvent::Leave(NodeOrToken::Node(_)) => Some(Event::LeaveNode),
            WalkEvent::Leave(NodeOrToken::Token(_)) => None,
        });

        let mut tuple = serializer.serialize_tuple(2)?;

        // TODO(Stupremee): We can easily avoid this allocation but it would
        // require more weird and annoying-to-write code, so I'll skip it for now.
        tuple.serialize_element(&events.collect::<Vec<_>>())?;
        tuple.serialize_element(&data_list)?;
        tuple.end()
    }
}

impl<'de, L, D> Deserialize<'de> for SyntaxNode<L, D, Rodeo>
where
    L: Language,
    <L as Language>::Kind: Deserialize<'de>,
    D: Deserialize<'de>,
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
            D: Deserialize<'de>,
        {
            type Value = (SyntaxNode<L, D, Rodeo>, Vec<u32>);

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a list of tree events")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut builder = GreenNodeBuilder::new();
                let mut ids = Vec::new();

                while let Some(next) = seq.next_element::<Event<'_, L>>()? {
                    match next {
                        Event::EnterNode(kind, id) => {
                            builder.start_node(L::kind_to_raw(kind));
                            ids.push(id);
                        }
                        Event::Token(kind, text) => builder.token(L::kind_to_raw(kind), text),
                        Event::LeaveNode => builder.finish_node(),
                    }
                }

                let (tree, resolver) = builder.finish();
                let tree = SyntaxNode::new_root_with_resolver(tree, resolver.unwrap());
                Ok((tree, ids))
            }
        }

        struct ProcessedEvents<L: Language, D: 'static>(SyntaxNode<L, D, Rodeo>, Vec<u32>);
        impl<'de, L, D> Deserialize<'de> for ProcessedEvents<L, D>
        where
            L: Language,
            <L as Language>::Kind: Deserialize<'de>,
            D: Deserialize<'de>,
        {
            fn deserialize<DE>(deserializer: DE) -> Result<Self, DE::Error>
            where
                DE: serde::Deserializer<'de>,
            {
                let (tree, ids) = deserializer.deserialize_seq(EventVisitor { _marker: PhantomData })?;
                Ok(Self(tree, ids))
            }
        }

        let (ProcessedEvents(tree, ids), mut data) = <(ProcessedEvents<L, D>, Vec<D>)>::deserialize(deserializer)?;

        let mut num_removed = 0;
        tree.descendants().zip(ids).for_each(|(node, id)| {
            if id == 0 {
                return;
            }

            num_removed += 1;
            let data = data.remove(id as usize - num_removed);
            node.set_data(data);
        });

        Ok(tree)
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
