//! Serialization and Deserialization for syntax trees.

use crate::{interning::Resolver, GreenNodeBuilder, Language, NodeOrToken, SyntaxKind, SyntaxNode, WalkEvent};
use serde::{
    de::{SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize, Serialize,
};
use std::{fmt, marker::PhantomData};

type Rodeo = lasso::Rodeo<lasso::Spur, fxhash::FxBuildHasher>;

/// Expands to the first expression, if there's
/// no expression following, otherwise return the second expression.
///
/// Required for having two different values if the argument is `$(...)?`.
macro_rules! data_list {
    ($_:expr, $list:expr) => {
        $list
    };

    ($list:expr,) => {
        $list
    };
}

/// Generate the code that should be put inside the [`Serialize`] implementation
/// of a [`SyntaxNode`]-like type.
///
/// It serializes a [`SyntaxNode`] into a tuple with 2 elements.
/// The first element is the serialized event stream that was generated
/// by [`SyntaxNode::preorder_with_tokens()`].
/// The second element is a list of `D`s, where `D` is the data of the nodes.
/// The data may only be serialized if it's `Some(data)`. Each `EnterNode` event
/// contains a boolean which indicates if this node has a data. If it has one,
/// the deserializer should pop the first element from the data list and continue.
///
/// The macro will not use the `$counter` if the data list is not given.
/// Takes the `Language` (`$l`), `SyntaxNode` (`$node`), `Resolver` (`$resolver`),
/// `Serializer` (`$serializer`), `counter` (which must be a `u16`),
/// and an optional `data_list` which must be a `mut Vec<D>`.
macro_rules! gen_serialize {
    ($l:ident, $node:expr, $resolver:expr, $ser:ident, $counter:ident, $($data_list:ident)?) => {{
        #[allow(unused_variables)]
        let events = $node.preorder_with_tokens().filter_map(|event| match event {
            WalkEvent::Enter(NodeOrToken::Node(node)) => {
                let id = 0;
                $(let id = node
                    .get_data()
                    .map(|data| {
                        $data_list.push(data);
                        $counter += 1;
                        $counter
                    })
                    .unwrap_or(0);)?

                Some(Event::EnterNode($l::kind_to_raw(node.kind()), id))
            }
            WalkEvent::Enter(NodeOrToken::Token(tok)) => Some(Event::Token($l::kind_to_raw(tok.kind()), tok.resolve_text($resolver))),

            WalkEvent::Leave(NodeOrToken::Node(_)) => Some(Event::LeaveNode),
            WalkEvent::Leave(NodeOrToken::Token(_)) => None,
        });

        let mut tuple = $ser.serialize_tuple(2)?;

        // TODO(Stupremee): We can easily avoid this allocation but it would
        // require more weird and annoying-to-write code, so I'll skip it for now.
        tuple.serialize_element(&events.collect::<Vec<_>>())?;
        tuple.serialize_element(&data_list!(Vec::<()>::new(), $($data_list)?))?;

        tuple.end()
    }};
}

#[derive(Deserialize, Serialize)]
#[serde(tag = "t", content = "c")]
enum Event<'text> {
    /// The second parameter represents the data of the node.
    /// `0` means there's no data, otherwise it's the `idx + 1`,
    /// where `idx` is the element inside the data list.
    EnterNode(SyntaxKind, u32),
    Token(SyntaxKind, &'text str),
    LeaveNode,
}

/// Make a `SyntaxNode` serializable, by using an external resolver instead of
/// the resolver that is inside the tree.
pub(crate) struct SerializeWithResolver<'node, 'resolver, L: Language, D: 'static, RN: 'static, R> {
    pub(crate) node:     &'node SyntaxNode<L, D, RN>,
    pub(crate) resolver: &'resolver R,
}

/// Make a `SyntaxNode` serializable, even if it doesn't have
/// data that is serializable.
pub(crate) struct SerializeWithData<'node, 'resolver, L: Language, D: 'static, RN: 'static, R> {
    pub(crate) node:     &'node SyntaxNode<L, D, RN>,
    pub(crate) resolver: &'resolver R,
}

impl<L, D, RN, R> Serialize for SerializeWithData<'_, '_, L, D, RN, R>
where
    L: Language,
    R: Resolver,
    D: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut counter = 0;
        let mut data_list = Vec::new();
        gen_serialize!(L, self.node, self.resolver, serializer, counter, data_list)
    }
}

impl<L, D, RN, R> Serialize for SerializeWithResolver<'_, '_, L, D, RN, R>
where
    L: Language,
    R: Resolver,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        gen_serialize!(L, self.node, self.resolver, serializer, __,)
    }
}

impl<L, D, R> Serialize for SyntaxNode<L, D, R>
where
    L: Language,
    D: Serialize,
    R: Resolver,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let node = SerializeWithResolver {
            node:     self,
            resolver: self.resolver().as_ref(),
        };
        node.serialize(serializer)
    }
}

impl<'de, L, D> Deserialize<'de> for SyntaxNode<L, D, Rodeo>
where
    L: Language,
    D: Deserialize<'de>,
{
    // Deserialization is done by walking down the deserialized event stream,
    // which is the first element inside the tuple. The events
    // are then passed to a `GreenNodeBuilder` which will do all
    // the hard work for use. While walking the event stream, we also store
    // a list of booleans, which indicates which node needs to set data.
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

                while let Some(next) = seq.next_element::<Event<'_>>()? {
                    match next {
                        Event::EnterNode(kind, id) => {
                            builder.start_node(kind);
                            ids.push(id);
                        }
                        Event::Token(kind, text) => builder.token(kind, text),
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
