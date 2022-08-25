//! Serialization and Deserialization for syntax trees.

use crate::{
    interning::{IntoResolver, Resolver},
    GreenNodeBuilder, Language, NodeOrToken, ResolvedNode, SyntaxKind, SyntaxNode, WalkEvent,
};
use serde::{
    de::{Error, SeqAccess, Visitor},
    ser::SerializeTuple,
    Deserialize, Serialize,
};
use std::{collections::VecDeque, fmt, marker::PhantomData};

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
/// Takes the `Language` (`$l`), `SyntaxNode` (`$node`), `Resolver` (`$resolver`),
/// `Serializer` (`$serializer`), and an optional `data_list` which must be a `mut Vec<D>`.
macro_rules! gen_serialize {
    ($l:ident, $node:expr, $resolver:expr, $ser:ident, $($data_list:ident)?) => {{
        #[allow(unused_variables)]
        let events = $node.preorder_with_tokens().filter_map(|event| match event {
            WalkEvent::Enter(NodeOrToken::Node(node)) => {
                let has_data = false;
                $(let has_data = node
                    .get_data()
                    .map(|data| {
                        $data_list.push(data);
                        true
                    })
                    .unwrap_or(false);)?

                Some(Event::EnterNode($l::kind_to_raw(node.kind()), has_data))
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
    /// The second parameter indicates if this node needs data.
    /// If the boolean is true, the next element inside the data list
    /// must be attached to this node.
    EnterNode(SyntaxKind, bool),
    Token(SyntaxKind, &'text str),
    LeaveNode,
}

/// Make a `SyntaxNode` serializable but without serializing the data.
pub(crate) struct SerializeWithResolver<'node, 'resolver, L: Language, D: 'static, R: ?Sized> {
    pub(crate) node:     &'node SyntaxNode<L, D>,
    pub(crate) resolver: &'resolver R,
}

/// Make a `SyntaxNode` serializable which will include the data for serialization.
pub(crate) struct SerializeWithData<'node, 'resolver, L: Language, D: 'static, R: ?Sized> {
    pub(crate) node:     &'node SyntaxNode<L, D>,
    pub(crate) resolver: &'resolver R,
}

impl<L, D, R> Serialize for SerializeWithData<'_, '_, L, D, R>
where
    L: Language,
    R: Resolver + ?Sized,
    D: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut data_list = Vec::new();
        gen_serialize!(L, self.node, self.resolver, serializer, data_list)
    }
}

impl<L, D, R> Serialize for SerializeWithResolver<'_, '_, L, D, R>
where
    L: Language,
    R: Resolver + ?Sized,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        gen_serialize!(L, self.node, self.resolver, serializer,)
    }
}

impl<L, D> Serialize for ResolvedNode<L, D>
where
    L: Language,
    D: Serialize,
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

impl<'de, L, D> Deserialize<'de> for ResolvedNode<L, D>
where
    L: Language,
    D: Deserialize<'de>,
{
    // Deserialization is done by walking down the deserialized event stream,
    // which is the first element inside the tuple. The events
    // are then passed to a `GreenNodeBuilder` which will do all
    // the hard work for use.
    //
    // While walking the event stream, we also store a list of booleans,
    // which indicate which node needs to set data. After creating the tree,
    // we walk down the nodes, check if the bool at `data_list[idx]` is true,
    // and if so, pop the first element of the data list and attach the data
    // to the current node.
    fn deserialize<DE>(deserializer: DE) -> Result<Self, DE::Error>
    where
        DE: serde::Deserializer<'de>,
    {
        struct EventVisitor<L: Language, D: 'static> {
            _marker: PhantomData<fn() -> ResolvedNode<L, D>>,
        }

        impl<'de, L, D> Visitor<'de> for EventVisitor<L, D>
        where
            L: Language,
            D: Deserialize<'de>,
        {
            type Value = (ResolvedNode<L, D>, VecDeque<bool>);

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a list of tree events")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut builder: GreenNodeBuilder<L> = GreenNodeBuilder::new();
                let mut data_indices = VecDeque::new();

                while let Some(next) = seq.next_element::<Event<'_>>()? {
                    match next {
                        Event::EnterNode(kind, has_data) => {
                            builder.start_node(L::kind_from_raw(kind));
                            data_indices.push_back(has_data);
                        }
                        Event::Token(kind, text) => builder.token(L::kind_from_raw(kind), text),
                        Event::LeaveNode => builder.finish_node(),
                    }
                }

                let (tree, cache) = builder.finish();
                let tree =
                    ResolvedNode::new_root_with_resolver(tree, cache.unwrap().into_interner().unwrap().into_resolver());
                Ok((tree, data_indices))
            }
        }

        struct ProcessedEvents<L: Language, D: 'static>(ResolvedNode<L, D>, VecDeque<bool>);
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

        let (ProcessedEvents(tree, data_indices), mut data) =
            <(ProcessedEvents<L, D>, VecDeque<D>)>::deserialize(deserializer)?;

        tree.descendants().zip(data_indices).try_for_each(|(node, has_data)| {
            if has_data {
                let data = data
                    .pop_front()
                    .ok_or_else(|| DE::Error::custom("invalid serialized tree"))?;
                node.set_data(data);
            }
            <Result<(), DE::Error>>::Ok(())
        })?;

        if !data.is_empty() {
            Err(DE::Error::custom(
                "serialized SyntaxNode contained too many data elements",
            ))
        } else {
            Ok(tree)
        }
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
