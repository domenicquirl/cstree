use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use cstree::{
    RawSyntaxKind,
    Syntax,
    build::*,
    green::GreenNode,
    interning::{Interner, new_interner},
};

#[derive(Debug)]
pub enum Element<'s> {
    Node(Vec<Element<'s>>),
    Token(&'s str),
    Plus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestKind {
    Element { n: u32 },
    Plus,
}

impl Syntax for TestKind {
    fn from_raw(raw: RawSyntaxKind) -> Self {
        if raw.0 == u32::MAX - 1 {
            TestKind::Plus
        } else {
            TestKind::Element { n: raw.0 }
        }
    }

    fn into_raw(self) -> RawSyntaxKind {
        match self {
            TestKind::Element { n } => RawSyntaxKind(n),
            TestKind::Plus => RawSyntaxKind(u32::MAX - 1),
        }
    }

    fn static_text(self) -> Option<&'static str> {
        match self {
            TestKind::Plus => Some("+"),
            TestKind::Element { .. } => None,
        }
    }
}

pub fn build_tree_with_cache<I>(root: &Element<'_>, cache: &mut NodeCache<'_, I>, use_static_text: bool) -> GreenNode
where
    I: Interner,
{
    let mut builder: GreenNodeBuilder<TestKind, I> = GreenNodeBuilder::with_cache(cache);
    build_recursive(root, &mut builder, 0, use_static_text);
    let (node, cache) = builder.finish();
    assert!(cache.is_none());
    node
}

pub fn build_recursive<I>(
    root: &Element<'_>,
    builder: &mut GreenNodeBuilder<'_, '_, TestKind, I>,
    mut from: u32,
    use_static_text: bool,
) -> u32
where
    I: Interner,
{
    match root {
        Element::Node(children) => {
            builder.start_node(TestKind::Element { n: from });
            for child in children {
                from = build_recursive(child, builder, from + 1, use_static_text);
            }
            builder.finish_node();
        }
        Element::Token(text) => {
            builder.token(TestKind::Element { n: from }, text);
        }
        Element::Plus if use_static_text => {
            builder.static_token(TestKind::Plus);
        }
        Element::Plus => {
            builder.token(TestKind::Plus, "+");
        }
    }
    from
}

fn two_level_tree() -> Element<'static> {
    use Element::*;
    Node(vec![
        Node(vec![Token("0.0"), Plus, Token("0.1")]),
        Node(vec![Token("1.0")]),
        Node(vec![Token("2.0"), Plus, Token("2.1"), Plus, Token("2.2")]),
    ])
}

pub fn create(c: &mut Criterion) {
    #[cfg(not(feature = "lasso_compat"))]
    const GROUP_NAME: &str = "two-level tree (default interner)";
    #[cfg(feature = "lasso_compat")]
    const GROUP_NAME: &str = "two-level tree (lasso)";

    let mut group = c.benchmark_group(GROUP_NAME);
    group.throughput(Throughput::Elements(1));

    let mut interner = new_interner();
    let mut cache = NodeCache::with_interner(&mut interner);
    let tree = two_level_tree();

    group.bench_function("with static text", |b| {
        b.iter(|| {
            let tree = build_tree_with_cache(&tree, &mut cache, true);
            black_box(tree);
        })
    });

    group.bench_function("without static text", |b| {
        b.iter(|| {
            let tree = build_tree_with_cache(&tree, &mut cache, false);
            black_box(tree);
        })
    });

    group.finish();
}

criterion_group!(benches, create);
criterion_main!(benches);
