use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};
use cstree::*;
use lasso::{Interner, Rodeo};

#[derive(Debug)]
pub enum Element<'s> {
    Node(Vec<Element<'s>>),
    Token(&'s str),
    Plus,
}

#[derive(Debug, Clone, Copy)]
pub enum TestKind {
    Element { n: u16 },
    Plus,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum TestLang {}
impl Language for TestLang {
    type Kind = TestKind;

    fn kind_from_raw(raw: SyntaxKind) -> Self::Kind {
        if raw.0 == u16::MAX - 1 {
            TestKind::Plus
        } else {
            TestKind::Element { n: raw.0 }
        }
    }

    fn kind_to_raw(kind: Self::Kind) -> SyntaxKind {
        match kind {
            TestKind::Element { n } => SyntaxKind(n),
            TestKind::Plus => SyntaxKind(u16::MAX - 1),
        }
    }

    fn static_text(kind: Self::Kind) -> Option<&'static str> {
        match kind {
            TestKind::Plus => Some("+"),
            TestKind::Element { .. } => None,
        }
    }
}

pub fn build_tree_with_cache<'c, 'i, I>(root: &Element<'_>, cache: &'c mut NodeCache<'i, I>) -> GreenNode
where
    I: Interner,
{
    let mut builder = GreenNodeBuilder::with_cache(cache);
    build_recursive(root, &mut builder, 0);
    let (node, cache) = builder.finish();
    assert!(cache.is_none());
    node
}

pub fn build_recursive<'c, 'i, I>(
    root: &Element<'_>,
    builder: &mut GreenNodeBuilder<'c, 'i, TestLang, I>,
    mut from: u16,
) -> u16
where
    I: Interner,
{
    match root {
        Element::Node(children) => {
            builder.start_node(TestKind::Element { n: from });
            for child in children {
                from = build_recursive(child, builder, from + 1);
            }
            builder.finish_node();
        }
        Element::Token(text) => {
            builder.token(TestKind::Element { n: from }, *text);
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
        Node(vec![Token("0.0"), Token("0.1")]),
        Node(vec![Token("1.0")]),
        Node(vec![Token("2.0"), Token("2.1"), Token("2.2")]),
    ])
}

pub fn create(c: &mut Criterion) {
    let mut group = c.benchmark_group("re-use cache");
    group.throughput(Throughput::Elements(1));

    let mut interner = Rodeo::new();
    let mut cache = NodeCache::with_interner(&mut interner);
    let tree = two_level_tree();

    group.bench_function("two-level tree", |b| {
        b.iter(|| {
            let tree = build_tree_with_cache(&tree, &mut cache);
            black_box(tree);
        })
    });

    group.finish();
}

criterion_group!(benches, create);
criterion_main!(benches);
