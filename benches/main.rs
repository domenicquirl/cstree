use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use cstree::*;
use lasso::{Interner, Rodeo};

#[derive(Debug)]
pub enum Element<'s> {
    Node(Vec<Element<'s>>),
    Token(&'s str),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum TestLang {}
impl Language for TestLang {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: SyntaxKind) -> Self::Kind {
        raw
    }

    fn kind_to_raw(kind: Self::Kind) -> SyntaxKind {
        kind
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

pub fn build_recursive<'c, 'i, I>(root: &Element<'_>, builder: &mut GreenNodeBuilder<'c, 'i, I>, mut from: u16) -> u16
where
    I: Interner,
{
    match root {
        Element::Node(children) => {
            builder.start_node(SyntaxKind(from));
            for child in children {
                from = build_recursive(child, builder, from + 1);
            }
            builder.finish_node();
        }
        Element::Token(text) => {
            builder.token(SyntaxKind(from), *text);
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
    let mut group = c.benchmark_group("qualification");
    group.throughput(Throughput::Elements(1));

    let mut interner = Rodeo::new();
    let mut cache = NodeCache::with_interner(&mut interner);
    let tree = two_level_tree();

    group.bench_function("two-level tree", |b| {
        b.iter(|| {
            for _ in 0..100_000 {
                let _tree = build_tree_with_cache(&tree, &mut cache);
            }
        })
    });

    group.finish();
}

criterion_group!(benches, create);
criterion_main!(benches);
