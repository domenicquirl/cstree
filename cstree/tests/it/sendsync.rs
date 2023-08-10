#![allow(clippy::redundant_clone)]

use crossbeam_utils::thread::scope;
use std::{thread, time::Duration};

use super::{build_recursive, Element, ResolvedNode, SyntaxKind, SyntaxNode};
use cstree::build::GreenNodeBuilder;

// Excercise the multi-threaded interner when the corresponding feature is enabled.

#[cfg(feature = "multi_threaded_interning")]
use cstree::interning::{new_threaded_interner, MultiThreadedTokenInterner};

#[cfg(not(feature = "multi_threaded_interning"))]
fn get_builder() -> GreenNodeBuilder<'static, 'static, SyntaxKind> {
    GreenNodeBuilder::new()
}

#[cfg(feature = "multi_threaded_interning")]
fn get_builder() -> GreenNodeBuilder<'static, 'static, SyntaxKind, MultiThreadedTokenInterner> {
    let interner = new_threaded_interner();
    GreenNodeBuilder::from_interner(interner)
}

fn build_tree<D>(root: &Element<'_>) -> ResolvedNode<D> {
    let mut builder = get_builder();
    build_recursive(root, &mut builder, 0);
    let (node, cache) = builder.finish();
    SyntaxNode::new_root_with_resolver(node, cache.unwrap().into_interner().unwrap())
}

fn two_level_tree() -> Element<'static> {
    use Element::*;
    Node(vec![
        Node(vec![Token("0.0"), Token("0.1")]),
        Node(vec![Token("1.0")]),
        Node(vec![Token("2.0"), Token("2.1"), Token("2.2")]),
    ])
}

#[test]
#[cfg_attr(miri, ignore)]
fn send() {
    let tree = two_level_tree();
    let tree = build_tree::<()>(&tree);
    let thread_tree = tree.clone();
    let thread = thread::spawn(move || {
        let leaf1_0 = thread_tree
            .children()
            .nth(1)
            .unwrap()
            .children_with_tokens()
            .next()
            .unwrap();
        let leaf1_0 = leaf1_0.into_token().unwrap();
        leaf1_0.text().to_string()
    });
    assert_eq!(thread.join().unwrap(), "1.0");
}

#[test]
#[cfg_attr(miri, ignore)]
fn send_data() {
    let tree = two_level_tree();
    let tree = build_tree::<String>(&tree);
    let thread_tree = tree.clone();
    {
        let node2 = tree.children().nth(2).unwrap();
        assert_eq!(*node2.try_set_data("data".into()).unwrap(), "data");
        let data = node2.get_data().unwrap();
        assert_eq!(data.as_str(), "data");
        node2.set_data("payload".into());
        let data = node2.get_data().unwrap();
        assert_eq!(data.as_str(), "payload");
    }
    let t = thread::spawn(move || {
        let node2 = thread_tree.children().nth(2).unwrap();
        assert!(node2.try_set_data("already present".into()).is_err());
        let data = node2.get_data().unwrap();
        assert_eq!(data.as_str(), "payload");
        node2.set_data("new data".into());
    });
    // wait for t to finish
    t.join().unwrap();
    {
        let node2 = tree.children().nth(2).unwrap();
        let data = node2.get_data().unwrap();
        assert_eq!(data.as_str(), "new data");
        node2.clear_data();
        // re-use `data` after node data was cleared
        assert_eq!(data.as_str(), "new data");
    }
    let thread_tree = tree.clone();
    thread::spawn(move || {
        let node2 = thread_tree.children().nth(2).unwrap();
        assert_eq!(node2.get_data(), None);
    })
    .join()
    .unwrap();
}

#[test]
#[cfg_attr(miri, ignore)]
fn sync() {
    let tree = two_level_tree();
    let tree = build_tree::<()>(&tree);
    let thread_tree = &tree;
    let result = scope(move |s| {
        s.spawn(move |_| {
            let leaf1_0 = thread_tree
                .children()
                .nth(1)
                .unwrap()
                .children_with_tokens()
                .next()
                .unwrap();
            let leaf1_0 = leaf1_0.into_token().unwrap();
            leaf1_0.resolve_text(thread_tree.resolver().as_ref()).to_string()
        })
        .join()
        .unwrap()
    });
    assert_eq!(result.unwrap(), "1.0");
}

#[test]
#[cfg_attr(miri, ignore)]
fn drop_send() {
    let tree = two_level_tree();
    let tree = build_tree::<()>(&tree);
    let thread_tree = tree.clone();
    let thread = thread::spawn(move || {
        drop(thread_tree);
    });
    thread.join().unwrap();
    thread::sleep(Duration::from_millis(500));
    drop(tree);

    let tree = two_level_tree();
    let tree = build_tree::<()>(&tree);
    let thread_tree = tree.clone();
    drop(tree);
    let thread = thread::spawn(move || {
        thread::sleep(Duration::from_millis(500));
        drop(thread_tree);
    });
    thread.join().unwrap();
}

#[test]
#[cfg_attr(miri, ignore)]
#[allow(dropping_references)]
fn drop_sync() {
    let tree = two_level_tree();
    let tree = build_tree::<()>(&tree);
    let thread_tree = &tree;
    scope(move |s| {
        s.spawn(move |_| {
            drop(thread_tree);
        });
    })
    .unwrap();
    thread::sleep(Duration::from_millis(500));
    drop(tree);
}
