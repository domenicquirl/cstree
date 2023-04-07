#![cfg(feature = "salsa_2022_compat")]

use cstree::{build::GreenNodeBuilder, impl_cstree_interning_for_salsa};

#[salsa::jar(db = Db)]
pub struct Jar(crate::SourceId);

pub trait Db: salsa::DbWithJar<Jar> {}
impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}

#[salsa::interned]
pub struct SourceId {
    #[return_ref]
    pub text: String,
}

#[derive(Default)]
#[salsa::db(crate::Jar)]
struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}

impl_cstree_interning_for_salsa!(impl Interning for Database => text as SourceId);

use cstree::{syntax::SyntaxNode, testing::*};

fn main() {
    let db = Database::default();
    let interned = SourceId::new(&db, "foo".to_string());
    let original = interned.text(&db);
    assert_eq!(original, "foo");

    let interner = db.as_interner();
    let mut shared_interner = &interner;
    let mut builder: GreenNodeBuilder<TestLang, _> = GreenNodeBuilder::with_interner(&mut shared_interner);
    let (tree, _no_interner_because_it_was_borrowed) = {
        builder.start_node(TestSyntaxKind::Plus);
        builder.token(TestSyntaxKind::Float, "2.05");
        builder.token(TestSyntaxKind::Whitespace, " ");
        builder.token(TestSyntaxKind::Plus, "+");
        builder.token(TestSyntaxKind::Whitespace, " ");
        builder.token(TestSyntaxKind::Float, "7.32");
        builder.finish_node();
        builder.finish()
    };
    let tree: SyntaxNode<TestLang> = SyntaxNode::new_root(tree);
    assert_eq!(tree.resolve_text(shared_interner), "2.05 + 7.32");
}
