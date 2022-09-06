#![cfg(feature = "salsa_2022_compat")]

use cstree::{interning::InternWithDb, GreenNodeBuilder};

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

trait AsInterner {
    fn as_interner(&self) -> InternWithDb<'_, Database, SourceId>;
}

impl AsInterner for Database {
    fn as_interner(&self) -> InternWithDb<'_, Database, SourceId> {
        InternWithDb::new(self, |db, text| SourceId::new(db, text), |db, id| id.text(db))
    }
}

use cstree::testing::*;

fn main() {
    let db = Database::default();
    let foo = SourceId::new(&db, "foo".to_string());
    let foo = foo.text(&db);
    assert_eq!(foo, "foo");

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
    assert_eq!(tree.resolve_text(&interner), "2.05 + 7.32");
}
