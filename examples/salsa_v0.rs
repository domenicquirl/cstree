#![cfg(feature = "salsa_v0_compat")]

use cstree::interning::TokenKey;

use salsa_v0 as salsa;

#[salsa::query_group(InternDatabaseStorage)]
trait InternDatabase {
    #[salsa::interned]
    fn intern_ident(&self, ident: String) -> TokenKey;
}

#[salsa::database(InternDatabaseStorage)]
#[derive(Default)]
struct Db {
    storage: salsa::Storage<Db>,
}

impl salsa::Database for Db {}

fn main() {
    let db = Db::default();
    let foo = db.intern_ident("foo".to_string());
    let foo = db.lookup_intern_ident(foo);
    assert_eq!(foo, "foo");
}
