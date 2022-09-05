//! Bridge between `cstree`'s and `lasso`'s types and traits.

#![cfg(feature = "lasso_compat")]

mod token_interner;
#[doc(inline)]
pub use token_interner::*;

mod traits;
