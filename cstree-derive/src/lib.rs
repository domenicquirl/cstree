//! This crate provides `cstree`'s derive macro for `Syntax`.
//!
//! ```
//! # use cstree_derive::Syntax;
//! #
//! # #[derive(Debug, Copy, Clone, PartialEq, Eq)]
//! #[derive(Syntax)]
//! # #[repr(u32)]
//! # enum SyntaxKind { Root }
//! ```
//!
//! Please refer to [the `cstree` main crate] for how to set this up.
//!
//! [the `cstree` main crate]: https://docs.rs/cstree/

use errors::ErrorContext;
use parsing::SyntaxKindEnum;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::{parse_macro_input, spanned::Spanned, DeriveInput};

mod errors;
mod parsing;
mod symbols;

use symbols::*;

#[proc_macro_derive(Syntax, attributes(static_text))]
pub fn language(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    expand_syntax(ast).unwrap_or_else(to_compile_errors).into()
}

fn expand_syntax(ast: DeriveInput) -> Result<TokenStream, Vec<syn::Error>> {
    let error_handler = ErrorContext::new();
    let Ok(syntax_kind_enum) = SyntaxKindEnum::parse_from_ast(&error_handler, &ast) else {
        return Err(error_handler.check().unwrap_err());
    };

    // Check that the `enum` is `#[repr(u32)]`
    match &syntax_kind_enum.repr {
        Some(repr) if repr == U32 => (),
        Some(_) | None => error_handler.error_at(
            syntax_kind_enum.source,
            "syntax kind definitions must be `#[repr(u32)]` to derive `Syntax`",
        ),
    }

    error_handler.check()?;

    let name = &syntax_kind_enum.name;
    let variant_count = syntax_kind_enum.variants.len() as u32;
    let static_texts = syntax_kind_enum.variants.iter().map(|variant| {
        let variant_name = &variant.name;
        let static_text = match variant.static_text.as_deref() {
            Some(text) => quote!(::core::option::Option::Some(#text)),
            None => quote!(::core::option::Option::None),
        };
        quote_spanned!(variant.source.span()=>
            #name :: #variant_name => #static_text,
        )
    });
    let trait_impl = quote_spanned! { syntax_kind_enum.source.span()=>
        #[automatically_derived]
        impl ::cstree::Syntax for #name {
            fn from_raw(raw: ::cstree::RawSyntaxKind) -> Self {
                assert!(raw.0 < #variant_count, "Invalid raw syntax kind: {}", raw.0);
                // Safety: discriminant is valid by the assert above
                unsafe { ::std::mem::transmute::<u32, #name>(raw.0) }
            }

            fn into_raw(self) -> ::cstree::RawSyntaxKind {
                ::cstree::RawSyntaxKind(self as u32)
            }

            fn static_text(self) -> ::core::option::Option<&'static str> {
                match self {
                    #( #static_texts )*
                }
            }
        }
    };
    Ok(trait_impl)
}

fn to_compile_errors(errors: Vec<syn::Error>) -> proc_macro2::TokenStream {
    let compile_errors = errors.iter().map(syn::Error::to_compile_error);
    quote!(#(#compile_errors)*)
}
