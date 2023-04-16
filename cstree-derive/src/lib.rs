use errors::ErrorContext;
use parsing::SyntaxKindEnum;
use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::{parse_macro_input, spanned::Spanned, DeriveInput};

mod errors;
mod parsing;
mod symbols;

use symbols::*;

#[proc_macro_derive(Language, attributes(language_name, static_text))]
pub fn language(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    expand_language(ast).unwrap_or_else(to_compile_errors).into()
}

fn expand_language(ast: DeriveInput) -> Result<TokenStream, Vec<syn::Error>> {
    let error_handler = ErrorContext::new();
    let Ok(syntax_kind_enum) = SyntaxKindEnum::parse_from_ast(&error_handler, &ast) else {
        return Err(error_handler.check().unwrap_err());
    };

    // Check that the `enum` is `#[repr(u32)]`
    match &syntax_kind_enum.repr {
        Some(repr) if repr == U32 => (),
        Some(_) | None => error_handler.error_at(
            syntax_kind_enum.source,
            "syntax kind definitions must be `#[repr(u32)]` to derive `Languge`",
        ),
    }

    error_handler.check()?;

    let vis = &syntax_kind_enum.vis;
    let language_name = &syntax_kind_enum.language_name;
    let language_type = quote! {
        #[automatically_derived]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #vis enum #language_name {}
    };

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
        impl ::cstree::Language for #language_name {
            type Kind = #name;

            fn kind_from_raw(raw: ::cstree::RawSyntaxKind) -> Self::Kind {
                assert!(raw.0 < #variant_count);
                // Safety: discriminant is valid by the assert above
                unsafe { ::std::mem::transmute::<u32, #name>(raw.0) }
            }

            fn kind_to_raw(kind: Self::Kind) -> ::cstree::RawSyntaxKind {
                ::cstree::RawSyntaxKind(kind as u32)
            }

            fn static_text(kind: Self::Kind) -> ::core::option::Option<&'static str> {
                match kind {
                    #( #static_texts )*
                }
            }
        }
    };

    let code = quote_spanned! {syntax_kind_enum.source.span()=>
        #language_type

        #trait_impl
    };
    Ok(code)
}

fn to_compile_errors(errors: Vec<syn::Error>) -> proc_macro2::TokenStream {
    let compile_errors = errors.iter().map(syn::Error::to_compile_error);
    quote!(#(#compile_errors)*)
}
