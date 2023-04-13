mod attributes;

use proc_macro2::Span;
use syn::{punctuated::Punctuated, Token};

use crate::{errors::ErrorContext, symbols::*};

use self::attributes::Attr;

/// Convenience for recording errors inside `ErrorContext` instead of the `Err` variant of the `Result`.
pub(crate) type Result<T, E = ()> = std::result::Result<T, E>;

pub(crate) struct SyntaxKindEnum<'i> {
    pub(crate) vis: syn::Visibility,
    pub(crate) name: syn::Ident,
    pub(crate) repr: Option<syn::Ident>,
    pub(crate) language_name: syn::Ident,
    pub(crate) variants: Vec<SyntaxKindVariant<'i>>,
    pub(crate) source: &'i syn::DeriveInput,
}

impl<'i> SyntaxKindEnum<'i> {
    pub(crate) fn parse_from_ast(error_handler: &ErrorContext, item: &'i syn::DeriveInput) -> Result<Self> {
        let vis = item.vis.clone();
        let syn::Data::Enum(data) = &item.data else {
            error_handler.error_at(item, "`Language` can only be derived on enums");
            return Err(());
        };

        let name = item.ident.clone();

        let mut repr = Attr::none(error_handler, REPR);
        for repr_attr in item.attrs.iter().filter(|&attr| attr.path().is_ident(&REPR)) {
            if let syn::Meta::List(nested) = &repr_attr.meta {
                if let Ok(nested) = nested.parse_args_with(Punctuated::<syn::Meta, Token![,]>::parse_terminated) {
                    for meta in nested {
                        if let syn::Meta::Path(path) = meta {
                            if let Some(ident) = path.get_ident() {
                                repr.set(repr_attr, ident.clone());
                            }
                        }
                    }
                }
            }
        }

        let mut language_name = Attr::none(error_handler, LANGUAGE_NAME);
        for name in item
            .attrs
            .iter()
            .flat_map(|attr| get_name_value(error_handler, attr, LANGUAGE_NAME))
        {
            language_name.set(name, name.value());
        }
        let Some(language_name) = language_name.get() else {
            error_handler.error_at(item, "missing language name: maybe you forgot to add a `#[language_name = \"...\"]` attribute?");
            return Err(());
        };
        let language_name = syn::Ident::new(&language_name, Span::call_site());

        let variants = data
            .variants
            .iter()
            .map(|variant| SyntaxKindVariant::parse_from_ast(error_handler, variant))
            .collect();

        Ok(Self {
            vis,
            name,
            repr: repr.get(),
            language_name,
            variants,
            source: item,
        })
    }
}

pub(crate) struct SyntaxKindVariant<'i> {
    pub(crate) name:        syn::Ident,
    pub(crate) static_text: Option<String>,
    pub(crate) source:      &'i syn::Variant,
}

impl<'i> SyntaxKindVariant<'i> {
    pub(crate) fn parse_from_ast(error_handler: &ErrorContext, variant: &'i syn::Variant) -> Self {
        let name = variant.ident.clone();

        // Check that `variant` is a unit variant
        match &variant.fields {
            syn::Fields::Unit => (),
            syn::Fields::Named(_) | syn::Fields::Unnamed(_) => {
                error_handler.error_at(variant, "syntax kinds with fields are not supported");
            }
        }

        // Check that discriminants are unaltered
        if variant.discriminant.is_some() {
            error_handler.error_at(
                variant,
                "syntax kinds are not allowed to have custom discriminant values",
            );
        }

        let mut static_text = Attr::none(error_handler, STATIC_TEXT);
        for text in variant
            .attrs
            .iter()
            .flat_map(|attr| get_name_value(error_handler, attr, STATIC_TEXT))
        {
            static_text.set(text, text.value());
        }
        Self {
            name,
            static_text: static_text.get(),
            source: variant,
        }
    }
}

fn get_name_value<'i>(error_handler: &ErrorContext, attr: &'i syn::Attribute, path: Symbol) -> Option<&'i syn::LitStr> {
    use syn::Meta::*;

    if attr.path() != path {
        return None;
    }

    match &attr.meta {
        NameValue(attr) if attr.path == path => get_literal_str(error_handler, path, &attr.value).ok(),
        List(_) | Path(_) | NameValue(_) => {
            error_handler.error_at(attr, format!("Expected `#[{path} = \"...\"]`"));
            None
        }
    }
}

fn get_literal_str<'i>(
    error_handler: &ErrorContext,
    attr_name: Symbol,
    expr: &'i syn::Expr,
) -> Result<&'i syn::LitStr> {
    let syn::Expr::Lit(lit) = expr else {
        error_handler.error_at(expr, format!("expected `{attr_name}` to be a string literal: `{attr_name} = \"...\"`"));
        return Err(());
    };
    let syn::Lit::Str(s) = &lit.lit else {
        error_handler.error_at(lit, format!("expected `{attr_name}` to be a string: `{attr_name} = \"...\"`"));
        return Err(());
    };
    Ok(s)
}
