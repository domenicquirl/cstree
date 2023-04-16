mod attributes;

use syn::{punctuated::Punctuated, Token};

use crate::{errors::ErrorContext, symbols::*};

use self::attributes::Attr;

/// Convenience for recording errors inside `ErrorContext` instead of the `Err` variant of the `Result`.
pub(crate) type Result<T, E = ()> = std::result::Result<T, E>;

pub(crate) struct SyntaxKindEnum<'i> {
    pub(crate) name:     syn::Ident,
    pub(crate) repr:     Option<syn::Ident>,
    pub(crate) variants: Vec<SyntaxKindVariant<'i>>,
    pub(crate) source:   &'i syn::DeriveInput,
}

impl<'i> SyntaxKindEnum<'i> {
    pub(crate) fn parse_from_ast(error_handler: &ErrorContext, item: &'i syn::DeriveInput) -> Result<Self> {
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

        let variants = data
            .variants
            .iter()
            .map(|variant| SyntaxKindVariant::parse_from_ast(error_handler, variant))
            .collect();

        Ok(Self {
            name,
            repr: repr.get(),
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
            .flat_map(|attr| get_static_text(error_handler, attr))
        {
            static_text.set(&text, text.value());
        }
        Self {
            name,
            static_text: static_text.get(),
            source: variant,
        }
    }
}

fn get_static_text(error_handler: &ErrorContext, attr: &syn::Attribute) -> Option<syn::LitStr> {
    use syn::Meta::*;

    if attr.path() != STATIC_TEXT {
        return None;
    }

    match &attr.meta {
        List(list) => match list.parse_args() {
            Ok(lit) => Some(lit),
            Err(e) => {
                error_handler.error_at(
                    list,
                    "argument to `static_text` must be a string literal: `#[static_text(\"...\")]`",
                );
                error_handler.syn_error(e);
                None
            }
        },
        Path(_) => {
            error_handler.error_at(attr, "missing text for `static_text`: try `#[static_text(\"...\")]`");
            None
        }
        NameValue(_) => {
            error_handler.error_at(
                attr,
                "`static_text` takes the text as a function argument: `#[static_text(\"...\")]`",
            );
            None
        }
    }
}
