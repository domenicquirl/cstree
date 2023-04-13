#![allow(unused)]

use super::*;
use proc_macro2::TokenStream;
use quote::ToTokens;

#[derive(Debug)]
pub(crate) struct Attr<'i, T> {
    error_handler: &'i ErrorContext,
    name: Symbol,
    tokens: TokenStream,
    value: Option<T>,
}

impl<'i, T> Attr<'i, T> {
    pub(super) fn none(error_handler: &'i ErrorContext, name: Symbol) -> Self {
        Attr {
            error_handler,
            name,
            tokens: TokenStream::new(),
            value: None,
        }
    }

    pub(super) fn set<S: ToTokens>(&mut self, source: S, value: T) {
        let tokens = source.into_token_stream();

        if self.value.is_some() {
            self.error_handler
                .error_at(tokens, format!("duplicate attribute: `{}`", self.name));
        } else {
            self.tokens = tokens;
            self.value = Some(value);
        }
    }

    pub(super) fn set_opt<S: ToTokens>(&mut self, source: S, value: Option<T>) {
        if let Some(value) = value {
            self.set(source, value);
        }
    }

    pub(super) fn set_if_none(&mut self, value: T) {
        if self.value.is_none() {
            self.value = Some(value);
        }
    }

    pub(super) fn get(self) -> Option<T> {
        self.value
    }

    pub(super) fn get_with_tokens(self) -> Option<(TokenStream, T)> {
        match self.value {
            Some(v) => Some((self.tokens, v)),
            None => None,
        }
    }
}
