use std::{cell::RefCell, fmt, thread};

use quote::ToTokens;

/// Context to collect multiple errors and output them all after parsing in order to not abort
/// immediately on the first error.
///
/// Ensures that the errors are handled using [`check`](ErrorContext::check) by otherwise panicking
/// on `Drop`.
#[derive(Debug, Default)]
pub(crate) struct ErrorContext {
    errors: RefCell<Option<Vec<syn::Error>>>,
}

impl ErrorContext {
    /// Create a new context.
    ///
    /// This context contains no errors, but will still trigger a panic if it is not `check`ed.
    pub fn new() -> Self {
        ErrorContext {
            errors: RefCell::new(Some(Vec::new())),
        }
    }

    /// Add an error to the context that points to `source`.
    pub fn error_at<S: ToTokens, T: fmt::Display>(&self, source: S, msg: T) {
        self.errors
            .borrow_mut()
            .as_mut()
            .unwrap()
            // Transform `ToTokens` here so we don't monomorphize `new_spanned` so much.
            .push(syn::Error::new_spanned(source.into_token_stream(), msg));
    }

    /// Add a `syn` parse error directly.
    pub fn syn_error(&self, err: syn::Error) {
        self.errors.borrow_mut().as_mut().unwrap().push(err);
    }

    /// Consume the context, producing a formatted error string if there are errors.
    pub fn check(self) -> Result<(), Vec<syn::Error>> {
        let errors = self.errors.borrow_mut().take().unwrap();
        match errors.len() {
            0 => Ok(()),
            _ => Err(errors),
        }
    }
}

impl Drop for ErrorContext {
    fn drop(&mut self) {
        if !thread::panicking() && self.errors.borrow().is_some() {
            panic!("forgot to check for errors");
        }
    }
}
