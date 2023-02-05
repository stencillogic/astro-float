//! Macros for multiple precision floating point numbers library `astro-float`.

use proc_macro::TokenStream;

/// Compute an expression with given precision and rounding mode.
#[proc_macro]
pub fn expr(input: TokenStream) -> TokenStream {
    input
}
