//! Utility functions.

use astro_float_num::BigFloat;
use core::str::FromStr;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;
use syn::Error;
use syn::ExprCall;

pub fn str_to_bigfloat_expr(s: &str, span: Span) -> Result<TokenStream, Error> {
    let f = BigFloat::from_str(s)
        .map_err(|_| Error::new(span, format!("failed to parse BigFloat from {}", s)))?;

    let q = if f.inexact() {
        quote!(astro_float::BigFloat::parse(#s, astro_float::Radix::Dec, p_wrk, astro_float::RoundingMode::None))
    } else if let Some((m, n, s, e, inexact)) = f.as_raw_parts() {
        let stoken = if s.is_positive() {
            quote!(astro_float::Sign::Pos)
        } else {
            quote!(astro_float::Sign::Neg)
        };
        quote!(astro_float::BigFloat::from_raw_parts(&[#(#m),*], #n, #stoken, #e, #inexact))
    } else {
        quote!(astro_float::BigFloat::nan())
    };

    Ok(q)
}

pub fn check_arg_num(narg: usize, expr: &ExprCall) -> Result<(), Error> {
    if expr.args.len() != narg {
        return Err(Error::new(
            expr.func.span(),
            if narg == 1 { "expected 1 argument." } else { "expected 2 arguments." },
        ));
    }
    Ok(())
}
