//! Utility functions.

use astro_float_num::BigFloat;
use astro_float_num::Consts;
use astro_float_num::Radix;
use astro_float_num::RoundingMode;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use quote::quote;
use syn::spanned::Spanned;
use syn::Error;
use syn::ExprCall;

pub fn str_to_bigfloat_expr(s: &str, span: Span, cc: &mut Consts) -> Result<TokenStream, Error> {
    let f = BigFloat::parse(s, Radix::Dec, usize::MAX, RoundingMode::ToEven, cc);
    if f.is_nan() {
        if let Some(err) = f.err() {
            return Err(Error::new(
                span,
                format!("failed to parse BigFloat from {}: {}", s, err),
            ));
        }
    }

    let q = if f.inexact() {
        quote!(astro_float::BigFloat::parse(#s, astro_float::Radix::Dec, p_wrk, astro_float::RoundingMode::ToEven, cc))
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
