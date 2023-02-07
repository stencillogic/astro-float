//! Macros for multiple precision floating point numbers library `astro-float`.

use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{Expr, Token, parse::Parse, ExprBinary, ExprCall, ExprCast, ExprUnary, ExprGroup, ExprIf, ExprLit, ExprParen, Error, spanned::Spanned};

struct MacroInput {
    p: Expr,
    rm: Expr,
    expr: Expr,
}

impl Parse for MacroInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let p = input.parse()?;
        input.parse::<Token![,]>()?;

        let rm = input.parse()?;
        input.parse::<Token![,]>()?;

        let expr = input.parse()?;
        
        Ok(MacroInput {
            p, 
            rm,
            expr
        })
    }
}

fn traverse_binary(mut expr: ExprBinary) -> Result<Expr, Error> {
    match expr.op {
        syn::BinOp::Add(_) => todo!(),
        syn::BinOp::Sub(_) => todo!(),
        syn::BinOp::Mul(_) => todo!(),
        syn::BinOp::Div(_) => todo!(),
        syn::BinOp::Rem(_) => todo!(),
        _ => Err(Error::new(expr.span(), "unexpected binary operator; only +, -, *, /, and % are allowed")),
    }
}

fn traverse_call(mut expr: ExprCall) -> Result<Expr, Error> {
    Ok(Expr::Call(expr))
}

fn traverse_cast(mut expr: ExprCast) -> Result<Expr, Error> {
    Ok(Expr::Cast(expr))
}

fn traverse_group(mut expr: ExprGroup) -> Result<Expr, Error> {
    Ok(Expr::Group(expr))
}

fn traverse_if(mut expr: ExprIf) -> Result<Expr, Error> {
    Ok(Expr::If(expr))
}

fn traverse_lit(mut expr: ExprLit) -> Result<Expr, Error> {
    Ok(Expr::Lit(expr))
}

fn traverse_paren(mut expr: ExprParen) -> Result<Expr, Error> {
    Ok(Expr::Paren(expr))
}

fn traverse_unary(mut expr: ExprUnary) -> Result<Expr, Error> {
    Ok(Expr::Unary(expr))
}

fn traverse_expr(mut expr: Expr) -> Result<Expr, Error> {
    match expr {
        Expr::Binary(e) => traverse_binary(e),
        Expr::Call(e) => traverse_call(e),
        Expr::Cast(e) => traverse_cast(e),
        Expr::Group(e) => traverse_group(e),
        Expr::If(e) => traverse_if(e),
        Expr::Lit(e) => traverse_lit(e),
        Expr::Paren(e) => traverse_paren(e),
        Expr::Unary(e) => traverse_unary(e),
        _ => Err(Error::new(expr.span(), "unexpected expression type")),
    }
}

/// Compute an expression with given precision and rounding mode.
#[proc_macro]
pub fn expr(input: TokenStream) -> TokenStream {
    let pmi = syn::parse_macro_input!(input as MacroInput);

    let MacroInput { p, rm, expr } = pmi;

    let expr = traverse_expr(expr)
                                .map(|x| x.to_token_stream())
                                .unwrap_or_else(|e| e.to_compile_error());

    let ret = quote!({
        let __astro_float_0140685_default_p: usize = #p;
        let __astro_float_0140685_default_rm: RoundingMode = #rm;

        let __astro_float_0140685_ret: astro_float::BigFloat = (#expr).into();

        __astro_float_0140685_ret
    });

    ret.into()
}
