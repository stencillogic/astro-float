//! Macros for multiple precision floating point numbers library `astro-float`.

mod util;

use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse::Parse, spanned::Spanned, BinOp, Error, Expr, ExprBinary, ExprCall, ExprGroup, ExprLit,
    ExprParen, ExprPath, ExprUnary, Lit, Token, UnOp,
};
use util::{check_arg_num, str_to_bigfloat_expr};

struct MacroInput {
    p: Expr,
    rm: Expr,
    cc: Expr,
    expr: Expr,
}

impl Parse for MacroInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let p = input.parse()?;
        input.parse::<Token![,]>()?;

        let rm = input.parse()?;
        input.parse::<Token![,]>()?;

        let cc = input.parse()?;
        input.parse::<Token![,]>()?;

        let expr = input.parse()?;

        Ok(MacroInput { p, rm, cc, expr })
    }
}

fn traverse_binary(expr: &ExprBinary) -> Result<TokenStream, Error> {
    let left_expr = traverse_expr(&expr.left)?;
    let right_expr = traverse_expr(&expr.right)?;
    match expr.op {
        BinOp::Add(_) => Ok(
            quote!(astro_float::BigFloat::add(&(#left_expr), &(#right_expr), __astro_float_0140685_default_p, __astro_float_0140685_default_rm)),
        ),
        BinOp::Sub(_) => Ok(
            quote!(astro_float::BigFloat::sub(&(#left_expr), &(#right_expr), __astro_float_0140685_default_p, __astro_float_0140685_default_rm)),
        ),
        BinOp::Mul(_) => Ok(
            quote!(astro_float::BigFloat::mul(&(#left_expr), &(#right_expr), __astro_float_0140685_default_p, __astro_float_0140685_default_rm)),
        ),
        BinOp::Div(_) => Ok(
            quote!(astro_float::BigFloat::div(&(#left_expr), &(#right_expr), __astro_float_0140685_default_p, __astro_float_0140685_default_rm)),
        ),
        BinOp::Rem(_) => Ok(quote!(astro_float::BigFloat::rem(&(#left_expr), &(#right_expr)))),
        _ => Err(Error::new(
            expr.span(),
            "unexpected binary operator. Only \"+\", \"-\", \"*\", \"/\", and \"%\" are allowed.",
        )),
    }
}

fn one_arg_fun(fun: TokenStream, expr: &ExprCall) -> Result<TokenStream, Error> {
    check_arg_num(1, expr)?;
    let arg = traverse_expr(&expr.args[0])?;
    Ok(quote!(#fun(&(#arg), __astro_float_0140685_default_p, __astro_float_0140685_default_rm)))
}

fn one_arg_fun_cc(fun: TokenStream, expr: &ExprCall) -> Result<TokenStream, Error> {
    check_arg_num(1, expr)?;
    let arg = traverse_expr(&expr.args[0])?;
    Ok(
        quote!(#fun(&(#arg), __astro_float_0140685_default_p, __astro_float_0140685_default_rm, __astro_float_0140685_default_cc)),
    )
}

fn two_arg_fun_cc(fun: TokenStream, expr: &ExprCall) -> Result<TokenStream, Error> {
    check_arg_num(2, expr)?;
    let arg1 = traverse_expr(&expr.args[0])?;
    let arg2 = traverse_expr(&expr.args[1])?;
    Ok(
        quote!(#fun(&(#arg1), &(#arg2), __astro_float_0140685_default_p, __astro_float_0140685_default_rm, __astro_float_0140685_default_cc)),
    )
}

fn traverse_call(expr: &ExprCall) -> Result<TokenStream, Error> {
    let errmes = "unexpected function name. Only \"recip\", \"sqrt\", \"cbrt\", \"ln\", \"log2\", \"log10\", \"log\", \"exp\", \"pow\", \"sin\", \"cos\", \"tan\", \"asin\", \"acos\", \"atan\", \"sinh\", \"cosh\", \"tanh\", \"asinh\", \"acosh\", \"atanh\" are allowed.";
    if let Expr::Path(fun) = expr.func.as_ref() {
        if let Some(fname) = fun.path.get_ident() {
            return match fname.to_string().as_str() {
                "recip" => one_arg_fun(quote!(astro_float::BigFloat::reciprocal), expr),
                "sqrt" => one_arg_fun(quote!(astro_float::BigFloat::sqrt), expr),
                "cbrt" => one_arg_fun(quote!(astro_float::BigFloat::cbrt), expr),
                "ln" => one_arg_fun_cc(quote!(astro_float::BigFloat::ln), expr),
                "log2" => one_arg_fun_cc(quote!(astro_float::BigFloat::log2), expr),
                "log10" => one_arg_fun_cc(quote!(astro_float::BigFloat::log10), expr),
                "log" => two_arg_fun_cc(quote!(astro_float::BigFloat::log), expr),
                "exp" => one_arg_fun_cc(quote!(astro_float::BigFloat::exp), expr),
                "pow" => two_arg_fun_cc(quote!(astro_float::BigFloat::pow), expr),
                "sin" => one_arg_fun_cc(quote!(astro_float::BigFloat::sin), expr),
                "cos" => one_arg_fun_cc(quote!(astro_float::BigFloat::cos), expr),
                "tan" => one_arg_fun_cc(quote!(astro_float::BigFloat::tan), expr),
                "asin" => one_arg_fun_cc(quote!(astro_float::BigFloat::asin), expr),
                "acos" => one_arg_fun_cc(quote!(astro_float::BigFloat::acos), expr),
                "atan" => one_arg_fun_cc(quote!(astro_float::BigFloat::atan), expr),
                "sinh" => one_arg_fun_cc(quote!(astro_float::BigFloat::sinh), expr),
                "cosh" => one_arg_fun_cc(quote!(astro_float::BigFloat::cosh), expr),
                "tanh" => one_arg_fun_cc(quote!(astro_float::BigFloat::tanh), expr),
                "asinh" => one_arg_fun_cc(quote!(astro_float::BigFloat::asinh), expr),
                "acosh" => one_arg_fun_cc(quote!(astro_float::BigFloat::acosh), expr),
                "atanh" => one_arg_fun_cc(quote!(astro_float::BigFloat::atanh), expr),
                _ => Err(Error::new(expr.span(), errmes)),
            };
        }
    }
    Err(Error::new(expr.span(), errmes))
}

fn traverse_group(expr: &ExprGroup) -> Result<TokenStream, Error> {
    traverse_expr(&expr.expr)
}

fn traverse_lit(expr: &ExprLit) -> Result<TokenStream, Error> {
    let span = expr.span();
    match &expr.lit {
        Lit::Str(v) => str_to_bigfloat_expr(&v.value(), span),
        Lit::Int(v) => str_to_bigfloat_expr(v.base10_digits(), span),
        Lit::Float(v) => str_to_bigfloat_expr(v.base10_digits(), span),
        _ => Err(Error::new(
            expr.span(),
            "unexpected literal. Only string, integer, or floating point literals are supported.",
        )),
    }
}

fn traverse_paren(expr: &ExprParen) -> Result<TokenStream, Error> {
    traverse_expr(&expr.expr)
}

fn traverse_path(expr: &ExprPath) -> Result<TokenStream, Error> {
    Ok(quote!(astro_float::BigFloat::from(#expr)))
}

fn traverse_unary(expr: &ExprUnary) -> Result<TokenStream, Error> {
    let op_expr = traverse_expr(&expr.expr)?;
    match expr.op {
        UnOp::Neg(_) => Ok(quote!(astro_float::BigFloat::neg(&(#op_expr)))),
        _ => Err(Error::new(
            expr.span(),
            "unexpected unary operator. Only \"-\" is allowed.",
        )),
    }
}

fn traverse_expr(expr: &Expr) -> Result<TokenStream, Error> {
    match expr {
        Expr::Binary(e) => traverse_binary(e),
        Expr::Call(e) => traverse_call(e),
        Expr::Group(e) => traverse_group(e),
        Expr::Lit(e) => traverse_lit(e),
        Expr::Paren(e) => traverse_paren(e),
        Expr::Path(e) => traverse_path(e),
        Expr::Unary(e) => traverse_unary(e),
        _ => Err(Error::new(expr.span(), "unexpected expression. Only operators \"+\", \"-\", \"*\", \"/\", \"%\", functions \"recip\", \"sqrt\", \"cbrt\", \"ln\", \"log2\", \"log10\", \"log\", \"exp\", \"pow\", \"sin\", \"cos\", \"tan\", \"asin\", \"acos\", \"atan\", \"sinh\", \"cosh\", \"tanh\", \"asinh\", \"acosh\", \"atanh\", literals and variables, and grouping with parentheses are supported.")),
    }
}

/// Compute an expression with given precision and rounding mode.
#[proc_macro]
pub fn expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let pmi = syn::parse_macro_input!(input as MacroInput);

    let MacroInput { p, rm, cc, expr } = pmi;

    let expr = traverse_expr(&expr).unwrap_or_else(|e| e.to_compile_error());

    let ret = quote!({
        let __astro_float_0140685_default_p: usize = #p;
        let __astro_float_0140685_default_rm: RoundingMode = #rm;
        let __astro_float_0140685_default_cc = &mut #cc;

        let __astro_float_0140685_ret: astro_float::BigFloat = (#expr).into();

        __astro_float_0140685_ret
    });

    ret.into()
}
