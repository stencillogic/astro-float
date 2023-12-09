//! Macros for multiple precision floating point numbers library `astro-float`.
//!
//! See main crate [docs](https://docs.rs/astro-float/latest/astro_float/).

#![deny(missing_docs)]
#![deny(clippy::suspicious)]

mod util;

use astro_float_num::{Consts, EXPONENT_BIT_SIZE};
use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse::Parse, spanned::Spanned, BinOp, Error, Expr, ExprBinary, ExprCall, ExprGroup, ExprLit,
    ExprParen, ExprPath, ExprUnary, Lit, Token, UnOp,
};
use util::{check_arg_num, str_to_bigfloat_expr};

// Speculative error estimation.
// This error is added upfront, before actual error is known.
// It helps to avoid additional recalculations due to changing error estimation.
const SPEC_ADD_ERR: usize = 32;

struct MacroInput {
    expr: Expr,
    ctx: Expr,
}

impl Parse for MacroInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let expr = input.parse()?;
        input.parse::<Token![,]>()?;

        let ctx = input.parse()?;

        Ok(MacroInput { expr, ctx })
    }
}

fn traverse_binary(
    expr: &ExprBinary,
    err: &mut Vec<usize>,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    let left_expr = traverse_expr(&expr.left, err, cc)?;
    let right_expr = traverse_expr(&expr.right, err, cc)?;

    let errs_id = err.len();

    let ts = match expr.op {
        BinOp::Add(_) => {
            err.push(2);
            quote!({
                let arg1 = #left_expr;
                let arg2 = #right_expr;
                let ret = astro_float::BigFloat::add(&arg1, &arg2, p_wrk, astro_float::RoundingMode::None);
                if arg1.inexact() || arg2.inexact() {
                    if let (Some(e1), Some(e2), Some(e3)) = (arg1.exponent(), arg2.exponent(), ret.exponent()) {
                        if (e1 as isize - e2 as isize).abs() <= 1 && arg1.sign() != arg2.sign() {
                            let newerr = (e1.max(e2) as isize - e3 as isize).unsigned_abs() + 1;
                            if errs[#errs_id] < newerr {
                                errs[#errs_id] = newerr;
                                continue;
                            }
                        }
                    }
                }
                ret
            })
        }
        BinOp::Sub(_) => {
            err.push(2);
            quote!({
                let arg1 = #left_expr;
                let arg2 = #right_expr;
                let ret = astro_float::BigFloat::sub(&arg1, &arg2, p_wrk, astro_float::RoundingMode::None);
                if arg1.inexact() || arg2.inexact() {
                    if let (Some(e1), Some(e2), Some(e3)) = (arg1.exponent(), arg2.exponent(), ret.exponent()) {
                        if (e1 as isize - e2 as isize).abs() <= 1 && arg1.sign() == arg2.sign() {
                            let newerr = (e1.max(e2) as isize - e3 as isize).unsigned_abs() + 1;
                            if errs[#errs_id] < newerr {
                                errs[#errs_id] = newerr;
                                continue;
                            }
                        }
                    }
                }
                ret
            })
        }
        BinOp::Mul(_) => {
            err.push(3);
            quote!(
                astro_float::BigFloat::mul(&(#left_expr), &(#right_expr), p_wrk, astro_float::RoundingMode::None))
        }
        BinOp::Div(_) => {
            err.push(3);
            quote!(astro_float::BigFloat::div(&(#left_expr), &(#right_expr), p_wrk, astro_float::RoundingMode::None))
        }
        BinOp::Rem(_) => {
            quote!(astro_float::BigFloat::rem(&(#left_expr), &(#right_expr)))
        }
        _ => return Err(Error::new(
            expr.span(),
            "unexpected binary operator. Only \"+\", \"-\", \"*\", \"/\", and \"%\" are allowed.",
        )),
    };

    Ok(ts)
}

fn one_arg_fun(
    fun: TokenStream,
    expr: &ExprCall,
    initial_err: usize,
    err: &mut Vec<usize>,
    cc: &mut Consts,
    use_cc: bool,
) -> Result<TokenStream, Error> {
    check_arg_num(1, expr)?;

    let arg = traverse_expr(&expr.args[0], err, cc)?;
    err.push(initial_err);

    let ret = if use_cc {
        quote!(#fun(&(#arg), p_wrk, astro_float::RoundingMode::None, cc))
    } else {
        quote!(#fun(&(#arg), p_wrk, astro_float::RoundingMode::None))
    };

    Ok(ret)
}

fn one_arg_fun_errcheck(
    fun: TokenStream,
    expr: &ExprCall,
    initial_err: usize,
    err: &mut Vec<usize>,
    errcheck: TokenStream,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    check_arg_num(1, expr)?;

    let arg = traverse_expr(&expr.args[0], err, cc)?;
    let errs_id = err.len();
    err.push(initial_err);

    Ok(quote!({
        let arg = #arg;

        let newerr = astro_float::macro_util::compute_added_err(#errcheck);
        if errs[#errs_id] < newerr {
            errs[#errs_id] = newerr;
            continue;
        }

        #fun(&arg, p_wrk, astro_float::RoundingMode::None, cc)
    }))
}

fn trig_fun(
    fun: TokenStream,
    expr: &ExprCall,
    initial_err: usize,
    err: &mut Vec<usize>,
    errfun: TokenStream,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    check_arg_num(1, expr)?;

    let arg = traverse_expr(&expr.args[0], err, cc)?;
    let errs_id = err.len();
    err.push(initial_err);

    Ok(quote!({
        let arg = astro_float::macro_util::check_exponent_range(#arg, emin, emax);

        let newerr = astro_float::macro_util::compute_added_err(astro_float::macro_util::ErrAlgo::Trig(&arg, p_wrk, #errfun, cc, emin));
        if errs[#errs_id] < newerr {
            errs[#errs_id] = newerr;
            continue;
        }

        #fun(&arg, p_wrk, astro_float::RoundingMode::None, cc)
    }))
}

fn two_arg_fun_errcheck(
    fun: TokenStream,
    expr: &ExprCall,
    initial_err: usize,
    err: &mut Vec<usize>,
    errcheck: TokenStream,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    check_arg_num(2, expr)?;

    let arg1 = traverse_expr(&expr.args[0], err, cc)?;
    let arg2 = traverse_expr(&expr.args[1], err, cc)?;

    let errs_id = err.len();

    err.push(initial_err);

    Ok(quote!({
        let arg1 = #arg1;
        let arg2 = #arg2;

        let newerr = astro_float::macro_util::compute_added_err(#errcheck);
        if errs[#errs_id] < newerr {
            errs[#errs_id] = newerr;
            continue;
        }

        #fun(&arg1, &arg2, p_wrk, astro_float::RoundingMode::None, cc)
    }))
}

fn traverse_call(
    expr: &ExprCall,
    err: &mut Vec<usize>,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    let errmes = "unexpected function name. Only \"recip\", \"sqrt\", \"cbrt\", \"ln\", \"log2\", \"log10\", \"log\", \"exp\", \"pow\", \"sin\", \"cos\", \"tan\", \"asin\", \"acos\", \"atan\", \"sinh\", \"cosh\", \"tanh\", \"asinh\", \"acosh\", \"atanh\" are allowed.";

    if let Expr::Path(fun) = expr.func.as_ref() {
        if let Some(fname) = fun.path.get_ident() {
            let ts = match fname.to_string().as_str() {
                "recip" => one_arg_fun(
                    quote!(astro_float::BigFloat::reciprocal),
                    expr,
                    2,
                    err,
                    cc,
                    false,
                ),
                "sqrt" => one_arg_fun(quote!(astro_float::BigFloat::sqrt), expr, 1, err, cc, false),
                "cbrt" => one_arg_fun(quote!(astro_float::BigFloat::cbrt), expr, 1, err, cc, false),
                "ln" => one_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::ln),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Log(&arg, 2, emin)),
                    cc,
                ),
                "log2" => one_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::log2),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Log(&arg, 3, emin)),
                    cc,
                ),
                "log10" => one_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::log10),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Log(&arg, 6, emin)),
                    cc,
                ),
                "log" => two_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::log),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Log2(&arg2, &arg1, emin)),
                    cc,
                ),
                "exp" => one_arg_fun(
                    quote!(astro_float::BigFloat::exp),
                    expr,
                    EXPONENT_BIT_SIZE + 1,
                    err,
                    cc,
                    true,
                ),
                "pow" => two_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::pow),
                    expr,
                    EXPONENT_BIT_SIZE + SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Pow(&arg1, &arg2, emin)),
                    cc,
                ),
                "sin" => trig_fun(
                    quote!(astro_float::BigFloat::sin),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::TrigFun::Sin),
                    cc,
                ),
                "cos" => trig_fun(
                    quote!(astro_float::BigFloat::cos),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::TrigFun::Cos),
                    cc,
                ),
                "tan" => trig_fun(
                    quote!(astro_float::BigFloat::tan),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::TrigFun::Tan),
                    cc,
                ),
                "asin" => one_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::asin),
                    expr,
                    SPEC_ADD_ERR / 2,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Asin(&arg, emin)),
                    cc,
                ),
                "acos" => one_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::acos),
                    expr,
                    SPEC_ADD_ERR / 2,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Acos(&arg, emin)),
                    cc,
                ),
                "atan" => one_arg_fun(quote!(astro_float::BigFloat::atan), expr, 2, err, cc, true),
                "sinh" => one_arg_fun(
                    quote!(astro_float::BigFloat::sinh),
                    expr,
                    EXPONENT_BIT_SIZE + 1,
                    err,
                    cc,
                    true,
                ),
                "cosh" => one_arg_fun(
                    quote!(astro_float::BigFloat::cosh),
                    expr,
                    EXPONENT_BIT_SIZE + 1,
                    err,
                    cc,
                    true,
                ),
                "tanh" => one_arg_fun(quote!(astro_float::BigFloat::tanh), expr, 2, err, cc, true),
                "asinh" => {
                    one_arg_fun(quote!(astro_float::BigFloat::asinh), expr, 2, err, cc, true)
                }
                "acosh" => one_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::acosh),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Acosh(&arg, emin)),
                    cc,
                ),
                "atanh" => one_arg_fun_errcheck(
                    quote!(astro_float::BigFloat::atanh),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    quote!(astro_float::macro_util::ErrAlgo::Atanh(&arg, emin)),
                    cc,
                ),
                _ => return Err(Error::new(expr.span(), errmes)),
            }?;

            return Ok(ts);
        }
    }
    Err(Error::new(expr.span(), errmes))
}

fn traverse_group(
    expr: &ExprGroup,
    err: &mut Vec<usize>,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    traverse_expr(&expr.expr, err, cc)
}

fn traverse_lit(expr: &ExprLit, cc: &mut Consts) -> Result<TokenStream, Error> {
    let span = expr.span();

    match &expr.lit {
        Lit::Str(v) => str_to_bigfloat_expr(&v.value(), span, cc),
        Lit::Int(v) => str_to_bigfloat_expr(v.base10_digits(), span, cc),
        Lit::Float(v) => str_to_bigfloat_expr(v.base10_digits(), span, cc),
        _ => Err(Error::new(
            expr.span(),
            "unexpected literal. Only string, integer, or floating point literals are supported.",
        )),
    }
}

fn traverse_paren(
    expr: &ExprParen,
    err: &mut Vec<usize>,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    traverse_expr(&expr.expr, err, cc)
}

fn traverse_path(expr: &ExprPath) -> Result<TokenStream, Error> {
    Ok(if expr.path.is_ident("pi") {
        quote!({ cc.pi(p_wrk, astro_float::RoundingMode::None) })
    } else if expr.path.is_ident("e") {
        quote!({ cc.e(p_wrk, astro_float::RoundingMode::None) })
    } else if expr.path.is_ident("ln_2") {
        quote!({ cc.ln_2(p_wrk, astro_float::RoundingMode::None) })
    } else if expr.path.is_ident("ln_10") {
        quote!({ cc.ln_10(p_wrk, astro_float::RoundingMode::None) })
    } else {
        quote!({
            let mut arg = astro_float::BigFloat::from_ext((#expr).clone(), p_wrk, astro_float::RoundingMode::ToEven, cc);
            arg.set_inexact(false);
            arg = astro_float::macro_util::check_exponent_range(arg, emin, emax);
            arg
        })
    })
}

fn traverse_unary(
    expr: &ExprUnary,
    err: &mut Vec<usize>,
    cc: &mut Consts,
) -> Result<TokenStream, Error> {
    let op_expr = traverse_expr(&expr.expr, err, cc)?;

    match expr.op {
        UnOp::Neg(_) => Ok(quote!(astro_float::BigFloat::neg(&(#op_expr)))),
        _ => Err(Error::new(
            expr.span(),
            "unexpected unary operator. Only \"-\" is allowed.",
        )),
    }
}

fn traverse_expr(expr: &Expr, err: &mut Vec<usize>, cc: &mut Consts) -> Result<TokenStream, Error> {
    match expr {
        Expr::Binary(e) => traverse_binary(e, err,cc),
        Expr::Call(e) => traverse_call(e, err,cc),
        Expr::Group(e) => traverse_group(e, err,cc),
        Expr::Lit(e) => traverse_lit(e, cc),
        Expr::Paren(e) => traverse_paren(e, err, cc),
        Expr::Path(e) => traverse_path(e),
        Expr::Unary(e) => traverse_unary(e, err, cc),
        _ => Err(Error::new(expr.span(), "unexpected expression. Only operators \"+\", \"-\", \"*\", \"/\", \"%\", functions \"recip\", \"sqrt\", \"cbrt\", \"ln\", \"log2\", \"log10\", \"log\", \"exp\", \"pow\", \"sin\", \"cos\", \"tan\", \"asin\", \"acos\", \"atan\", \"sinh\", \"cosh\", \"tanh\", \"asinh\", \"acosh\", \"atanh\", literals and variables, and grouping with parentheses are supported.")),
    }
}

// Docs for the macro are in the astro-float crate.

///
#[proc_macro]
pub fn expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let pmi = syn::parse_macro_input!(input as MacroInput);

    let MacroInput { expr, ctx } = pmi;

    let mut err = Vec::new();

    let mut cc = Consts::new().expect("Failed to initialize constant cache.");

    let expr = traverse_expr(&expr, &mut err, &mut cc).unwrap_or_else(|e| e.to_compile_error());

    let err_sz = err.len();

    let ret = quote!({
        use astro_float::FromExt;
        use astro_float::ctx::Contextable;

        let mut ctx = &mut (#ctx);
        let p: usize = ctx.precision();
        let rm = ctx.rounding_mode();
        let emin = ctx.emin();
        let emax = ctx.emax();
        let cc = ctx.consts();

        let mut p_rnd = p + astro_float::WORD_BIT_SIZE;
        let mut errs: [usize; #err_sz] = [#(#err, )*];

        loop {
            let p_wrk = p_rnd.saturating_add(errs.iter().sum());

            let mut ret: astro_float::BigFloat = (#expr).into();

            if let Err(err) = ret.set_precision(p, rm) {
                ret = astro_float::BigFloat::nan(Some(err));
            }

            break astro_float::macro_util::check_exponent_range(ret, emin, emax);
        }
    });

    ret.into()
}
