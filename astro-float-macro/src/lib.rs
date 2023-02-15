//! Macros for multiple precision floating point numbers library `astro-float`.
//! 
//! See main crate [docs](https://docs.rs/astro-float/latest/astro_float/).

mod util;

use astro_float::Exponent;
use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse::Parse, spanned::Spanned, BinOp, Error, Expr, ExprBinary, ExprCall, ExprGroup, ExprLit,
    ExprParen, ExprPath, ExprUnary, Lit, Token, UnOp,
};
use util::{check_arg_num, str_to_bigfloat_expr};

// Size of exponent in bits.
const EXPONENT_BIT_SIZE: usize = core::mem::size_of::<Exponent>() * 8;

// Speculative error estimation.
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

// Algorithm of error computation.
#[derive(Copy, Clone, Debug, PartialEq)]
enum ErrAlgo {
    None,
    Log,
    Log2,
    Pow,
    SinCos,
    Tan,
    AsinAcos,
}

fn traverse_binary(expr: &ExprBinary, err: &mut Vec<usize>) -> Result<TokenStream, Error> {
    let left_expr = traverse_expr(&expr.left, err)?;
    let right_expr = traverse_expr(&expr.right, err)?;

    let ts = match expr.op {
        BinOp::Add(_) => {
            quote!(astro_float::BigFloat::add(&(#left_expr), &(#right_expr), p_wrk, astro_float::RoundingMode::None))
        }
        BinOp::Sub(_) => {
            quote!(astro_float::BigFloat::sub(&(#left_expr), &(#right_expr), p_wrk, astro_float::RoundingMode::None))
        }
        BinOp::Mul(_) => {
            quote!(astro_float::BigFloat::mul(&(#left_expr), &(#right_expr), p_wrk, astro_float::RoundingMode::None))
        }
        BinOp::Div(_) => {
            quote!(astro_float::BigFloat::div(&(#left_expr), &(#right_expr), p_wrk, astro_float::RoundingMode::None))
        }
        BinOp::Rem(_) => quote!(astro_float::BigFloat::rem(&(#left_expr), &(#right_expr))),
        _ => return Err(Error::new(
            expr.span(),
            "unexpected binary operator. Only \"+\", \"-\", \"*\", \"/\", and \"%\" are allowed.",
        )),
    };

    err.push(1);

    Ok(ts)
}

fn one_arg_fun(
    fun: TokenStream,
    expr: &ExprCall,
    added_err: usize,
    err: &mut Vec<usize>,
) -> Result<TokenStream, Error> {
    check_arg_num(1, expr)?;
    let arg = traverse_expr(&expr.args[0], err)?;
    err.push(added_err);
    Ok(quote!(#fun(&(#arg), p_wrk, astro_float::RoundingMode::None)))
}

fn one_arg_fun_cc(
    fun: TokenStream,
    expr: &ExprCall,
    added_err: usize,
    err: &mut Vec<usize>,
    algo: ErrAlgo,
) -> Result<TokenStream, Error> {
    check_arg_num(1, expr)?;

    let arg = traverse_expr(&expr.args[0], err)?;

    let errs_id = err.len();

    if algo == ErrAlgo::Tan {
        // for tan check the returned value
        let ts = quote!({
            let arg = #arg;

            let ret = #fun(&arg, p_wrk, astro_float::RoundingMode::None, cc);

            if let Some(e) = ret.exponent() {
                let h = 2 * (e.unsigned_abs() as isize) - p as isize;
                if (errs[#errs_id] as isize) < h {
                    errs[#errs_id] = h as usize;
                    continue;
                }
            }

            ret
        });

        err.push(added_err);

        Ok(ts)
    } else {
        let errcheck = match algo {
            ErrAlgo::None => quote!(), // the error is constant
            ErrAlgo::Log => quote!({
                let newerr = compute_added_err_near_one(&arg, p_wrk) + 2;
                if errs[#errs_id] < newerr {
                    errs[#errs_id] = newerr;
                    continue;
                }
            }),
            ErrAlgo::SinCos => quote!({
                if let Some(e) = arg.exponent() {
                    if (errs[#errs_id] as isize) < (e as isize) {
                        errs[#errs_id] = e as usize;
                        continue;
                    }
                }
            }),
            ErrAlgo::AsinAcos => quote!({
                let newerr = compute_added_err_near_one(&arg, p_wrk) / 2;
                if errs[#errs_id] < newerr {
                    errs[#errs_id] = newerr;
                    continue;
                }
            }),
            _ => return Err(Error::new(expr.span(), "unexpected error in macro logic.")),
        };

        err.push(added_err);

        Ok(quote!({
            let arg = #arg;

            #errcheck

            #fun(&arg, p_wrk, astro_float::RoundingMode::None, cc)
        }))
    }
}

fn two_arg_fun_cc(
    fun: TokenStream,
    expr: &ExprCall,
    added_err: usize,
    err: &mut Vec<usize>,
    algo: ErrAlgo,
) -> Result<TokenStream, Error> {
    check_arg_num(2, expr)?;

    let arg1 = traverse_expr(&expr.args[0], err)?;
    let arg2 = traverse_expr(&expr.args[1], err)?;

    let errs_id = err.len();
    let errcheck = match algo {
        ErrAlgo::Log2 => quote!({
            let newerr1 = compute_added_err_near_one(&arg1, p_wrk);
            let newerr2 = compute_added_err_near_one(&arg2, p_wrk);
            let newerr = newerr1 + newerr2 + 2;
            if errs[#errs_id] < newerr {
                errs[#errs_id] = newerr;
                continue;
            }
        }),
        ErrAlgo::Pow => quote!({
            let mut newerr = EXPONENT_BIT_SIZE + 2;
            if let Some(en) = arg2.exponent() {
                if let Some(1 | 0) = arg1.exponent() {
                    if en > 0 {
                        let c = compute_added_err_near_one(&arg1, p_wrk);
                        if en as usize <= c + EXPONENT_BIT_SIZE {
                            newerr += en as usize;
                        } // result is zero or inf otherwise
                    }
                }
            }
            if errs[#errs_id] < newerr {
                errs[#errs_id] = newerr;
                continue;
            }
        }),
        _ => return Err(Error::new(expr.span(), "unexpected error in macro logic.")),
    };

    err.push(added_err);

    Ok(quote!({
        let arg1 = #arg1;
        let arg2 = #arg2;

        #errcheck

        #fun(&arg1, &arg2, p_wrk, astro_float::RoundingMode::None, cc)
    }))
}

fn traverse_call(expr: &ExprCall, err: &mut Vec<usize>) -> Result<TokenStream, Error> {
    let errmes = "unexpected function name. Only \"recip\", \"sqrt\", \"cbrt\", \"ln\", \"log2\", \"log10\", \"log\", \"exp\", \"pow\", \"sin\", \"cos\", \"tan\", \"asin\", \"acos\", \"atan\", \"sinh\", \"cosh\", \"tanh\", \"asinh\", \"acosh\", \"atanh\" are allowed.";

    if let Expr::Path(fun) = expr.func.as_ref() {
        if let Some(fname) = fun.path.get_ident() {
            let ts = match fname.to_string().as_str() {
                "recip" => one_arg_fun(quote!(astro_float::BigFloat::reciprocal), expr, 2, err),
                "sqrt" => one_arg_fun(quote!(astro_float::BigFloat::sqrt), expr, 1, err),
                "cbrt" => one_arg_fun(quote!(astro_float::BigFloat::cbrt), expr, 1, err),
                "ln" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::ln),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    ErrAlgo::Log,
                ),
                "log2" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::log2),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    ErrAlgo::Log,
                ),
                "log10" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::log10),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    ErrAlgo::Log,
                ),
                "log" => two_arg_fun_cc(
                    quote!(astro_float::BigFloat::log),
                    expr,
                    SPEC_ADD_ERR * 2,
                    err,
                    ErrAlgo::Log2,
                ),
                "exp" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::exp),
                    expr,
                    EXPONENT_BIT_SIZE,
                    err,
                    ErrAlgo::None,
                ),
                "pow" => two_arg_fun_cc(
                    quote!(astro_float::BigFloat::pow),
                    expr,
                    EXPONENT_BIT_SIZE + SPEC_ADD_ERR,
                    err,
                    ErrAlgo::Pow,
                ),
                "sin" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::sin),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    ErrAlgo::SinCos,
                ),
                "cos" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::cos),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    ErrAlgo::SinCos,
                ),
                "tan" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::tan),
                    expr,
                    2 * SPEC_ADD_ERR,
                    err,
                    ErrAlgo::Tan,
                ),
                "asin" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::asin),
                    expr,
                    SPEC_ADD_ERR / 2,
                    err,
                    ErrAlgo::AsinAcos,
                ),
                "acos" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::acos),
                    expr,
                    SPEC_ADD_ERR / 2,
                    err,
                    ErrAlgo::AsinAcos,
                ),
                "atan" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::atan),
                    expr,
                    1,
                    err,
                    ErrAlgo::None,
                ),
                "sinh" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::sinh),
                    expr,
                    EXPONENT_BIT_SIZE,
                    err,
                    ErrAlgo::None,
                ),
                "cosh" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::cosh),
                    expr,
                    EXPONENT_BIT_SIZE,
                    err,
                    ErrAlgo::None,
                ),
                "tanh" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::tanh),
                    expr,
                    1,
                    err,
                    ErrAlgo::None,
                ),
                "asinh" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::asinh),
                    expr,
                    2,
                    err,
                    ErrAlgo::None,
                ),
                "acosh" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::acosh),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    ErrAlgo::Log,
                ),
                "atanh" => one_arg_fun_cc(
                    quote!(astro_float::BigFloat::atanh),
                    expr,
                    SPEC_ADD_ERR,
                    err,
                    ErrAlgo::Log,
                ),
                _ => return Err(Error::new(expr.span(), errmes)),
            }?;

            return Ok(ts);
        }
    }
    Err(Error::new(expr.span(), errmes))
}

fn traverse_group(expr: &ExprGroup, err: &mut Vec<usize>) -> Result<TokenStream, Error> {
    traverse_expr(&expr.expr, err)
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

fn traverse_paren(expr: &ExprParen, err: &mut Vec<usize>) -> Result<TokenStream, Error> {
    traverse_expr(&expr.expr, err)
}

fn traverse_path(expr: &ExprPath) -> Result<TokenStream, Error> {
    Ok(
        quote!(astro_float::BigFloat::from_ext((#expr).clone(), p_wrk, astro_float::RoundingMode::None)),
    )
}

fn traverse_unary(expr: &ExprUnary, err: &mut Vec<usize>) -> Result<TokenStream, Error> {
    let op_expr = traverse_expr(&expr.expr, err)?;

    match expr.op {
        UnOp::Neg(_) => Ok(quote!(astro_float::BigFloat::neg(&(#op_expr)))),
        _ => Err(Error::new(
            expr.span(),
            "unexpected unary operator. Only \"-\" is allowed.",
        )),
    }
}

fn traverse_expr(expr: &Expr, err: &mut Vec<usize>) -> Result<TokenStream, Error> {
    match expr {
        Expr::Binary(e) => traverse_binary(e, err),
        Expr::Call(e) => traverse_call(e, err),
        Expr::Group(e) => traverse_group(e, err),
        Expr::Lit(e) => traverse_lit(e),
        Expr::Paren(e) => traverse_paren(e, err),
        Expr::Path(e) => traverse_path(e),
        Expr::Unary(e) => traverse_unary(e, err),
        _ => Err(Error::new(expr.span(), "unexpected expression. Only operators \"+\", \"-\", \"*\", \"/\", \"%\", functions \"recip\", \"sqrt\", \"cbrt\", \"ln\", \"log2\", \"log10\", \"log\", \"exp\", \"pow\", \"sin\", \"cos\", \"tan\", \"asin\", \"acos\", \"atan\", \"sinh\", \"cosh\", \"tanh\", \"asinh\", \"acosh\", \"atanh\", literals and variables, and grouping with parentheses are supported.")),
    }
}

/// Computes an expression with the specified precision and rounding mode.
/// 
/// The macro accepts an expression to compute and a context.
/// In the expression you can specify:
/// 
///  - Path expressions: variable names, constant names, etc.
///  - Integer literals, e.g. `123`, `-5`.
///  - Floating point literals, e.g. `1.234e-567`.
///  - String literals, e.g. `"-1.234_e-567"`.
///  - Binary operators.
///  - Unary `-` operator.
///  - Mathematical functions.
///  - Grouping with `(` and `)`.
/// 
/// Supported binary operators:
/// 
///  - `+`: addition.
///  - `-`: subtraction.
///  - `*`: multiplication.
///  - `/`: division.
///  - `%`: modular division.
/// 
/// Supported mathematical functions:
/// 
///  - `recip(x)`: reciprocal of `x`.
///  - `sqrt(x)`: square root of `x`.
///  - `cbrt(x)`: cube root of `x`.
///  - `ln(x)`: natural logarithm of `x`.
///  - `log2(x)`: logarithm base 2 of `x`.
///  - `log10(x)`: logarithm base 10 of `x`.
///  - `log(x, b)`: logarithm with base `b` of `x`.
///  - `exp(x)`: `e` to the power of `x`.
///  - `pow(b, x)`: `b` to the power of `x`.
///  - `sin(x)`: sine of `x`.
///  - `cos(x)`: cosine of `x`.
///  - `tan(x)`: tangent of `x`.
///  - `asin(x)`: arcsine of `x`.
///  - `acos(x)`: arccosine of `x`.
///  - `atan(x)`: arctangent of `x`.
///  - `sinh(x)`: hyperbolic sine of `x`.
///  - `cosh(x)`: hyperbolic cosine of `x`.
///  - `tanh(x)`: hyperbolic tangent of `x`.
///  - `asinh(x)`: hyperbolic arcsine of `x`.
///  - `acosh(x)`: hyperbolic arccosine of `x`.
///  - `atanh(x)`: hyperbolic arctangent of `x`.
/// 
/// The context determines the precision, the rounding mode of the result, and also contains the cache of constants.
/// Tuple `(usize, RoundingMode, &mut Consts)` can also be used as a temporary context (see example below).
/// 
/// The macro will determine additional precision needed to compensate error and perform correct rounding. 
/// It will also try to eliminate cancellation which may appear when expression is computed.
/// 
/// 
/// **Avoid passing expressions which contain mathematical identity if you need correctly rounded result**. 
/// 
/// Examples of such expressions:
/// 
///  - `expr!(sin(x) - sin(x), ctx)`
///  - `expr!(ln(exp(x)), ctx)`,
///  - `expr!(sin(x) * sin(x) / (1 - cos(x) * cos(x)), ctx)`,
/// 
/// Macro does not analyze the expression for presense of identity and will increase the precision infinitely and will never return.
/// 
/// Although, you can specify rounding mode `None`. In this case, macro will return even if you pass an identity expression.
/// 
/// ## Examples
/// 
/// ```
/// use astro_float_macro::expr;
/// use astro_float::RoundingMode;
/// use astro_float::Consts;
/// use astro_float::BigFloat;
/// use astro_float::ctx::Context;
/// 
/// // Precision, rounding mode, and constants cache.
/// let p = 128;
/// let rm = RoundingMode::Up;
/// let mut cc = Consts::new().expect("Failed to allocate constants cache");
/// 
/// // Create a context.
/// let mut ctx = Context::new(p, rm, cc);
/// 
/// let x = 123;
/// let y = "2345";
/// let z = 234.5e+1;
/// 
/// // Compute an expression.
/// let ret = expr!(x + y / z - ("120" - 120), &mut ctx);
/// 
/// assert_eq!(ret, BigFloat::from(124));
/// 
/// // Destructure context.
/// let (p, rm, mut cc) = ctx.to_raw_parts();
/// 
/// // Compute an expression using temporary context.
/// let ret = expr!(x + y / z, (p, rm, &mut cc));
/// 
/// assert_eq!(ret, BigFloat::from(124));
/// ```
#[proc_macro]
pub fn expr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let pmi = syn::parse_macro_input!(input as MacroInput);

    let MacroInput { expr, ctx } = pmi;

    let mut err = Vec::new();

    let expr = traverse_expr(&expr, &mut err).unwrap_or_else(|e| e.to_compile_error());

    let err_sz = err.len();

    let ret = quote!({
        use astro_float::FromExt;
        use astro_float::ctx::Contextable;

        const EXPONENT_BIT_SIZE: usize = core::mem::size_of::<astro_float::Exponent>() * 8;

        let mut ctx = &mut (#ctx);
        let p: usize = ctx.precision();
        let rm = ctx.rounding_mode();
        let cc = ctx.consts();

        let mut p_inc = astro_float::WORD_BIT_SIZE;
        let mut p_rnd = p + p_inc;
        let mut errs: [usize; #err_sz] = [#(#err, )*];

        fn compute_added_err_near_one(arg: &astro_float::BigFloat, p: usize) -> usize {
            let d: astro_float::BigFloat;
            if arg.is_zero() {
                return 0;
            }

            if let Some(arg_sign) = arg.sign() {
                let one = astro_float::BigFloat::from(arg_sign.to_int());

                if let Some(0) = arg.exponent() {
                    d = one.sub(&arg, p, astro_float::RoundingMode::None);
                } else if let Some(1) = arg.exponent() {
                    d = arg.sub(&one, p, astro_float::RoundingMode::None);
                } else {
                    return 0;
                }

                if d.is_zero() && d.inexact() {
                    return p;
                } else if let Some(e) = d.exponent() {
                    return (-e) as usize;
                }
            }

            return 0;
        }

        loop {
            let p_wrk = p_rnd.saturating_add(errs.iter().sum());

            let mut ret: astro_float::BigFloat = (#expr).into();

            if ret.inexact() {
                if ret.try_set_precision(p, rm, p_rnd) {
                    break ret;
                }
            } else {
                break ret;
            }

            p_rnd = p_rnd.saturating_add(p_inc);
            p_inc = (((p_rnd / 5).saturating_add(astro_float::WORD_BIT_SIZE - 1)) / astro_float::WORD_BIT_SIZE) * astro_float::WORD_BIT_SIZE;
        }
    });

    ret.into()
}
